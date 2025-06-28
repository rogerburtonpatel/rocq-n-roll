"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.TrialCoqtop = exports.LookupCoqtop = exports.DeautoCoqtop = void 0;
const child_process_1 = require("child_process");
const readline = require("node:readline");
const print_1 = require("./print");
const parse_1 = require("./parse");
const vscode = require("vscode");
// We implement run-atomic (for now) by calling into [coqtop].
class Coqtop {
    stream;
    rl;
    constructor(path) {
        this.stream = (0, child_process_1.spawn)(path, ["-emacs", "2>&1"], { shell: true });
        this.rl = readline
            .createInterface({
            input: this.stream.stdout,
            output: this.stream.stdin,
        })[Symbol.asyncIterator]();
    }
    write(command) {
        function chunk(s, n) {
            if (s.length < n) {
                return [s];
            }
            const dot = /\.\s(?!.*\.\s)/g;
            const lastDot = s.search(dot) + 1;
            const rest = chunk(s.slice(lastDot + 1), n);
            rest.unshift(s.slice(0, lastDot));
            return rest;
        }
        for (const c of chunk(command, 1000)) {
            // console.log(c);
            this.stream.stdin.write(c + "\n");
        }
    }
    async line() {
        const line = (await this.rl.next()).value;
        // console.log(line);
        return line;
    }
    async readUntil(stops) {
        let lines = "";
        while (true) {
            const line = await this.line();
            const end = stops.find((s) => line.includes(s));
            if (end) {
                return [lines, end];
            }
            else {
                lines += " " + line;
            }
        }
    }
}
class Goals {
    // 1-indexed, to be consistent with n: selectors
    goals;
    constructor(goals) {
        this.goals = [...goals];
    }
    get(n) {
        return this.goals[n - 1];
    }
    indexOf(goal) {
        const idx = this.goals.findIndex((g) => g[0] === goal[0]) + 1;
        if (idx < 1) {
            throw new Error("invalid goal id");
        }
        return idx;
    }
    get length() {
        return this.goals.length;
    }
    [Symbol.iterator]() {
        return this.goals[Symbol.iterator]();
    }
    diff(orig, gs) {
        return this.goals.filter((g) => g === orig || !gs.goals.map(([id, _]) => id).includes(g[0]));
    }
}
class DeautoCoqtop extends Coqtop {
    goals;
    end = "endcommand";
    ends = [
        this.end,
        "No more goals.",
        "This subproof is complete",
        "You need to go back and solve them.",
    ];
    undos;
    saved;
    constructor(path, prelude) {
        super(path);
        this.write(prelude);
    }
    write(command) {
        super.write(command);
        super.write(`idtac "${this.end}".`);
    }
    async init() {
        // consume the prelude
        await this.readUntil([this.end]);
        // show the goals
        this.write("Show.");
        this.updateGoals(await this.readUntil(this.ends));
        if (this.goals.length !== 1) {
            throw new Error("initializion error");
        }
        return this.goals.get(1);
    }
    async runAtomic(a, goal) {
        const [_, result] = await this.writeAtN(a, this.goals.indexOf(goal));
        return result;
    }
    mark() {
        this.undos = 0;
        this.saved = this.goals;
    }
    async undo() {
        this.write(`Undo ${this.undos}.`);
        await this.readUntil([this.end]);
        this.goals = this.saved;
    }
    async writeAtN(a, n) {
        const olds = this.goals;
        this.write(`${n}: ${a}.`);
        const [out, end] = await this.readUntil(this.ends);
        if (out.includes("Error:")) {
            this.undos += 1;
            const re = /\(level (\d+)\)/g;
            const match = re.exec(out);
            if (match !== null) {
                // failure level > 0
                return [out, +match[1]];
            }
            else {
                return [out, 0];
            }
        }
        else {
            this.undos += end === this.end ? 2 : 1;
        }
        this.updateGoals([out, end]);
        return [out, this.goals.diff(olds.get(n), olds)];
    }
    updateGoals([out, end]) {
        if (end !== this.end) {
            // goals were solved
            this.goals = new Goals([]);
            return;
        }
        const re = /\(ID (\d+)\)/g;
        let match;
        const ids = [];
        while ((match = re.exec(out)) !== null) {
            ids.push(+match[1]);
        }
        const parts = out.split(/goal .+? is:/g);
        // sometimes coqtop returns no output if no change
        if (parts.length === 1 && !parts[0].includes("ID")) {
            return;
        }
        const contents = [parts[0].split(/\(ID \d+\)/g)[1], ...parts.slice(1)].map((s) => s.trim());
        this.goals = new Goals(ids.map((elem, idx) => [elem, contents[idx]]));
    }
    async generateMatches(t, goal) {
        function printMsgAndFail(msg) {
            return { type: "opaque", atomic: `idtac "${msg}"; fail` };
        }
        const tests = [];
        for (let i = 0; i < t.branches.length; i++) {
            tests.push([t.branches[i][0], printMsgAndFail(`matched-with-${i}`)]);
        }
        tests.push(["_", printMsgAndFail("end match")]);
        const testMatch = {
            type: "match",
            branches: tests,
        };
        super.write(`${this.goals.indexOf(goal)}: { Fail (${(0, print_1.untactic)(testMatch).replaceAll("\n", " ")}).`);
        const [out, _] = await this.readUntil(["end match"]);
        const branchNums = [...out.matchAll(/matched-with-([0-9]+)/g)].map((m) => +m[1]);
        super.write(`Undo 2.`);
        return {
            type: "first",
            body: branchNums.map((i) => t.branches[i][1]),
        };
    }
    async writeAuto(autotext, goal) {
        const n = this.goals.indexOf(goal);
        const endauto = "endauto";
        const a = `info_${autotext}; idtac "${endauto}"`;
        const [out, _] = await this.writeAtN(a, n);
        const startauto = `(* info ${autotext}: *)`;
        const info = out
            .substring(out.indexOf(startauto) + startauto.length, out.indexOf("<infomsg>" + endauto))
            .replaceAll("Logic.", "")
            .replaceAll("(in core)", "");
        if (this.goals.length === 0) {
            await this.readUntil(["No such goal."]);
        }
        return (0, parse_1.parse)(info);
    }
}
exports.DeautoCoqtop = DeautoCoqtop;
class LookupCoqtop extends Coqtop {
    constructor(path, prelude) {
        super(path);
        this.write(prelude);
    }
    async lookup(name) {
        this.write(`Print Ltac ${name}.`);
        const stop = "stopprint";
        this.write(`Definition ${name}_temp : unit := ltac:(idtac "${stop}"; exact tt).`);
        let lhs = `Ltac ${name}`;
        let [out, _] = await this.readUntil([stop]);
        out = out.substring(out.indexOf(lhs) + lhs.length);
        const defeq = ":=";
        lhs += out.split(defeq)[0] + defeq;
        let rhs = out.split(defeq)[1];
        rhs = (0, print_1.untactic)((0, parse_1.parseTactic)(rhs.trim())); // pretty-print
        return [lhs.trim(), (0, parse_1.parseTactic)(rhs)];
    }
}
exports.LookupCoqtop = LookupCoqtop;
class TrialCoqtop extends Coqtop {
    async attempt() {
        // check if coqtop path is working
        const init = await this.line();
        if (!init.includes("Welcome")) {
            vscode.window.showErrorMessage("Error starting coqtop. " + init);
        }
    }
}
exports.TrialCoqtop = TrialCoqtop;
//# sourceMappingURL=coqtop.js.map