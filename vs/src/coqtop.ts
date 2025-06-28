import { ChildProcessWithoutNullStreams, spawn } from "child_process";
import * as readline from "node:readline";
import { Match, Script, Tactic, atomic } from "./syntax";
import { untactic } from "./print";
import { parse, parseTactic } from "./parse";
import * as vscode from "vscode";

// We implement run-atomic (for now) by calling into [coqtop].

class Coqtop {
  stream: ChildProcessWithoutNullStreams;
  rl: AsyncIterableIterator<string>;

  constructor(path: string) {
    this.stream = spawn(path, ["-emacs", "2>&1"], { shell: true });
    this.rl = readline
      .createInterface({
        input: this.stream.stdout,
        output: this.stream.stdin,
      })
      [Symbol.asyncIterator]();
  }

  write(command: string) {
    function chunk(s: string, n: number): string[] {
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

  async line(): Promise<string> {
    const line = (await this.rl.next()).value;
    // console.log(line);
    return line;
  }

  async readUntil(stops: string[]): Promise<[string, string]> {
    let lines = "";
    while (true) {
      const line = await this.line();
      const end = stops.find((s) => line.includes(s));
      if (end) {
        return [lines, end];
      } else {
        lines += " " + line;
      }
    }
  }
}

export type goal = [number, string];

class Goals {
  // 1-indexed, to be consistent with n: selectors
  goals: goal[];

  constructor(goals: goal[]) {
    this.goals = [...goals];
  }

  get(n: number): goal {
    return this.goals[n - 1];
  }

  indexOf(goal: goal): number {
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

  diff(orig: goal, gs: Goals) {
    return this.goals.filter(
      (g) => g === orig || !gs.goals.map(([id, _]) => id).includes(g[0])
    );
  }
}

export class DeautoCoqtop extends Coqtop {
  private goals!: Goals;
  private end = "endcommand";
  private ends = [
    this.end,
    "No more goals.",
    "This subproof is complete",
    "You need to go back and solve them.",
  ];
  private undos!: number;
  private saved!: Goals;

  constructor(path: string, prelude: string) {
    super(path);
    this.write(prelude);
  }

  write(command: string) {
    super.write(command);
    super.write(`idtac "${this.end}".`);
  }

  async init(): Promise<goal> {
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

  async runAtomic(a: atomic, goal: goal): Promise<goal[] | number> {
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

  private async writeAtN(
    a: atomic,
    n: number
  ): Promise<[string, goal[] | number]> {
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
      } else {
        return [out, 0];
      }
    } else {
      this.undos += end === this.end ? 2 : 1;
    }

    this.updateGoals([out, end]);
    return [out, this.goals.diff(olds.get(n), olds)];
  }

  private updateGoals([out, end]: [string, string]) {
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

    const contents = [parts[0].split(/\(ID \d+\)/g)[1], ...parts.slice(1)].map(
      (s) => s.trim()
    );

    this.goals = new Goals(ids.map((elem, idx) => [elem, contents[idx]]));
  }

  async generateMatches(t: Match, goal: goal): Promise<Tactic> {
    function printMsgAndFail(msg: string): Tactic {
      return { type: "opaque", atomic: `idtac "${msg}"; fail` };
    }

    const tests: [string, Tactic][] = [];
    for (let i = 0; i < t.branches.length; i++) {
      tests.push([t.branches[i][0], printMsgAndFail(`matched-with-${i}`)]);
    }
    tests.push(["_", printMsgAndFail("end match")]);

    const testMatch: Tactic = {
      type: "match",
      branches: tests,
    };

    super.write(
      `${this.goals.indexOf(goal)}: { Fail (${untactic(testMatch).replaceAll(
        "\n",
        " "
      )}).`
    );
    const [out, _] = await this.readUntil(["end match"]);
    const branchNums = [...out.matchAll(/matched-with-([0-9]+)/g)].map(
      (m) => +m[1]
    );

    super.write(`Undo 2.`);

    return {
      type: "first",
      body: branchNums.map((i) => t.branches[i][1]),
    };
  }

  async writeAuto(autotext : string, goal: goal): Promise<Script> {
    const n = this.goals.indexOf(goal);
    const endauto = "endauto";
    const a = `info_${autotext}; idtac "${endauto}"`;

    const [out, _] = await this.writeAtN(a, n);

    const startauto = `(* info ${autotext}: *)`;
    const info = out
      .substring(
        out.indexOf(startauto) + startauto.length,
        out.indexOf("<infomsg>" + endauto)
      )
      .replaceAll("Logic.", "")
      .replaceAll("(in core)", "");

    if (this.goals.length === 0) {
      await this.readUntil(["No such goal."]);
    }

    return parse(info);
  }
}

export class LookupCoqtop extends Coqtop {
  constructor(path: string, prelude: string) {
    super(path);
    this.write(prelude);
  }

  async lookup(name: string): Promise<[string, Tactic]> {
    this.write(`Print Ltac ${name}.`);
    const stop = "stopprint";
    this.write(
      `Definition ${name}_temp : unit := ltac:(idtac "${stop}"; exact tt).`
    );
    let lhs = `Ltac ${name}`;
    let [out, _] = await this.readUntil([stop]);
    out = out.substring(out.indexOf(lhs) + lhs.length);

    const defeq = ":=";
    lhs += out.split(defeq)[0] + defeq;

    let rhs = out.split(defeq)[1];
    rhs = untactic(parseTactic(rhs.trim())); // pretty-print
    return [lhs.trim(), parseTactic(rhs)];
  }
}

export class TrialCoqtop extends Coqtop {
  async attempt() {
    // check if coqtop path is working
    const init = await this.line();
    if (!init.includes("Welcome")) {
      vscode.window.showErrorMessage("Error starting coqtop. " + init);
    }
  }
}
