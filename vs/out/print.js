"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.untactic = untactic;
exports.unsentence = unsentence;
exports.unscript = unscript;
function untactic(tactic) {
    function f(tactic) {
        switch (tactic.type) {
            case "opaque":
                return tactic.atomic;
            case "semicolon":
                return (f(tactic.left) +
                    " ; " +
                    (tactic.right.type === "dispatch"
                        ? `( ${f(tactic.right)} )`
                        : f(tactic.right)));
            case "dispatch":
                return (f(tactic.left) + " ; " + `[ ${tactic.right.map(f).join(" | ")} ]`);
            case "first":
                return "first " + `[ ${tactic.body.map(f).join(" | ")} ]`;
            case "try":
                return "try " + paren(tactic.body);
            case "progress":
                return "progress " + paren(tactic.body);
            case "repeat":
                return "repeat " + paren(tactic.body);
            case "match":
                const lines = ["match goal with"];
                for (const branch of tactic.branches) {
                    lines.push(`| ${branch[0]} => ${paren(branch[1])}`);
                }
                lines.push("end");
                return lines.join("\n");
            case "auto":
            case "eauto":
                return tactic.type;
            default:
                return "";
        }
    }
    function paren(t) {
        var simpl;
        switch (t.type) {
            case "opaque":
            case "auto":
            case "empty":
                simpl = true;
                break;
            default:
                simpl = false;
        }
        return simpl ? f(t) : "( " + f(t) + " )";
    }
    return f(tactic);
}
function unsentence(sentence) {
    switch (sentence.type) {
        case "one":
            return untactic(sentence.body) + ".";
        case "nth":
            return `${sentence.n}: ` + untactic(sentence.body) + ".";
        case "all":
            return "all: " + untactic(sentence.body) + ".";
    }
}
function unscript(script) {
    var startoffocus = true;
    function loop(script, indent) {
        if (!script.length) {
            return "";
        }
        const head = script[0];
        const tail = script.slice(1);
        const bullets = ["-", "+", "*"];
        let result;
        switch (head.type) {
            case "focus":
                startoffocus = true;
                result = "\n" + "  ".repeat(indent);
                result += bullets[(indent - 1) % 3].repeat(Math.ceil(indent / 3)) + " ";
                result += loop(head.block, indent + 1);
                break;
            case "comment":
                result = "";
                if (!startoffocus) {
                    result += "\n" + "  ".repeat(indent);
                }
                result += "(* " + head.body + " *)";
                result += "\n" + "  ".repeat(indent);
                break;
            default:
                startoffocus = false;
                result = unsentence(head) + " ";
                break;
        }
        return result + loop(tail, indent);
    }
    return loop(script, 1);
}
//# sourceMappingURL=print.js.map