"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.slice = slice;
exports.makeOpaque = makeOpaque;
exports.mapScript = mapScript;
const print_1 = require("./print");
function slice(script) {
    function loop(t, slices) {
        switch (t.type) {
            case "semicolon":
                loop(t.left, slices);
                slices.push({ start: t.loc, end: t.loc + 1 });
                loop(t.right, slices);
                break;
            case "dispatch":
                loop(t.left, slices);
                slices.push({ start: t.loc, end: t.loc + 1 });
                for (const r of t.right) {
                    loop(r, slices);
                }
                break;
            case "first":
                slices.push({ start: t.loc, end: t.loc + 5 });
                for (const r of t.body) {
                    loop(r, slices);
                }
                break;
            case "progress":
            case "try":
            case "repeat":
                slices.push({ start: t.loc, end: t.loc + t.type.length });
                loop(t.body, slices);
                break;
            case "auto":
            case "eauto":
                slices.push({ start: t.loc, end: t.loc + t.type.length });
                break;
        }
    }
    const slices = [];
    mapScript((sentence) => {
        loop(sentence.body, slices);
        return sentence;
    }, script);
    return slices;
}
// support partial deautomation by making deselected constructs opaque
function makeOpaque(script, grays) {
    function opaquify(t) {
        return { type: "opaque", atomic: (0, print_1.untactic)(t) };
    }
    function loop(t) {
        switch (t.type) {
            case "semicolon":
                if (grays.includes(t.loc)) {
                    return opaquify(t);
                }
                else {
                    return { ...t, left: loop(t.left), right: loop(t.right) };
                }
            case "dispatch":
                if (grays.includes(t.loc)) {
                    return opaquify(t);
                }
                else {
                    return { ...t, left: loop(t.left), right: t.right.map(loop) };
                }
            case "first":
                if (grays.includes(t.loc)) {
                    return opaquify(t);
                }
                return { ...t, body: t.body.map(loop) };
            case "progress":
            case "try":
            case "repeat":
                if (grays.includes(t.loc)) {
                    return opaquify(t);
                }
                return { ...t, body: loop(t.body) };
            case "auto":
            case "eauto":
                if (grays.includes(t.loc)) {
                    return opaquify(t);
                }
                return t;
            default:
                return t;
        }
    }
    return mapScript((sentence) => ({ ...sentence, body: loop(sentence.body) }), script);
}
function mapScript(f, script) {
    if (!script.length) {
        return script;
    }
    const head = script[0];
    const tail = script.slice(1);
    switch (head.type) {
        case "focus":
            return [
                { ...head, block: mapScript(f, head.block) },
                ...mapScript(f, tail),
            ];
        case "comment":
            return mapScript(f, tail);
        default:
            return [f(head), ...mapScript(f, tail)];
    }
}
//# sourceMappingURL=partial.js.map