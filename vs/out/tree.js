"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.lengthTree = lengthTree;
exports.leafGoals = leafGoals;
exports.extractScriptTree = extractScriptTree;
exports.applyEachTree = applyEachTree;
exports.applyAllTree = applyAllTree;
exports.applyNthTree = applyNthTree;
const print_1 = require("./print");
const syntax_1 = require("./syntax");
function makeSentence(atomic) {
    return { type: "one", body: { type: "opaque", atomic: atomic } };
}
function printError(e) {
    switch (e.type) {
        case "atomic_failure":
            return makeSentence(`Fail ${e.atomic}`);
        case "tactic_failure":
            return makeSentence(`Fail ${(0, print_1.untactic)(e.tactic)}`);
        case "out_of_fuel":
            return { type: "comment", body: "ran out of fuel" };
    }
}
function lengthTree(r) {
    switch (r.type) {
        case "hole":
            return 1;
        case "node":
            return r.children.map(lengthTree).reduce((a, b) => a + b, 0);
        case "failed":
            return 1;
        case "trace":
            return lengthTree(r.head);
    }
}
const admit = makeSentence("admit");
function leafGoals(r) {
    switch (r.type) {
        case "hole":
            return [r.goal];
        case "node":
            return r.children.map(leafGoals).flat(1);
        case "failed":
            return [r.goal];
        case "trace":
            return leafGoals(r.head);
    }
}
function failedTree(r) {
    switch (r.type) {
        case "hole":
            return false;
        case "node":
            return r.children.some(failedTree);
        case "failed":
            return true;
        case "trace":
            return failedTree(r.head);
    }
}
function extractScriptTree(r) {
    function loop(r) {
        switch (r.type) {
            case "hole":
                return [admit];
            case "node":
                const atomics = [];
                atomics.push(makeSentence(r.atomic));
                const branches = r.children.length > 1;
                for (const child of r.children) {
                    const catomics = loop(child);
                    branches
                        ? atomics.push({ type: "focus", block: catomics })
                        : atomics.push.apply(atomics, catomics);
                }
                return atomics;
            case "failed":
                return [printError(r.error), admit];
            case "trace":
                const commented = failedTree(r.head)
                    ? r.trace
                        .slice()
                        .reverse()
                        .map((r_) => ({
                        type: "comment",
                        body: "tried and failed to run: " + (0, print_1.unscript)(prettyTrace(r_)),
                    }))
                        .flat(1)
                    : [];
                return [...commented, ...loop(r.head)];
        }
    }
    function prettyTrace(r) {
        switch (r.type) {
            case "node":
                return [makeSentence(r.atomic), ...r.children.map(prettyTrace).flat(1)];
            case "hole":
                return [];
            case "failed":
                if (r.error.type === "out_of_fuel") {
                    return [];
                }
                else if (r.error.type === "atomic_failure") {
                    return [makeSentence(r.error.atomic)];
                }
                else {
                    return [{ type: "one", body: r.error.tactic }];
                }
            case "trace":
                const commented = r.trace
                    .slice()
                    .reverse()
                    .map(prettyTrace)
                    .flat(1);
                return [...commented, ...prettyTrace(r.head)];
        }
    }
    return loop(r);
}
async function applyEachTree(fs, r) {
    async function aux(fs, r) {
        switch (r.type) {
            case "hole":
                return (await fs[0](r.goal)).fmap((r_) => [fs.slice(1), r_]);
            case "node":
                return (await aux_list(fs, r.children)).fmap(([fs_, rs_]) => [
                    fs_,
                    { ...r, children: rs_ },
                ]);
            case "failed":
                return (0, syntax_1.pure)([fs.slice(1), r]);
            case "trace":
                return (await aux(fs, r.head)).fmap(([fs_, r_]) => [
                    fs_,
                    { ...r, head: r_ },
                ]);
        }
    }
    async function aux_list(fs, rs) {
        if (rs.length === 0) {
            return (0, syntax_1.pure)([fs, rs]);
        }
        return (await aux(fs, rs[0])).bindA(async ([fs_, r_]) => (await aux_list(fs_, rs.slice(1))).bindA(async ([fs__, rs__]) => (0, syntax_1.pure)([fs__, [r_, ...rs__]])));
    }
    return (await aux(fs, r)).fmap((fsr) => fsr[1]);
}
async function applyAllTree(f, r) {
    const fs = Array(lengthTree(r)).fill(f);
    return applyEachTree(fs, r);
}
async function applyNthTree(f, n, r) {
    const treeid = (g) => (0, syntax_1.pure)({
        type: "hole",
        goal: g,
    });
    const fs = [
        ...Array(n - 1).fill(treeid),
        f,
        ...Array(lengthTree(r) - n).fill(treeid),
    ];
    return applyEachTree(fs, r);
}
//# sourceMappingURL=tree.js.map