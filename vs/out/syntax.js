"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.No = exports.Yes = exports.Result = void 0;
exports.pure = pure;
exports.subst = subst;
class Result {
    fmap(func) {
        return this.bind((t) => pure(func(t)));
    }
    bind(func) {
        throw new Error("abstract");
    }
    async bindA(func) {
        throw new Error("abstract");
    }
    failed() {
        throw new Error("abstract");
    }
}
exports.Result = Result;
class Yes extends Result {
    t;
    level;
    constructor(t, level) {
        super();
        this.t = t;
        this.level = level;
    }
    transform(mu) {
        if (mu instanceof No) {
            return mu;
        }
        else {
            const yu = mu;
            const level = this.level === null ? yu.level : this.level;
            return new Yes(yu.t, level);
        }
    }
    bind(func) {
        const mu = func(this.t);
        return this.transform(mu);
    }
    async bindA(func) {
        const mu = await func(this.t);
        return this.transform(mu);
    }
    failed() {
        return this.level !== null;
    }
    decr() {
        if (this.level !== null) {
            return Math.max(this.level - 1, 0);
        }
        else {
            return this.level;
        }
    }
}
exports.Yes = Yes;
class No extends Result {
    level;
    constructor(level) {
        super();
        this.level = level;
    }
    bind(func) {
        return new No(this.level);
    }
    async bindA(func) {
        return new No(this.level);
    }
    failed() {
        return true;
    }
}
exports.No = No;
function pure(t) {
    return new Yes(t, null);
}
function subst(x, t1, t2) {
    switch (t1.type) {
        case "tvar":
            if (x === t1) {
                return t2;
            }
            else {
                return t1;
            }
        case "semicolon":
            return {
                ...t1,
                left: subst(x, t1.left, t2),
                right: subst(x, t1.right, t2),
            };
        case "dispatch":
            return {
                ...t1,
                left: subst(x, t1.left, t2),
                right: t1.right.map((t) => subst(x, t, t2)),
            };
        case "first":
            return {
                ...t1,
                body: t1.body.map((t) => subst(x, t, t2)),
            };
        case "fix":
            if (x === t1.binder) {
                return t1;
            }
            else {
                return { ...t1, body: subst(x, t1.body, t2) };
            }
        case "progress":
        case "try":
        case "repeat":
            return { ...t1, body: subst(x, t1.body, t2) };
        case "match":
            return {
                ...t1,
                branches: t1.branches.map((b) => [b[0], subst(x, b[1], t2)]),
            };
        case "opaque":
        case "empty":
        case "auto":
        case "eauto":
            return t1;
    }
}
//# sourceMappingURL=syntax.js.map