"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.parse = parse;
exports.parseTactic = parseTactic;
const antlr4_1 = require("antlr4");
const ScriptLexer_1 = require("./script-parser/ScriptLexer");
const ScriptParser_1 = require("./script-parser/ScriptParser");
const ScriptVisitor_1 = require("./script-parser/ScriptVisitor");
class MyScriptVisitor extends ScriptVisitor_1.default {
    locFinder;
    constructor(locFinder) {
        super();
        this.locFinder = locFinder;
    }
    visitScript(ctx) {
        const result = [];
        const scripts = [result];
        const visitor = new MySentenceVisitor(this.locFinder, scripts);
        ctx.sentence_list().map((s) => visitor.visit(s));
        return result;
    }
}
class MySentenceVisitor extends ScriptVisitor_1.SentenceVisitor {
    locFinder;
    scripts;
    bullets;
    constructor(locFinder, scripts) {
        super();
        this.locFinder = locFinder;
        this.scripts = scripts;
        this.bullets = [];
    }
    visitOne(ctx) {
        this.scripts[0].push({
            type: "one",
            body: new MyTacticVisitor(this.locFinder).visit(ctx.stactic()),
        });
    }
    visitNth(ctx) {
        const nth = ctx.NTH().getText();
        this.scripts[0].push({
            type: "nth",
            n: +nth.substring(0, nth.indexOf(":")),
            body: new MyTacticVisitor(this.locFinder).visit(ctx.stactic()),
        });
    }
    visitAll(ctx) {
        this.scripts[0].push({
            type: "all",
            body: new MyTacticVisitor(this.locFinder).visit(ctx.stactic()),
        });
    }
    visitLBrace(ctx) {
        this.focus();
    }
    visitRBrace(ctx) {
        this.unfocus();
    }
    visitBullet(ctx) {
        const bullet = ctx.BULLET().getText();
        for (let i = 0; i < this.bullets.length; i++) {
            if (bullet === this.bullets[i]) {
                for (let j = i; j < this.bullets.length; j++) {
                    this.unfocus();
                }
                this.bullets = this.bullets.slice(0, i);
            }
        }
        this.bullets.push(bullet);
        this.focus();
    }
    visitComment(ctx) {
        const text = ctx.COMMENT().getText();
        const start = text.indexOf("*");
        const end = text.lastIndexOf("*");
        this.scripts[0].push({
            type: "comment",
            body: text.substring(start + 1, end).trim(),
        });
    }
    focus() {
        const block = [];
        this.scripts[0].push({ type: "focus", block: block });
        this.scripts.unshift(block);
    }
    unfocus() {
        this.scripts.shift();
    }
}
class MyTacticVisitor extends ScriptVisitor_1.TacticVisitor {
    locFinder;
    constructor(locFinder) {
        super();
        this.locFinder = locFinder;
    }
    visitSemicolon(ctx) {
        const left = this.visit(ctx.stactic());
        const loc = this.locFinder(ctx.start.line, ctx.start.column) +
            ctx.stactic().getText().length;
        return {
            type: "semicolon",
            left: left,
            right: this.visit(ctx.tactic()),
            loc: loc,
        };
    }
    visitSemicolonMany(ctx) {
        const left = this.visit(ctx.stactic());
        const loc = this.locFinder(ctx.start.line, ctx.start.column) +
            ctx.stactic().getText().length;
        return {
            type: "dispatch",
            left: left,
            right: new MyBracketVisitor(this).visit(ctx.bracket()),
            loc: loc,
        };
    }
    visitGeneral(ctx) {
        return this.visit(ctx.tactic());
    }
    visitFirst(ctx) {
        const loc = this.locFinder(ctx.start.line, ctx.start.column);
        return {
            type: "first",
            body: new MyBracketVisitor(this).visit(ctx.bracket()),
            loc: loc,
        };
    }
    visitProgress(ctx) {
        const loc = this.locFinder(ctx.start.line, ctx.start.column);
        return {
            type: "progress",
            body: this.visit(ctx.tactic()),
            loc: loc,
        };
    }
    visitTry(ctx) {
        const loc = this.locFinder(ctx.start.line, ctx.start.column);
        return {
            type: "try",
            body: this.visit(ctx.tactic()),
            loc: loc,
        };
    }
    visitRepeat(ctx) {
        const loc = this.locFinder(ctx.start.line, ctx.start.column);
        return {
            type: "repeat",
            body: this.visit(ctx.tactic()),
            loc: loc,
        };
    }
    visitMatch(ctx) {
        const lhs = ctx
            .CASE_list()
            .map((c) => /\| (.+?) =>/g.exec(c.getText())[1]);
        const rhs = ctx.tactic_list().map((t) => this.visit(t));
        return {
            type: "match",
            branches: lhs.map(function (e, i) {
                return [e, rhs[i]];
            }),
        };
    }
    visitAuto(ctx) {
        const loc = this.locFinder(ctx.start.line, ctx.start.column);
        const txt = ctx.getText().trim();
        if (txt === "auto") {
            return { type: "auto", loc: loc };
        }
        else {
            return { type: "eauto", loc: loc };
        }
    }
    visitFail(ctx) {
        return { type: "opaque", atomic: ctx.getText() };
    }
    visitOpaque(ctx) {
        const loc = this.locFinder(ctx.start.line, ctx.start.column);
        return {
            type: "opaque",
            atomic: ctx.getText().trim(),
            loc: loc,
        };
    }
    visitParen(ctx) {
        return this.visit(ctx.stactic());
    }
}
function getParser(s) {
    const chars = new antlr4_1.CharStream(s);
    const lexer = new ScriptLexer_1.default(chars);
    const tokens = new antlr4_1.CommonTokenStream(lexer);
    return new ScriptParser_1.default(tokens);
}
function parse(s) {
    return new MyScriptVisitor(getLocFinder(s)).visit(getParser(s).script());
}
function parseTactic(s) {
    return new MyTacticVisitor(getLocFinder(s)).visit(getParser(s).tactic());
}
class MyBracketVisitor extends ScriptVisitor_1.BracketVisitor {
    tvisitor;
    constructor(tvisitor) {
        super();
        this.tvisitor = tvisitor;
    }
    visitBracket(ctx) {
        function isBracket(s) {
            return s === "[" || s === "]";
        }
        function isBar(s) {
            return s === "|";
        }
        const count = ctx.getChildCount();
        const body = [];
        for (let i = 0; i < count; i++) {
            const child = ctx.getChild(i);
            const text = child.getText().trim();
            if (isBracket(text)) {
            }
            else if (isBar(text)) {
                if (body.length === 0) {
                    body.push({ type: "empty" });
                }
                const next = ctx
                    .getChild(i + 1)
                    .getText()
                    .trim();
                if (isBracket(next) || isBar(next)) {
                    body.push({ type: "empty" });
                }
            }
            else {
                body.push(this.tvisitor.visit(child));
            }
        }
        return body;
    }
}
function getLocFinder(s) {
    const lines = s.split("\n").map((l) => l.length);
    return (line, column) => {
        const offset = lines.slice(0, line - 1).reduce((a, b) => a + b, line - 1);
        return offset + column;
    };
}
//# sourceMappingURL=parse.js.map