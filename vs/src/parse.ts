import { CharStream, CommonTokenStream } from "antlr4";
import ScriptLexer from "./script-parser/ScriptLexer";
import ScriptParser, {
  AllContext,
  AutoContext,
  OneContext,
  OpaqueContext,
  ParenContext,
  LBraceContext,
  RBraceContext,
  ScriptContext,
  SemicolonContext,
  BracketContext,
  SemicolonManyContext,
  FirstContext,
  CommentContext,
  TryContext,
  ProgressContext,
  GeneralContext,
  FailContext,
  RepeatContext,
  MatchContext,
  NthContext,
  BulletContext,
} from "./script-parser/ScriptParser";
import ScriptVisitor, {
  BracketVisitor,
  SentenceVisitor,
  TacticVisitor,
} from "./script-parser/ScriptVisitor";
import { Script, Tactic } from "./syntax";

class MyScriptVisitor extends ScriptVisitor<Script> {
  locFinder: (line: number, column: number) => number;

  constructor(locFinder: (line: number, column: number) => number) {
    super();
    this.locFinder = locFinder;
  }

  visitScript(ctx: ScriptContext): Script {
    const result: Script = [];
    const scripts: Script[] = [result];
    const visitor = new MySentenceVisitor(this.locFinder, scripts);
    ctx.sentence_list().map((s) => visitor.visit(s));
    return result;
  }
}

class MySentenceVisitor extends SentenceVisitor<void> {
  locFinder: (line: number, column: number) => number;
  scripts: Script[];
  bullets: string[];

  constructor(
    locFinder: (line: number, column: number) => number,
    scripts: Script[]
  ) {
    super();
    this.locFinder = locFinder;
    this.scripts = scripts;
    this.bullets = [];
  }

  visitOne(ctx: OneContext) {
    this.scripts[0].push({
      type: "one",
      body: new MyTacticVisitor(this.locFinder).visit(ctx.stactic()),
    });
  }

  visitNth(ctx: NthContext) {
    const nth = ctx.NTH().getText();
    this.scripts[0].push({
      type: "nth",
      n: +nth.substring(0, nth.indexOf(":")),
      body: new MyTacticVisitor(this.locFinder).visit(ctx.stactic()),
    });
  }

  visitAll(ctx: AllContext) {
    this.scripts[0].push({
      type: "all",
      body: new MyTacticVisitor(this.locFinder).visit(ctx.stactic()),
    });
  }

  visitLBrace(ctx: LBraceContext) {
    this.focus();
  }

  visitRBrace(ctx: RBraceContext) {
    this.unfocus();
  }

  visitBullet(ctx: BulletContext) {
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

  visitComment(ctx: CommentContext) {
    const text = ctx.COMMENT().getText();
    const start = text.indexOf("*");
    const end = text.lastIndexOf("*");
    this.scripts[0].push({
      type: "comment",
      body: text.substring(start + 1, end).trim(),
    });
  }

  focus() {
    const block: Script = [];
    this.scripts[0].push({ type: "focus", block: block });
    this.scripts.unshift(block);
  }

  unfocus() {
    this.scripts.shift();
  }
}

class MyTacticVisitor extends TacticVisitor<Tactic> {
  locFinder: (line: number, column: number) => number;

  constructor(locFinder: (line: number, column: number) => number) {
    super();
    this.locFinder = locFinder;
  }

  visitSemicolon(ctx: SemicolonContext): Tactic {
    const left = this.visit(ctx.stactic());
    const loc =
      this.locFinder(ctx.start.line, ctx.start.column) +
      ctx.stactic().getText().length;
    return {
      type: "semicolon",
      left: left,
      right: this.visit(ctx.tactic()),
      loc: loc,
    };
  }

  visitSemicolonMany(ctx: SemicolonManyContext): Tactic {
    const left = this.visit(ctx.stactic());
    const loc =
      this.locFinder(ctx.start.line, ctx.start.column) +
      ctx.stactic().getText().length;
    return {
      type: "dispatch",
      left: left,
      right: new MyBracketVisitor(this).visit(ctx.bracket()),
      loc: loc,
    };
  }

  visitGeneral(ctx: GeneralContext): Tactic {
    return this.visit(ctx.tactic());
  }

  visitFirst(ctx: FirstContext): Tactic {
    const loc = this.locFinder(ctx.start.line, ctx.start.column);
    return {
      type: "first",
      body: new MyBracketVisitor(this).visit(ctx.bracket()),
      loc: loc,
    };
  }

  visitProgress(ctx: ProgressContext): Tactic {
    const loc = this.locFinder(ctx.start.line, ctx.start.column);
    return {
      type: "progress",
      body: this.visit(ctx.tactic()),
      loc: loc,
    };
  }

  visitTry(ctx: TryContext): Tactic {
    const loc = this.locFinder(ctx.start.line, ctx.start.column);
    return {
      type: "try",
      body: this.visit(ctx.tactic()),
      loc: loc,
    };
  }

  visitRepeat(ctx: RepeatContext): Tactic {
    const loc = this.locFinder(ctx.start.line, ctx.start.column);
    return {
      type: "repeat",
      body: this.visit(ctx.tactic()),
      loc: loc,
    };
  }

  visitMatch(ctx: MatchContext): Tactic {
    const lhs = ctx
      .CASE_list()
      .map((c) => /\| (.+?) =>/g.exec(c.getText())![1]);
    const rhs = ctx.tactic_list().map((t) => this.visit(t));

    return {
      type: "match",
      branches: lhs.map(function (e, i) {
        return [e, rhs[i]];
      }),
    };
  }

  visitAuto(ctx: AutoContext): Tactic {
    const loc = this.locFinder(ctx.start.line, ctx.start.column);
    const txt =  ctx.getText().trim();
    if (txt === "auto") {
      return { type: "auto", loc: loc };
    } else {
      return { type: "eauto", loc: loc };
    }
  }

  visitFail(ctx: FailContext): Tactic {
    return { type: "opaque", atomic: ctx.getText() };
  }

  visitOpaque(ctx: OpaqueContext): Tactic {
    const loc = this.locFinder(ctx.start.line, ctx.start.column);
    return {
      type: "opaque",
      atomic: ctx.getText().trim(),
      loc: loc,
    };
  }

  visitParen(ctx: ParenContext): Tactic {
    return this.visit(ctx.stactic());
  }
}

function getParser(s: string) {
  const chars = new CharStream(s);
  const lexer = new ScriptLexer(chars);
  const tokens = new CommonTokenStream(lexer);
  return new ScriptParser(tokens);
}

export function parse(s: string): Script {
  return new MyScriptVisitor(getLocFinder(s)).visit(getParser(s).script());
}

export function parseTactic(s: string): Tactic {
  return new MyTacticVisitor(getLocFinder(s)).visit(getParser(s).tactic());
}

class MyBracketVisitor extends BracketVisitor<Tactic[]> {
  tvisitor: MyTacticVisitor;

  constructor(tvisitor: MyTacticVisitor) {
    super();
    this.tvisitor = tvisitor;
  }

  visitBracket(ctx: BracketContext): Tactic[] {
    function isBracket(s: string): boolean {
      return s === "[" || s === "]";
    }

    function isBar(s: string): boolean {
      return s === "|";
    }

    const count = ctx.getChildCount();
    const body: Tactic[] = [];
    for (let i = 0; i < count; i++) {
      const child = ctx.getChild(i);
      const text = child.getText().trim();
      if (isBracket(text)) {
      } else if (isBar(text)) {
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
      } else {
        body.push(this.tvisitor.visit(child));
      }
    }

    return body;
  }
}

function getLocFinder(s: string) {
  const lines = s.split("\n").map((l) => l.length);
  return (line: number, column: number): number => {
    const offset = lines.slice(0, line - 1).reduce((a, b) => a + b, line - 1);
    return offset + column;
  };
}
