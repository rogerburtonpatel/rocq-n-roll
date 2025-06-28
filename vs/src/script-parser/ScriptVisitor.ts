// Generated from Script.g4 by ANTLR 4.13.1

import { ParseTreeVisitor } from "antlr4";

import {
  AllContext,
  AutoContext,
  BracketContext,
  BulletContext,
  CommentContext,
  FailContext,
  FirstContext,
  GeneralContext,
  LBraceContext,
  MatchContext,
  NthContext,
  OneContext,
  OpaqueContext,
  ParenContext,
  ProgressContext,
  RBraceContext,
  RepeatContext,
  ScriptContext,
  SemicolonContext,
  SemicolonManyContext,
  TryContext,
} from "./ScriptParser";

export default class ScriptVisitor<Result> extends ParseTreeVisitor<Result> {
  visitScript?(ctx: ScriptContext): Result;
}

export class SentenceVisitor<Result> extends ParseTreeVisitor<Result> {
  visitOne?(ctx: OneContext): Result;
  visitNth?(ctx: NthContext): Result;
  visitAll?(ctx: AllContext): Result;
  visitLBrace?(ctx: LBraceContext): Result;
  visitRBrace?(ctx: RBraceContext): Result;
  visitBullet?(ctx: BulletContext): Result;
  visitComment?(ctx: CommentContext): Result;
}

export class TacticVisitor<Result> extends ParseTreeVisitor<Result> {
  visitSemicolon?(ctx: SemicolonContext): Result;
  visitSemicolonMany?(ctx: SemicolonManyContext): Result;
  visitGeneral?(ctx: GeneralContext): Result;
  visitFirst?(ctx: FirstContext): Result;
  visitProgress?(ctx: ProgressContext): Result;
  visitTry?(ctx: TryContext): Result;
  visitRepeat?(ctx: RepeatContext): Result;
  visitAuto?(ctx: AutoContext): Result;
  visitMatch?(ctx: MatchContext): Result;
  visitFail?(ctx: FailContext): Result;
  visitParen?(ctx: ParenContext): Result;
  visitOpaque?(ctx: OpaqueContext): Result;
}

export class BracketVisitor<Result> extends ParseTreeVisitor<Result> {
  visitBracket?(ctx: BracketContext): Result;
}
