// Generated from Script.g4 by ANTLR 4.13.2

import {ParseTreeListener} from "antlr4";


import { ScriptContext } from "./ScriptParser.js";
import { OneContext } from "./ScriptParser.js";
import { NthContext } from "./ScriptParser.js";
import { AllContext } from "./ScriptParser.js";
import { LBraceContext } from "./ScriptParser.js";
import { RBraceContext } from "./ScriptParser.js";
import { BulletContext } from "./ScriptParser.js";
import { CommentContext } from "./ScriptParser.js";
import { SemicolonContext } from "./ScriptParser.js";
import { SemicolonManyContext } from "./ScriptParser.js";
import { GeneralContext } from "./ScriptParser.js";
import { FirstContext } from "./ScriptParser.js";
import { ProgressContext } from "./ScriptParser.js";
import { TryContext } from "./ScriptParser.js";
import { RepeatContext } from "./ScriptParser.js";
import { AutoContext } from "./ScriptParser.js";
import { FailContext } from "./ScriptParser.js";
import { MatchContext } from "./ScriptParser.js";
import { ParenContext } from "./ScriptParser.js";
import { OpaqueContext } from "./ScriptParser.js";
import { BracketContext } from "./ScriptParser.js";


/**
 * This interface defines a complete listener for a parse tree produced by
 * `ScriptParser`.
 */
export default class ScriptListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by `ScriptParser.script`.
	 * @param ctx the parse tree
	 */
	enterScript?: (ctx: ScriptContext) => void;
	/**
	 * Exit a parse tree produced by `ScriptParser.script`.
	 * @param ctx the parse tree
	 */
	exitScript?: (ctx: ScriptContext) => void;
	/**
	 * Enter a parse tree produced by the `One`
	 * labeled alternative in `ScriptParser.sentence`.
	 * @param ctx the parse tree
	 */
	enterOne?: (ctx: OneContext) => void;
	/**
	 * Exit a parse tree produced by the `One`
	 * labeled alternative in `ScriptParser.sentence`.
	 * @param ctx the parse tree
	 */
	exitOne?: (ctx: OneContext) => void;
	/**
	 * Enter a parse tree produced by the `Nth`
	 * labeled alternative in `ScriptParser.sentence`.
	 * @param ctx the parse tree
	 */
	enterNth?: (ctx: NthContext) => void;
	/**
	 * Exit a parse tree produced by the `Nth`
	 * labeled alternative in `ScriptParser.sentence`.
	 * @param ctx the parse tree
	 */
	exitNth?: (ctx: NthContext) => void;
	/**
	 * Enter a parse tree produced by the `All`
	 * labeled alternative in `ScriptParser.sentence`.
	 * @param ctx the parse tree
	 */
	enterAll?: (ctx: AllContext) => void;
	/**
	 * Exit a parse tree produced by the `All`
	 * labeled alternative in `ScriptParser.sentence`.
	 * @param ctx the parse tree
	 */
	exitAll?: (ctx: AllContext) => void;
	/**
	 * Enter a parse tree produced by the `LBrace`
	 * labeled alternative in `ScriptParser.sentence`.
	 * @param ctx the parse tree
	 */
	enterLBrace?: (ctx: LBraceContext) => void;
	/**
	 * Exit a parse tree produced by the `LBrace`
	 * labeled alternative in `ScriptParser.sentence`.
	 * @param ctx the parse tree
	 */
	exitLBrace?: (ctx: LBraceContext) => void;
	/**
	 * Enter a parse tree produced by the `RBrace`
	 * labeled alternative in `ScriptParser.sentence`.
	 * @param ctx the parse tree
	 */
	enterRBrace?: (ctx: RBraceContext) => void;
	/**
	 * Exit a parse tree produced by the `RBrace`
	 * labeled alternative in `ScriptParser.sentence`.
	 * @param ctx the parse tree
	 */
	exitRBrace?: (ctx: RBraceContext) => void;
	/**
	 * Enter a parse tree produced by the `Bullet`
	 * labeled alternative in `ScriptParser.sentence`.
	 * @param ctx the parse tree
	 */
	enterBullet?: (ctx: BulletContext) => void;
	/**
	 * Exit a parse tree produced by the `Bullet`
	 * labeled alternative in `ScriptParser.sentence`.
	 * @param ctx the parse tree
	 */
	exitBullet?: (ctx: BulletContext) => void;
	/**
	 * Enter a parse tree produced by the `Comment`
	 * labeled alternative in `ScriptParser.sentence`.
	 * @param ctx the parse tree
	 */
	enterComment?: (ctx: CommentContext) => void;
	/**
	 * Exit a parse tree produced by the `Comment`
	 * labeled alternative in `ScriptParser.sentence`.
	 * @param ctx the parse tree
	 */
	exitComment?: (ctx: CommentContext) => void;
	/**
	 * Enter a parse tree produced by the `Semicolon`
	 * labeled alternative in `ScriptParser.stactic`.
	 * @param ctx the parse tree
	 */
	enterSemicolon?: (ctx: SemicolonContext) => void;
	/**
	 * Exit a parse tree produced by the `Semicolon`
	 * labeled alternative in `ScriptParser.stactic`.
	 * @param ctx the parse tree
	 */
	exitSemicolon?: (ctx: SemicolonContext) => void;
	/**
	 * Enter a parse tree produced by the `SemicolonMany`
	 * labeled alternative in `ScriptParser.stactic`.
	 * @param ctx the parse tree
	 */
	enterSemicolonMany?: (ctx: SemicolonManyContext) => void;
	/**
	 * Exit a parse tree produced by the `SemicolonMany`
	 * labeled alternative in `ScriptParser.stactic`.
	 * @param ctx the parse tree
	 */
	exitSemicolonMany?: (ctx: SemicolonManyContext) => void;
	/**
	 * Enter a parse tree produced by the `General`
	 * labeled alternative in `ScriptParser.stactic`.
	 * @param ctx the parse tree
	 */
	enterGeneral?: (ctx: GeneralContext) => void;
	/**
	 * Exit a parse tree produced by the `General`
	 * labeled alternative in `ScriptParser.stactic`.
	 * @param ctx the parse tree
	 */
	exitGeneral?: (ctx: GeneralContext) => void;
	/**
	 * Enter a parse tree produced by the `First`
	 * labeled alternative in `ScriptParser.tactic`.
	 * @param ctx the parse tree
	 */
	enterFirst?: (ctx: FirstContext) => void;
	/**
	 * Exit a parse tree produced by the `First`
	 * labeled alternative in `ScriptParser.tactic`.
	 * @param ctx the parse tree
	 */
	exitFirst?: (ctx: FirstContext) => void;
	/**
	 * Enter a parse tree produced by the `Progress`
	 * labeled alternative in `ScriptParser.tactic`.
	 * @param ctx the parse tree
	 */
	enterProgress?: (ctx: ProgressContext) => void;
	/**
	 * Exit a parse tree produced by the `Progress`
	 * labeled alternative in `ScriptParser.tactic`.
	 * @param ctx the parse tree
	 */
	exitProgress?: (ctx: ProgressContext) => void;
	/**
	 * Enter a parse tree produced by the `Try`
	 * labeled alternative in `ScriptParser.tactic`.
	 * @param ctx the parse tree
	 */
	enterTry?: (ctx: TryContext) => void;
	/**
	 * Exit a parse tree produced by the `Try`
	 * labeled alternative in `ScriptParser.tactic`.
	 * @param ctx the parse tree
	 */
	exitTry?: (ctx: TryContext) => void;
	/**
	 * Enter a parse tree produced by the `Repeat`
	 * labeled alternative in `ScriptParser.tactic`.
	 * @param ctx the parse tree
	 */
	enterRepeat?: (ctx: RepeatContext) => void;
	/**
	 * Exit a parse tree produced by the `Repeat`
	 * labeled alternative in `ScriptParser.tactic`.
	 * @param ctx the parse tree
	 */
	exitRepeat?: (ctx: RepeatContext) => void;
	/**
	 * Enter a parse tree produced by the `Auto`
	 * labeled alternative in `ScriptParser.tactic`.
	 * @param ctx the parse tree
	 */
	enterAuto?: (ctx: AutoContext) => void;
	/**
	 * Exit a parse tree produced by the `Auto`
	 * labeled alternative in `ScriptParser.tactic`.
	 * @param ctx the parse tree
	 */
	exitAuto?: (ctx: AutoContext) => void;
	/**
	 * Enter a parse tree produced by the `Fail`
	 * labeled alternative in `ScriptParser.tactic`.
	 * @param ctx the parse tree
	 */
	enterFail?: (ctx: FailContext) => void;
	/**
	 * Exit a parse tree produced by the `Fail`
	 * labeled alternative in `ScriptParser.tactic`.
	 * @param ctx the parse tree
	 */
	exitFail?: (ctx: FailContext) => void;
	/**
	 * Enter a parse tree produced by the `Match`
	 * labeled alternative in `ScriptParser.tactic`.
	 * @param ctx the parse tree
	 */
	enterMatch?: (ctx: MatchContext) => void;
	/**
	 * Exit a parse tree produced by the `Match`
	 * labeled alternative in `ScriptParser.tactic`.
	 * @param ctx the parse tree
	 */
	exitMatch?: (ctx: MatchContext) => void;
	/**
	 * Enter a parse tree produced by the `Paren`
	 * labeled alternative in `ScriptParser.tactic`.
	 * @param ctx the parse tree
	 */
	enterParen?: (ctx: ParenContext) => void;
	/**
	 * Exit a parse tree produced by the `Paren`
	 * labeled alternative in `ScriptParser.tactic`.
	 * @param ctx the parse tree
	 */
	exitParen?: (ctx: ParenContext) => void;
	/**
	 * Enter a parse tree produced by the `Opaque`
	 * labeled alternative in `ScriptParser.tactic`.
	 * @param ctx the parse tree
	 */
	enterOpaque?: (ctx: OpaqueContext) => void;
	/**
	 * Exit a parse tree produced by the `Opaque`
	 * labeled alternative in `ScriptParser.tactic`.
	 * @param ctx the parse tree
	 */
	exitOpaque?: (ctx: OpaqueContext) => void;
	/**
	 * Enter a parse tree produced by `ScriptParser.bracket`.
	 * @param ctx the parse tree
	 */
	enterBracket?: (ctx: BracketContext) => void;
	/**
	 * Exit a parse tree produced by `ScriptParser.bracket`.
	 * @param ctx the parse tree
	 */
	exitBracket?: (ctx: BracketContext) => void;
}

