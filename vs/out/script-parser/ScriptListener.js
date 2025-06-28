"use strict";
// Generated from Script.g4 by ANTLR 4.13.2
Object.defineProperty(exports, "__esModule", { value: true });
const antlr4_1 = require("antlr4");
/**
 * This interface defines a complete listener for a parse tree produced by
 * `ScriptParser`.
 */
class ScriptListener extends antlr4_1.ParseTreeListener {
    /**
     * Enter a parse tree produced by `ScriptParser.script`.
     * @param ctx the parse tree
     */
    enterScript;
    /**
     * Exit a parse tree produced by `ScriptParser.script`.
     * @param ctx the parse tree
     */
    exitScript;
    /**
     * Enter a parse tree produced by the `One`
     * labeled alternative in `ScriptParser.sentence`.
     * @param ctx the parse tree
     */
    enterOne;
    /**
     * Exit a parse tree produced by the `One`
     * labeled alternative in `ScriptParser.sentence`.
     * @param ctx the parse tree
     */
    exitOne;
    /**
     * Enter a parse tree produced by the `Nth`
     * labeled alternative in `ScriptParser.sentence`.
     * @param ctx the parse tree
     */
    enterNth;
    /**
     * Exit a parse tree produced by the `Nth`
     * labeled alternative in `ScriptParser.sentence`.
     * @param ctx the parse tree
     */
    exitNth;
    /**
     * Enter a parse tree produced by the `All`
     * labeled alternative in `ScriptParser.sentence`.
     * @param ctx the parse tree
     */
    enterAll;
    /**
     * Exit a parse tree produced by the `All`
     * labeled alternative in `ScriptParser.sentence`.
     * @param ctx the parse tree
     */
    exitAll;
    /**
     * Enter a parse tree produced by the `LBrace`
     * labeled alternative in `ScriptParser.sentence`.
     * @param ctx the parse tree
     */
    enterLBrace;
    /**
     * Exit a parse tree produced by the `LBrace`
     * labeled alternative in `ScriptParser.sentence`.
     * @param ctx the parse tree
     */
    exitLBrace;
    /**
     * Enter a parse tree produced by the `RBrace`
     * labeled alternative in `ScriptParser.sentence`.
     * @param ctx the parse tree
     */
    enterRBrace;
    /**
     * Exit a parse tree produced by the `RBrace`
     * labeled alternative in `ScriptParser.sentence`.
     * @param ctx the parse tree
     */
    exitRBrace;
    /**
     * Enter a parse tree produced by the `Bullet`
     * labeled alternative in `ScriptParser.sentence`.
     * @param ctx the parse tree
     */
    enterBullet;
    /**
     * Exit a parse tree produced by the `Bullet`
     * labeled alternative in `ScriptParser.sentence`.
     * @param ctx the parse tree
     */
    exitBullet;
    /**
     * Enter a parse tree produced by the `Comment`
     * labeled alternative in `ScriptParser.sentence`.
     * @param ctx the parse tree
     */
    enterComment;
    /**
     * Exit a parse tree produced by the `Comment`
     * labeled alternative in `ScriptParser.sentence`.
     * @param ctx the parse tree
     */
    exitComment;
    /**
     * Enter a parse tree produced by the `Semicolon`
     * labeled alternative in `ScriptParser.stactic`.
     * @param ctx the parse tree
     */
    enterSemicolon;
    /**
     * Exit a parse tree produced by the `Semicolon`
     * labeled alternative in `ScriptParser.stactic`.
     * @param ctx the parse tree
     */
    exitSemicolon;
    /**
     * Enter a parse tree produced by the `SemicolonMany`
     * labeled alternative in `ScriptParser.stactic`.
     * @param ctx the parse tree
     */
    enterSemicolonMany;
    /**
     * Exit a parse tree produced by the `SemicolonMany`
     * labeled alternative in `ScriptParser.stactic`.
     * @param ctx the parse tree
     */
    exitSemicolonMany;
    /**
     * Enter a parse tree produced by the `General`
     * labeled alternative in `ScriptParser.stactic`.
     * @param ctx the parse tree
     */
    enterGeneral;
    /**
     * Exit a parse tree produced by the `General`
     * labeled alternative in `ScriptParser.stactic`.
     * @param ctx the parse tree
     */
    exitGeneral;
    /**
     * Enter a parse tree produced by the `First`
     * labeled alternative in `ScriptParser.tactic`.
     * @param ctx the parse tree
     */
    enterFirst;
    /**
     * Exit a parse tree produced by the `First`
     * labeled alternative in `ScriptParser.tactic`.
     * @param ctx the parse tree
     */
    exitFirst;
    /**
     * Enter a parse tree produced by the `Progress`
     * labeled alternative in `ScriptParser.tactic`.
     * @param ctx the parse tree
     */
    enterProgress;
    /**
     * Exit a parse tree produced by the `Progress`
     * labeled alternative in `ScriptParser.tactic`.
     * @param ctx the parse tree
     */
    exitProgress;
    /**
     * Enter a parse tree produced by the `Try`
     * labeled alternative in `ScriptParser.tactic`.
     * @param ctx the parse tree
     */
    enterTry;
    /**
     * Exit a parse tree produced by the `Try`
     * labeled alternative in `ScriptParser.tactic`.
     * @param ctx the parse tree
     */
    exitTry;
    /**
     * Enter a parse tree produced by the `Repeat`
     * labeled alternative in `ScriptParser.tactic`.
     * @param ctx the parse tree
     */
    enterRepeat;
    /**
     * Exit a parse tree produced by the `Repeat`
     * labeled alternative in `ScriptParser.tactic`.
     * @param ctx the parse tree
     */
    exitRepeat;
    /**
     * Enter a parse tree produced by the `Auto`
     * labeled alternative in `ScriptParser.tactic`.
     * @param ctx the parse tree
     */
    enterAuto;
    /**
     * Exit a parse tree produced by the `Auto`
     * labeled alternative in `ScriptParser.tactic`.
     * @param ctx the parse tree
     */
    exitAuto;
    /**
     * Enter a parse tree produced by the `Fail`
     * labeled alternative in `ScriptParser.tactic`.
     * @param ctx the parse tree
     */
    enterFail;
    /**
     * Exit a parse tree produced by the `Fail`
     * labeled alternative in `ScriptParser.tactic`.
     * @param ctx the parse tree
     */
    exitFail;
    /**
     * Enter a parse tree produced by the `Match`
     * labeled alternative in `ScriptParser.tactic`.
     * @param ctx the parse tree
     */
    enterMatch;
    /**
     * Exit a parse tree produced by the `Match`
     * labeled alternative in `ScriptParser.tactic`.
     * @param ctx the parse tree
     */
    exitMatch;
    /**
     * Enter a parse tree produced by the `Paren`
     * labeled alternative in `ScriptParser.tactic`.
     * @param ctx the parse tree
     */
    enterParen;
    /**
     * Exit a parse tree produced by the `Paren`
     * labeled alternative in `ScriptParser.tactic`.
     * @param ctx the parse tree
     */
    exitParen;
    /**
     * Enter a parse tree produced by the `Opaque`
     * labeled alternative in `ScriptParser.tactic`.
     * @param ctx the parse tree
     */
    enterOpaque;
    /**
     * Exit a parse tree produced by the `Opaque`
     * labeled alternative in `ScriptParser.tactic`.
     * @param ctx the parse tree
     */
    exitOpaque;
    /**
     * Enter a parse tree produced by `ScriptParser.bracket`.
     * @param ctx the parse tree
     */
    enterBracket;
    /**
     * Exit a parse tree produced by `ScriptParser.bracket`.
     * @param ctx the parse tree
     */
    exitBracket;
}
exports.default = ScriptListener;
//# sourceMappingURL=ScriptListener.js.map