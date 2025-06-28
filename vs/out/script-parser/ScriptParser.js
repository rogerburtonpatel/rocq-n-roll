"use strict";
// Generated from Script.g4 by ANTLR 4.13.2
// noinspection ES6UnusedImports,JSUnusedGlobalSymbols,JSUnusedLocalSymbols
Object.defineProperty(exports, "__esModule", { value: true });
exports.BracketContext = exports.ParenContext = exports.MatchContext = exports.FailContext = exports.FirstContext = exports.RepeatContext = exports.TryContext = exports.OpaqueContext = exports.ProgressContext = exports.AutoContext = exports.TacticContext = exports.GeneralContext = exports.SemicolonManyContext = exports.SemicolonContext = exports.StacticContext = exports.OneContext = exports.RBraceContext = exports.NthContext = exports.CommentContext = exports.BulletContext = exports.LBraceContext = exports.AllContext = exports.SentenceContext = exports.ScriptContext = void 0;
const antlr4_1 = require("antlr4");
class ScriptParser extends antlr4_1.Parser {
    static PERIOD = 1;
    static SEMICOLON = 2;
    static LPAREN = 3;
    static RPAREN = 4;
    static LBRACE = 5;
    static RBRACE = 6;
    static LBRACK = 7;
    static RBRACK = 8;
    static BULLET = 9;
    static BAR = 10;
    static ALL = 11;
    static NTH = 12;
    static FIRST = 13;
    static PROGRESS = 14;
    static TRY = 15;
    static REPEAT = 16;
    static AUTO = 17;
    static MATCHGOAL = 18;
    static CASE = 19;
    static END = 20;
    static FAIL = 21;
    static COMMENT = 22;
    static TANY = 23;
    static WS = 24;
    static EOF = antlr4_1.Token.EOF;
    static RULE_script = 0;
    static RULE_sentence = 1;
    static RULE_stactic = 2;
    static RULE_tactic = 3;
    static RULE_bracket = 4;
    static literalNames = [];
    static symbolicNames = [null, "PERIOD",
        "SEMICOLON",
        "LPAREN", "RPAREN",
        "LBRACE", "RBRACE",
        "LBRACK", "RBRACK",
        "BULLET", "BAR",
        "ALL", "NTH",
        "FIRST", "PROGRESS",
        "TRY", "REPEAT",
        "AUTO", "MATCHGOAL",
        "CASE", "END",
        "FAIL", "COMMENT",
        "TANY", "WS"];
    // tslint:disable:no-trailing-whitespace
    static ruleNames = [
        "script", "sentence", "stactic", "tactic", "bracket",
    ];
    get grammarFileName() { return "Script.g4"; }
    get literalNames() { return ScriptParser.literalNames; }
    get symbolicNames() { return ScriptParser.symbolicNames; }
    get ruleNames() { return ScriptParser.ruleNames; }
    get serializedATN() { return ScriptParser._serializedATN; }
    createFailedPredicateException(predicate, message) {
        return new antlr4_1.FailedPredicateException(this, predicate, message);
    }
    constructor(input) {
        super(input);
        this._interp = new antlr4_1.ParserATNSimulator(this, ScriptParser._ATN, ScriptParser.DecisionsToDFA, new antlr4_1.PredictionContextCache());
    }
    // @RuleVersion(0)
    script() {
        let localctx = new ScriptContext(this, this._ctx, this.state);
        this.enterRule(localctx, 0, ScriptParser.RULE_script);
        let _la;
        try {
            this.enterOuterAlt(localctx, 1);
            {
                this.state = 13;
                this._errHandler.sync(this);
                _la = this._input.LA(1);
                while (_la === 24) {
                    {
                        {
                            this.state = 10;
                            this.match(ScriptParser.WS);
                        }
                    }
                    this.state = 15;
                    this._errHandler.sync(this);
                    _la = this._input.LA(1);
                }
                this.state = 19;
                this._errHandler.sync(this);
                _la = this._input.LA(1);
                while ((((_la) & ~0x1F) === 0 && ((1 << _la) & 15202920) !== 0)) {
                    {
                        {
                            this.state = 16;
                            this.sentence();
                        }
                    }
                    this.state = 21;
                    this._errHandler.sync(this);
                    _la = this._input.LA(1);
                }
            }
        }
        catch (re) {
            if (re instanceof antlr4_1.RecognitionException) {
                localctx.exception = re;
                this._errHandler.reportError(this, re);
                this._errHandler.recover(this, re);
            }
            else {
                throw re;
            }
        }
        finally {
            this.exitRule();
        }
        return localctx;
    }
    // @RuleVersion(0)
    sentence() {
        let localctx = new SentenceContext(this, this._ctx, this.state);
        this.enterRule(localctx, 2, ScriptParser.RULE_sentence);
        try {
            this.state = 37;
            this._errHandler.sync(this);
            switch (this._input.LA(1)) {
                case 3:
                case 13:
                case 14:
                case 15:
                case 16:
                case 17:
                case 18:
                case 21:
                case 23:
                    localctx = new OneContext(this, localctx);
                    this.enterOuterAlt(localctx, 1);
                    {
                        this.state = 22;
                        this.stactic(0);
                        this.state = 23;
                        this.match(ScriptParser.PERIOD);
                    }
                    break;
                case 12:
                    localctx = new NthContext(this, localctx);
                    this.enterOuterAlt(localctx, 2);
                    {
                        this.state = 25;
                        this.match(ScriptParser.NTH);
                        this.state = 26;
                        this.stactic(0);
                        this.state = 27;
                        this.match(ScriptParser.PERIOD);
                    }
                    break;
                case 11:
                    localctx = new AllContext(this, localctx);
                    this.enterOuterAlt(localctx, 3);
                    {
                        this.state = 29;
                        this.match(ScriptParser.ALL);
                        this.state = 30;
                        this.stactic(0);
                        this.state = 31;
                        this.match(ScriptParser.PERIOD);
                    }
                    break;
                case 5:
                    localctx = new LBraceContext(this, localctx);
                    this.enterOuterAlt(localctx, 4);
                    {
                        this.state = 33;
                        this.match(ScriptParser.LBRACE);
                    }
                    break;
                case 6:
                    localctx = new RBraceContext(this, localctx);
                    this.enterOuterAlt(localctx, 5);
                    {
                        this.state = 34;
                        this.match(ScriptParser.RBRACE);
                    }
                    break;
                case 9:
                    localctx = new BulletContext(this, localctx);
                    this.enterOuterAlt(localctx, 6);
                    {
                        this.state = 35;
                        this.match(ScriptParser.BULLET);
                    }
                    break;
                case 22:
                    localctx = new CommentContext(this, localctx);
                    this.enterOuterAlt(localctx, 7);
                    {
                        this.state = 36;
                        this.match(ScriptParser.COMMENT);
                    }
                    break;
                default:
                    throw new antlr4_1.NoViableAltException(this);
            }
        }
        catch (re) {
            if (re instanceof antlr4_1.RecognitionException) {
                localctx.exception = re;
                this._errHandler.reportError(this, re);
                this._errHandler.recover(this, re);
            }
            else {
                throw re;
            }
        }
        finally {
            this.exitRule();
        }
        return localctx;
    }
    // @RuleVersion(0)
    stactic(_p) {
        if (_p === undefined) {
            _p = 0;
        }
        let _parentctx = this._ctx;
        let _parentState = this.state;
        let localctx = new StacticContext(this, this._ctx, _parentState);
        let _prevctx = localctx;
        let _startState = 4;
        this.enterRecursionRule(localctx, 4, ScriptParser.RULE_stactic, _p);
        try {
            let _alt;
            this.enterOuterAlt(localctx, 1);
            {
                {
                    localctx = new GeneralContext(this, localctx);
                    this._ctx = localctx;
                    _prevctx = localctx;
                    this.state = 40;
                    this.tactic();
                }
                this._ctx.stop = this._input.LT(-1);
                this.state = 50;
                this._errHandler.sync(this);
                _alt = this._interp.adaptivePredict(this._input, 4, this._ctx);
                while (_alt !== 2 && _alt !== antlr4_1.ATN.INVALID_ALT_NUMBER) {
                    if (_alt === 1) {
                        if (this._parseListeners != null) {
                            this.triggerExitRuleEvent();
                        }
                        _prevctx = localctx;
                        {
                            this.state = 48;
                            this._errHandler.sync(this);
                            switch (this._interp.adaptivePredict(this._input, 3, this._ctx)) {
                                case 1:
                                    {
                                        localctx = new SemicolonContext(this, new StacticContext(this, _parentctx, _parentState));
                                        this.pushNewRecursionContext(localctx, _startState, ScriptParser.RULE_stactic);
                                        this.state = 42;
                                        if (!(this.precpred(this._ctx, 3))) {
                                            throw this.createFailedPredicateException("this.precpred(this._ctx, 3)");
                                        }
                                        this.state = 43;
                                        this.match(ScriptParser.SEMICOLON);
                                        this.state = 44;
                                        this.tactic();
                                    }
                                    break;
                                case 2:
                                    {
                                        localctx = new SemicolonManyContext(this, new StacticContext(this, _parentctx, _parentState));
                                        this.pushNewRecursionContext(localctx, _startState, ScriptParser.RULE_stactic);
                                        this.state = 45;
                                        if (!(this.precpred(this._ctx, 2))) {
                                            throw this.createFailedPredicateException("this.precpred(this._ctx, 2)");
                                        }
                                        this.state = 46;
                                        this.match(ScriptParser.SEMICOLON);
                                        this.state = 47;
                                        this.bracket();
                                    }
                                    break;
                            }
                        }
                    }
                    this.state = 52;
                    this._errHandler.sync(this);
                    _alt = this._interp.adaptivePredict(this._input, 4, this._ctx);
                }
            }
        }
        catch (re) {
            if (re instanceof antlr4_1.RecognitionException) {
                localctx.exception = re;
                this._errHandler.reportError(this, re);
                this._errHandler.recover(this, re);
            }
            else {
                throw re;
            }
        }
        finally {
            this.unrollRecursionContexts(_parentctx);
        }
        return localctx;
    }
    // @RuleVersion(0)
    tactic() {
        let localctx = new TacticContext(this, this._ctx, this.state);
        this.enterRule(localctx, 6, ScriptParser.RULE_tactic);
        let _la;
        try {
            let _alt;
            this.state = 92;
            this._errHandler.sync(this);
            switch (this._input.LA(1)) {
                case 13:
                    localctx = new FirstContext(this, localctx);
                    this.enterOuterAlt(localctx, 1);
                    {
                        this.state = 53;
                        this.match(ScriptParser.FIRST);
                        this.state = 54;
                        this.bracket();
                    }
                    break;
                case 14:
                    localctx = new ProgressContext(this, localctx);
                    this.enterOuterAlt(localctx, 2);
                    {
                        this.state = 55;
                        this.match(ScriptParser.PROGRESS);
                        this.state = 56;
                        this.tactic();
                    }
                    break;
                case 15:
                    localctx = new TryContext(this, localctx);
                    this.enterOuterAlt(localctx, 3);
                    {
                        this.state = 57;
                        this.match(ScriptParser.TRY);
                        this.state = 58;
                        this.tactic();
                    }
                    break;
                case 16:
                    localctx = new RepeatContext(this, localctx);
                    this.enterOuterAlt(localctx, 4);
                    {
                        this.state = 59;
                        this.match(ScriptParser.REPEAT);
                        this.state = 60;
                        this.tactic();
                    }
                    break;
                case 17:
                    localctx = new AutoContext(this, localctx);
                    this.enterOuterAlt(localctx, 5);
                    {
                        this.state = 61;
                        this.match(ScriptParser.AUTO);
                    }
                    break;
                case 21:
                    localctx = new FailContext(this, localctx);
                    this.enterOuterAlt(localctx, 6);
                    {
                        this.state = 62;
                        this.match(ScriptParser.FAIL);
                        this.state = 63;
                        this.stactic(0);
                    }
                    break;
                case 18:
                    localctx = new MatchContext(this, localctx);
                    this.enterOuterAlt(localctx, 7);
                    {
                        this.state = 64;
                        this.match(ScriptParser.MATCHGOAL);
                        this.state = 69;
                        this._errHandler.sync(this);
                        _la = this._input.LA(1);
                        while (_la === 19) {
                            {
                                {
                                    this.state = 65;
                                    this.match(ScriptParser.CASE);
                                    this.state = 66;
                                    this.tactic();
                                }
                            }
                            this.state = 71;
                            this._errHandler.sync(this);
                            _la = this._input.LA(1);
                        }
                        this.state = 72;
                        this.match(ScriptParser.END);
                    }
                    break;
                case 3:
                    localctx = new ParenContext(this, localctx);
                    this.enterOuterAlt(localctx, 8);
                    {
                        this.state = 73;
                        this.match(ScriptParser.LPAREN);
                        this.state = 74;
                        this.stactic(0);
                        this.state = 75;
                        this.match(ScriptParser.RPAREN);
                    }
                    break;
                case 23:
                    localctx = new OpaqueContext(this, localctx);
                    this.enterOuterAlt(localctx, 9);
                    {
                        this.state = 88;
                        this._errHandler.sync(this);
                        _alt = 1;
                        do {
                            switch (_alt) {
                                case 1:
                                    {
                                        {
                                            this.state = 78;
                                            this._errHandler.sync(this);
                                            _alt = 1;
                                            do {
                                                switch (_alt) {
                                                    case 1:
                                                        {
                                                            {
                                                                this.state = 77;
                                                                this.match(ScriptParser.TANY);
                                                            }
                                                        }
                                                        break;
                                                    default:
                                                        throw new antlr4_1.NoViableAltException(this);
                                                }
                                                this.state = 80;
                                                this._errHandler.sync(this);
                                                _alt = this._interp.adaptivePredict(this._input, 6, this._ctx);
                                            } while (_alt !== 2 && _alt !== antlr4_1.ATN.INVALID_ALT_NUMBER);
                                            this.state = 85;
                                            this._errHandler.sync(this);
                                            _alt = this._interp.adaptivePredict(this._input, 7, this._ctx);
                                            while (_alt !== 2 && _alt !== antlr4_1.ATN.INVALID_ALT_NUMBER) {
                                                if (_alt === 1) {
                                                    {
                                                        {
                                                            this.state = 82;
                                                            this.match(ScriptParser.WS);
                                                        }
                                                    }
                                                }
                                                this.state = 87;
                                                this._errHandler.sync(this);
                                                _alt = this._interp.adaptivePredict(this._input, 7, this._ctx);
                                            }
                                        }
                                    }
                                    break;
                                default:
                                    throw new antlr4_1.NoViableAltException(this);
                            }
                            this.state = 90;
                            this._errHandler.sync(this);
                            _alt = this._interp.adaptivePredict(this._input, 8, this._ctx);
                        } while (_alt !== 2 && _alt !== antlr4_1.ATN.INVALID_ALT_NUMBER);
                    }
                    break;
                default:
                    throw new antlr4_1.NoViableAltException(this);
            }
        }
        catch (re) {
            if (re instanceof antlr4_1.RecognitionException) {
                localctx.exception = re;
                this._errHandler.reportError(this, re);
                this._errHandler.recover(this, re);
            }
            else {
                throw re;
            }
        }
        finally {
            this.exitRule();
        }
        return localctx;
    }
    // @RuleVersion(0)
    bracket() {
        let localctx = new BracketContext(this, this._ctx, this.state);
        this.enterRule(localctx, 8, ScriptParser.RULE_bracket);
        let _la;
        try {
            this.enterOuterAlt(localctx, 1);
            {
                this.state = 94;
                this.match(ScriptParser.LBRACK);
                this.state = 96;
                this._errHandler.sync(this);
                _la = this._input.LA(1);
                if ((((_la) & ~0x1F) === 0 && ((1 << _la) & 11001864) !== 0)) {
                    {
                        this.state = 95;
                        this.stactic(0);
                    }
                }
                this.state = 104;
                this._errHandler.sync(this);
                _la = this._input.LA(1);
                while (_la === 10) {
                    {
                        {
                            this.state = 98;
                            this.match(ScriptParser.BAR);
                            this.state = 100;
                            this._errHandler.sync(this);
                            _la = this._input.LA(1);
                            if ((((_la) & ~0x1F) === 0 && ((1 << _la) & 11001864) !== 0)) {
                                {
                                    this.state = 99;
                                    this.stactic(0);
                                }
                            }
                        }
                    }
                    this.state = 106;
                    this._errHandler.sync(this);
                    _la = this._input.LA(1);
                }
                this.state = 107;
                this.match(ScriptParser.RBRACK);
            }
        }
        catch (re) {
            if (re instanceof antlr4_1.RecognitionException) {
                localctx.exception = re;
                this._errHandler.reportError(this, re);
                this._errHandler.recover(this, re);
            }
            else {
                throw re;
            }
        }
        finally {
            this.exitRule();
        }
        return localctx;
    }
    sempred(localctx, ruleIndex, predIndex) {
        switch (ruleIndex) {
            case 2:
                return this.stactic_sempred(localctx, predIndex);
        }
        return true;
    }
    stactic_sempred(localctx, predIndex) {
        switch (predIndex) {
            case 0:
                return this.precpred(this._ctx, 3);
            case 1:
                return this.precpred(this._ctx, 2);
        }
        return true;
    }
    static _serializedATN = [4, 1, 24, 110, 2, 0, 7, 0, 2,
        1, 7, 1, 2, 2, 7, 2, 2, 3, 7, 3, 2, 4, 7, 4, 1, 0, 5, 0, 12, 8, 0, 10, 0, 12, 0, 15, 9, 0, 1, 0, 5, 0, 18,
        8, 0, 10, 0, 12, 0, 21, 9, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 1, 1, 1, 3, 1, 38, 8, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 5, 2, 49, 8, 2, 10,
        2, 12, 2, 52, 9, 2, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 5,
        3, 68, 8, 3, 10, 3, 12, 3, 71, 9, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 4, 3, 79, 8, 3, 11, 3, 12, 3,
        80, 1, 3, 5, 3, 84, 8, 3, 10, 3, 12, 3, 87, 9, 3, 4, 3, 89, 8, 3, 11, 3, 12, 3, 90, 3, 3, 93, 8, 3, 1,
        4, 1, 4, 3, 4, 97, 8, 4, 1, 4, 1, 4, 3, 4, 101, 8, 4, 5, 4, 103, 8, 4, 10, 4, 12, 4, 106, 9, 4, 1, 4,
        1, 4, 1, 4, 0, 1, 4, 5, 0, 2, 4, 6, 8, 0, 0, 129, 0, 13, 1, 0, 0, 0, 2, 37, 1, 0, 0, 0, 4, 39, 1, 0, 0,
        0, 6, 92, 1, 0, 0, 0, 8, 94, 1, 0, 0, 0, 10, 12, 5, 24, 0, 0, 11, 10, 1, 0, 0, 0, 12, 15, 1, 0, 0, 0,
        13, 11, 1, 0, 0, 0, 13, 14, 1, 0, 0, 0, 14, 19, 1, 0, 0, 0, 15, 13, 1, 0, 0, 0, 16, 18, 3, 2, 1, 0, 17,
        16, 1, 0, 0, 0, 18, 21, 1, 0, 0, 0, 19, 17, 1, 0, 0, 0, 19, 20, 1, 0, 0, 0, 20, 1, 1, 0, 0, 0, 21, 19,
        1, 0, 0, 0, 22, 23, 3, 4, 2, 0, 23, 24, 5, 1, 0, 0, 24, 38, 1, 0, 0, 0, 25, 26, 5, 12, 0, 0, 26, 27,
        3, 4, 2, 0, 27, 28, 5, 1, 0, 0, 28, 38, 1, 0, 0, 0, 29, 30, 5, 11, 0, 0, 30, 31, 3, 4, 2, 0, 31, 32,
        5, 1, 0, 0, 32, 38, 1, 0, 0, 0, 33, 38, 5, 5, 0, 0, 34, 38, 5, 6, 0, 0, 35, 38, 5, 9, 0, 0, 36, 38, 5,
        22, 0, 0, 37, 22, 1, 0, 0, 0, 37, 25, 1, 0, 0, 0, 37, 29, 1, 0, 0, 0, 37, 33, 1, 0, 0, 0, 37, 34, 1,
        0, 0, 0, 37, 35, 1, 0, 0, 0, 37, 36, 1, 0, 0, 0, 38, 3, 1, 0, 0, 0, 39, 40, 6, 2, -1, 0, 40, 41, 3, 6,
        3, 0, 41, 50, 1, 0, 0, 0, 42, 43, 10, 3, 0, 0, 43, 44, 5, 2, 0, 0, 44, 49, 3, 6, 3, 0, 45, 46, 10, 2,
        0, 0, 46, 47, 5, 2, 0, 0, 47, 49, 3, 8, 4, 0, 48, 42, 1, 0, 0, 0, 48, 45, 1, 0, 0, 0, 49, 52, 1, 0, 0,
        0, 50, 48, 1, 0, 0, 0, 50, 51, 1, 0, 0, 0, 51, 5, 1, 0, 0, 0, 52, 50, 1, 0, 0, 0, 53, 54, 5, 13, 0, 0,
        54, 93, 3, 8, 4, 0, 55, 56, 5, 14, 0, 0, 56, 93, 3, 6, 3, 0, 57, 58, 5, 15, 0, 0, 58, 93, 3, 6, 3, 0,
        59, 60, 5, 16, 0, 0, 60, 93, 3, 6, 3, 0, 61, 93, 5, 17, 0, 0, 62, 63, 5, 21, 0, 0, 63, 93, 3, 4, 2,
        0, 64, 69, 5, 18, 0, 0, 65, 66, 5, 19, 0, 0, 66, 68, 3, 6, 3, 0, 67, 65, 1, 0, 0, 0, 68, 71, 1, 0, 0,
        0, 69, 67, 1, 0, 0, 0, 69, 70, 1, 0, 0, 0, 70, 72, 1, 0, 0, 0, 71, 69, 1, 0, 0, 0, 72, 93, 5, 20, 0,
        0, 73, 74, 5, 3, 0, 0, 74, 75, 3, 4, 2, 0, 75, 76, 5, 4, 0, 0, 76, 93, 1, 0, 0, 0, 77, 79, 5, 23, 0,
        0, 78, 77, 1, 0, 0, 0, 79, 80, 1, 0, 0, 0, 80, 78, 1, 0, 0, 0, 80, 81, 1, 0, 0, 0, 81, 85, 1, 0, 0, 0,
        82, 84, 5, 24, 0, 0, 83, 82, 1, 0, 0, 0, 84, 87, 1, 0, 0, 0, 85, 83, 1, 0, 0, 0, 85, 86, 1, 0, 0, 0,
        86, 89, 1, 0, 0, 0, 87, 85, 1, 0, 0, 0, 88, 78, 1, 0, 0, 0, 89, 90, 1, 0, 0, 0, 90, 88, 1, 0, 0, 0, 90,
        91, 1, 0, 0, 0, 91, 93, 1, 0, 0, 0, 92, 53, 1, 0, 0, 0, 92, 55, 1, 0, 0, 0, 92, 57, 1, 0, 0, 0, 92, 59,
        1, 0, 0, 0, 92, 61, 1, 0, 0, 0, 92, 62, 1, 0, 0, 0, 92, 64, 1, 0, 0, 0, 92, 73, 1, 0, 0, 0, 92, 88, 1,
        0, 0, 0, 93, 7, 1, 0, 0, 0, 94, 96, 5, 7, 0, 0, 95, 97, 3, 4, 2, 0, 96, 95, 1, 0, 0, 0, 96, 97, 1, 0,
        0, 0, 97, 104, 1, 0, 0, 0, 98, 100, 5, 10, 0, 0, 99, 101, 3, 4, 2, 0, 100, 99, 1, 0, 0, 0, 100, 101,
        1, 0, 0, 0, 101, 103, 1, 0, 0, 0, 102, 98, 1, 0, 0, 0, 103, 106, 1, 0, 0, 0, 104, 102, 1, 0, 0, 0,
        104, 105, 1, 0, 0, 0, 105, 107, 1, 0, 0, 0, 106, 104, 1, 0, 0, 0, 107, 108, 5, 8, 0, 0, 108, 9, 1,
        0, 0, 0, 13, 13, 19, 37, 48, 50, 69, 80, 85, 90, 92, 96, 100, 104];
    static __ATN;
    static get _ATN() {
        if (!ScriptParser.__ATN) {
            ScriptParser.__ATN = new antlr4_1.ATNDeserializer().deserialize(ScriptParser._serializedATN);
        }
        return ScriptParser.__ATN;
    }
    static DecisionsToDFA = ScriptParser._ATN.decisionToState.map((ds, index) => new antlr4_1.DFA(ds, index));
}
exports.default = ScriptParser;
class ScriptContext extends antlr4_1.ParserRuleContext {
    constructor(parser, parent, invokingState) {
        super(parent, invokingState);
        this.parser = parser;
    }
    WS_list() {
        return this.getTokens(ScriptParser.WS);
    }
    WS(i) {
        return this.getToken(ScriptParser.WS, i);
    }
    sentence_list() {
        return this.getTypedRuleContexts(SentenceContext);
    }
    sentence(i) {
        return this.getTypedRuleContext(SentenceContext, i);
    }
    get ruleIndex() {
        return ScriptParser.RULE_script;
    }
    enterRule(listener) {
        if (listener.enterScript) {
            listener.enterScript(this);
        }
    }
    exitRule(listener) {
        if (listener.exitScript) {
            listener.exitScript(this);
        }
    }
    // @Override
    accept(visitor) {
        if (visitor.visitScript) {
            return visitor.visitScript(this);
        }
        else {
            return visitor.visitChildren(this);
        }
    }
}
exports.ScriptContext = ScriptContext;
class SentenceContext extends antlr4_1.ParserRuleContext {
    constructor(parser, parent, invokingState) {
        super(parent, invokingState);
        this.parser = parser;
    }
    get ruleIndex() {
        return ScriptParser.RULE_sentence;
    }
    copyFrom(ctx) {
        super.copyFrom(ctx);
    }
}
exports.SentenceContext = SentenceContext;
class AllContext extends SentenceContext {
    constructor(parser, ctx) {
        super(parser, ctx.parentCtx, ctx.invokingState);
        super.copyFrom(ctx);
    }
    ALL() {
        return this.getToken(ScriptParser.ALL, 0);
    }
    stactic() {
        return this.getTypedRuleContext(StacticContext, 0);
    }
    PERIOD() {
        return this.getToken(ScriptParser.PERIOD, 0);
    }
    enterRule(listener) {
        if (listener.enterAll) {
            listener.enterAll(this);
        }
    }
    exitRule(listener) {
        if (listener.exitAll) {
            listener.exitAll(this);
        }
    }
    // @Override
    accept(visitor) {
        if (visitor.visitAll) {
            return visitor.visitAll(this);
        }
        else {
            return visitor.visitChildren(this);
        }
    }
}
exports.AllContext = AllContext;
class LBraceContext extends SentenceContext {
    constructor(parser, ctx) {
        super(parser, ctx.parentCtx, ctx.invokingState);
        super.copyFrom(ctx);
    }
    LBRACE() {
        return this.getToken(ScriptParser.LBRACE, 0);
    }
    enterRule(listener) {
        if (listener.enterLBrace) {
            listener.enterLBrace(this);
        }
    }
    exitRule(listener) {
        if (listener.exitLBrace) {
            listener.exitLBrace(this);
        }
    }
    // @Override
    accept(visitor) {
        if (visitor.visitLBrace) {
            return visitor.visitLBrace(this);
        }
        else {
            return visitor.visitChildren(this);
        }
    }
}
exports.LBraceContext = LBraceContext;
class BulletContext extends SentenceContext {
    constructor(parser, ctx) {
        super(parser, ctx.parentCtx, ctx.invokingState);
        super.copyFrom(ctx);
    }
    BULLET() {
        return this.getToken(ScriptParser.BULLET, 0);
    }
    enterRule(listener) {
        if (listener.enterBullet) {
            listener.enterBullet(this);
        }
    }
    exitRule(listener) {
        if (listener.exitBullet) {
            listener.exitBullet(this);
        }
    }
    // @Override
    accept(visitor) {
        if (visitor.visitBullet) {
            return visitor.visitBullet(this);
        }
        else {
            return visitor.visitChildren(this);
        }
    }
}
exports.BulletContext = BulletContext;
class CommentContext extends SentenceContext {
    constructor(parser, ctx) {
        super(parser, ctx.parentCtx, ctx.invokingState);
        super.copyFrom(ctx);
    }
    COMMENT() {
        return this.getToken(ScriptParser.COMMENT, 0);
    }
    enterRule(listener) {
        if (listener.enterComment) {
            listener.enterComment(this);
        }
    }
    exitRule(listener) {
        if (listener.exitComment) {
            listener.exitComment(this);
        }
    }
    // @Override
    accept(visitor) {
        if (visitor.visitComment) {
            return visitor.visitComment(this);
        }
        else {
            return visitor.visitChildren(this);
        }
    }
}
exports.CommentContext = CommentContext;
class NthContext extends SentenceContext {
    constructor(parser, ctx) {
        super(parser, ctx.parentCtx, ctx.invokingState);
        super.copyFrom(ctx);
    }
    NTH() {
        return this.getToken(ScriptParser.NTH, 0);
    }
    stactic() {
        return this.getTypedRuleContext(StacticContext, 0);
    }
    PERIOD() {
        return this.getToken(ScriptParser.PERIOD, 0);
    }
    enterRule(listener) {
        if (listener.enterNth) {
            listener.enterNth(this);
        }
    }
    exitRule(listener) {
        if (listener.exitNth) {
            listener.exitNth(this);
        }
    }
    // @Override
    accept(visitor) {
        if (visitor.visitNth) {
            return visitor.visitNth(this);
        }
        else {
            return visitor.visitChildren(this);
        }
    }
}
exports.NthContext = NthContext;
class RBraceContext extends SentenceContext {
    constructor(parser, ctx) {
        super(parser, ctx.parentCtx, ctx.invokingState);
        super.copyFrom(ctx);
    }
    RBRACE() {
        return this.getToken(ScriptParser.RBRACE, 0);
    }
    enterRule(listener) {
        if (listener.enterRBrace) {
            listener.enterRBrace(this);
        }
    }
    exitRule(listener) {
        if (listener.exitRBrace) {
            listener.exitRBrace(this);
        }
    }
    // @Override
    accept(visitor) {
        if (visitor.visitRBrace) {
            return visitor.visitRBrace(this);
        }
        else {
            return visitor.visitChildren(this);
        }
    }
}
exports.RBraceContext = RBraceContext;
class OneContext extends SentenceContext {
    constructor(parser, ctx) {
        super(parser, ctx.parentCtx, ctx.invokingState);
        super.copyFrom(ctx);
    }
    stactic() {
        return this.getTypedRuleContext(StacticContext, 0);
    }
    PERIOD() {
        return this.getToken(ScriptParser.PERIOD, 0);
    }
    enterRule(listener) {
        if (listener.enterOne) {
            listener.enterOne(this);
        }
    }
    exitRule(listener) {
        if (listener.exitOne) {
            listener.exitOne(this);
        }
    }
    // @Override
    accept(visitor) {
        if (visitor.visitOne) {
            return visitor.visitOne(this);
        }
        else {
            return visitor.visitChildren(this);
        }
    }
}
exports.OneContext = OneContext;
class StacticContext extends antlr4_1.ParserRuleContext {
    constructor(parser, parent, invokingState) {
        super(parent, invokingState);
        this.parser = parser;
    }
    get ruleIndex() {
        return ScriptParser.RULE_stactic;
    }
    copyFrom(ctx) {
        super.copyFrom(ctx);
    }
}
exports.StacticContext = StacticContext;
class SemicolonContext extends StacticContext {
    constructor(parser, ctx) {
        super(parser, ctx.parentCtx, ctx.invokingState);
        super.copyFrom(ctx);
    }
    stactic() {
        return this.getTypedRuleContext(StacticContext, 0);
    }
    SEMICOLON() {
        return this.getToken(ScriptParser.SEMICOLON, 0);
    }
    tactic() {
        return this.getTypedRuleContext(TacticContext, 0);
    }
    enterRule(listener) {
        if (listener.enterSemicolon) {
            listener.enterSemicolon(this);
        }
    }
    exitRule(listener) {
        if (listener.exitSemicolon) {
            listener.exitSemicolon(this);
        }
    }
    // @Override
    accept(visitor) {
        if (visitor.visitSemicolon) {
            return visitor.visitSemicolon(this);
        }
        else {
            return visitor.visitChildren(this);
        }
    }
}
exports.SemicolonContext = SemicolonContext;
class SemicolonManyContext extends StacticContext {
    constructor(parser, ctx) {
        super(parser, ctx.parentCtx, ctx.invokingState);
        super.copyFrom(ctx);
    }
    stactic() {
        return this.getTypedRuleContext(StacticContext, 0);
    }
    SEMICOLON() {
        return this.getToken(ScriptParser.SEMICOLON, 0);
    }
    bracket() {
        return this.getTypedRuleContext(BracketContext, 0);
    }
    enterRule(listener) {
        if (listener.enterSemicolonMany) {
            listener.enterSemicolonMany(this);
        }
    }
    exitRule(listener) {
        if (listener.exitSemicolonMany) {
            listener.exitSemicolonMany(this);
        }
    }
    // @Override
    accept(visitor) {
        if (visitor.visitSemicolonMany) {
            return visitor.visitSemicolonMany(this);
        }
        else {
            return visitor.visitChildren(this);
        }
    }
}
exports.SemicolonManyContext = SemicolonManyContext;
class GeneralContext extends StacticContext {
    constructor(parser, ctx) {
        super(parser, ctx.parentCtx, ctx.invokingState);
        super.copyFrom(ctx);
    }
    tactic() {
        return this.getTypedRuleContext(TacticContext, 0);
    }
    enterRule(listener) {
        if (listener.enterGeneral) {
            listener.enterGeneral(this);
        }
    }
    exitRule(listener) {
        if (listener.exitGeneral) {
            listener.exitGeneral(this);
        }
    }
    // @Override
    accept(visitor) {
        if (visitor.visitGeneral) {
            return visitor.visitGeneral(this);
        }
        else {
            return visitor.visitChildren(this);
        }
    }
}
exports.GeneralContext = GeneralContext;
class TacticContext extends antlr4_1.ParserRuleContext {
    constructor(parser, parent, invokingState) {
        super(parent, invokingState);
        this.parser = parser;
    }
    get ruleIndex() {
        return ScriptParser.RULE_tactic;
    }
    copyFrom(ctx) {
        super.copyFrom(ctx);
    }
}
exports.TacticContext = TacticContext;
class AutoContext extends TacticContext {
    constructor(parser, ctx) {
        super(parser, ctx.parentCtx, ctx.invokingState);
        super.copyFrom(ctx);
    }
    AUTO() {
        return this.getToken(ScriptParser.AUTO, 0);
    }
    enterRule(listener) {
        if (listener.enterAuto) {
            listener.enterAuto(this);
        }
    }
    exitRule(listener) {
        if (listener.exitAuto) {
            listener.exitAuto(this);
        }
    }
    // @Override
    accept(visitor) {
        if (visitor.visitAuto) {
            return visitor.visitAuto(this);
        }
        else {
            return visitor.visitChildren(this);
        }
    }
}
exports.AutoContext = AutoContext;
class ProgressContext extends TacticContext {
    constructor(parser, ctx) {
        super(parser, ctx.parentCtx, ctx.invokingState);
        super.copyFrom(ctx);
    }
    PROGRESS() {
        return this.getToken(ScriptParser.PROGRESS, 0);
    }
    tactic() {
        return this.getTypedRuleContext(TacticContext, 0);
    }
    enterRule(listener) {
        if (listener.enterProgress) {
            listener.enterProgress(this);
        }
    }
    exitRule(listener) {
        if (listener.exitProgress) {
            listener.exitProgress(this);
        }
    }
    // @Override
    accept(visitor) {
        if (visitor.visitProgress) {
            return visitor.visitProgress(this);
        }
        else {
            return visitor.visitChildren(this);
        }
    }
}
exports.ProgressContext = ProgressContext;
class OpaqueContext extends TacticContext {
    constructor(parser, ctx) {
        super(parser, ctx.parentCtx, ctx.invokingState);
        super.copyFrom(ctx);
    }
    TANY_list() {
        return this.getTokens(ScriptParser.TANY);
    }
    TANY(i) {
        return this.getToken(ScriptParser.TANY, i);
    }
    WS_list() {
        return this.getTokens(ScriptParser.WS);
    }
    WS(i) {
        return this.getToken(ScriptParser.WS, i);
    }
    enterRule(listener) {
        if (listener.enterOpaque) {
            listener.enterOpaque(this);
        }
    }
    exitRule(listener) {
        if (listener.exitOpaque) {
            listener.exitOpaque(this);
        }
    }
    // @Override
    accept(visitor) {
        if (visitor.visitOpaque) {
            return visitor.visitOpaque(this);
        }
        else {
            return visitor.visitChildren(this);
        }
    }
}
exports.OpaqueContext = OpaqueContext;
class TryContext extends TacticContext {
    constructor(parser, ctx) {
        super(parser, ctx.parentCtx, ctx.invokingState);
        super.copyFrom(ctx);
    }
    TRY() {
        return this.getToken(ScriptParser.TRY, 0);
    }
    tactic() {
        return this.getTypedRuleContext(TacticContext, 0);
    }
    enterRule(listener) {
        if (listener.enterTry) {
            listener.enterTry(this);
        }
    }
    exitRule(listener) {
        if (listener.exitTry) {
            listener.exitTry(this);
        }
    }
    // @Override
    accept(visitor) {
        if (visitor.visitTry) {
            return visitor.visitTry(this);
        }
        else {
            return visitor.visitChildren(this);
        }
    }
}
exports.TryContext = TryContext;
class RepeatContext extends TacticContext {
    constructor(parser, ctx) {
        super(parser, ctx.parentCtx, ctx.invokingState);
        super.copyFrom(ctx);
    }
    REPEAT() {
        return this.getToken(ScriptParser.REPEAT, 0);
    }
    tactic() {
        return this.getTypedRuleContext(TacticContext, 0);
    }
    enterRule(listener) {
        if (listener.enterRepeat) {
            listener.enterRepeat(this);
        }
    }
    exitRule(listener) {
        if (listener.exitRepeat) {
            listener.exitRepeat(this);
        }
    }
    // @Override
    accept(visitor) {
        if (visitor.visitRepeat) {
            return visitor.visitRepeat(this);
        }
        else {
            return visitor.visitChildren(this);
        }
    }
}
exports.RepeatContext = RepeatContext;
class FirstContext extends TacticContext {
    constructor(parser, ctx) {
        super(parser, ctx.parentCtx, ctx.invokingState);
        super.copyFrom(ctx);
    }
    FIRST() {
        return this.getToken(ScriptParser.FIRST, 0);
    }
    bracket() {
        return this.getTypedRuleContext(BracketContext, 0);
    }
    enterRule(listener) {
        if (listener.enterFirst) {
            listener.enterFirst(this);
        }
    }
    exitRule(listener) {
        if (listener.exitFirst) {
            listener.exitFirst(this);
        }
    }
    // @Override
    accept(visitor) {
        if (visitor.visitFirst) {
            return visitor.visitFirst(this);
        }
        else {
            return visitor.visitChildren(this);
        }
    }
}
exports.FirstContext = FirstContext;
class FailContext extends TacticContext {
    constructor(parser, ctx) {
        super(parser, ctx.parentCtx, ctx.invokingState);
        super.copyFrom(ctx);
    }
    FAIL() {
        return this.getToken(ScriptParser.FAIL, 0);
    }
    stactic() {
        return this.getTypedRuleContext(StacticContext, 0);
    }
    enterRule(listener) {
        if (listener.enterFail) {
            listener.enterFail(this);
        }
    }
    exitRule(listener) {
        if (listener.exitFail) {
            listener.exitFail(this);
        }
    }
    // @Override
    accept(visitor) {
        if (visitor.visitFail) {
            return visitor.visitFail(this);
        }
        else {
            return visitor.visitChildren(this);
        }
    }
}
exports.FailContext = FailContext;
class MatchContext extends TacticContext {
    constructor(parser, ctx) {
        super(parser, ctx.parentCtx, ctx.invokingState);
        super.copyFrom(ctx);
    }
    MATCHGOAL() {
        return this.getToken(ScriptParser.MATCHGOAL, 0);
    }
    END() {
        return this.getToken(ScriptParser.END, 0);
    }
    CASE_list() {
        return this.getTokens(ScriptParser.CASE);
    }
    CASE(i) {
        return this.getToken(ScriptParser.CASE, i);
    }
    tactic_list() {
        return this.getTypedRuleContexts(TacticContext);
    }
    tactic(i) {
        return this.getTypedRuleContext(TacticContext, i);
    }
    enterRule(listener) {
        if (listener.enterMatch) {
            listener.enterMatch(this);
        }
    }
    exitRule(listener) {
        if (listener.exitMatch) {
            listener.exitMatch(this);
        }
    }
    // @Override
    accept(visitor) {
        if (visitor.visitMatch) {
            return visitor.visitMatch(this);
        }
        else {
            return visitor.visitChildren(this);
        }
    }
}
exports.MatchContext = MatchContext;
class ParenContext extends TacticContext {
    constructor(parser, ctx) {
        super(parser, ctx.parentCtx, ctx.invokingState);
        super.copyFrom(ctx);
    }
    LPAREN() {
        return this.getToken(ScriptParser.LPAREN, 0);
    }
    stactic() {
        return this.getTypedRuleContext(StacticContext, 0);
    }
    RPAREN() {
        return this.getToken(ScriptParser.RPAREN, 0);
    }
    enterRule(listener) {
        if (listener.enterParen) {
            listener.enterParen(this);
        }
    }
    exitRule(listener) {
        if (listener.exitParen) {
            listener.exitParen(this);
        }
    }
    // @Override
    accept(visitor) {
        if (visitor.visitParen) {
            return visitor.visitParen(this);
        }
        else {
            return visitor.visitChildren(this);
        }
    }
}
exports.ParenContext = ParenContext;
class BracketContext extends antlr4_1.ParserRuleContext {
    constructor(parser, parent, invokingState) {
        super(parent, invokingState);
        this.parser = parser;
    }
    LBRACK() {
        return this.getToken(ScriptParser.LBRACK, 0);
    }
    RBRACK() {
        return this.getToken(ScriptParser.RBRACK, 0);
    }
    stactic_list() {
        return this.getTypedRuleContexts(StacticContext);
    }
    stactic(i) {
        return this.getTypedRuleContext(StacticContext, i);
    }
    BAR_list() {
        return this.getTokens(ScriptParser.BAR);
    }
    BAR(i) {
        return this.getToken(ScriptParser.BAR, i);
    }
    get ruleIndex() {
        return ScriptParser.RULE_bracket;
    }
    enterRule(listener) {
        if (listener.enterBracket) {
            listener.enterBracket(this);
        }
    }
    exitRule(listener) {
        if (listener.exitBracket) {
            listener.exitBracket(this);
        }
    }
    // @Override
    accept(visitor) {
        if (visitor.visitBracket) {
            return visitor.visitBracket(this);
        }
        else {
            return visitor.visitChildren(this);
        }
    }
}
exports.BracketContext = BracketContext;
//# sourceMappingURL=ScriptParser.js.map