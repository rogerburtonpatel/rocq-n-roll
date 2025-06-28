// Generated from Script.g4 by ANTLR 4.13.2
// noinspection ES6UnusedImports,JSUnusedGlobalSymbols,JSUnusedLocalSymbols

import {
	ATN,
	ATNDeserializer, DecisionState, DFA, FailedPredicateException,
	RecognitionException, NoViableAltException, BailErrorStrategy,
	Parser, ParserATNSimulator,
	RuleContext, ParserRuleContext, PredictionMode, PredictionContextCache,
	TerminalNode, RuleNode,
	Token, TokenStream,
	Interval, IntervalSet
} from 'antlr4';
import ScriptListener from "./ScriptListener.js";
import ScriptVisitor from "./ScriptVisitor.js";

// for running tests with parameters, TODO: discuss strategy for typed parameters in CI
// eslint-disable-next-line no-unused-vars
type int = number;

export default class ScriptParser extends Parser {
	public static readonly PERIOD = 1;
	public static readonly SEMICOLON = 2;
	public static readonly LPAREN = 3;
	public static readonly RPAREN = 4;
	public static readonly LBRACE = 5;
	public static readonly RBRACE = 6;
	public static readonly LBRACK = 7;
	public static readonly RBRACK = 8;
	public static readonly BULLET = 9;
	public static readonly BAR = 10;
	public static readonly ALL = 11;
	public static readonly NTH = 12;
	public static readonly FIRST = 13;
	public static readonly PROGRESS = 14;
	public static readonly TRY = 15;
	public static readonly REPEAT = 16;
	public static readonly AUTO = 17;
	public static readonly MATCHGOAL = 18;
	public static readonly CASE = 19;
	public static readonly END = 20;
	public static readonly FAIL = 21;
	public static readonly COMMENT = 22;
	public static readonly TANY = 23;
	public static readonly WS = 24;
	public static override readonly EOF = Token.EOF;
	public static readonly RULE_script = 0;
	public static readonly RULE_sentence = 1;
	public static readonly RULE_stactic = 2;
	public static readonly RULE_tactic = 3;
	public static readonly RULE_bracket = 4;
	public static readonly literalNames: (string | null)[] = [  ];
	public static readonly symbolicNames: (string | null)[] = [ null, "PERIOD", 
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
                                                             "TANY", "WS" ];
	// tslint:disable:no-trailing-whitespace
	public static readonly ruleNames: string[] = [
		"script", "sentence", "stactic", "tactic", "bracket",
	];
	public get grammarFileName(): string { return "Script.g4"; }
	public get literalNames(): (string | null)[] { return ScriptParser.literalNames; }
	public get symbolicNames(): (string | null)[] { return ScriptParser.symbolicNames; }
	public get ruleNames(): string[] { return ScriptParser.ruleNames; }
	public get serializedATN(): number[] { return ScriptParser._serializedATN; }

	protected createFailedPredicateException(predicate?: string, message?: string): FailedPredicateException {
		return new FailedPredicateException(this, predicate, message);
	}

	constructor(input: TokenStream) {
		super(input);
		this._interp = new ParserATNSimulator(this, ScriptParser._ATN, ScriptParser.DecisionsToDFA, new PredictionContextCache());
	}
	// @RuleVersion(0)
	public script(): ScriptContext {
		let localctx: ScriptContext = new ScriptContext(this, this._ctx, this.state);
		this.enterRule(localctx, 0, ScriptParser.RULE_script);
		let _la: number;
		try {
			this.enterOuterAlt(localctx, 1);
			{
			this.state = 13;
			this._errHandler.sync(this);
			_la = this._input.LA(1);
			while (_la===24) {
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
			if (re instanceof RecognitionException) {
				localctx.exception = re;
				this._errHandler.reportError(this, re);
				this._errHandler.recover(this, re);
			} else {
				throw re;
			}
		}
		finally {
			this.exitRule();
		}
		return localctx;
	}
	// @RuleVersion(0)
	public sentence(): SentenceContext {
		let localctx: SentenceContext = new SentenceContext(this, this._ctx, this.state);
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
				throw new NoViableAltException(this);
			}
		}
		catch (re) {
			if (re instanceof RecognitionException) {
				localctx.exception = re;
				this._errHandler.reportError(this, re);
				this._errHandler.recover(this, re);
			} else {
				throw re;
			}
		}
		finally {
			this.exitRule();
		}
		return localctx;
	}

	public stactic(): StacticContext;
	public stactic(_p: number): StacticContext;
	// @RuleVersion(0)
	public stactic(_p?: number): StacticContext {
		if (_p === undefined) {
			_p = 0;
		}

		let _parentctx: ParserRuleContext = this._ctx;
		let _parentState: number = this.state;
		let localctx: StacticContext = new StacticContext(this, this._ctx, _parentState);
		let _prevctx: StacticContext = localctx;
		let _startState: number = 4;
		this.enterRecursionRule(localctx, 4, ScriptParser.RULE_stactic, _p);
		try {
			let _alt: number;
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
			while (_alt !== 2 && _alt !== ATN.INVALID_ALT_NUMBER) {
				if (_alt === 1) {
					if (this._parseListeners != null) {
						this.triggerExitRuleEvent();
					}
					_prevctx = localctx;
					{
					this.state = 48;
					this._errHandler.sync(this);
					switch ( this._interp.adaptivePredict(this._input, 3, this._ctx) ) {
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
			if (re instanceof RecognitionException) {
				localctx.exception = re;
				this._errHandler.reportError(this, re);
				this._errHandler.recover(this, re);
			} else {
				throw re;
			}
		}
		finally {
			this.unrollRecursionContexts(_parentctx);
		}
		return localctx;
	}
	// @RuleVersion(0)
	public tactic(): TacticContext {
		let localctx: TacticContext = new TacticContext(this, this._ctx, this.state);
		this.enterRule(localctx, 6, ScriptParser.RULE_tactic);
		let _la: number;
		try {
			let _alt: number;
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
				while (_la===19) {
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
								throw new NoViableAltException(this);
							}
							this.state = 80;
							this._errHandler.sync(this);
							_alt = this._interp.adaptivePredict(this._input, 6, this._ctx);
						} while (_alt !== 2 && _alt !== ATN.INVALID_ALT_NUMBER);
						this.state = 85;
						this._errHandler.sync(this);
						_alt = this._interp.adaptivePredict(this._input, 7, this._ctx);
						while (_alt !== 2 && _alt !== ATN.INVALID_ALT_NUMBER) {
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
						throw new NoViableAltException(this);
					}
					this.state = 90;
					this._errHandler.sync(this);
					_alt = this._interp.adaptivePredict(this._input, 8, this._ctx);
				} while (_alt !== 2 && _alt !== ATN.INVALID_ALT_NUMBER);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (re) {
			if (re instanceof RecognitionException) {
				localctx.exception = re;
				this._errHandler.reportError(this, re);
				this._errHandler.recover(this, re);
			} else {
				throw re;
			}
		}
		finally {
			this.exitRule();
		}
		return localctx;
	}
	// @RuleVersion(0)
	public bracket(): BracketContext {
		let localctx: BracketContext = new BracketContext(this, this._ctx, this.state);
		this.enterRule(localctx, 8, ScriptParser.RULE_bracket);
		let _la: number;
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
			while (_la===10) {
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
			if (re instanceof RecognitionException) {
				localctx.exception = re;
				this._errHandler.reportError(this, re);
				this._errHandler.recover(this, re);
			} else {
				throw re;
			}
		}
		finally {
			this.exitRule();
		}
		return localctx;
	}

	public sempred(localctx: RuleContext, ruleIndex: number, predIndex: number): boolean {
		switch (ruleIndex) {
		case 2:
			return this.stactic_sempred(localctx as StacticContext, predIndex);
		}
		return true;
	}
	private stactic_sempred(localctx: StacticContext, predIndex: number): boolean {
		switch (predIndex) {
		case 0:
			return this.precpred(this._ctx, 3);
		case 1:
			return this.precpred(this._ctx, 2);
		}
		return true;
	}

	public static readonly _serializedATN: number[] = [4,1,24,110,2,0,7,0,2,
	1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,1,0,5,0,12,8,0,10,0,12,0,15,9,0,1,0,5,0,18,
	8,0,10,0,12,0,21,9,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
	1,1,1,1,1,3,1,38,8,1,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,5,2,49,8,2,10,
	2,12,2,52,9,2,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,5,
	3,68,8,3,10,3,12,3,71,9,3,1,3,1,3,1,3,1,3,1,3,1,3,4,3,79,8,3,11,3,12,3,
	80,1,3,5,3,84,8,3,10,3,12,3,87,9,3,4,3,89,8,3,11,3,12,3,90,3,3,93,8,3,1,
	4,1,4,3,4,97,8,4,1,4,1,4,3,4,101,8,4,5,4,103,8,4,10,4,12,4,106,9,4,1,4,
	1,4,1,4,0,1,4,5,0,2,4,6,8,0,0,129,0,13,1,0,0,0,2,37,1,0,0,0,4,39,1,0,0,
	0,6,92,1,0,0,0,8,94,1,0,0,0,10,12,5,24,0,0,11,10,1,0,0,0,12,15,1,0,0,0,
	13,11,1,0,0,0,13,14,1,0,0,0,14,19,1,0,0,0,15,13,1,0,0,0,16,18,3,2,1,0,17,
	16,1,0,0,0,18,21,1,0,0,0,19,17,1,0,0,0,19,20,1,0,0,0,20,1,1,0,0,0,21,19,
	1,0,0,0,22,23,3,4,2,0,23,24,5,1,0,0,24,38,1,0,0,0,25,26,5,12,0,0,26,27,
	3,4,2,0,27,28,5,1,0,0,28,38,1,0,0,0,29,30,5,11,0,0,30,31,3,4,2,0,31,32,
	5,1,0,0,32,38,1,0,0,0,33,38,5,5,0,0,34,38,5,6,0,0,35,38,5,9,0,0,36,38,5,
	22,0,0,37,22,1,0,0,0,37,25,1,0,0,0,37,29,1,0,0,0,37,33,1,0,0,0,37,34,1,
	0,0,0,37,35,1,0,0,0,37,36,1,0,0,0,38,3,1,0,0,0,39,40,6,2,-1,0,40,41,3,6,
	3,0,41,50,1,0,0,0,42,43,10,3,0,0,43,44,5,2,0,0,44,49,3,6,3,0,45,46,10,2,
	0,0,46,47,5,2,0,0,47,49,3,8,4,0,48,42,1,0,0,0,48,45,1,0,0,0,49,52,1,0,0,
	0,50,48,1,0,0,0,50,51,1,0,0,0,51,5,1,0,0,0,52,50,1,0,0,0,53,54,5,13,0,0,
	54,93,3,8,4,0,55,56,5,14,0,0,56,93,3,6,3,0,57,58,5,15,0,0,58,93,3,6,3,0,
	59,60,5,16,0,0,60,93,3,6,3,0,61,93,5,17,0,0,62,63,5,21,0,0,63,93,3,4,2,
	0,64,69,5,18,0,0,65,66,5,19,0,0,66,68,3,6,3,0,67,65,1,0,0,0,68,71,1,0,0,
	0,69,67,1,0,0,0,69,70,1,0,0,0,70,72,1,0,0,0,71,69,1,0,0,0,72,93,5,20,0,
	0,73,74,5,3,0,0,74,75,3,4,2,0,75,76,5,4,0,0,76,93,1,0,0,0,77,79,5,23,0,
	0,78,77,1,0,0,0,79,80,1,0,0,0,80,78,1,0,0,0,80,81,1,0,0,0,81,85,1,0,0,0,
	82,84,5,24,0,0,83,82,1,0,0,0,84,87,1,0,0,0,85,83,1,0,0,0,85,86,1,0,0,0,
	86,89,1,0,0,0,87,85,1,0,0,0,88,78,1,0,0,0,89,90,1,0,0,0,90,88,1,0,0,0,90,
	91,1,0,0,0,91,93,1,0,0,0,92,53,1,0,0,0,92,55,1,0,0,0,92,57,1,0,0,0,92,59,
	1,0,0,0,92,61,1,0,0,0,92,62,1,0,0,0,92,64,1,0,0,0,92,73,1,0,0,0,92,88,1,
	0,0,0,93,7,1,0,0,0,94,96,5,7,0,0,95,97,3,4,2,0,96,95,1,0,0,0,96,97,1,0,
	0,0,97,104,1,0,0,0,98,100,5,10,0,0,99,101,3,4,2,0,100,99,1,0,0,0,100,101,
	1,0,0,0,101,103,1,0,0,0,102,98,1,0,0,0,103,106,1,0,0,0,104,102,1,0,0,0,
	104,105,1,0,0,0,105,107,1,0,0,0,106,104,1,0,0,0,107,108,5,8,0,0,108,9,1,
	0,0,0,13,13,19,37,48,50,69,80,85,90,92,96,100,104];

	private static __ATN: ATN;
	public static get _ATN(): ATN {
		if (!ScriptParser.__ATN) {
			ScriptParser.__ATN = new ATNDeserializer().deserialize(ScriptParser._serializedATN);
		}

		return ScriptParser.__ATN;
	}


	static DecisionsToDFA = ScriptParser._ATN.decisionToState.map( (ds: DecisionState, index: number) => new DFA(ds, index) );

}

export class ScriptContext extends ParserRuleContext {
	constructor(parser?: ScriptParser, parent?: ParserRuleContext, invokingState?: number) {
		super(parent, invokingState);
    	this.parser = parser;
	}
	public WS_list(): TerminalNode[] {
	    	return this.getTokens(ScriptParser.WS);
	}
	public WS(i: number): TerminalNode {
		return this.getToken(ScriptParser.WS, i);
	}
	public sentence_list(): SentenceContext[] {
		return this.getTypedRuleContexts(SentenceContext) as SentenceContext[];
	}
	public sentence(i: number): SentenceContext {
		return this.getTypedRuleContext(SentenceContext, i) as SentenceContext;
	}
    public get ruleIndex(): number {
    	return ScriptParser.RULE_script;
	}
	public enterRule(listener: ScriptListener): void {
	    if(listener.enterScript) {
	 		listener.enterScript(this);
		}
	}
	public exitRule(listener: ScriptListener): void {
	    if(listener.exitScript) {
	 		listener.exitScript(this);
		}
	}
	// @Override
	public accept<Result>(visitor: ScriptVisitor<Result>): Result {
		if (visitor.visitScript) {
			return visitor.visitScript(this);
		} else {
			return visitor.visitChildren(this);
		}
	}
}


export class SentenceContext extends ParserRuleContext {
	constructor(parser?: ScriptParser, parent?: ParserRuleContext, invokingState?: number) {
		super(parent, invokingState);
    	this.parser = parser;
	}
    public get ruleIndex(): number {
    	return ScriptParser.RULE_sentence;
	}
	public override copyFrom(ctx: SentenceContext): void {
		super.copyFrom(ctx);
	}
}
export class AllContext extends SentenceContext {
	constructor(parser: ScriptParser, ctx: SentenceContext) {
		super(parser, ctx.parentCtx, ctx.invokingState);
		super.copyFrom(ctx);
	}
	public ALL(): TerminalNode {
		return this.getToken(ScriptParser.ALL, 0);
	}
	public stactic(): StacticContext {
		return this.getTypedRuleContext(StacticContext, 0) as StacticContext;
	}
	public PERIOD(): TerminalNode {
		return this.getToken(ScriptParser.PERIOD, 0);
	}
	public enterRule(listener: ScriptListener): void {
	    if(listener.enterAll) {
	 		listener.enterAll(this);
		}
	}
	public exitRule(listener: ScriptListener): void {
	    if(listener.exitAll) {
	 		listener.exitAll(this);
		}
	}
	// @Override
	public accept<Result>(visitor: ScriptVisitor<Result>): Result {
		if (visitor.visitAll) {
			return visitor.visitAll(this);
		} else {
			return visitor.visitChildren(this);
		}
	}
}
export class LBraceContext extends SentenceContext {
	constructor(parser: ScriptParser, ctx: SentenceContext) {
		super(parser, ctx.parentCtx, ctx.invokingState);
		super.copyFrom(ctx);
	}
	public LBRACE(): TerminalNode {
		return this.getToken(ScriptParser.LBRACE, 0);
	}
	public enterRule(listener: ScriptListener): void {
	    if(listener.enterLBrace) {
	 		listener.enterLBrace(this);
		}
	}
	public exitRule(listener: ScriptListener): void {
	    if(listener.exitLBrace) {
	 		listener.exitLBrace(this);
		}
	}
	// @Override
	public accept<Result>(visitor: ScriptVisitor<Result>): Result {
		if (visitor.visitLBrace) {
			return visitor.visitLBrace(this);
		} else {
			return visitor.visitChildren(this);
		}
	}
}
export class BulletContext extends SentenceContext {
	constructor(parser: ScriptParser, ctx: SentenceContext) {
		super(parser, ctx.parentCtx, ctx.invokingState);
		super.copyFrom(ctx);
	}
	public BULLET(): TerminalNode {
		return this.getToken(ScriptParser.BULLET, 0);
	}
	public enterRule(listener: ScriptListener): void {
	    if(listener.enterBullet) {
	 		listener.enterBullet(this);
		}
	}
	public exitRule(listener: ScriptListener): void {
	    if(listener.exitBullet) {
	 		listener.exitBullet(this);
		}
	}
	// @Override
	public accept<Result>(visitor: ScriptVisitor<Result>): Result {
		if (visitor.visitBullet) {
			return visitor.visitBullet(this);
		} else {
			return visitor.visitChildren(this);
		}
	}
}
export class CommentContext extends SentenceContext {
	constructor(parser: ScriptParser, ctx: SentenceContext) {
		super(parser, ctx.parentCtx, ctx.invokingState);
		super.copyFrom(ctx);
	}
	public COMMENT(): TerminalNode {
		return this.getToken(ScriptParser.COMMENT, 0);
	}
	public enterRule(listener: ScriptListener): void {
	    if(listener.enterComment) {
	 		listener.enterComment(this);
		}
	}
	public exitRule(listener: ScriptListener): void {
	    if(listener.exitComment) {
	 		listener.exitComment(this);
		}
	}
	// @Override
	public accept<Result>(visitor: ScriptVisitor<Result>): Result {
		if (visitor.visitComment) {
			return visitor.visitComment(this);
		} else {
			return visitor.visitChildren(this);
		}
	}
}
export class NthContext extends SentenceContext {
	constructor(parser: ScriptParser, ctx: SentenceContext) {
		super(parser, ctx.parentCtx, ctx.invokingState);
		super.copyFrom(ctx);
	}
	public NTH(): TerminalNode {
		return this.getToken(ScriptParser.NTH, 0);
	}
	public stactic(): StacticContext {
		return this.getTypedRuleContext(StacticContext, 0) as StacticContext;
	}
	public PERIOD(): TerminalNode {
		return this.getToken(ScriptParser.PERIOD, 0);
	}
	public enterRule(listener: ScriptListener): void {
	    if(listener.enterNth) {
	 		listener.enterNth(this);
		}
	}
	public exitRule(listener: ScriptListener): void {
	    if(listener.exitNth) {
	 		listener.exitNth(this);
		}
	}
	// @Override
	public accept<Result>(visitor: ScriptVisitor<Result>): Result {
		if (visitor.visitNth) {
			return visitor.visitNth(this);
		} else {
			return visitor.visitChildren(this);
		}
	}
}
export class RBraceContext extends SentenceContext {
	constructor(parser: ScriptParser, ctx: SentenceContext) {
		super(parser, ctx.parentCtx, ctx.invokingState);
		super.copyFrom(ctx);
	}
	public RBRACE(): TerminalNode {
		return this.getToken(ScriptParser.RBRACE, 0);
	}
	public enterRule(listener: ScriptListener): void {
	    if(listener.enterRBrace) {
	 		listener.enterRBrace(this);
		}
	}
	public exitRule(listener: ScriptListener): void {
	    if(listener.exitRBrace) {
	 		listener.exitRBrace(this);
		}
	}
	// @Override
	public accept<Result>(visitor: ScriptVisitor<Result>): Result {
		if (visitor.visitRBrace) {
			return visitor.visitRBrace(this);
		} else {
			return visitor.visitChildren(this);
		}
	}
}
export class OneContext extends SentenceContext {
	constructor(parser: ScriptParser, ctx: SentenceContext) {
		super(parser, ctx.parentCtx, ctx.invokingState);
		super.copyFrom(ctx);
	}
	public stactic(): StacticContext {
		return this.getTypedRuleContext(StacticContext, 0) as StacticContext;
	}
	public PERIOD(): TerminalNode {
		return this.getToken(ScriptParser.PERIOD, 0);
	}
	public enterRule(listener: ScriptListener): void {
	    if(listener.enterOne) {
	 		listener.enterOne(this);
		}
	}
	public exitRule(listener: ScriptListener): void {
	    if(listener.exitOne) {
	 		listener.exitOne(this);
		}
	}
	// @Override
	public accept<Result>(visitor: ScriptVisitor<Result>): Result {
		if (visitor.visitOne) {
			return visitor.visitOne(this);
		} else {
			return visitor.visitChildren(this);
		}
	}
}


export class StacticContext extends ParserRuleContext {
	constructor(parser?: ScriptParser, parent?: ParserRuleContext, invokingState?: number) {
		super(parent, invokingState);
    	this.parser = parser;
	}
    public get ruleIndex(): number {
    	return ScriptParser.RULE_stactic;
	}
	public override copyFrom(ctx: StacticContext): void {
		super.copyFrom(ctx);
	}
}
export class SemicolonContext extends StacticContext {
	constructor(parser: ScriptParser, ctx: StacticContext) {
		super(parser, ctx.parentCtx, ctx.invokingState);
		super.copyFrom(ctx);
	}
	public stactic(): StacticContext {
		return this.getTypedRuleContext(StacticContext, 0) as StacticContext;
	}
	public SEMICOLON(): TerminalNode {
		return this.getToken(ScriptParser.SEMICOLON, 0);
	}
	public tactic(): TacticContext {
		return this.getTypedRuleContext(TacticContext, 0) as TacticContext;
	}
	public enterRule(listener: ScriptListener): void {
	    if(listener.enterSemicolon) {
	 		listener.enterSemicolon(this);
		}
	}
	public exitRule(listener: ScriptListener): void {
	    if(listener.exitSemicolon) {
	 		listener.exitSemicolon(this);
		}
	}
	// @Override
	public accept<Result>(visitor: ScriptVisitor<Result>): Result {
		if (visitor.visitSemicolon) {
			return visitor.visitSemicolon(this);
		} else {
			return visitor.visitChildren(this);
		}
	}
}
export class SemicolonManyContext extends StacticContext {
	constructor(parser: ScriptParser, ctx: StacticContext) {
		super(parser, ctx.parentCtx, ctx.invokingState);
		super.copyFrom(ctx);
	}
	public stactic(): StacticContext {
		return this.getTypedRuleContext(StacticContext, 0) as StacticContext;
	}
	public SEMICOLON(): TerminalNode {
		return this.getToken(ScriptParser.SEMICOLON, 0);
	}
	public bracket(): BracketContext {
		return this.getTypedRuleContext(BracketContext, 0) as BracketContext;
	}
	public enterRule(listener: ScriptListener): void {
	    if(listener.enterSemicolonMany) {
	 		listener.enterSemicolonMany(this);
		}
	}
	public exitRule(listener: ScriptListener): void {
	    if(listener.exitSemicolonMany) {
	 		listener.exitSemicolonMany(this);
		}
	}
	// @Override
	public accept<Result>(visitor: ScriptVisitor<Result>): Result {
		if (visitor.visitSemicolonMany) {
			return visitor.visitSemicolonMany(this);
		} else {
			return visitor.visitChildren(this);
		}
	}
}
export class GeneralContext extends StacticContext {
	constructor(parser: ScriptParser, ctx: StacticContext) {
		super(parser, ctx.parentCtx, ctx.invokingState);
		super.copyFrom(ctx);
	}
	public tactic(): TacticContext {
		return this.getTypedRuleContext(TacticContext, 0) as TacticContext;
	}
	public enterRule(listener: ScriptListener): void {
	    if(listener.enterGeneral) {
	 		listener.enterGeneral(this);
		}
	}
	public exitRule(listener: ScriptListener): void {
	    if(listener.exitGeneral) {
	 		listener.exitGeneral(this);
		}
	}
	// @Override
	public accept<Result>(visitor: ScriptVisitor<Result>): Result {
		if (visitor.visitGeneral) {
			return visitor.visitGeneral(this);
		} else {
			return visitor.visitChildren(this);
		}
	}
}


export class TacticContext extends ParserRuleContext {
	constructor(parser?: ScriptParser, parent?: ParserRuleContext, invokingState?: number) {
		super(parent, invokingState);
    	this.parser = parser;
	}
    public get ruleIndex(): number {
    	return ScriptParser.RULE_tactic;
	}
	public override copyFrom(ctx: TacticContext): void {
		super.copyFrom(ctx);
	}
}
export class AutoContext extends TacticContext {
	constructor(parser: ScriptParser, ctx: TacticContext) {
		super(parser, ctx.parentCtx, ctx.invokingState);
		super.copyFrom(ctx);
	}
	public AUTO(): TerminalNode {
		return this.getToken(ScriptParser.AUTO, 0);
	}
	public enterRule(listener: ScriptListener): void {
	    if(listener.enterAuto) {
	 		listener.enterAuto(this);
		}
	}
	public exitRule(listener: ScriptListener): void {
	    if(listener.exitAuto) {
	 		listener.exitAuto(this);
		}
	}
	// @Override
	public accept<Result>(visitor: ScriptVisitor<Result>): Result {
		if (visitor.visitAuto) {
			return visitor.visitAuto(this);
		} else {
			return visitor.visitChildren(this);
		}
	}
}
export class ProgressContext extends TacticContext {
	constructor(parser: ScriptParser, ctx: TacticContext) {
		super(parser, ctx.parentCtx, ctx.invokingState);
		super.copyFrom(ctx);
	}
	public PROGRESS(): TerminalNode {
		return this.getToken(ScriptParser.PROGRESS, 0);
	}
	public tactic(): TacticContext {
		return this.getTypedRuleContext(TacticContext, 0) as TacticContext;
	}
	public enterRule(listener: ScriptListener): void {
	    if(listener.enterProgress) {
	 		listener.enterProgress(this);
		}
	}
	public exitRule(listener: ScriptListener): void {
	    if(listener.exitProgress) {
	 		listener.exitProgress(this);
		}
	}
	// @Override
	public accept<Result>(visitor: ScriptVisitor<Result>): Result {
		if (visitor.visitProgress) {
			return visitor.visitProgress(this);
		} else {
			return visitor.visitChildren(this);
		}
	}
}
export class OpaqueContext extends TacticContext {
	constructor(parser: ScriptParser, ctx: TacticContext) {
		super(parser, ctx.parentCtx, ctx.invokingState);
		super.copyFrom(ctx);
	}
	public TANY_list(): TerminalNode[] {
	    	return this.getTokens(ScriptParser.TANY);
	}
	public TANY(i: number): TerminalNode {
		return this.getToken(ScriptParser.TANY, i);
	}
	public WS_list(): TerminalNode[] {
	    	return this.getTokens(ScriptParser.WS);
	}
	public WS(i: number): TerminalNode {
		return this.getToken(ScriptParser.WS, i);
	}
	public enterRule(listener: ScriptListener): void {
	    if(listener.enterOpaque) {
	 		listener.enterOpaque(this);
		}
	}
	public exitRule(listener: ScriptListener): void {
	    if(listener.exitOpaque) {
	 		listener.exitOpaque(this);
		}
	}
	// @Override
	public accept<Result>(visitor: ScriptVisitor<Result>): Result {
		if (visitor.visitOpaque) {
			return visitor.visitOpaque(this);
		} else {
			return visitor.visitChildren(this);
		}
	}
}
export class TryContext extends TacticContext {
	constructor(parser: ScriptParser, ctx: TacticContext) {
		super(parser, ctx.parentCtx, ctx.invokingState);
		super.copyFrom(ctx);
	}
	public TRY(): TerminalNode {
		return this.getToken(ScriptParser.TRY, 0);
	}
	public tactic(): TacticContext {
		return this.getTypedRuleContext(TacticContext, 0) as TacticContext;
	}
	public enterRule(listener: ScriptListener): void {
	    if(listener.enterTry) {
	 		listener.enterTry(this);
		}
	}
	public exitRule(listener: ScriptListener): void {
	    if(listener.exitTry) {
	 		listener.exitTry(this);
		}
	}
	// @Override
	public accept<Result>(visitor: ScriptVisitor<Result>): Result {
		if (visitor.visitTry) {
			return visitor.visitTry(this);
		} else {
			return visitor.visitChildren(this);
		}
	}
}
export class RepeatContext extends TacticContext {
	constructor(parser: ScriptParser, ctx: TacticContext) {
		super(parser, ctx.parentCtx, ctx.invokingState);
		super.copyFrom(ctx);
	}
	public REPEAT(): TerminalNode {
		return this.getToken(ScriptParser.REPEAT, 0);
	}
	public tactic(): TacticContext {
		return this.getTypedRuleContext(TacticContext, 0) as TacticContext;
	}
	public enterRule(listener: ScriptListener): void {
	    if(listener.enterRepeat) {
	 		listener.enterRepeat(this);
		}
	}
	public exitRule(listener: ScriptListener): void {
	    if(listener.exitRepeat) {
	 		listener.exitRepeat(this);
		}
	}
	// @Override
	public accept<Result>(visitor: ScriptVisitor<Result>): Result {
		if (visitor.visitRepeat) {
			return visitor.visitRepeat(this);
		} else {
			return visitor.visitChildren(this);
		}
	}
}
export class FirstContext extends TacticContext {
	constructor(parser: ScriptParser, ctx: TacticContext) {
		super(parser, ctx.parentCtx, ctx.invokingState);
		super.copyFrom(ctx);
	}
	public FIRST(): TerminalNode {
		return this.getToken(ScriptParser.FIRST, 0);
	}
	public bracket(): BracketContext {
		return this.getTypedRuleContext(BracketContext, 0) as BracketContext;
	}
	public enterRule(listener: ScriptListener): void {
	    if(listener.enterFirst) {
	 		listener.enterFirst(this);
		}
	}
	public exitRule(listener: ScriptListener): void {
	    if(listener.exitFirst) {
	 		listener.exitFirst(this);
		}
	}
	// @Override
	public accept<Result>(visitor: ScriptVisitor<Result>): Result {
		if (visitor.visitFirst) {
			return visitor.visitFirst(this);
		} else {
			return visitor.visitChildren(this);
		}
	}
}
export class FailContext extends TacticContext {
	constructor(parser: ScriptParser, ctx: TacticContext) {
		super(parser, ctx.parentCtx, ctx.invokingState);
		super.copyFrom(ctx);
	}
	public FAIL(): TerminalNode {
		return this.getToken(ScriptParser.FAIL, 0);
	}
	public stactic(): StacticContext {
		return this.getTypedRuleContext(StacticContext, 0) as StacticContext;
	}
	public enterRule(listener: ScriptListener): void {
	    if(listener.enterFail) {
	 		listener.enterFail(this);
		}
	}
	public exitRule(listener: ScriptListener): void {
	    if(listener.exitFail) {
	 		listener.exitFail(this);
		}
	}
	// @Override
	public accept<Result>(visitor: ScriptVisitor<Result>): Result {
		if (visitor.visitFail) {
			return visitor.visitFail(this);
		} else {
			return visitor.visitChildren(this);
		}
	}
}
export class MatchContext extends TacticContext {
	constructor(parser: ScriptParser, ctx: TacticContext) {
		super(parser, ctx.parentCtx, ctx.invokingState);
		super.copyFrom(ctx);
	}
	public MATCHGOAL(): TerminalNode {
		return this.getToken(ScriptParser.MATCHGOAL, 0);
	}
	public END(): TerminalNode {
		return this.getToken(ScriptParser.END, 0);
	}
	public CASE_list(): TerminalNode[] {
	    	return this.getTokens(ScriptParser.CASE);
	}
	public CASE(i: number): TerminalNode {
		return this.getToken(ScriptParser.CASE, i);
	}
	public tactic_list(): TacticContext[] {
		return this.getTypedRuleContexts(TacticContext) as TacticContext[];
	}
	public tactic(i: number): TacticContext {
		return this.getTypedRuleContext(TacticContext, i) as TacticContext;
	}
	public enterRule(listener: ScriptListener): void {
	    if(listener.enterMatch) {
	 		listener.enterMatch(this);
		}
	}
	public exitRule(listener: ScriptListener): void {
	    if(listener.exitMatch) {
	 		listener.exitMatch(this);
		}
	}
	// @Override
	public accept<Result>(visitor: ScriptVisitor<Result>): Result {
		if (visitor.visitMatch) {
			return visitor.visitMatch(this);
		} else {
			return visitor.visitChildren(this);
		}
	}
}
export class ParenContext extends TacticContext {
	constructor(parser: ScriptParser, ctx: TacticContext) {
		super(parser, ctx.parentCtx, ctx.invokingState);
		super.copyFrom(ctx);
	}
	public LPAREN(): TerminalNode {
		return this.getToken(ScriptParser.LPAREN, 0);
	}
	public stactic(): StacticContext {
		return this.getTypedRuleContext(StacticContext, 0) as StacticContext;
	}
	public RPAREN(): TerminalNode {
		return this.getToken(ScriptParser.RPAREN, 0);
	}
	public enterRule(listener: ScriptListener): void {
	    if(listener.enterParen) {
	 		listener.enterParen(this);
		}
	}
	public exitRule(listener: ScriptListener): void {
	    if(listener.exitParen) {
	 		listener.exitParen(this);
		}
	}
	// @Override
	public accept<Result>(visitor: ScriptVisitor<Result>): Result {
		if (visitor.visitParen) {
			return visitor.visitParen(this);
		} else {
			return visitor.visitChildren(this);
		}
	}
}


export class BracketContext extends ParserRuleContext {
	constructor(parser?: ScriptParser, parent?: ParserRuleContext, invokingState?: number) {
		super(parent, invokingState);
    	this.parser = parser;
	}
	public LBRACK(): TerminalNode {
		return this.getToken(ScriptParser.LBRACK, 0);
	}
	public RBRACK(): TerminalNode {
		return this.getToken(ScriptParser.RBRACK, 0);
	}
	public stactic_list(): StacticContext[] {
		return this.getTypedRuleContexts(StacticContext) as StacticContext[];
	}
	public stactic(i: number): StacticContext {
		return this.getTypedRuleContext(StacticContext, i) as StacticContext;
	}
	public BAR_list(): TerminalNode[] {
	    	return this.getTokens(ScriptParser.BAR);
	}
	public BAR(i: number): TerminalNode {
		return this.getToken(ScriptParser.BAR, i);
	}
    public get ruleIndex(): number {
    	return ScriptParser.RULE_bracket;
	}
	public enterRule(listener: ScriptListener): void {
	    if(listener.enterBracket) {
	 		listener.enterBracket(this);
		}
	}
	public exitRule(listener: ScriptListener): void {
	    if(listener.exitBracket) {
	 		listener.exitBracket(this);
		}
	}
	// @Override
	public accept<Result>(visitor: ScriptVisitor<Result>): Result {
		if (visitor.visitBracket) {
			return visitor.visitBracket(this);
		} else {
			return visitor.visitChildren(this);
		}
	}
}
