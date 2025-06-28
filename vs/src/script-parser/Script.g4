grammar Script;

script: WS* sentence*;
sentence:
    stactic PERIOD #One
    | NTH stactic PERIOD #Nth
    | ALL stactic PERIOD #All
    | LBRACE #LBrace
    | RBRACE #RBrace
    | BULLET #Bullet
    | COMMENT #Comment
    ;
stactic:
    stactic SEMICOLON tactic #Semicolon
    | stactic SEMICOLON bracket #SemicolonMany
    | tactic #General
    ;
tactic:
    FIRST bracket #First
    | PROGRESS tactic #Progress
    | TRY tactic #Try
    | REPEAT tactic #Repeat
    | AUTO #Auto
    | FAIL stactic #Fail
    | MATCHGOAL (CASE tactic)* END #Match
    | LPAREN stactic RPAREN #Paren
    | (TANY+ WS*)+ #Opaque
    ;
bracket:
    LBRACK stactic? (BAR stactic?)* RBRACK
    ;

PERIOD: '.' (WS+ | EOF);
SEMICOLON: ';' WS*;

LPAREN: '(' WS*;
RPAREN: ')' WS*;
LBRACE: '{' WS*;
RBRACE: '}' WS*;
LBRACK: '[' WS*;
RBRACK: ']' WS*;

BULLET: ('-' | '+' | '*')+ WS+;

BAR: '|' WS*;

ALL: 'all' WS* ':' WS+;
NTH: [1-9][0-9]* WS* ':' WS+;
FIRST: 'first' WS+;
PROGRESS: 'progress' WS+;
TRY: 'try' WS+;
REPEAT: 'repeat' WS+;
AUTO: 'e'?'auto' WS*;
MATCHGOAL: 'match' WS+ 'goal' WS+ 'with' WS*;
CASE: '|' .+? '=>' WS*;
END: 'end' WS*;

FAIL: 'Fail' WS+;

COMMENT: '(*' (COMMENT | .)*? '*)' WS*;

TANY: [A-Za-z0-9@_,];
WS: [ \n\t\r];