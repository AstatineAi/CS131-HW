%{
open Ast
open Lexing

let loc (startpos:Lexing.position) (endpos:Lexing.position) (elt:'a) : 'a node =
  { elt ; loc=Range.mk_lex_range startpos endpos }

%}

/* Declare your tokens here. */
%token EOF
%token <int64>  INT
%token NULL
%token <string> STRING
%token <string> IDENT

%token TINT     /* int */
%token TVOID    /* void */
%token TSTRING  /* string */
%token TBOOL    /* bool */
%token TRUE     /* true */
%token FALSE    /* false */
%token IF       /* if */
%token ELSE     /* else */
%token WHILE    /* while */
%token FOR      /* for */
%token RETURN   /* return */
%token VAR      /* var */
%token SEMI     /* ; */
%token COMMA    /* , */
%token LBRACE   /* { */
%token RBRACE   /* } */
%token PLUS     /* + */
%token DASH     /* - */
%token STAR     /* * */
%token EQEQ     /* == */
%token EQ       /* = */
%token LPAREN   /* ( */
%token RPAREN   /* ) */
%token LBRACKET /* [ */
%token RBRACKET /* ] */
%token TILDE    /* ~ */
%token BANG     /* ! */
%token NEQ      /* != */
%token LT       /* < */
%token LTE      /* <= */
%token GT       /* > */
%token GTE      /* >= */
%token SHR      /* >> */
%token SAR      /* >>> */
%token SHL      /* << */
%token AND      /* & */
%token OR       /* | */
%token IAND     /* [&] */
%token IOR      /* [|] */
%token GLOBAL   /* global */
%token NEW      /* new */


%left IOR             /* precedence 20 */
%left IAND            /* precedence 30 */
%left OR              /* precedence 40 */
%left AND             /* precedence 50 */
%left EQEQ NEQ        /* precedence 60 */
%left LT LTE GT GTE   /* precedence 70 */
%left SHL SHR SAR     /* precedence 80 */
%left PLUS DASH       /* precedence 90 */
%left STAR            /* precedence 100 */
%nonassoc BANG
%nonassoc TILDE
%nonassoc LBRACKET
%nonassoc LPAREN

/* ---------------------------------------------------------------------- */

%start prog
%start exp_top
%start stmt_top
%type <Ast.exp Ast.node> exp_top
%type <Ast.stmt Ast.node> stmt_top

%type <Ast.prog> prog
%type <Ast.exp Ast.node> exp
%type <Ast.stmt Ast.node> stmt
%type <Ast.block> block
%type <Ast.ty> ty
%%

exp_top:
  | e=exp EOF { e }

stmt_top:
  | s=stmt EOF { s }

prog:
  | p=list(decl) EOF  { p }

decl:
  | GLOBAL name=IDENT EQ init=gexp SEMI
    { Gvdecl (loc $startpos $endpos { name; init }) }
  | frtyp=ret_ty fname=IDENT LPAREN args=arglist RPAREN body=block
    { Gfdecl (loc $startpos $endpos { frtyp; fname; args; body }) }

arglist:
  | l=separated_list(COMMA, pair(ty,IDENT)) { l }
    
ty:
  | TBOOL  { TBool }
  | TINT   { TInt }
  | r=rtyp { TRef r } 


%inline ret_ty:
  | TVOID  { RetVoid }
  | t=ty   { RetVal t }

%inline rtyp:
  | TSTRING { RString }
  | t=ty LBRACKET RBRACKET { RArray t }

%inline bop:
  | PLUS   { Add }
  | DASH   { Sub }
  | STAR   { Mul }
  | EQEQ   { Eq } 
  | NEQ    { Neq }
  | LT     { Lt }
  | LTE    { Lte }
  | GT     { Gt }
  | GTE    { Gte }
  | AND    { And }
  | OR     { Or }
  | IAND   { IAnd }
  | IOR    { IOr }
  | SHL    { Shl }
  | SHR    { Shr }
  | SAR    { Sar }

%inline uop:
  | DASH  { Neg }
  | BANG  { Lognot }
  | TILDE { Bitnot }

gexp:
  | t=rtyp NULL  { loc $startpos $endpos @@ CNull t }
  | i=INT        { loc $startpos $endpos @@ CInt i } 
  | s=STRING     { loc $startpos $endpos @@ CStr s }
  | TRUE         { loc $startpos $endpos @@ CBool true }
  | FALSE        { loc $startpos $endpos @@ CBool false }
  | NEW t=ty LBRACKET RBRACKET LBRACE es=separated_list(COMMA, gexp) RBRACE
                 { loc $startpos $endpos @@ CArr (t, es) }

lhs:  
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  | e=exp LBRACKET i=exp RBRACKET
                        { loc $startpos $endpos @@ Index (e, i) }

exp:
  | i=INT               { loc $startpos $endpos @@ CInt i }
  | s=STRING            { loc $startpos $endpos @@ CStr s }
  | t=rtyp NULL         { loc $startpos $endpos @@ CNull t }
  | TRUE                { loc $startpos $endpos @@ CBool true }
  | FALSE               { loc $startpos $endpos @@ CBool false }
  | e1=exp b=bop e2=exp { loc $startpos $endpos @@ Bop (b, e1, e2) }
  | u=uop e=exp         { loc $startpos $endpos @@ Uop (u, e) }
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  | e=exp LBRACKET i=exp RBRACKET
                        { loc $startpos $endpos @@ Index (e, i) }
  | e=exp LPAREN es=separated_list(COMMA, exp) RPAREN
                        { loc $startpos $endpos @@ Call (e,es) }
  | LPAREN e=exp RPAREN { e } 
  | NEW t=ty LBRACKET RBRACKET LBRACE es=separated_list(COMMA, exp) RBRACE
                        { loc $startpos $endpos @@ CArr (t, es) }
  | NEW t=ty LBRACKET e=exp RBRACKET
                        { loc $startpos $endpos @@ NewArr (t, e) }

exp_opt:
  | (* empty *) { None }
  | e=exp       { Some e }

vdecl:
  | VAR id=IDENT EQ init=exp { (id, init) }

stmt: 
  | d=vdecl SEMI        { loc $startpos $endpos @@ Decl(d) }
  | p=lhs EQ e=exp SEMI { loc $startpos $endpos @@ Assn(p,e) }
  | e=exp LPAREN es=separated_list(COMMA, exp) RPAREN SEMI
                        { loc $startpos $endpos @@ SCall (e, es) }
  | ifs=if_stmt         { ifs }
  | RETURN SEMI         { loc $startpos $endpos @@ Ret(None) }
  | RETURN e=exp SEMI   { loc $startpos $endpos @@ Ret(Some e) }
  | WHILE LPAREN e=exp RPAREN b=block  
                        { loc $startpos $endpos @@ While(e, b) } 
  | FOR LPAREN v=separated_list(COMMA, vdecl) SEMI e_opt=exp_opt SEMI s_opt=stmt_opt RPAREN b=block
                        { loc $startpos $endpos @@ For(v, e_opt, s_opt, b) }

stmt_opt:
  | (* empty *) { None }
  | s=stmt      { Some s }

block:
  | LBRACE stmts=list(stmt) RBRACE { stmts }

if_stmt:
  | IF LPAREN e=exp RPAREN b1=block b2=else_stmt
    { loc $startpos $endpos @@ If(e,b1,b2) }

else_stmt:
  | (* empty *)       { [] }
  | ELSE b=block      { b }
  | ELSE ifs=if_stmt  { [ ifs ] }
