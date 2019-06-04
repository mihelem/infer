%{
  module F = Format
%}

%token <string> IDENTIFIER
%token <string> CFLOAT
%token PLUS
%token MINUS
%token DIV
%token MULT
%token LPAR
%token RPAR
%token LAND
%token LOR
%token NE
%token LE
%token GE
%token EQ
%token LT
%token GT
%token NOT
%token EOL

%left LOR
%left LAND
%nonassoc EQ, NE, LT, LE, GT, GE
%right NOT
%left PLUS, MINUS
%left MULT
%left DIV

%start <string> expr
%%

aexpr:
  | IDENTIFIER { $1 }
  | CFLOAT { F.sprintf "Const.Cfloat %s" $1 }
  | LPAR aexpr RPAR { $2 }
  | MINUS aexpr { F.sprintf "Exp.UnOp (Unop.Neg, %s, None)" $2 }
  | aexpr PLUS aexpr { F.sprintf "Exp.BinOp (Binop.PlusA None, %s, %s)" $1 $3 }
  | aexpr MINUS aexpr { F.sprintf "Exp.BinOp (Binop.MinusA None, %s, %s)" $1 $3 }
  | aexpr MULT aexpr { F.sprintf "Exp.BinOp (Binop.Mult None, %s, %s)" $1 $3 }
  | aexpr DIV aexpr { F.sprintf "Exp.BinOp (Binop.Div, %s, %s)" $1 $3 }
  ;

bexpr:
  | LPAR bexpr RPAR { $2 }
  | bexpr LOR bexpr { F.sprintf "Exp.BinOp (Binop.LOr, %s, %s)" $1 $3 }
  | bexpr LAND bexpr { F.sprintf "Exp.BinOp (Binop.LAnd, %s, %s)" $1 $3 }
  | NOT bexpr { F.sprintf "Exp.UnOp (Unop.LNot, %s)" $2 }
  | aexpr LE aexpr { F.sprintf "Exp.BinOp (Binop.Le, %s, %s)" $1 $3}
  | aexpr LT aexpr { F.sprintf "Exp.BinOp (Binop.Lt, %s, %s)" $1 $3 }
  | aexpr GE aexpr { F.sprintf "Exp.BinOp (Binop.Ge, %s, %s)" $1 $3 }
  | aexpr GT aexpr { F.sprintf "Exp.BinOp (Binop.Gt, %s, %s)" $1 $3 }
  | aexpr EQ aexpr { F.sprintf "Exp.BinOp (Binop.Eq, %s, %s)" $1 $3 }
  | aexpr NE aexpr { "Exp.BinOp (Binop.Ne, "^ $1 ^", "^$3^")" }
  ;

expr:
  | bexpr EOL { $1 }  
