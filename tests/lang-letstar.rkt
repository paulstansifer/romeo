#lang alpha-agnostic

type Expr/Let is
  | App/Let Expr/Let Expr/Let
  | Lam/Let binder Expr/Let↓0
  | Var/Let reference
  | LetStar Let-Clauses Expr/Let↓0
end.

type Let-Clauses is
  | LCNone
  | LCBind binder Expr/Let Let-Clauses↓0 ↑ 0 #+ 2
end.

type Expr is
  | App Expr Expr
  | Lam binder Expr↓0
  | Var reference
end.

fun convert (e : Expr/Let) returns out : Expr where true -> fr out = fr e   is
  match e with
  | App/Let e1 e2 => App(convert(e1) convert(e2))
  | Lam/Let x e1 => Lam(x convert(e1))
  | Var/Let x => Var(x)
  | LetStar lc e1 =>
    match lc with
    | LCNone => convert(e1)
    | LCBind x be rest => App( Lam( x convert (LetStar (rest e1))) convert(be))
    end.
  end.
end.
