#lang alpha-agnostic

type lam is
  | Var reference
  | Lam binder lam↓0
  | App lam lam
end.

type sem is
  | L env binder lam↓0 @ 1
  | N neu
end.

type neu is
  | V reference
  | A neu sem
end.

type env is
  | ENil
  | ECons env binder sem ↑0 @ 1
end.

fun reify (s : sem) returns r : lam
  where true -> fr r <= fr s is
  match s with
  | L env y t =>
      fresh x in
      Lam(x reify( evals( ECons( env y N(V(x))) t)))
  | N n =>
      reifyn(n)
  end.
end.

fun reifyn (n : neu) returns r: lam
  where true -> fr r <= fr n is
  match n with
  | V x =>
    Var(x)
  | A nn d =>
    App( reifyn(nn) reify(d))
  end.
end.

fun evals (env : env t : lam) returns v : sem
  where true -> f v <= fr env + (fa t \ fb env) is
  match t with
  | Var x =>
    match env with
    | ENil =>
      N(V(x))
    | ECons tail y v =>
      if x = y then v
      else evals(tail t)
    end.
  | Lam x tt =>
    L(env x tt)
  | App t1 t2 =>
    match evals(env t1) with
    | L cenv x tt =>
      evals(ECons(cenv x evals(env t2)) tt)
    | N n =>
      N(A(n evals(env t2)))
    end.
  end.
end.

fun eval (t : lam) returns sem is
  evals(ENil() t)
end.

fun normalize (t : lam) returns lam is
  reify(eval(t))
end.