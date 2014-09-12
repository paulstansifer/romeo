#lang alpha-agnostic

type term is
  | Var reference
  | Lambda binder term↓0
  | App term term
  | Let binder term term↓0
  | If term term term
end.

type context is
  | CEmpty
  | CLet binder term context↓0 ↑0 @ 2
  | CCompose context context↓0 ↑0 @ 1
end.

type closure is
  | Clo context term↓0
end.

type bool is
  | True
  | False
end.

fun fill (clo : closure) returns r : term
  where true -> fr r = fr clo is
  match clo with
  | Clo c t =>
    match c with
    | CEmpty => 
       t
    | CLet x t1 c2 =>
       Let(x t1 fill(Clo(c2 t)))
    | CCompose c1 c2 =>
       fill(Clo(c1 fill(Clo(c2 t))))
    end.
  end.
end.

fun norm (t : term) returns r : term
  where true -> fr r = fr t is
  fill(split(t False()))
end.

fun split (t : term mode : bool) returns r : closure 
  where true -> fr r = fr t is
  match t with
  | Var x =>
    Clo(CEmpty() t)
  | Lambda x tt =>
    Clo(CEmpty() Lambda(x norm(tt)))
  | App t1 t2 =>
    ilet s1 = split(t1,True()) in
      match s1 with
      | Clo c1 u1 =>
        match split(t2 True()) with
        | Clo c2 u2 =>
          valueify(Clo(CCompose(c1 c2) App(u1 u2)) mode)
        end.
      end.
  | Let x t1 t2 =>
    match split(t1 False()) with
    | Clo c1 u1 =>
      match split(t2 mode) with
      | Clo c2 u2 =>
        Clo(CCompose(c1 CLet(x u1 c2)) u2)
      end.
    end.
  | If t1 t2 t3 =>
    match split(t1 True()) with
    | Clo c1 u1 =>
      valueify(Clo(c1 If(u1 norm(t2) norm(t3))) mode)
    end.
  end.
end.

fun valueify (clo : closure mode: bool) returns r: closure
  where true -> fr r = fr clo is
  match mode with
  | True =>
    match clo with
    | Clo c t =>
      fresh gaga in
      Clo(CCompose(c CLet(gaga t CEmpty())) Var(gaga))
    end.
  | False =>
    clo
  end.
end.
    






