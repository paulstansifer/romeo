#lang alpha-agnostic


type expr is
  | Val value
  | App expr expr
end.
   
type value is
  | Var reference
  | Abs binder expr↓0
end.
 
fun transform_expr (e : expr, k : reference) returns r : expr where true -> fr e + fr k = fr r is
  match e with
  | Val v => App(Val(Var(k)), transform_value(v))
  | App e0 e1 => transform_application(e0, e1, Var(k))
  end.
end.
   
fun transform_application (e0 : expr, e1 : expr, k : value) returns r : expr where true -> fr e0 + fr e1 + fr k = fr r is
  match e0 with
  | Val v0 => match e1 with
              | Val v1 => App(App(transform_value(v0), transform_value(v1)), Val(k))
              | App e10 e11 => fresh x1 in
                                 transform_application (e10, e11, Abs(x1, App(App(transform_value(v0), Val(Var (x1))), Val(k))))
              end.
  | App e00 e01 => match e1 with
                   | Val v1 => fresh x0 in
                                 transform_application (e00, e01, Abs(x0, App(App(Val(Var(x0)), transform_value (v1)), Val(k))))

                   | App e10 e11 => fresh x0 x1 in
                                      transform_application (e00, e01, Abs (x0, transform_application(e10, e11, Abs(x1, App(App(Val(Var(x0)), Val(Var(x1))), Val(k))))))
                   end.
  end.
end.

fun transform_value (v : value) returns r : expr where true -> fr v = fr r is
 match v with
 | Var x => Val(v)
 | Abs x e => fresh k in
                Val(Abs (x, Val(Abs (k, transform_expr(e k)))))
  end.
end.

fun transform (e : expr) returns r : expr where true -> fr e = fr r is
  fresh k in Val(Abs (k, transform_expr(e k)))
end.
