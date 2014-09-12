#lang alpha-agnostic

type Pair is
  | P binder binder ↑0@1
end.
  
fun incomp (b1 : binder b2 : binder b3 : binder p : Pair) returns out : Pair
  where fb b1 # fb b2 && fb b1 # fb b3 && fb b2 # fb b3 && fb b1 + fb b2 + fb b3 <= fb p && fr b1 = () -> fb out = fb p is
; This goes through:
  p
; This is found to be absurd (opening and re-constructing p):
;  match p with
;   | P pb1 pb2 => P(pb1 pb2)
;  end.
end.