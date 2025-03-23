Require Export ssreflect Utf8 CpdtTactics Frap ZArith.
Close Scope string_scope.
Open Scope Z_scope.


(* A useful tactic to quickly break (x ?= y) into cases. *)
Hint Rewrite Z.compare_eq_iff Z.compare_lt_iff Z.compare_gt_iff : core.
Ltac case_compare' x y :=
  let i := fresh "Heq" in
  remember (x ?= y) as e eqn:i;
  symmetry in i;
  destruct e; simplify.
(* A variant that also adds `crush` to try to close out as many goals as possible. *)
Ltac case_compare x y :=
  case_compare' x y; crush.
