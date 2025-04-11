Require Import ssreflect Utf8 CpdtTactics Util FunInd.
Require Import Arith Orders OrdersTac OrdersFacts.
Require Import DecidableClass.
Require Import ssrbool.
Require Import FrapWithoutSets.
Require Import Psatz.
From Coq.micromega Require Import RingMicromega QMicromega EnvRing Tauto Zify.
Require Import Classical ClassicalDescription IndefiniteDescription.

Set Implicit Arguments.
Close Scope string_scope.
Close Scope boolean_if_scope.
Open Scope general_if_scope.
Close Scope Z_scope.
Search (?a ^ ?b) "mul".


(* we're going to say no to setoid hell today, please give us the usual equality thank you *)
Module AVL (OT : UsualOrderedType').
  Include EqLtNotation OT.
  Include CmpNotation OT OT.

  Include OrderedTypeFacts OT.
  Include OrderedTypeTest OT.

  Local Notation A := OT.t.
  Notation compare := OT.compare.

  Local Notation Eq := Datatypes.Eq.
  Local Notation Lt := Datatypes.Lt.
  Local Notation Gt := Datatypes.Gt.

  Hint Rewrite compare_eq_iff compare_lt_iff compare_gt_iff : core.
  Hint Extern 1 => order : core.
  (* Hint Rewrite compare_refl : core. *)

  (* if we're trying to match a compare in the goal,
  then we automatically simplify it depending on the assumptions present.  *)
  Ltac rewrite_match_compare :=
    match goal with
    | [ |- context[match compare ?x ?x with | _ => _ end] ] =>
        rewrite compare_refl
    | [ H : ?x < ?y |- context[match compare ?x ?y with | _ => _ end] ] =>
        rewrite (proj2 (compare_lt_iff x y) H)
    | [ H : ?y < ?x |- context[match compare ?x ?y with | _ => _ end] ] =>
        rewrite (proj2 (compare_gt_iff x y) H)
    end.
  Hint Extern 1 => rewrite_match_compare : core.

  Ltac case_compare' x y :=
    let i := fresh "Heq" in
    let e := fresh in
    remember (compare x y) as e eqn:i;
    symmetry in i;
    destruct e; simplify; try order.
  (* A variant that also adds `crush` to try to close out as many goals as possible. *)
  Ltac case_compare x y :=
    case_compare' x y; crush; try order.

  (* binary tree of our ordered type *)
  Inductive tree : Type :=
  | Nil  : tree
  | Node : ∀ (v : A) (l : tree) (r : tree), tree.
  Hint Constructors tree : core.
  (* in this file, we don't bother with storing the heights or sizes as in-node information.
  * as a consequence, all operations are far slower than they actually could be.
  * the trade-off is that we have less to juggle. *)

  Definition singleton x : tree := Node x Nil Nil.

  (* get the height of a tree  *)
  Fixpoint height (t : tree) : nat :=
    match t with
    | Nil => 0
    | Node _ l r => 1 + Nat.max (height l) (height r)
    end.

  Fixpoint size (t : tree) : nat :=
    match t with
    | Nil => 0
    | Node _ l r => 1 + (size l) + (size r)
    end.

  Section Contains_In.

    (* returns true if x in t else false; only guaranteed if t is a BST *)
    Fixpoint Containsb x t : bool :=
      match t with
      | Nil => false
      | Node v l r =>
          match (v ?= x) with
          | Eq => true
          | Gt => Containsb x l
          | Lt => Containsb x r
          end
      end.
    Locate Eq.

    (* prop-valued version *)
    Fixpoint Contains x t : Prop :=
      match t with
      | Nil => False
      | Node v l r =>
          match (v ?= x) with
          | Eq => True
          | Gt => Contains x l
          | Lt => Contains x r
          end
      end.

    (* And as an inductive proposition instead *)
    Inductive Contains' (x : A) : tree → Prop :=
    | Contains'_node  : ∀ l r,   Contains' x (Node x l r)
    | Contains'_left  : ∀ y l r, Contains' x l → x < y → Contains' x (Node y l r)
    | Contains'_right : ∀ y l r, Contains' x r → y < x → Contains' x (Node y l r).
    Hint Constructors Contains' : core.

    Lemma Contains_Nil_False x : ¬ Contains x Nil.
    Proof.
      by crush.
    Qed.

    Lemma Contains'_Nil_False x : ¬ Contains' x Nil.
    Proof.
      move=> H; by invert H.
    Qed.

    Lemma Contains_not_Nil x t : Contains x t → t ≠ Nil.
    Proof.
      by crush.
    Qed.

    Lemma Contains'_not_Nil x t : Contains' x t → t ≠ Nil.
    Proof.
      move=> H bad; by invert H.
    Qed.

    (* These two definitions capture the same notion. *)
    Lemma Contains'_iff_Contains x t : Contains' x t ↔ Contains x t.
    Proof.
      split; induction t.
      - move=> H; by invert H.
      - move=> H; invert H; by crush.
      - move=> H; by crush.
      - move=> H; crush; by case_compare v x.
      (* this case_compare actually invokes rewrite_match_compare! *)
    Qed.

    Hint Resolve
      Contains_Nil_False Contains'_Nil_False
      Contains_not_Nil Contains'_not_Nil : core.

    Hint Rewrite Contains'_iff_Contains : core.

    (* a true "Contains" which works on any tree, not just BST *)
    Fixpoint In (x : A) (t : tree) : Prop :=
      match t with
      | Nil => False
      | Node v l r =>
          v = x ∨ In x l ∨ In x r
      end.

    (* As an inductive proposition instead. *)
    Inductive In'  (x : A) : tree → Prop :=
    | In'_node      : ∀ l r, In' x (Node x l r)
    | In'_left      : ∀ y l r, In' x l → In' x (Node y l r)
    | In'_right     : ∀ y l r, In' x r → In' x (Node y l r).
    Hint Constructors In' : core.
    Arguments In'_node [x] l r.

    Lemma In_Nil_False x : ¬ In x Nil.
    Proof.
      by crush.
    Qed.

    Lemma In_not_Nil x t : In x t → t ≠ Nil.
    Proof.
      by crush.
    Qed.

    Lemma In'_Nil_False x : ¬ In' x Nil.
    Proof.
      move=> H; by invert H.
    Qed.

    Lemma In'_not_Nil x t : In' x t → t ≠ Nil.
    Proof.
      move=> H bad; by invert H.
    Qed.

    Hint Resolve In_Nil_False In_not_Nil In'_Nil_False In'_not_Nil : core.

    (* These two definitions capture the exact same thing. *)
    Lemma In'_iff_In x t : In' x t ↔ In x t.
    Proof.
      split; induction t.
      - move=> H; by invert H.
      - move=> H.
        invert H; by crush.
      - move=> H; by invert H.
      - rewrite /In.
        by case_compare v x.
    Qed.
    Hint Rewrite In'_iff_In : core.

    (* `Contains` is a strictly stronger condition than In. *)
    Lemma Contains_In x t : Contains x t → In x t.
    Proof.
      induction t.
      - done.
      - rewrite /Contains /In; move=> Contains_x.
        by case_compare v x.
    Qed.
    Hint Resolve Contains_In : core.

  End Contains_In.
  Hint Constructors In' Contains' : core.
  Hint Resolve
    Contains_Nil_False Contains'_Nil_False
    Contains_not_Nil Contains'_not_Nil
    In_Nil_False In_not_Nil In'_Nil_False In'_not_Nil
    Contains_In
    : core.
  Hint Rewrite Contains'_iff_Contains : core.

  (* a really simple tactic to deconstruct ands/ors of bools *)
  Ltac simplify_bool :=
    repeat match goal with
    | [H: (?a && ?b) = true |- _ ] =>
        let H1 := fresh in
        let H2 := fresh in
        have {H}[H1 H2] := andb_prop _ _ H
    | [H: (?a || ?b) = false |- _] =>
        let H1 := fresh in
        let H2 := fresh in
        have {H}[H1 H2] := orb_false_elim _ _ H
    | [H: (?a || ?b) = true |- _] =>
        apply orb_prop in H;
        invert H
    | [H: (?a && ?b) = false |- _] =>
        apply andb_false_elim in H;
        invert H
    end.
  Hint Extern 2 => simplify_bool : core.

  Section AnyAll.

    Fixpoint Any (P : A → Prop) (t : tree) : Prop :=
      match t with
      | Nil => False
      | Node v l r =>
          P v ∨ Any P l ∨ Any P r
      end.

    Fixpoint Anyb (P : A → bool) (t : tree) : bool :=
      match t with
      | Nil => false
      | Node v l r =>
          P v || Anyb P l || Anyb P r
      end.

    Fixpoint All (P : A → Prop) (t : tree) : Prop :=
      match t with
      | Nil => True
      | Node v l r =>
          P v ∧ All P l ∧ All P r
      end.

    Fixpoint Allb (P : A → bool) (t : tree) : bool :=
      match t with
      | Nil => true
      | Node v l r =>
          P v && Allb P l && Allb P r
      end.

    Lemma Any_Nil_False P : ¬ Any P Nil.
    Proof.
      by crush.
    Qed.

    (* Note here: for both of these iff results, we use In' rather than In,
     * since chances are, if you actually need to rewrite away from the fixpoint Any
     * to prove something, you probably want to have an inductive In'
     * (which you can then perform case analysis on) instead of a fixpoint In.
     *)
    Lemma Any_iff_exists' P t :
      Any P t ↔ (∃ x, In' x t ∧ P x).
    Proof.
      split.
      - (* forwards *)
        setoid_rewrite In'_iff_In.
        induction t.
        + by crush.
        + move => [H|[H|H]].
          * exists v; by crush.
          * have {H}[x [x_In' Px]] := IHt1 H.
            exists x; by crush.
          * have {H}[x [x_In' Px]] := IHt2 H.
            exists x; by crush.
      - (* backwards *)
        move=> [x [x_In' Px]].
        induction x_In'; by crush.
    Qed.

    Lemma Any_iff_exists P t :
      Any P t ↔ (∃ x, In x t ∧ P x).
    Proof.
      setoid_rewrite <- In'_iff_In.
      exact: Any_iff_exists'.
    Qed.

    Lemma All_iff_forall' P t :
      All P t ↔ (∀ x, In' x t → P x).
    Proof.
      split.
      - (* forwards *)
        setoid_rewrite In'_iff_In.
        induction t; by crush.
      - (* backwards *)
        move=> H.
        induction t; by crush.
    Qed.

    Lemma All_iff_forall P t :
      All P t ↔ (∀ x, In x t → P x).
    Proof.
      setoid_rewrite <- In'_iff_In.
      exact: All_iff_forall'.
    Qed.

    Lemma In_All P x t : In x t → All P t → P x.
    Proof.
      rewrite All_iff_forall; by eauto.
    Qed.

    Lemma In'_All P x t : In' x t → All P t → P x.
    Proof.
      rewrite All_iff_forall'; by eauto.
    Qed.

    (* Hint Rewrite Any_iff_exists' All_iff_forall' : core. *)


    Lemma Allb_iff_All P t : Allb P t = true ↔ All (fun x => P x = true) t.
    Proof.
      induction t; by crush.
    Qed.

    Lemma Anyb_iff_Any P t : Anyb P t = true ↔ Any (fun x => P x = true) t.
    Proof.
       induction t; by crush.
    Qed.

    (* we can weaken on All *)
    Lemma All_imp (p : A → Prop) {q : A → Prop} (H : ∀ {x}, p x → q x) :
      ∀ {t}, All p t → All q t.
    Proof.
      induction t; by crush.
    Qed.

    Lemma Allb_spec0 P t : reflect (All (fun x => P x = true) t) (Allb P t).
    Proof.
      move Heq : (Allb P t) => b.
      destruct b.
      - setoid_rewrite Allb_iff_All in Heq.
        by constructor.
      - constructor.
        setoid_rewrite <-Allb_iff_All.
        by crush.
    Defined.

    Lemma All_dec (P : A → Prop) (t : tree) :
      (∀ x, {P x} + {¬ P x}) → {All P t} + {¬ All P t}.
    Proof.
      move=>P_dec.
      induction t.
      - by left.
      - destruct (P_dec v) as [Px|Px], IHt1 as [IHt1|IHt1], IHt2 as [IHt2|IHt2].
        all: try (right; by crush).
        by left.
    Defined.

    Lemma Any_dec (P : A → Prop) (t : tree) :
      (∀ x, {P x} + {¬ P x}) → {Any P t} + {¬ Any P t}.
    Proof.
      move=>P_dec.
      induction t.
      - by right.
      - destruct (P_dec v) as [Px|Px], IHt1 as [IHt1|IHt1], IHt2 as [IHt2|IHt2].
        all: try (left; by crush).
        right; by crush.
    Defined.

  End AnyAll.
  Hint Resolve All_dec Any_dec : core.
  Hint Rewrite Allb_iff_All Anyb_iff_Any Any_iff_exists' : core.
  (* Hint Rewrite All_iff_forall' Any_iff_exists' Allb_iff_All Anyb_iff_Any : core. *)

  Section Rotations.
    (* rotate root towards left *)
    Definition rotate_left v l r : tree :=
      match r with
      | Node rv rl rr => Node rv (Node v l rl) rr
      | r => Node v l r
      end.

    (* rotate root towards right *)
    Definition rotate_right (v : A) (l r : tree) : tree :=
      match l with
      | Node lv ll lr => Node lv ll (Node v lr r)
      | l => Node v l r
      end.

    (* left heavy *)
    Definition balance_left (v : A) (l r : tree) : tree :=
      if (1 + height r) <? (height l) then
        match l with
        (* this is never true in a well-formed AVL tree *)
        | Nil => Node v l r
        (* rather, we will always be in this case *)
        | Node lv ll lr as l =>
            if height lr <? height ll then
              (* left-left, one rotation *)
              rotate_right v l r
            else
              (* left-right, two rotations *)
              rotate_right v (rotate_left lv ll lr) r
        end
      else
        Node v l r.

    (* right heavy *)
    Definition balance_right (v : A) (l r : tree) : tree :=
      if 1 + height l <? height r then
        match r with
        | Nil => Node v l r
        | Node rv rl rr as r =>
            if height rl <? height rr then
              (* right-right, one rotation *)
              rotate_left v l r
            else
              (* right-left, two rotations *)
              rotate_left v l (rotate_right rv rl rr)
        end
      else
        Node v l r.

  End Rotations.
  Functional Scheme rotate_left_ind := Induction for rotate_left Sort Prop.
  Functional Scheme rotate_right_ind := Induction for rotate_right Sort Prop.
  Functional Scheme balance_left_ind := Induction for balance_left Sort Prop.
  Functional Scheme balance_right_ind := Induction for balance_right Sort Prop.

  Theorem tree_eq_dec (t1 t2 : tree) : {t1 = t2} + {¬ t1 = t2}.
  Proof.
    decide equality.
    exact: eq_dec.
  Defined.

  Section InsertDelete.

  Fixpoint insert x t :=
    match t with
    | Nil => Node x Nil Nil
    | Node v l r =>
        match (v ?= x) with
        | Eq => Node v l r
        | Lt => balance_right v l (insert x r)
        | Gt => balance_left  v (insert x l) r
        end
    end.

  Fixpoint stupid_insert x t :=
    match t with
    | Nil => Node x Nil Nil
    | Node v l r =>
        match (v ?= x) with
        | Eq => Node v l r
        | Lt => Node v l (stupid_insert x r)
        | Gt => Node v (stupid_insert x l) r
        end
    end.

  Theorem option_eq_dec (x y : option A) : {x = y} + {¬ x = y}.
  Proof.
    decide equality.
    exact: eq_dec.
  Defined.

  (* shrink_max removes and returns the maximum (right-most) element of a tree *)
  Fixpoint shrink_max (t : tree) : option A * tree :=
    match t with
    | Nil => (None, Nil)
    | Node v l r =>
        match fst (shrink_max r) with
        | None => (Some v, l)
        | Some x => (Some x, balance_left v l (snd (shrink_max r)))
        end
    end.

  (* del_root l r deletes the root, t = (Node _ l r).
  * it accomplishes this by swapping the root node's value with the max element of its left subtree,
  * then deleting the max element instead.
  *)
  Definition del_root (l r : tree) : tree :=
    match shrink_max l with
    | (None, _) => r
    | (Some x, l') => balance_right x l' r
    end.

  Fixpoint delete x t :=
    match t with
    | Nil => Nil
    | Node v l r =>
        match (v ?= x) with
        | Eq => del_root l r
        | Lt => balance_left  v l (delete x r)
        | Gt => balance_right v (delete x l) r
        end
    end.

  Inductive path : Type :=
  | Path_root  : path
  | Path_left  : ∀ (parent : path) (v : A) (r : tree), path
  | Path_right : ∀ (parent : path) (v : A) (l : tree), path.

  Fixpoint get_path' x t p : tree * path :=
    match t with
    | Nil => (Nil, p)
    | Node v l r =>
        match (v ?= x) with
        | Eq => (Node v l r, p)
        | Lt => get_path' x r (Path_right p v l)
        | Gt => get_path' x l (Path_left  p v r)
        end
    end.
  Definition get_path x t : tree * path := get_path' x t Path_root.
  End InsertDelete.
  Functional Scheme insert_ind := Induction for insert Sort Prop.
  Functional Scheme del_root_ind := Induction for del_root Sort Prop.
  Functional Scheme shrink_max_ind := Induction for shrink_max Sort Prop.
  Functional Scheme delete_ind := Induction for delete Sort Prop.
  Hint Constructors path : core.

  Section OfToList.
    Definition of_list (l : list A) : tree :=
      fold_right insert Nil l.

    Fixpoint to_list (t : tree) : list A :=
      match t with
      | Nil => []
      | Node v l r => (to_list l) ++ v :: (to_list r)
      end.
  End OfToList.

  Section WF_def.
    (* is our tree actually a BST? *)
    Fixpoint Ordered (t : tree) : Prop :=
      match t with
      | Nil => True
      | Node v l r =>
          (All (fun x => x < v) l ∧ Ordered l) ∧ (All (fun x => v < x) r ∧ Ordered r)
      end.

    Inductive Ordered' : tree → Prop :=
    | Ordered'_nil  : Ordered' Nil
    | Ordered'_node :
      ∀ v l r, All (fun x => x < v) l → Ordered' l →
               All (fun x => v < x) r → Ordered' r →
               Ordered' (Node v l r).
    Hint Constructors Ordered' : core.

    (* does the AVL invariant hold? *)
    Inductive Balanced : tree → Prop :=
    (* a leaf node is Balanced *)
    | Balanced_nil : Balanced Nil
    (* two children of equal height is Balanced *)
    | Balanced_equal :
      ∀ l r, Balanced l → Balanced r → height l = height r → ∀ v, Balanced (Node v l r)
    (* if height l = height r + 1, then the resulting thing is Balanced *)
    | Balanced_left_heavy :
      ∀ l r, Balanced l → Balanced r → height l = 1 + height r → ∀ v, Balanced (Node v l r)
    (* symmetric. *)
    | Balanced_right_heavy :
      ∀ l r, Balanced l → Balanced r → 1 + height l = height r → ∀ v, Balanced (Node v l r).
    Hint Constructors Balanced : core.

    (* well-formedness invariant *)
    Inductive WF : tree → Prop :=
    (* an AVL tree (that is, a well-formed tree) is ordered and has the balance invariant *)
    | WF_base :
      ∀ t, Ordered t → Balanced t → WF t
    (* inserting into a well-formed tree results in a well-formed tree *)
    | WF_insert :
      ∀ t, WF t → ∀ x, WF (insert x t)
    (* deleting from a well-formed tree results in a well-formed tree *)
    | WF_delete :
      ∀ t, WF t → ∀ x, WF (delete x t).
    Hint Constructors WF : core.


  End WF_def.
  Hint Constructors Ordered' Balanced WF : core.

  Ltac invert_ordered' :=
    repeat match goal with
    | [ H : Ordered' (Node _ _ _) |- _ ] => invert H
    end.

  Tactic Notation "split_ifs" ident(h) :=
    match goal with
    | [ |- context[if ?exp then _ else _ ] ] =>
        let i := fresh h in
        let b := fresh in
        move i : exp => b;
        destruct b
    end.
  Tactic Notation "split_ifs" := split_ifs Hb.

  Ltac ltb_to_lt :=
    match goal with
    | [ H : (?a <? ?b)%nat = true |- _ ] => rewrite Nat.ltb_lt in H
    | [ H : (?a <? ?b)%nat = false |- _ ] => rewrite Nat.ltb_ge in H
    end.
  Hint Rewrite Nat.ltb_lt Nat.ltb_ge : core.

  Ltac match_compare :=
    rewrite_match_compare ||
    match goal with
    | [ |- context[match compare ?v ?x with |_ => _ end] ] =>
        elim_compare v x
    | [ _ : context[match compare ?v ?x with | _ => _ end] |- _] =>
        elim_compare v x
    end.
  Hint Extern 1 => match_compare : core.

  Hint Rewrite Nat.max_id : core.


  Lemma height_eq_zero_nil t : height t = 0 → t = Nil.
  Proof.
    by destruct t.
  Qed.

  Lemma height_eq_one_singleton t : height t = 1 → ∃ v, t = Node v Nil Nil.
  Proof.
    move => t_height.
    destruct t.
    - by crush.
    - exists v.
      invert t_height.
      have t1_zero : (height t1) = 0 by lia.
      have t2_zero : (height t2) = 0 by lia.
      by rewrite (height_eq_zero_nil _ t1_zero) (height_eq_zero_nil _ t2_zero).
  Qed.

  Lemma size_eq_zero_nil t : size t = 0 → t = Nil.
  Proof.
    by destruct t.
  Qed.

  Lemma size_eq_one_singleton t : size t = 1 → ∃ v, t = Node v Nil Nil.
  Proof.
    move => t_size.
    destruct t.
    - by crush.
    - exists v.
      invert t_size.
      have t1_zero : size t1 = 0 by lia.
      have t2_zero : size t2 = 0 by lia.
      by rewrite (size_eq_zero_nil _ t1_zero) (size_eq_zero_nil _ t2_zero).
  Qed.

  Lemma node_neq_nil {v l r} : Node v l r ≠ Nil.
    by crush.
  Qed.

  Lemma nil_neq_node {v l r} : Nil ≠ Node v l r.
    by crush.
  Qed.

  Hint Resolve node_neq_nil nil_neq_node : core.

  (* Section Facts. *)

    Lemma All_lt_dec v l : {All (fun x => x < v) l} + {¬ All (fun x => x < v) l}.
    Proof.
      apply All_dec.
      move=>x.
      by apply lt_dec.
    Defined.

    Lemma All_gt_dec v r : {All (fun x => v < x) r} + {¬ All (fun x => v < x) r}.
    Proof.
      apply All_dec.
      move=>x; by apply lt_dec.
    Defined.

    Lemma Ordered_dec t : {Ordered t} + {¬ Ordered t}.
    Proof.
      induction t.
      - by left.
      - destruct IHt1, IHt2, (All_lt_dec v t1), (All_gt_dec v t2).
        all: try (right; by crush).
        left; by crush.
    Defined.

    Lemma Ordered_iff_Ordered' t : Ordered t ↔ Ordered' t.
    Proof.
      split.
      - move=>Ordered_t .
        induction t.
        + by constructor.
        + crush; by constructor.
      - move=>Ordered_t.
        induction Ordered_t; by crush.
    Qed.
    Hint Rewrite Ordered_iff_Ordered' : core.

    (* Contains behaves exactly like In when the tree is Ordered. *)
    Lemma Ordered_In_Contains x t : Ordered t → In x t → Contains x t.
    Proof.
      move=>t_Ordered x_In.
      rewrite -In'_iff_In in x_In.
      induction x_In.
      - by crush.
      - crush.
        rewrite All_iff_forall' in H1.
        specialize (H1 x x_In).
        by match_compare.
        (* rewrite All_iff_forall' in H1. *)
        (* specialize (H1 x x_In). *)
        (* by case_compare y x. *)
      - crush.
        rewrite All_iff_forall' in H.
        specialize (H x x_In).
        by match_compare.
    Qed.

    Lemma Ordered_In_iff_Contains x t : Ordered t → In x t ↔ Contains x t.
    Proof.
      move=>t_Ordered.
      split.
      - by apply: Ordered_In_Contains.
      - by apply: Contains_In.
    Qed.

    Lemma rotate_left_preserves_Ordered v l r : Ordered (Node v l r) → Ordered (rotate_left v l r).
    Proof.
      rewrite !Ordered_iff_Ordered' /rotate_left.
      move=>ordered.
      destruct r; invert_ordered'; try by constructor.
      constructor; crush.
      apply (All_imp (fun x => x < v)); crush.
      (* - apply (All_imp (fun x => x < v)); crush. *)
      (* - constructor; by crush. *)
    Qed.

    Lemma rotate_right_preserves_Ordered v l r : Ordered (Node v l r) → Ordered (rotate_right v l r).
    Proof.
      rewrite !Ordered_iff_Ordered' /rotate_right.
      intros; destruct l; invert_ordered'; try by constructor.
      constructor; crush.
      apply (All_imp (fun x => v < x)); by crush.
      (* - apply (All_imp (fun x => v < x)); by crush. *)
      (* - constructor; by crush. *)
    Qed.

    Lemma rotate_left_preserves_Ordered' v l r : Ordered' (Node v l r) → Ordered' (rotate_left v l r).
      rewrite -!Ordered_iff_Ordered'.
      exact: rotate_left_preserves_Ordered.
    Qed.

    Lemma rotate_right_preserves_Ordered' v l r : Ordered' (Node v l r) → Ordered' (rotate_right v l r).
      rewrite -!Ordered_iff_Ordered'.
      exact: rotate_right_preserves_Ordered.
    Qed.


    (* Tactic Notation "split_ifs" := let h := fresh in split_ifs h. *)
      (* repeat match goal with *)
      (* | [ |- context[if ?b then _ else _ ] ] => *)
      (*     let i := fresh "Heq" in *)
      (*     let e := fresh in *)
      (*     move i : b => e; *)
      (*     destruct e *)
      (* end. *)

    Lemma rotate_left_preserves_All P v l r : (All P (Node v l r)) → All P (rotate_left v l r).
    Proof.
      move=>[Pv [Pl Pr]].
      destruct r; by crush.
    Qed.

    Lemma rotate_right_preserves_All P v l r : All P (Node v l r) → All P (rotate_right v l r).
    Proof.
      destruct l; by crush.
    Qed.

    Ltac unrotate :=
      match goal with
      | [ |- All _ (rotate_left _ _ _) ] => eapply rotate_left_preserves_All
      | [ |- All _ (rotate_right _ _ _) ] => eapply rotate_right_preserves_All
      | [ |- Ordered' (rotate_left _ _ _) ] => eapply rotate_left_preserves_Ordered'
      | [ |- Ordered' (rotate_right _ _ _) ] => eapply rotate_right_preserves_Ordered'
      end.
    Hint Extern 1 => unrotate : core.

    (* Hint Resolve rotate_left_preserves_Ordered' rotate_right_preserves_Ordered' : core. *)
    (* Hint Resolve rotate_left_preserves_All rotate_right_preserves_All : core. *)

    Lemma balance_left_preserves_Ordered v l r : Ordered (Node v l r) → Ordered (balance_left v l r).
    Proof.
      move => H_order.
      have := H_order.
      rewrite !Ordered_iff_Ordered' /balance_left.
      intros; invert_ordered'.
      split_ifs.
      - destruct l.
        + by crush.
        + crush.
          split_ifs.
          * constructor; crush.
            apply (All_imp (fun x => v < x)); by crush.
            (* -- apply (All_imp (fun x => v < x)); by crush. *)
            (* -- constructor; by crush. *)
          * unrotate.
            constructor; crush.
            unrotate; by crush.
      - destruct l.
        + constructor; by crush.
        + try repeat constructor; by crush.
    Qed.

    Lemma balance_right_preserves_Ordered v l r : Ordered (Node v l r) → Ordered (balance_right v l r).
    Proof.
      move => H_order.
      have := H_order.
      rewrite !Ordered_iff_Ordered' /balance_right.
      intros; invert_ordered'.
      split_ifs.
      - destruct r; try repeat constructor; crush.
        split_ifs; try repeat constructor; crush.
        + apply (All_imp (fun x => x < v)); by crush.
        + unrotate; repeat constructor; crush.
          unrotate; by crush.
      - destruct r; try repeat constructor; by crush.
    Qed.

    Lemma balance_left_preserves_Ordered' v l r : Ordered' (Node v l r) → Ordered' (balance_left v l r).
    Proof.
      rewrite -!Ordered_iff_Ordered'.
      exact: balance_left_preserves_Ordered.
    Qed.

    Lemma balance_right_preserves_Ordered' v l r : Ordered' (Node v l r) → Ordered' (balance_right v l r).
    Proof.
      rewrite -!Ordered_iff_Ordered'.
      exact: balance_right_preserves_Ordered.
    Qed.

    Hint Resolve
      balance_left_preserves_Ordered
      balance_left_preserves_Ordered'
      balance_right_preserves_Ordered
      balance_right_preserves_Ordered'
      : core.

    Lemma balance_left_preserves_All P v l r : All P (Node v l r) → All P (balance_left v l r).
    Proof.
      move=> Pt.
      rewrite /balance_left.
      split_ifs; destruct l; try repeat (split_ifs || constructor || unrotate); crush; done.
    Qed.

    Lemma balance_right_preserves_All P v l r : All P (Node v l r) → All P (balance_right v l r).
    Proof.
      move=> Pt.
      rewrite /balance_right.
      split_ifs; destruct r; try repeat (split_ifs || constructor || unrotate); crush; done.
    Qed.

    Lemma insert_preserves_All P x t : All P t → P x → All P (insert x t).
    Proof.
      move=>Pt Px.
      induction t.
      - by crush.
      - crush.
        match_compare; crush;
          (apply balance_left_preserves_All || apply balance_right_preserves_All); crush;
          done.
    Qed.

    Lemma insert_preserves_Ordered' x t : Ordered' t → Ordered' (insert x t).
    Proof.
      move=>t_Ordered.
      induction t_Ordered; crush.
      - repeat constructor; by crush.
      - match_compare; repeat constructor; crush;
        (apply balance_left_preserves_Ordered' || apply balance_right_preserves_Ordered');
        repeat constructor; crush;
        apply insert_preserves_All; crush;
        done.
    Qed.

    Lemma insert_preserves_Ordered x t : Ordered t → Ordered (insert x t).
    Proof.
      rewrite !Ordered_iff_Ordered'.
      exact: insert_preserves_Ordered'.
    Qed.

    Hint Resolve
      insert_preserves_Ordered' insert_preserves_Ordered : core.

    Lemma In_singleton x y : In y (Node x Nil Nil) → y = x.
    Proof.
      by crush.
    Qed.

    Lemma Contains_singleton x y : Contains y (Node x Nil Nil) → y = x.
    Proof.
      crush.
    Qed.

    Hint Rewrite In_singleton Contains_singleton : core.

    Lemma rotate_left_In_complete x v l r : In x (Node v l r) → In x (rotate_left v l r).
    Proof.
      move => H_In.
      destruct r; simpl;
      by repeat match goal with
      | [ H : In _ (Node _ _ _) |- _ ] => destruct H; subst; eauto
      | [ H : _ ∨ _ |- _] => destruct H; subst; eauto
      end.
    Qed.

    Lemma rotate_right_In_complete x v l r : In x (Node v l r) → In x (rotate_right v l r).
    Proof.
      move => H_In.
      destruct l; simpl;
      by repeat match goal with
      | [ H : In _ (Node _ _ _) |- _ ] => destruct H; subst; eauto
      | [ H : _ ∨ _ |- _] => destruct H; subst; eauto
      end.
    Qed.

    Lemma rotate_left_In_correct x v l r : In x (rotate_left v l r) → In x (Node v l r).
    Proof.
      destruct r; simpl; tauto.
    Qed.

    Lemma rotate_right_In_correct x v l r : In x (rotate_right v l r) → In x (Node v l r).
    Proof.
      destruct l; simpl; tauto.
    Qed.

    Lemma rotate_left_In_iff x v l r : In x (rotate_left v l r) <-> In x (Node v l r).
    Proof.
      split; by eauto using rotate_left_In_correct, rotate_left_In_complete.
    Qed.

    Lemma rotate_right_In_iff x v l r : In x (rotate_right v l r) <-> In x (Node v l r).
      split; by eauto using rotate_right_In_correct, rotate_right_In_complete.
    Qed.

    Hint Extern 1 (In _ (rotate_left _ _ _)) => eapply rotate_left_In_complete : core.
    Hint Extern 1 (In _ (rotate_right _ _ _)) => eapply rotate_right_In_complete : core.
    Hint Rewrite rotate_left_In_iff rotate_right_In_iff : core.

    Lemma rotate_left_In_tac1 x v lv ll lr r : In x (Node v (Node lv ll lr) r) → In x (Node v (rotate_left lv ll lr) r).
    Proof.
      move => H.
      destruct H as [H | [ H | H ]]; subst.
      all: try by (rewrite /In; propositional).
      right; left; by rewrite rotate_left_In_iff.
    Qed.

    Lemma rotate_left_In_tac2 x v l rv rl rr : In x (Node v l (Node rv rl rr)) → In x (Node v l (rotate_left rv rl rr)).
    Proof.
      move => H.
      destruct H as [H | [H | H]]; subst; try by (rewrite /In; propositional).
      right; right; by rewrite rotate_left_In_iff.
    Qed.

    Lemma rotate_right_In_tac1 x v lv ll lr r : In x (Node v (Node lv ll lr) r) → In x (Node v (rotate_right lv ll lr) r).
    Proof.
      move => H.
      destruct H as [H | [ H | H ]]; subst.
      all: try by (rewrite /In; propositional).
      right; left; by rewrite rotate_right_In_iff.
    Qed.

    Lemma rotate_right_In_tac2 x v l rv rl rr : In x (Node v l (Node rv rl rr)) → In x (Node v l (rotate_right rv rl rr)).
    Proof.
      move => H.
      destruct H as [H | [H | H]]; subst; try by (rewrite /In; propositional).
      right; right; by rewrite rotate_right_In_iff.
    Qed.

    (* this is awful, we should really be using proof search instead *)
    Ltac solve_In :=
      match goal with
      | [ H : In _ (Node _ _ _) |- _ ] => destruct H; simplify; subst; eauto
      | [ H : _ ∨ _ |- _] => destruct H; subst; eauto
      | [ H : In _ (rotate_left _ _ _) |- _ ] => rewrite rotate_left_In_iff in H
      | [ H : In _ (rotate_right _ _ _) |- _ ] => rewrite rotate_right_In_iff in H
      | [ |- In _ (rotate_left _ _ _) ] => rewrite rotate_left_In_iff
      | [ |- In _ (rotate_right _ _ _) ] => rewrite rotate_right_In_iff
      | [ |- In ?x (Node ?x _ _) ] => rewrite /In; propositional
      | [ _ : In ?x ?t |- In ?x (Node _ ?t _) ] => rewrite /In; propositional
      | [ _ : In ?x ?t |- In ?x (Node _ _ ?t) ] => rewrite /In; propositional
      | [ |- In _ (Node _ (rotate_left _ _ _) _) ] => apply rotate_left_In_tac1
      | [ |- In _ (Node _ _ (rotate_left _ _ _)) ] => apply rotate_left_In_tac2
      | [ |- In _ (Node _ (rotate_right _ _ _) _) ] => apply rotate_right_In_tac1
      | [ |- In _ (Node _ _ (rotate_right _ _ _)) ] => apply rotate_right_In_tac2
      end.

    Lemma balance_left_In_complete x v l r : In x (Node v l r) → In x (balance_left v l r).
    Proof.
      functional induction (balance_left v l r); simplify; repeat solve_In.
    Qed.

    Lemma balance_right_In_complete x v l r : In x (Node v l r) → In x (balance_right v l r).
    Proof.
      functional induction (balance_right v l r); simplify; repeat solve_In.
    Qed.

    Lemma balance_left_In_correct x v l r : In x (balance_left v l r) → In x (Node v l r).
    Proof.
      functional induction (balance_left v l r); simplify; tauto || (repeat solve_In).
    Qed.

    Lemma balance_right_In_correct x v l r : In x (balance_right v l r) → In x (Node v l r).
    Proof.
      functional induction (balance_right v l r); simplify; tauto || (repeat solve_In).
    Qed.

    Lemma balance_left_In_iff x v l r : In x (balance_left v l r) <-> In x (Node v l r).
    Proof.
      split; by eauto using balance_left_In_correct, balance_left_In_complete.
    Qed.

    Lemma balance_right_In_iff x v l r : In x (balance_right v l r) <-> In x (Node v l r).
    Proof.
      split; by eauto using balance_right_In_correct, balance_right_In_complete.
    Qed.

    Hint Extern 1 (In _ (balance_left _ _ _)) => apply balance_left_In_complete : core.
    Hint Extern 1 (In _ (balance_right _ _ _)) => apply balance_right_In_complete : core.
    Hint Rewrite balance_left_In_iff balance_right_In_iff : core.

    (* INSERT IS CORRECT WRT TO IN *)
    Theorem insert_In_complete1 x y t : In x t → In x (insert y t).
    Proof.
      move => hyp.
      functional induction (insert y t); simplify; try by eauto; repeat solve_In.
    Qed.

    Theorem insert_In_complete2 x t : In x (insert x t).
    Proof.
      functional induction (insert x t); simplify; by eauto.
    Qed.

    Theorem insert_In_correct x y t : In x (insert y t) → x = y ∨ In x t.
    Proof.
      functional induction (insert y t); simplify; eauto; repeat solve_In.
    - apply IHt0 in H; by repeat solve_In.
    - apply IHt0 in H; by repeat solve_In.
    Qed.

    Lemma rotate_left_preserves_size v l r : size (rotate_left v l r) = size (Node v l r).
    Proof.
      functional induction (rotate_left v l r); simplify; lia.
    Qed.

    Lemma rotate_right_preserves_size v l r : size (rotate_right v l r) = size (Node v l r).
    Proof.
      functional induction (rotate_right v l r); simplify; lia.
    Qed.

    Hint Rewrite rotate_left_preserves_size rotate_right_preserves_size : core.

    Lemma balance_left_preserves_size v l r : size (balance_left v l r) = size (Node v l r).
    Proof.
      functional induction (balance_left v l r); simplify; lia.
    Qed.

    Lemma balance_right_preserves_size v l r : size (balance_right v l r) = size (Node v l r).
    Proof.
      functional induction (balance_right v l r); simplify; lia.
    Qed.

    Hint Rewrite rotate_left_preserves_size rotate_right_preserves_size : core.
    (* note, insert is only idempotent if it is already balanced *)

    Search "<?" true.
    Search "<?" false.
    Search (S ?a = S ?b).
    Search (S ?a ≤ S ?b).
    Search (S ?a < S ?b)%nat.
      (* Nat.succ_inj le_S_n : core. *)
    (* Hint Resolve le_n_S : core. *)

    Lemma invert_Balanced_left v l r : Balanced (Node v l r) → Balanced l.
    Proof.
      move=>H; by invert H.
    Qed.

    Lemma invert_Balanced_right v l r : Balanced (Node v l r) → Balanced r.
    Proof.
      move=>H; by invert H.
    Qed.
    Hint Resolve invert_Balanced_left invert_Balanced_right : core.

    Lemma rotate_left_height_le v l r :
      height (rotate_left v l r) ≤ 1 + height (Node v l r).
    Proof.
      destruct r; by crush.
    Qed.

    Lemma rotate_right_height_le v l r :
      height (rotate_right v l r) ≤ 1 + height (Node v l r).
    Proof.
      destruct l; by crush.
    Qed.

    Lemma rotate_left_height_ge v l r :
      l ≠ Nil →
      height (Node v l r) ≤ 1 + height (rotate_left v l r).
    Proof.
      destruct r; by crush.
    Qed.

    Lemma rotate_right_height_ge v l r :
      r ≠ Nil →
      height (Node v l r) ≤ 1 + height (rotate_right v l r).
    Proof.
      destruct l; by crush.
    Qed.
    
    Lemma rotate_left_height_change v l r :
      (height (rotate_left v l r) = height (Node v l r))
      ∨ (height (rotate_left v l r) = 1 + height (Node v l r))
      ∨ (1 + height (rotate_left v l r) = height (Node v l r)).
    Proof.
      destruct r; by crush.
    Qed.

    Lemma rotate_right_height_change v l r :
      (height (rotate_right v l r) = height (Node v l r))
      ∨ (height (rotate_right v l r) = 1 + height (Node v l r))
      ∨ (1 + height (rotate_right v l r) = height (Node v l r)).
    Proof.
      destruct l; by crush.
    Qed.

    Lemma rotate_left_right_heavy v l r :
      (height l < height r)%nat → height (rotate_left v l r) ≤ height (Node v l r).
    Proof.
      destruct r; by crush.
    Qed.

    Lemma rotate_right_left_heavy v l r :
      (height r < height l)%nat → height (rotate_right v l r) ≤ height (Node v l r).
    Proof.
      destruct l; by crush.
    Qed.

    Lemma rotate_left_right_heavy' v l r :
      (height l < height r)%nat →
        height (rotate_left v l r) = height (Node v l r)
        ∨ 1 + height (rotate_left v l r) = height (Node v l r).
    Proof.
      destruct r; by crush.
    Qed.

    Lemma rotate_right_left_heavy' v l r :
      (height r < height l)%nat →
        height (rotate_right v l r) = height (Node v l r)
        ∨ 1 + height (rotate_right v l r) = height (Node v l r).
    Proof.
      destruct l; by crush.
    Qed.

    Lemma rotate_left_right_heavy_1 v l rv rl rr :
      (1 + height l < height (Node rv rl rr))%nat →
      (height rl < height rr)%nat →
      1 + height (rotate_left v l (Node rv rl rr)) = height (Node v l (Node rv rl rr)).
    Proof.
      by crush.
    Qed.


    Lemma rotate_left_equal v l r :
      r ≠ Nil → height l = height r → height (rotate_left v l r) = 1 + height (Node v l r).
    Proof.
      destruct r; by crush.
    Qed.

    Lemma rotate_right_equal v l r :
      l ≠ Nil → height l = height r → height (rotate_right v l r) = 1 + height (Node v l r).
    Proof.
      destruct l; by crush.
    Qed.

    Lemma balance_left_preserves_Balanced v l r : Balanced (Node v l r) → Balanced (balance_left v l r).
    Proof.
      move => Hbal.
      functional induction (balance_left v l r); simplify; eauto.
      - invert Hbal; by crush.
      - invert Hbal; by crush.
    Qed.

    Lemma balance_right_preserves_Balanced v l r : Balanced (Node v l r) → Balanced (balance_right v l r).
    Proof.
      move => Hbal.
      functional induction (balance_right v l r); simplify; eauto; invert Hbal; by crush.
    Qed.

    Lemma balance_left_Balanced_same v l r : Balanced (Node v l r) → balance_left v l r = Node v l r.
    Proof.
      move=> Hbal.
      functional induction (balance_left v l r); simplify; eauto; invert Hbal; by crush.
    Qed.

    Lemma balance_right_Balanced_same v l r : Balanced (Node v l r) → balance_right v l r = Node v l r.
    Proof.
      move=>Hbal.
      functional induction (balance_right v l r); simplify; eauto; invert Hbal; by crush.
    Qed.

    Lemma rotate_left_not_Nil v l r : rotate_left v l r = Nil → False.
    Proof.
      by destruct r.
    Qed.

    Lemma rotate_right_not_Nil v l r : rotate_right v l r = Nil → False.
    Proof.
      by destruct l.
    Qed.
    (* Hint Resolve rotate_left_not_Nil rotate_right_not_Nil : core. *)

    Ltac rotate_not_nil :=
      match goal with
      | [ H : Node _ _ _ = Nil |- _ ] => by invert H
      | [ H : rotate_left _ _ _ = Nil |- _ ] => exfalso; exact: rotate_left_not_Nil _ _ _ H
      | [ H : rotate_right _ _ _ = Nil |- _ ] => exfalso; exact: rotate_right_not_Nil _ _ _ H
      end.
    Hint Extern 0 => rotate_not_nil : core.

    Lemma balance_left_not_Nil v l r : balance_left v l r = Nil → False.
    Proof.
      rewrite /balance_left.
      split_ifs; destruct l; try split_ifs; by crush.
    Qed.

    Lemma balance_right_not_Nil v l r : balance_right v l r = Nil → False.
    Proof.
      rewrite /balance_right.
      split_ifs; destruct r; try split_ifs; by crush.
    Qed.

    Ltac balance_not_nil :=
      match goal with
      | [ H : balance_left _ _ _ = Nil |- _ ] => exfalso; exact: balance_left_not_Nil _ _ _ H
      | [ H : balance_right _ _ _  = Nil |- _ ] => exfalso; exact: balance_right_not_Nil _ _ _ H
      end.
    Hint Extern 0 => balance_not_nil : core.

    Lemma insert_not_Nil x t : insert x t ≠ Nil.
    Proof.
      move=>bad.
      induction t.
      - invert bad.
      - rewrite /insert in bad.
        elim_compare v x; rewrite -/insert in bad; by crush.
    Qed.

    Hint Extern 0 =>
      match goal with
      | [ H : insert _ _ = Nil |- _ ] => exfalso; exact: insert_not_Nil _ _ H
      end : core.

    Ltac gen_destruct exp :=
      let eq := fresh "Heq" in
      let e := fresh "e" in
      move eq : exp => e;
      destruct e.

    Lemma balance_left_height_le v l r :
      height (balance_left v l r) ≤ height (Node v l r).
    Proof.
      functional induction (balance_left v l r); simplify; eauto; crush.
      destruct lr; by crush.
    Qed.

    Lemma balance_right_height_le v l r :
      height (balance_right v l r) ≤ height (Node v l r).
    Proof.
      functional induction (balance_right v l r); simplify; eauto; crush.
      destruct rl; by crush.
    Qed.

    Lemma balance_left_height_ge v l r :
      height (Node v l r) ≤ 2 + height (balance_left v l r).
    Proof.
      functional induction (balance_left v l r).
      - by crush.
      - by crush.
      - repeat ltb_to_lt.
        destruct (rotate_left_height_change lv ll lr) as [|[|]],
            (rotate_right_height_change v (rotate_left lv ll lr) r) as [|[|]]; by crush.
      - ltb_to_lt.
        by crush.
    Qed.

    Lemma balance_right_height_ge v l r :
      height (Node v l r) ≤ 2 + height (balance_right v l r).
    Proof.
      functional induction (balance_right v l r).
      - by crush.
      - by crush.
      - destruct (rotate_right_height_change rv rl rr) as [|[|]],
            (rotate_left_height_change v l (rotate_right rv rl rr)) as [|[|]]; by crush.
      - by crush.
    Qed.


    Search Nat.max le.
    Hint Extern 0 =>
      match goal with
      | [ H : (?a < ?b)%nat |- context[Nat.max ?a ?b] ] =>
          rewrite (Nat.max_r _ _ (Nat.lt_le_incl _ _ H))
      | [ H : (?b < ?a)%nat |- context[Nat.max ?a ?b] ] =>
          rewrite (Nat.max_l _ _ (Nat.lt_le_incl _ _ H))
      end : core.


    Lemma insert_height_upper_bound x t : height (insert x t) ≤ 1 + height t.
    Proof.
      functional induction (insert x t); [by crush| lia | | ].
      - transitivity (height (Node v l (insert x r))); [apply balance_right_height_le|].
        rewrite /height -/height.
        lia.
      - transitivity (height (Node v (insert x l) r)); [apply balance_left_height_le|].
        rewrite /height -/height; lia.
    Qed.

    Lemma eq_or_succ_cases {a b} : a ≤ b → b ≤ 1 + a → b = a ∨ b = 1 + a.
    Proof.
      lia.
    Qed.


    Search (S _ ≤ S _).
    Search S Nat.max.
    Search (S _ < S _)%nat.
    Ltac linear_arithmetic' := intros;
      repeat match goal with
      | [ |- S _ ≤ S _ ] =>
          apply le_n_S
      | [ H : (S _ < S _)%nat |- _ ] => rewrite -Nat.succ_lt_mono in H
      | [ H : S _ = S _ |- _ ] => apply Nat.succ_inj in H
      | [ |- context[Nat.max ?a ?b] ] =>
        let Heq := fresh "Heq" in destruct (Nat.max_spec a b) as [[? Heq] | [? Heq]];
          rewrite -> Heq in *; clear Heq
      | [ _ : context[Nat.max ?a ?b] |- _ ] =>
        let Heq := fresh "Heq" in destruct (Nat.max_spec a b) as [[? Heq] | [? Heq]];
          rewrite -> Heq in *; clear Heq
      | [ |- context[min ?a ?b] ] =>
        let Heq := fresh "Heq" in destruct (Nat.min_spec a b) as [[? Heq] | [? Heq]];
          rewrite -> Heq in *; clear Heq
      | [ _ : context[min ?a ?b] |- _ ] =>
        let Heq := fresh "Heq" in destruct (Nat.min_spec a b) as [[? Heq] | [? Heq]];
          rewrite -> Heq in *; clear Heq
      end.

    Lemma invert_insert x t : ∃ v l r, insert x t = Node v l r.
    Proof.
      functional induction (insert x t); eauto.
      - destruct IHt0 as [v' [l' [r' Heq]]].
        rewrite {}Heq.
        functional induction (balance_right v l (Node v' l' r')); eauto.
        + destruct rl; simplify; eauto.
        + destruct rl; simplify; eauto.
      - destruct IHt0 as [v' [l' [r' Heq]]].
        rewrite {}Heq.
        functional induction (balance_left v (Node v' l' r') r); eauto;
        destruct lr; simplify; eauto.
    Qed.

    (* this is in general, NOT TRUE!! *)
    Lemma hmmm v l r :
      Balanced l → Balanced r → 2 + height l = height r →
      Balanced (balance_right v l r).
    Proof.
    Abort.
    (* AVL trees work specifically because you can only ever have at most 1 broken invariant, not 2 *)

    Definition left_child t :=
      match t with
      | Nil => Nil
      | Node _ l _ => l
      end.

    Definition right_child t :=
      match t with
      | Nil => Nil
      | Node _ _ r => r
      end.

    Hint Unfold left_child right_child : core.

    Lemma insert_preserves_Balanced0 x t :
      Balanced t →
      Balanced (insert x t) ∧
        height t ≤ height (insert x t) ∧
        (t ≠ Nil → 1 + height t = height (insert x t) → height (left_child (insert x t)) ≠ height (right_child (insert x t))).
    Proof.
      functional induction (insert x t); move => t_bal; repeat split; simplify; eauto.
      - exfalso; lia.
      - have r_bal : Balanced r by invert t_bal.
        have {r_bal}IHt0 := IHt0 r_bal.
        destruct IHt0 as [insert_bal [IH_height IH_unbal]].
        have r_height_lower := insert_height_upper_bound x r.
        invert t_bal; simplify.
        + (* equal heights *)
          apply balance_right_preserves_Balanced.
          destruct (eq_or_succ_cases IH_height r_height_lower) as [H|H].
          * apply Balanced_equal; by crush.
          * apply Balanced_right_heavy; by crush.
        + (* left heavy *)
          apply balance_right_preserves_Balanced.
          destruct (eq_or_succ_cases IH_height r_height_lower).
          * apply Balanced_left_heavy; by crush.
          * apply Balanced_equal; by crush.
        + (* right heavy *)
          destruct (eq_or_succ_cases IH_height r_height_lower) as [H|H];
            [apply balance_right_preserves_Balanced, Balanced_right_heavy; by crush|].
          (* now we have a +2 height diff, so balance_right must kick in. *)
          destruct r; [crush|].
          have r_nonnil : Node v0 r1 r2 ≠ Nil by done.
          symmetry in H.
          have {r_nonnil}IH_unbal := IH_unbal r_nonnil H.
          functional induction (balance_right v l (insert x (Node v0 r1 r2))); simplify; eauto; try lia.
          * invert insert_bal; try lia.
            linear_arithmetic'; invert H3; try lia; apply Balanced_equal; crush.
          * have {e2 IH_unbal} IH_unbal : 1 + height rr = height rl by (invert insert_bal; lia).
            destruct rl; [simplify; lia|].
            simplify.
            invert insert_bal; invert H3; linear_arithmetic'; simplify; try lia;
              invert H6; try lia; apply Balanced_equal; crush.
      - have r_bal : Balanced r by invert t_bal.
        have {r_bal IHt0}[insert_bal [height_le unbal]] := IHt0 r_bal.
        Search (height _ = 0).
        have r_height_lower := insert_height_upper_bound x r.
        destruct r.
        { invert t_bal; simplify; try lia.
          rewrite (height_eq_zero_nil l H4); simplify; crush.
          destruct l; [simplify; lia|simplify].
          have l1_nil : height l1 = 0 by lia.
          have l2_nil : height l2 = 0 by lia.
          rewrite (height_eq_zero_nil l1 l1_nil) (height_eq_zero_nil l2 l2_nil); simplify; crush.
        }
        have {}unbal := unbal node_neq_nil.
        destruct (eq_or_succ_cases height_le r_height_lower) as [H|H].
        {
          functional induction (balance_right v l (insert x (Node v0 r1 r2)));
            invert t_bal;
            simplify; try lia.
        }
        functional induction (balance_right v l (insert x (Node v0 r1 r2))); invert t_bal; simplify; try lia.
        destruct rl; [simplify; lia|].
        invert insert_bal; simplify; try lia.
      - have r_bal : Balanced r by invert t_bal.
        have {r_bal IHt0}[insert_bal [height_ge unbal]] := IHt0 r_bal.
        have r_height_lower := insert_height_upper_bound x r.
        destruct r.
        {
          clear unbal height_ge insert_bal H r_height_lower.
          simplify.
          invert t_bal; [| |simplify; try lia].
          -
            rewrite (height_eq_zero_nil l H5) /balance_right; simplify; lia.
          - exfalso.
            rewrite /balance_right in H0; simplify; lia.
        }
        have l_bal_diff : (1 + height l < height (balance_right v l (insert x (Node v0 r1 r2))))%nat by lia.
        functional induction (balance_right v l (insert x (Node v0 r1 r2))); simplify; try lia.
        destruct rl; [simplify; lia|].
        invert insert_bal; simplify; lia.
      - (* all cases from here on are symmetric. *)
        have l_bal : Balanced l by invert t_bal.
        have {l_bal}IHt0 := IHt0 l_bal.
        destruct IHt0 as [insert_bal [IH_height IH_unbal]].
        have l_height_lower := insert_height_upper_bound x l.
        invert t_bal; simplify.
        + (* equal heights *)
          apply balance_left_preserves_Balanced.
          destruct (eq_or_succ_cases IH_height l_height_lower) as [H|H].
          * apply Balanced_equal; by crush.
          * apply Balanced_left_heavy; by crush.
        + (* left heavy *)
          destruct (eq_or_succ_cases IH_height l_height_lower) as [H|H];
            [apply balance_left_preserves_Balanced, Balanced_left_heavy; by crush|].
          (* now we have a +2 height diff, so balance_left must kick in *)
          destruct l; [crush|].
          symmetry in H.
          have {}IH_unbal := IH_unbal node_neq_nil H.
          functional induction (balance_left v (insert x (Node v0 l1 l2)) r); simplify; eauto; try lia.
          * invert insert_bal; try lia.
            linear_arithmetic'; invert H2; try lia; apply Balanced_equal; crush.
          * have {e2 IH_unbal}IH_unbal : 1 + height ll = height lr by (invert insert_bal; lia).
            destruct lr; [simplify; lia|].
            invert insert_bal; invert H2; invert H7; simplify; try lia; apply Balanced_equal; crush.
        + (* right heavy *)
          apply balance_left_preserves_Balanced.
          destruct (eq_or_succ_cases IH_height l_height_lower).
          * apply Balanced_right_heavy; by crush.
          * apply Balanced_equal; by crush.
      - have l_bal : Balanced l by invert t_bal.
        have {l_bal}IHt0 := IHt0 l_bal.
        have l_height_lower := insert_height_upper_bound x l.
        destruct IHt0 as [insert_bal [insert_height_ge unbal]].
        destruct l.
        {
          invert t_bal; simplify; try lia.
          symmetry in H4.
          rewrite (height_eq_zero_nil r H4); simplify; crush.
          destruct r; [simplify; lia| simplify].
          have r1_nil : height r1 = 0 by lia.
          have r2_nil : height r2 = 0 by lia.
          rewrite (height_eq_zero_nil _ r1_nil) (height_eq_zero_nil _ r2_nil); simplify; crush.
        }
        have {}unbal := unbal node_neq_nil.
        destruct (eq_or_succ_cases insert_height_ge l_height_lower) as [H|H].
        {
          functional induction (balance_left v (insert x (Node v0 l1 l2)) r);
            invert t_bal; simplify; lia.
        }
        functional induction (balance_left v (insert x (Node v0 l1 l2)) r); invert t_bal; simplify; try lia.
        destruct lr; [simplify; lia|].
        invert insert_bal; simplify; lia.
      - have l_bal : Balanced l by invert t_bal.
        have {l_bal IHt0}[insert_bal [insert_height_ge unbal]] := IHt0 l_bal.
        have l_height_lower := insert_height_upper_bound x l.
        destruct l.
        {
          clear unbal insert_height_ge insert_bal H.
          simplify.
          invert t_bal; [| simplify; try lia|].
          - symmetry in H5.
            rewrite (height_eq_zero_nil r H5) /balance_left; simplify; lia.
          - exfalso.
            rewrite /balance_left in H0; simplify; lia.
        }
        have r_bal_diff : (1 + height r < height (balance_left v (insert x (Node v0 l1 l2)) r))%nat by lia.
        functional induction (balance_left v (insert x (Node v0 l1 l2)) r); simplify; try lia.
        destruct lr; [simplify; lia|].
        invert insert_bal; simplify; lia.
    Qed.


    (* INSERT PRESERVES BALANCE! *)
    Theorem insert_preserves_Balanced x t : Balanced t → Balanced (insert x t).
    Proof.
      move => t_bal.
      have := insert_preserves_Balanced0 x t_bal.
      tauto.
    Qed.

    Lemma insert_height_lower_bound x t : Balanced t → height t ≤ height (insert x t).
      move => t_bal.
      have := insert_preserves_Balanced0 x t_bal; tauto.
    Qed.

    (* insert is idempotent if the tree was balanced *)
    Theorem insert_idempotent x t : Balanced t → Contains x t → insert x t = t.
    Proof.
      functional induction (insert x t); move => t_bal x_in; eauto.
      - by invert x_in.
      - have x_in_r : Contains x r by
          rewrite /Contains in x_in; case_compare v x.
        have r_bal : Balanced r by invert t_bal.
        have {}IHt0 := IHt0 r_bal x_in_r.
        rewrite IHt0.
        by apply balance_right_Balanced_same.
      - have x_in_l : Contains x l by
          rewrite /Contains in x_in; case_compare' v x.
        have l_bal : Balanced l by invert t_bal.
        have {}IHt0 := IHt0 l_bal x_in_l.
        rewrite IHt0.
        by apply balance_left_Balanced_same.
    Qed.

    Theorem insert_idempotent' x t : Balanced t → Ordered t → insert x (insert x t) = insert x t.
    Proof.
      move => t_bal t_ord.
      apply insert_idempotent.
      - exact: insert_preserves_Balanced.
      - apply Ordered_In_Contains.
        + exact: insert_preserves_Ordered.
        + exact: insert_In_complete2.
    Qed.

    Lemma insert_not_Contains_size x t : ¬ Contains x t → size (insert x t) = 1 + size t.
    Proof.
      functional induction (insert x t); move => not_in; eauto.
      - exfalso; apply: not_in.
        by rewrite /Contains e0.
      - have not_in_r : ¬ Contains x r by
          move => not_in_r; apply: not_in; by rewrite /Contains e0.
        have {not_in_r}IHt0 := IHt0 not_in_r.
        rewrite balance_right_preserves_size; simplify; lia.
      - have not_in_l : ¬ Contains x l by
          move => not_in_l; apply: not_in; by rewrite /Contains e0.
        have {not_in_l}IHt0 := IHt0 not_in_l.
        rewrite balance_left_preserves_size; simplify; lia.
    Qed.

    Lemma insert_Contains_size x t : Contains x t → size (insert x t) = size t.
    Proof.
      functional induction (insert x t); move => x_in; eauto.
      - exfalso; by invert x_in.
      - have x_in_r : Contains x r by
          by rewrite /Contains e0 in x_in.
        have {x_in_r}IHt0 := IHt0 x_in_r.
        rewrite balance_right_preserves_size; simplify; lia.
      - have x_in_l : Contains x l by
          by rewrite /Contains e0 in x_in.
        have {x_in_l}IHt0 := IHt0 x_in_l.
        rewrite balance_left_preserves_size; simplify; lia.
    Qed.

    (* TODO: move up *)
    Lemma Node_inj v1 l1 r1 v2 l2 r2 :
      Node v1 l1 r1 = Node v2 l2 r2 →
      v1 = v2 ∧ l1 = l2 ∧ r1 = r2.
    Proof.
      move => h.
      by invert h.
    Qed.

    Lemma Node_inj_val v1 l1 r1 v2 l2 r2 :
      Node v1 l1 r1 = Node v2 l2 r2 → v1 = v2.
    Proof.
      move => h; by invert h.
    Qed.

    Lemma Node_inj_left v1 l1 r1 v2 l2 r2 :
      Node v1 l1 r1 = Node v2 l2 r2 → l1 = l2.
    Proof.
      move => h; by invert h.
    Qed.

    Lemma Node_inj_right v1 l1 r1 v2 l2 r2 :
      Node v1 l1 r1 = Node v2 l2 r2 → r1 = r2.
    Proof.
      move => h; by invert h.
    Qed.
    Hint Rewrite Node_inj_val Node_inj_left Node_inj_right : core.

    Infix "∘" := ssrfun.comp (at level 60, right associativity).

    Local Notation shrink_max2 := (snd ∘ shrink_max).

    Lemma Some_neq_None X (x : X) : Some x ≠ None.
    Proof.
      move => bad; by invert bad.
    Qed.

    Lemma None_neq_Some X (x : X) : None ≠ Some x.
    Proof.
      move => bad; by invert bad.
    Qed.

    Hint Resolve Some_neq_None None_neq_Some : core.
    Hint Extern 0 =>
      match goal with
      | [ H : Some _ = Some _ |- _ ] => invert H
      | [ H : Some _ = None |- _] => by invert H
      | [ H : None = Some _ |- _] => by invert H
      | [ H : (Some _, _) = (None, _) |- _ ] => by invert H
      | [ H : (None, _) = (Some _, _) |- _ ] => by invert H
      | [ H : (_, Node _ _ _) = (_, Nil) |- _ ] => by invert H
      | [ H : (_, Nil) = (_, Node _ _ _) |- _ ] => by invert H
      end : core.

    Function find_max t : option A :=
      match t with
      | Nil => None
      | Node v l r =>
          match find_max r with
          | None => Some v
          | Some x => Some x
          end
      end.

    Function prune_max t : tree :=
      match t with
      | Nil => Nil
      | Node v l Nil => l
      | Node v l r =>
          balance_left v l (prune_max r)
      end.

    Lemma prune_max_subset x t: In x (prune_max t) → In x t.
    Proof.
      functional induction (prune_max t); move => x_in; simplify; eauto.
      destruct x_in as [|[|]]; eauto.
    Qed.

    Lemma prune_max_subset' x t : In' x (prune_max t) → In' x t.
    Proof.
      rewrite !In'_iff_In; exact: prune_max_subset.
    Qed.

    Lemma prune_max_Nil_right v l : prune_max (Node v l Nil) = l.
    Proof.
      reflexivity.
    Qed.

    Lemma prune_max_descendents v l r : r ≠ Nil → prune_max (Node v l r) = balance_left v l (prune_max r).
    Proof.
      by destruct r.
    Qed.

    Lemma find_max_None_iff t : find_max t = None ↔ t = Nil.
    Proof.
      functional induction (find_max t); split; simplify; eauto.
    Qed.

    Lemma find_max_descendents v l r :
      r ≠ Nil →
      find_max (Node v l r) = find_max r.
    Proof.
      move heq : (Node v l r) => t.
      functional induction (find_max t); move => r_nonnil; simplify; eauto.
      - exfalso.
        apply r_nonnil.
        rewrite (Node_inj_right heq).
        by rewrite find_max_None_iff in e0.
      - by rewrite (Node_inj_right heq).
    Qed.

    Lemma find_max_Some_In x t :
      find_max t = Some x → In x t.
    Proof.
      functional induction (find_max t); move => max_def; simplify; by eauto.
    Qed.

    Lemma find_max_Some_In' x t :
      find_max t = Some x → In' x t.
    Proof.
      functional induction (find_max t); move => max_def; simplify; by eauto.
    Qed.

    Lemma find_max_is_max x t :
      Ordered t →
      find_max t = Some x →
      All (fun v => v = x ∨ v < x) t.
    Proof.
      rewrite Ordered_iff_Ordered'.
      revert x.
      induction t as [|v l IHl r IHr]; [unfold All; eauto|].
      move => x t_ord max_def.
      destruct r.
      - have heq : v = x by invert max_def.
        rewrite -heq.
        repeat split.
        + by left.
        + invert max_def.
          invert t_ord.
          apply: All_imp _ _ H3.
          tauto.
      - invert t_ord.
        have h : find_max (Node v0 r1 r2) = Some x by
          rewrite -max_def; symmetry; apply find_max_descendents, node_neq_nil.
        have x_in_r : In x (Node v0 r1 r2) := find_max_Some_In _ h.
        have v_lt_x := In_All _ _ _ x_in_r H4.
        split; [eauto|].
        split.
        + apply: All_imp _ _ H2; by eauto.
        + apply IHr; by eauto.
    Qed.

    (* TODO: MOVE UP *)
    Lemma All_subset P t1 t2 :
      All P t2 → (∀ x, In x t1 → In x t2) → All P t1.
    Proof.
      rewrite !All_iff_forall.
      by eauto.
    Qed.

    (* TODO: MOVE UP *)
    Lemma All_subset' P t1 t2 :
      All P t2 → (∀ x, In' x t1 → In' x t2) → All P t1.
    Proof.
      rewrite !All_iff_forall'; by eauto.
    Qed.

    (* TODO: MOVE UP *)
    Lemma Ordered_unique_val v l r :
      Ordered (Node v l r) → ¬ In v l ∧ ¬ In v r.
    Proof.
      intros [[all_l l_ord] [all_r r_ord]].
      rewrite !All_iff_forall in all_l all_r.
      split; move => bad; (suff : v < v by order); by eauto.
    Qed.

    (* TODO: MOVE UP *)
    Lemma Ordered_unique_In_left x v l r :
      Ordered (Node v l r) → In x l → x ≠ v ∧ ¬ In x r.
    Proof.
      intros [[all_l l_ord] [all_r r_ord]] x_in_l.
      split.
      - move => bad; invert bad.
        suff : v < v by order.
        rewrite All_iff_forall in all_l.
        by eauto.
      - move => bad.
        rewrite !All_iff_forall in all_l all_r.
        suff : x < x by order.
        transitivity v; by eauto.
    Qed.

    (* TODO: MOVE UP *)
    Lemma Ordered_unique_In_right x v l r :
      Ordered (Node v l r) → In x r → x ≠ v ∧ ¬ In x l.
    Proof.
      intros [[all_l l_ord] [all_r r_ord]] x_in_r.
      split.
      - move => bad; invert bad.
        suff : v < v by order.
        rewrite All_iff_forall in all_r.
        by eauto.
      - move => bad.
        rewrite !All_iff_forall in all_l all_r.
        suff : x < x by order.
        transitivity v; by eauto.
    Qed.

    Lemma prune_max_preserves_All P t :
      All P t → All P (prune_max t).
    Proof.
      rewrite !All_iff_forall.
      move => t_ord x x_in.
      by apply t_ord, prune_max_subset.
    Qed.

    Lemma prune_max_preserves_Ordered t :
      Ordered t → Ordered (prune_max t).
    Proof.
      move => t_ord.
      functional induction (prune_max t); eauto.
      - by destruct t_ord as [[_ l_ord] _].
      - apply balance_left_preserves_Ordered.
        destruct t_ord as [[l_all l_ord] [r_all r_ord]].
        have {}IHt0 := IHt0 r_ord.
        split; eauto.
        split; eauto.
        by apply prune_max_preserves_All.
    Qed.

    Lemma prune_max_extracts x t :
      Ordered t →
      find_max t = Some x →
      ¬ Contains x (prune_max t).
    Proof.
      functional induction (find_max t); move => t_ord max_def.
      - by eauto.
      - clear IHo.
        invert max_def.
        rewrite find_max_None_iff in e0.
        subst.
        rewrite prune_max_Nil_right.
        move => bad.
        destruct t_ord as [[all_l l_ord] _].
        Search Contains In.
        apply Contains_In in bad.
        apply (fun x => In_All _ _ _ x all_l) in bad.
        by order.
      - invert max_def.
        have r_nonnil : r ≠ Nil by
          move => bad; subst; invert e0.
        rewrite (prune_max_descendents _ _ r_nonnil).
        move => bad.
        Search In balance_left.
        apply Contains_In in bad.
        rewrite balance_left_In_iff in bad.
        have t_ord' := t_ord.
        destruct t_ord as [[all_l l_ord] [all_r r_ord]].
        have {}IHo := IHo r_ord e0.
        have x_in_r : In x r by apply find_max_Some_In.
        apply: IHo.
        Search Contains In.
        apply Ordered_In_Contains; [by apply prune_max_preserves_Ordered|].
        rewrite -!In'_iff_In in bad |- *.
        invert bad.
        + suff : v < v by order.
          rewrite All_iff_forall in all_r.
          by eauto.
        + exfalso.
          rewrite In'_iff_In in H0.
          have := Ordered_unique_In_right _ t_ord' x_in_r.
          tauto.
        + assumption.
    Qed.

    Lemma prune_max_size t :
      t ≠ Nil → 1 + size (prune_max t) = size t.
    Proof.
      move => t_nonnil.
      functional induction (prune_max t); simplify; try by eauto.
      f_equal.
      rewrite balance_left_preserves_size.
      destruct r.
      - simplify; lia.
      - rewrite /size -/size.
        have {}IHt0 := IHt0 node_neq_nil.
        simplify; lia.
    Qed.


    Lemma prune_max_height_upper_bound t :
      height (prune_max t) ≤ height t.
    Proof.
      functional induction (prune_max t); simplify; try lia.
      Search balance_left height.
      transitivity (height (Node v l (prune_max r))); [apply balance_left_height_le|].
      simplify; lia.
    Qed.


    (* TODO: MOVE *)
    Lemma wf_lt_height : well_founded (fun t1 t2 => (height t1 < height t2)%nat).
    Proof.
      move => t.
      induction t; [constructor; simplify; lia|].
      destruct IHt1 as [IHt1].
      destruct IHt2 as [IHt2].
      constructor.
      move => y y_rel.
      destruct y as [|yv yl yr]; [constructor; simplify; lia|].
      constructor.
      move => z z_rel.
      have : ((height z) < Nat.max (height t1) (height t2))%nat by simplify; lia.
      linear_arithmetic'; eauto.
    Qed.

    (*TODO: MOVE*)
    Search (S _ ≤ S _)%nat.
    Ltac clear_zero_height :=
      repeat (match goal with
      | [ H : height ?t = 0 |- _ ] =>
          let h := fresh in
          have h := (height_eq_zero_nil _ H);
          clear H;
          symmetry in h; destruct h
      | [ H : 0 = height ?t |- _ ] =>
          symmetry in H;
          let h := fresh in
          have h := (height_eq_zero_nil _ H);
          clear H;
          symmetry in h; destruct h
      | [ H : (_ < 1)%nat |- _ ] =>
          rewrite Nat.lt_1_r in H
      | [ H : _ ≤ 0 |- _] =>
          rewrite Nat.le_0_r in H
      | [ H : (S _ < S _)%nat |- _ ] => rewrite -Nat.succ_lt_mono in H
      | [ H : S _ = S _ |- _ ] => apply Nat.succ_inj in H
      | [ H : S _ ≤ S _ |- _ ] => apply le_S_n in H
      | [ H : height ?t = 1 |- _ ] => destruct t; linear_arithmetic'
      | [ H : 1 = height ?t |- _ ] => destruct t; linear_arithmetic'
      | [ H : height ?t ≤ 1 |- _ ] => destruct t; linear_arithmetic'
      | [ H : context[Nat.max _ _] |- _ ] => linear_arithmetic'
      | [ H : context[Nat.min _ _] |- _ ] => linear_arithmetic'
      end; simplify).

    Ltac clear_useless :=
      repeat match goal with
      | [ H : True |- _ ] => clear H
      | [ H : ?x = ?x |- _] => clear H
      | [ H : Balanced Nil |- _ ] => clear H
      | [ H : Ordered Nil |- _ ] => clear H
      | [ H : 0 ≤ _ |- _ ] => clear H
      | [ H : ?x ≤ ?x |- _ ] => clear H
      end.
    Hint Extern 1 => clear_zero_height : core.
    Hint Resolve height_eq_zero_nil : core.

    Ltac bal_invert :=
      match goal with
      | [ H : Balanced (Node _ _ _) |- _]  => invert H
      end.

    Function bal v l r : tree :=
      if (1 + height r <? height l) then
        balance_left v l r
      else
      if (1 + height l <? height r) then
        balance_right v l r
      else
        Node v l r.

    Function del_max t :=
      match t with
      | Nil => Nil
      | Node v l r =>
          bal v l (del_max r)
      end.

    Lemma bal_preserves_Balanced v l r :
      Balanced (Node v l r) → Balanced (bal v l r).
    Proof.
      move => t_bal.
      functional induction (bal v l r); simplify; try lia; try assumption.
      - by apply balance_left_preserves_Balanced.
      - by apply balance_right_preserves_Balanced.
    Qed.

    Lemma bal_Balanced_same v l r :
      Balanced (Node v l r) → bal v l r = Node v l r.
    Proof.
      move => t_bal.
      functional induction (bal v l r); simplify; try lia; try done.
      - by apply balance_left_Balanced_same.
      - by apply balance_right_Balanced_same.
    Qed.

    Lemma bal_height_upper_bound v l r :
      height (bal v l r) ≤ height (Node v l r).
    Proof.
      functional induction (bal v l r); simplify; try lia; try done.
      - by apply balance_left_height_le.
      - by apply balance_right_height_le.
    Qed.

    Lemma del_max_height_upper_bound t :
      height (del_max t) ≤ height t.
    Proof.
      functional induction (del_max t); [simplify;lia|].
      transitivity (height (Node v l (del_max r))).
      apply bal_height_upper_bound.
      simplify; lia.
    Qed.

    Lemma del_max_eq_Nil v l r :
      del_max (Node v l r) = Nil → l = Nil ∧ r = Nil.
    Proof.
      move heq : (Node v l r) => t.
      move => is_nil.
      functional induction (del_max t); [eauto| ].
      symmetry in heq; invert heq.
      rewrite /bal in is_nil.
      move: is_nil; (repeat split_ifs) => is_nil; eauto.
    Qed.

    Lemma del_max_preserves_Balanced t :
      Balanced t →
      Balanced (del_max t) ∧
        height t ≤ 1 + height (del_max t) ∧
        (del_max t ≠ Nil → height t = 1 + height (del_max t) →
           1 + height (left_child t) = height (right_child t)).
    Proof.
      functional induction (del_max t); [eauto|].
      move => t_bal.
      have r_bal : Balanced r by invert t_bal.
      have {IHt0}[r'_bal [r'_height_lower unbal]] := IHt0 r_bal.
      repeat split.
      -
        functional induction (bal v l (del_max r)).
        + functional induction (balance_left v l (del_max r)); simplify; try lia.


    Lemma prune_max_eq_Nil v l r :
      prune_max (Node v l r) = Nil → l = Nil ∧ r = Nil.
    Proof.
      move heq : (Node v l r) => t.
      move => is_nil.
      functional induction (prune_max t); [eauto| |]; invert heq; by eauto.
    Qed.

    Lemma prune_max_exists t :
      prune_max t ≠ Nil → ∃ v l r, prune_max t = (Node v l r).
    Proof.
      move => t_nonnil.
      move heq : (prune_max t) => t'.
      destruct t'; [tauto|eauto].
    Qed.

    Lemma prune_max_preserves_Balanced t :
      Balanced t →
      Balanced (prune_max t) ∧
        height t ≤ 1 + height (prune_max t) ∧
        (prune_max t ≠ Nil → height t = 1 + height (prune_max t) →
           1 + height (left_child t) = height (right_child t) ∧
           height (left_child (prune_max t)) = height (right_child (prune_max t))).
    Proof.
      induction t as [|v l _ r IHr]; [eauto|].
      move => t_bal.
      repeat split.
      - destruct r as [|rv rl rr]; [simplify; by invert t_bal|].
        rewrite prune_max_descendents; [eauto|].
        have r_bal : Balanced (Node rv rl rr) by invert t_bal.
        have {r_bal IHr}[r'_bal [r'_height_lower unbal]] := IHr r_bal.
        have r'_height_upper := prune_max_height_upper_bound (Node rv rl rr).
        destruct (eq_or_succ_cases r'_height_upper r'_height_lower).
        {
        invert t_bal; apply balance_left_preserves_Balanced.
          * apply Balanced_equal; eauto; lia.
          * apply Balanced_left_heavy; eauto; lia.
          * apply Balanced_right_heavy; eauto; lia.
        }
        invert t_bal.
        1: apply balance_left_preserves_Balanced, Balanced_left_heavy; eauto; lia.
        2: apply balance_left_preserves_Balanced, Balanced_equal; eauto; lia.
        (* +2 diff *)
        destruct (tree_eq_dec (prune_max (Node rv rl rr)) Nil) as [heq|heq].
        { rewrite heq.
          have [rl_nil rr_nil] := prune_max_eq_Nil _ _ _ heq.
          subst.
          simplify.
          destruct l; simplify; try lia.
          linear_arithmetic'; simplify; clear_zero_height; try lia;
            clear_useless;
            rewrite /balance_left; split_ifs; simplify; try lia;
            constructor; by eauto.
        }
        have {unbal}[unbal1 unbal2] := unbal heq H.
        simpl in unbal1.
        destruct (prune_max_exists _ heq) as [rv' [rl' [rr' r'_spec]]].
        symmetry in r'_spec; destruct r'_spec.
        rewrite /balance_left; split_ifs; [ltb_to_lt|simplify; lia].
        destruct l as [|lv ll lr].
        { repeat bal_invert; simplify; clear_zero_height; try lia. }
        split_ifs; ltb_to_lt.
        simplify; repeat bal_invert; clear_zero_height; try lia.
        apply Balanced_equal; crush.
        apply Balanced_equal; crush.
        destruct lr as [|lrv lrl lrr]; simplify.
        {
          clear_zero_height; try lia.
        }
        clear_zero_height; try lia.
        {
        repeat bal_invert; simplify; clear_zero_height; try lia.
        apply Balanced_equal; crush.
        apply Balanced_equal; crush.
        }
        {
        repeat bal_invert; simplify; clear_zero_height; try lia.
        apply Balanced_equal; crush.
        apply Balanced_equal; crush.
        apply Balanced_equal; crush.
        apply Balanced_right_heavy; crush.
        }
        {
          repeat bal_invert; simplify; clear_zero_height; try lia.
          apply Balanced_equal.
          apply Balanced_left_heavy; try assumption; try lia.
          lia.
        }


        invert H3; simplify; clear_zero_height; try lia.

        functional induction (balance_left v l (Node rv' rl' rr')).

        Search prune_max .
        destruct l.
        { repeat bal_invert; simplify; clear_zero_height; try lia. }
        split_ifs; ltb_to_lt.
        + invert r'_bal;
          repeat bal_invert; clear_zero_height; try lia;
          apply Balanced_equal; crush.


        move heq2 : (prune_max (Node rv rl rr)) => r'.
        functional induction (balance_left v l r'); try lia.
        + simplify; try lia.
        + repeat ltb_to_lt.
          invert r'_bal; simplify; clear_zero_height; try lia.
          simpl.


        functional induction (balance_left v l (prune_max (Node rv rl rr))); simplify; try lia; clear_zero_height; try lia.
        + repeat bal_invert; simplify; clear_zero_height; try lia.
          apply Balanced_equal; crush.
        + repeat bal_invert; simplify; clear_zero_height; try lia.
          destruct lr; [simplify; lia|].
          simplify.
          repeat bal_invert; clear_zero_height; try lia;
            apply Balanced_equal; crush.
        + repeat bal_invert; simplify; clear_zero_height; try lia.
          destruct lr; simplify; [lia|].
          clear_zero_height; try lia.
          2: repeat bal_invert; clear_zero_height; try lia; apply Balanced_left_heavy; by crush.

          repeat bal_invert; clear_zero_height; try lia;
            try (apply Balanced_left_heavy; by crush).
          apply Balanced_equal; crush.

          have : height ll = height lr1 ∨ S (height ll) = height lr1 ∨ height ll = S (height lr1).
          destruct (eq_or_succ_cases )
          apply Balanced_left_heavy; crush.
          clear_zero_height; try lia.
          repeat
          apply Balanced_; crush.


        destruct rl as [|rlv rl1 rl2], rr as [|rrv rr1 rr2].
        { simplify.
          move heq: Nil => r.
          functional induction (balance_left v l r); simplify; try lia.
          - linear_arithmetic'; try lia.
            have h : height lr = 0 by lia.
            clear_zero_height.
            clear_useless.
            apply Balanced_equal; simplify; try lia.
            clear_useless.
            linear_arithmetic'; clear_zero_height; try lia.
            repeat bal_invert; simplify; linear_arithmetic'; simplify; clear_zero_height; try lia.
            constructor; by eauto.
          - clear_useless.
            invert H3; linear_arithmetic'; clear_zero_height; try lia.
            + simplify; linear_arithmetic'; clear_zero_height; try lia.
              linear_arithmetic'; clear_zero_height; try lia.
              constructor; by eauto.
            + linear_arithmetic'; clear_zero_height; try lia.
              constructor; by eauto.
        }
        {
          rewrite prune_max_descendents; [eauto|].

        }

              have h : (height ll1 = 0) by lia.
              symmetry in h; destruct h.
              (have h : height ll2 = 0 by lia); symmetry in h; destruct h.
              simplify
              linear_arithmetic'; clear_zero_height; try lia.

            { destruct ll, lr; linear_arithmetic'; simplify; try lia.
              clear_zero_height; linear_arithmetic'; try lia.
              clear_zero_height.
              invert H2; invert H6; linear_arithmetic'; simplify; clear_zero_height; try lia.
              crush.
              eauto.
            }
            clear_zero_height.
            +
              destruct ll; simplify; try lia.
            destruct ll; simplify; try lia.

          destruct l; simplify; [lia|].

        }


        destruct
        invert t_bal.
        + apply balance_left_preserves_Balanced.
          apply Balanced_equal; .

        destruct rr as [|rrv rrl rrr]; simplify.
        {  }
        rewrite /prune_max -/prune_max.
        destruct l as [|lv ll lr]; [simplify|].
        move heq : (Node v l r) => t.
        functional induction (prune_max t); simplify.
        + by eauto.
        + invert heq; by invert t_bal.
        + symmetry in heq; invert heq.
          clear IHt0.
          destruct r as [|rv rl rr]; [simplify; by exfalso|].
          clear_useless.
          have r_bal : Balanced (Node rv rl rr) by invert t_bal.
          have {r_bal IHr}[r'_bal [r'_height_lower unbal]] := IHr r_bal.
          have r'_height_upper := prune_max_height_upper_bound (Node rv rl rr).
          destruct (eq_or_succ_cases r'_height_upper r'_height_lower).
          * apply balance_left_preserves_Balanced.
             invert t_bal.
             -- apply Balanced_equal; eauto; try lia.
             -- apply Balanced_left_heavy; eauto; try lia.
             -- apply Balanced_right_heavy; eauto; try lia.
          *


          clear

        destruct r as [|rv rl rr]; [invert t_bal; simplify; eauto|].
        have r_bal : Balanced (Node rv rl rr) by invert t_bal.
        have {r_bal IHr}[r'_bal [r'_height_lower unbal]] := IHr r_bal.
        destruct rr

        { invert t_bal; simplify; eauto. }

      functional induction (prune_max t); repeat split; simplify; try lia; eauto.
      -
        invert t_bal; simplify; clear_zero_height; simplify; try lia.
        by destruct H.
        destruct l; simplify; clear_zero_height; simplify; try lia.
      - have r_bal : Balanced r by invert t_bal.
        have {r_bal IHt0}[r'_bal [r'_height_lower unbal]] := IHt0 r_bal.
        have r'_height_upper := prune_max_height_upper_bound r.
        destruct (eq_or_succ_cases r'_height_upper r'_height_lower) as [H|H].
        + apply balance_left_preserves_Balanced.
          invert t_bal.
          * apply Balanced_equal; eauto; try lia.
          * apply Balanced_left_heavy; eauto; try lia.
          * apply Balanced_right_heavy; eauto; try lia.
        + invert t_bal;
            [apply balance_left_preserves_Balanced, Balanced_left_heavy; eauto; lia|
            |
            apply balance_left_preserves_Balanced, Balanced_equal; eauto; lia].
          (* there's now a +2 diff, balance_left kicks in *)
          clear r'_height_lower r'_height_upper.
          have {}unbal := unbal H.
          destruct r as [|rv rl rr]; [crush|].
          functional induction (balance_left v l (prune_max (Node rv rl rr))); simplify; try lia.
          * do 2 bal_invert; linear_arithmetic'; try lia;
              apply Balanced_equal; by crush.
          * destruct lr; simplify; [lia|].
            repeat bal_invert; simplify; linear_arithmetic'; simplify; clear_zero_height; try lia.
            3: { lia. }
            3: have : S (height ll) = height lr1 ∨ height ll = S (height lr1) ∨ height ll = height lr1 by
              (left; lia) || (right; left; lia) || (right; right; lia).
            all: have : Balanced (Node v lr2 r) by crush.

            destruct ll, lr; simplify; [lia| | lia| ].
            {
              repeat bal_invert; simplify; linear_arithmetic'; simplify; clear_zero_height; try lia.
              apply Balanced_equal; by crush.
            }

            invert H3; invert H7; invert H4; simplify; linear_arithmetic'; try lia.
            apply Balanced_left_heavy; crush.
            apply Balanced_left_heavy; crush.
          
            repeat bal_invert; simplify; linear_arithmetic'; try lia.
            destruct r'_bal; linear_arithmetic'; simplify; clear_zero_height; try lia.
            simplify; clear_zero_height.
            invert H4; linear_arithmetic'; try lia.
            simplify.
            apply Balanced_left_heavy; crush.
            apply Balanced_left_heavy; crush.
            apply Balanced_left_heavy; crush.
            apply Balanced_; crush.
            linear_arithmetic'; simplify.


            bal_invert.

            apply Balanced_equal; crush.
            apply Balanced_equal; crush.
            apply Balanced_equal; crush.
          simpl in unbal.


    Lemma shrink_max_eq_None t : fst (shrink_max t) = None → t = Nil.
    Proof.
      functional induction (shrink_max t); simplify; by eauto.
    Qed.

    Lemma shrink_max_Nil : shrink_max Nil = (None, Nil).
    Proof.
      reflexivity.
    Qed.

    Lemma shrink_max_subset x t : In x (snd (shrink_max t)) → In x t.
    Proof.
      functional induction (shrink_max t); move => In_shrink; simplify; eauto.
      destruct In_shrink as [|[|]]; by eauto.
    Qed.

    Lemma shrink_max_subset' x t : In' x (snd (shrink_max t)) → In' x t.
    Proof.
      rewrite !In'_iff_In.
      exact: shrink_max_subset.
    Qed.

    Lemma shrink_max_right_child_nil v l : shrink_max (Node v l Nil) = (Some v, l).
    Proof.
      reflexivity.
    Qed.

    Lemma shrink_max_exists v l r : ∃ x t, shrink_max (Node v l r) = (Some x, t).
    Proof.
      move heq : (Node v l r) => t'.
      functional induction (shrink_max t'); by eauto.
    Qed.


    Lemma shrink_max_descendents_fst v l r :
      r ≠ Nil →
      fst (shrink_max (Node v l r)) = fst (shrink_max r).
    Proof.
      move heq : (Node v l r) => t'.
      functional induction (shrink_max t'); move => r_nonnil; simplify; eauto.
      - by rewrite (Node_inj_right heq).
      - rewrite (shrink_max_eq_None _ e0) in heq.
        exfalso; apply r_nonnil.
        eapply Node_inj_right; eassumption.
    Qed.

    Lemma shrink_max_descendents_snd v l r :
      r ≠ Nil →
      snd (shrink_max (Node v l r)) = balance_left v l (snd (shrink_max r)).
    Proof.
      move heq : (Node v l r) => t'.
      move => r_nonnil.
      functional induction (shrink_max t'); simplify; eauto.
      - symmetry in heq; invert heq.
        reflexivity.
      - symmetry in heq; invert heq.
        exfalso.
        apply r_nonnil.
        by apply shrink_max_eq_None.
    Qed.

    Lemma shrink_max_Some_In t x t' :
      shrink_max t = (Some x, t') → In x t.
    Proof.
      revert x t'.
      functional induction (shrink_max t); move => x' t'' is_some; simplify; eauto.
      - destruct r; [simplify;by eauto|].
        right; right.
        have [x'' [t t_eq]] := shrink_max_exists v0 r1 r2.
        have heq1 : x'' = x.
        suff h : Some x'' = Some x by invert h.
        change (fst (Some x'', t) = Some x).
        by rewrite -e0 t_eq.
        have heq2 : x' = x by invert is_some.
        rewrite heq2 -heq1.
        by have := IHp x'' t t_eq.
      - left; by invert is_some.
    Qed.

    Lemma shrink_max_preserves_All P t : All P t → All P (snd (shrink_max t)).
    Proof.
      move => h_all.
      rewrite !All_iff_forall' in h_all |- *.
      move => x x_in'.
      by apply h_all, shrink_max_subset'.
    Qed.

    Lemma shrink_max_preserves_Ordered' t : Ordered' t → Ordered' (snd (shrink_max t)).
    Proof.
      functional induction (shrink_max t); simplify; eauto.
      -
        apply balance_left_preserves_Ordered'.
        invert H.
        constructor; eauto.
        by apply shrink_max_preserves_All.
      - by invert H.
    Qed.

    Lemma shrink_max_preserves_Ordered t : Ordered t → Ordered (snd (shrink_max t)).
    Proof.
      rewrite !Ordered_iff_Ordered'.
      exact: shrink_max_preserves_Ordered'.
    Qed.

    Lemma shrink_max_eq t : shrink_max t = (find_max t, prune_max t).
    Proof.
      induction t as [|v l IHl r IHr]; [reflexivity|].
      destruct r as [|rv rl rr]; [reflexivity|].
      destruct (shrink_max_exists v l (Node rv rl rr)) as [x [r' spec]].
      rewrite spec pair_equal_spec; split.
      - replace (Some x) with (fst (Some x, r')) by reflexivity.
        rewrite -spec.
        rewrite shrink_max_descendents_fst; [eauto|].
        rewrite find_max_descendents; [eauto|].
        by rewrite IHr.
      - replace r' with (snd (Some x, r')) by reflexivity.
        rewrite -spec.
        rewrite prune_max_descendents; [eauto|].
        rewrite shrink_max_descendents_snd; [eauto|].
        by rewrite IHr.
    Qed.

    Lemma shrink_max_eq_fst t : fst (shrink_max t) = find_max t.
    Proof.
      by rewrite shrink_max_eq.
    Qed.

    Lemma shrink_max_eq_snd t : snd (shrink_max t) = prune_max t.
    Proof.
      by rewrite shrink_max_eq.
    Qed.

    Lemma rotate_left_preserves_shrink_max v l r :
      shrink_max (rotate_left v l r) = shrink_max (Node v l r).
      Abort.


    Lemma shrink_max_extracts x t :
      Ordered t →
      fst (shrink_max t) = Some x →
      ¬ Contains x (snd (shrink_max t)).
    Proof.
      functional induction (shrink_max t); move => t_ord max_def; eauto.
      Abort.

    Lemma shrink_max_is_max x t :
      Ordered t →
      fst (shrink_max t) = Some x →
      All (fun v => v = x ∨ v < x) t.
    Proof.
      rewrite Ordered_iff_Ordered'.
      revert x.
      functional induction (shrink_max t); move => x0 t_ord max_def; repeat split; simplify; eauto.
      - symmetry in max_def; invert max_def.
        Abort.

    Lemma shrink_max_height_upper_bound t : height (snd (shrink_max t)) ≤ height t.
    Proof.
      functional induction (shrink_max t); simplify; eauto.
      - transitivity (height (Node v l (snd (shrink_max r)))); [by apply balance_left_height_le |].
        simplify; lia.
      - lia.
    Qed.

    Lemma shrink_max_height_lower_bound t : Balanced t → height t ≤ 1 + height (snd (shrink_max t)).
    Proof.
      functional induction (shrink_max t); move => t_bal; simplify; eauto.
      - Abort.

    Lemma shrink_max_preserves_Balanced t : Balanced t → Balanced (snd (shrink_max t)).
    Proof.
      functional induction (shrink_max t); move => t_bal; simplify; eauto; [| by invert t_bal].
      Abort.


  (* End Facts. *)
End AVL.

Module M := AVL PeanoNat.Nat.
Import M.

Definition tt := insert 45 (insert 20 (insert 42 (insert 6 (insert 7 (insert 5 (insert 92 Nil)))))).
Compute tt.
Compute to_list tt.
Compute of_list (to_list tt).
Definition tt_l := [45; 20; 42; 6; 7; 5; 92].
Compute of_list tt_l.
Compute tt.
Compute (Allb (fun x => 3 <? x) tt).
Compute (Ordered_dec tt).
Compute (compare 7 7).
Print sumbool.
Definition not_ordered := (Node 5 (Node 7 Nil Nil) Nil).
Compute (match (Ordered_dec tt) with | left _ => 0 | right _ => 1 end).
Compute (match (Ordered_dec not_ordered) with | left _ => 0 | right _ => 1 end).

Print M.tree.

