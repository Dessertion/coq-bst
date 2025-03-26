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
    Lemma Any_iff_exists P t :
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

    Lemma All_iff_forall P t :
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

    (* Hint Rewrite Any_iff_exists All_iff_forall : core. *)


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
  Hint Rewrite Allb_iff_All Anyb_iff_Any Any_iff_exists : core.
  (* Hint Rewrite All_iff_forall Any_iff_exists Allb_iff_All Anyb_iff_Any : core. *)

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
        | Node lv ll lr =>
            if height lr <? height ll then
              (* left-left, one rotation *)
              rotate_right v (Node lv ll lr) r
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
        | Node rv rl rr =>
            if height rl <? height rr then
              (* right-right, one rotation *)
              rotate_left v l (Node rv rl rr)
            else
              (* right-left, two rotations *)
              rotate_left v l (rotate_right rv rl rr)
        end
      else
        Node v l r.

  End Rotations.
  Functional Scheme balance_left_ind := Induction for balance_left Sort Prop.
  Functional Scheme balance_right_ind := Induction for balance_right Sort Prop.

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

  (* shrink_max removes and returns the maximum (right-most) element of a tree *)
  Fixpoint shrink_max (t : tree) : option A * tree :=
    match t with
    | Nil => (None, Nil)
    | Node v l r =>
        match shrink_max r with
        | (None, _) => (Some v, l)
        | (Some x, r') => (Some x, balance_right v l r')
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
  Functional Scheme del_root_ind := Induction for insert Sort Prop.
  Functional Scheme delete_ind := Induction for insert Sort Prop.
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
    end.
  Hint Extern 1 => match_compare : core.

  Hint Rewrite Nat.max_id : core.

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
        rewrite All_iff_forall in H1.
        specialize (H1 x x_In).
        by match_compare.
        (* rewrite All_iff_forall in H1. *)
        (* specialize (H1 x x_In). *)
        (* by case_compare y x. *)
      - crush.
        rewrite All_iff_forall in H.
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

    (* Hint Resolve balance_left_preserves_Ordered : core. *)
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
      move=> Hbal.
      rewrite /balance_left.
      split_ifs.
      - destruct l.
        + by crush.
        + split_ifs; invert Hbal; by crush.
      - assumption.
    Qed.

    Lemma balance_right_preserves_Balanced v l r : Balanced (Node v l r) → Balanced (balance_right v l r).
    Proof.
      move=>Hbal.
      rewrite /balance_right.
      split_ifs.
      - destruct r.
        + by crush.
        + split_ifs; invert Hbal; by crush.
      - assumption.
    Qed.

    Lemma balance_left_Balanced_same v l r : Balanced (Node v l r) → balance_left v l r = Node v l r.
    Proof.
      move=>Hbal.
      rewrite /balance_left.
      split_ifs.
      - destruct l.
        + done.
        + split_ifs; invert Hbal; by crush.
      - done.
    Qed.

    Lemma balance_right_Balanced_same v l r : Balanced (Node v l r) → balance_right v l r = Node v l r.
    Proof.
      move=>Hbal.
      rewrite /balance_right.
      split_ifs; destruct r; try (split_ifs; invert Hbal); by crush.
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
      rewrite /balance_left.
      split_ifs; destruct l; try split_ifs; crush.
      destruct l2; by crush.
    Qed.

    Lemma balance_right_height_le v l r :
      height (balance_right v l r) ≤ height (Node v l r).
    Proof.
      rewrite /balance_right.
      split_ifs; destruct r; try split_ifs; crush.
      destruct r1; by crush.
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


    Lemma insert_height_le x t : height (insert x t) ≤ 1 + height t.
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

    Lemma hmmm x t :
      Balanced t →
      Balanced (insert x t) ∧ height t ≤ height (insert x t).
    Proof.
      induction t; [by crush|].
      move => bal.
      split.
      - rewrite /insert -/insert; match_compare; [by crush| | ].
        + apply balance_right_preserves_Balanced.
          have Hle := insert_height_le x t2.
          invert bal.
          * have [bal Hle2] := IHt2 H4.
            destruct (eq_or_succ_cases Hle2 Hle); crush.
          * have [bal Hle2] := IHt2 H4.
            destruct (eq_or_succ_cases Hle2 Hle); crush.
          * have [bal Hle2] := IHt2 H4.
            destruct (eq_or_succ_cases Hle2 Hle); [crush|].
            Abort.
      

    Lemma hmmm x v l r :
      Balanced (Node v l r) →
      Balanced (insert x (Node v l r)) ∧
        height (Node v l r) ≤ height (insert x (Node v l r)) ∧
        height (Node v l r) ≤ height (balance_left v (insert x l) r) ∧
        height (Node v l r) ≤ height (balance_right v l (insert x r)).
    Proof.
      induction l, r.
      - crush; match_compare.
        + by constructor.
        + apply balance_right_preserves_Balanced; by repeat constructor.
        + apply balance_left_preserves_Balanced; by repeat constructor.
      - Abort.
      (* - by crush. *)
      (* - repeat split. *)
      (*   + rewrite /insert -/insert; match_compare; [by constructor| |] . *)
      (*     * apply balance_right_preserves_Balanced. *)
      (*       have {}[ins_bal [Hle _]] := IHBalanced2. *)
      (*       have Hle2 := insert_height_le x r0. *)
      (*       destruct (eq_or_succ_cases Hle Hle2); [constructor; by crush|]. *)
      (*       apply Balanced_right_heavy; by crush. *)
      (*     * apply balance_left_preserves_Balanced. *)
      (*       have {}[ins_bal [Hle _]] := IHBalanced1. *)
      (*       have Hle2 := insert_height_le x l0. *)
      (*       destruct (eq_or_succ_cases Hle Hle2); [constructor; by crush|]. *)
      (*       apply Balanced_left_heavy; by crush. *)
      (*   + rewrite /insert -/insert; match_compare; [lia | |].  *)
      (*     * Abort. *)
      

    Lemma insert_height_ge x t :
      Balanced t →
      Balanced (insert x t) ∧ height t ≤ height (insert x t) .
    Proof.
      induction 1.
      - by crush.
      - have ans1 : Balanced (insert x (Node v l r)).
        {
        rewrite /insert -/insert; match_compare; [by constructor| |].
        * apply balance_right_preserves_Balanced.
          clear IHBalanced1.
          have {}[ins_bal Hle] := IHBalanced2.
          have Hle2 := insert_height_le x r.
          destruct (eq_or_succ_cases Hle Hle2); [constructor; by crush|].
          apply Balanced_right_heavy; by crush.
        * apply balance_left_preserves_Balanced.
          have {}[ins_bal Hle] := IHBalanced1.
          have Hle2 := insert_height_le x l.
          destruct (eq_or_succ_cases Hle Hle2); [constructor; by crush|].
          apply Balanced_left_heavy; by crush.
        }
        split; [assumption|].
        rewrite /insert -/insert in ans1 |- *; match_compare; [lia | |]. 
        Abort.


    Lemma insert_preserves_Balanced x t : Balanced t → Balanced (insert x t).
    Proof.
      (* move=>Hbal. *)
      (* functional induction (insert x t); [by constructor| assumption| |]. *)
      (* - apply balance_right_preserves_Balanced. *)
      (*   invert Hbal; simplify. *)
      (*   + *)
      (* -  *)
      (* induction t; try by constructor. *)
      (* rewrite /insert -/insert. *)
      (* have {}IHt1 := IHt1 (invert_Balanced_left Hbal). *)
      (* have {}IHt2 := IHt2 (invert_Balanced_right Hbal). *)
      (* elim_compare v x; simplify. *)
      (* - assumption. *)
      (* - invert Hbal. *)

        Admitted.






  (* End Facts. *)


  Section MaxHeight.

    Lemma size_lt_height t :
      (size t < 2 ^ (height t))%nat.
    Proof.
      induction t.
      { by crush. }
      rewrite /size -/size.
      rewrite /height -/height.
      have one_lt_two : (1 < 2)%nat by lia.
      suff :
        ∀ t1 t2, (size t1 < 2 ^ height t1)%nat → (size t2 < 2 ^ height t2)%nat → (height t1 < height t2)%nat →
                 (1 + size t1 + size t2 < 2 ^ (1 + Nat.max (height t1) (height t2)))%nat.
      { move => winner.
        destruct (Nat.lt_trichotomy (height t1) (height t2)) as [h|[h|h]].
        - by apply winner.
        - destruct h; by crush.
        -
          rewrite Nat.max_comm.
          replace (1 + size t1 + size t2) with (1 + size t2 + size t1) by ring.
          by apply winner.
      }
      clear v t1 t2 IHt1 IHt2.
      move=>t1 t2 IHt1 IHt2 h.
      have : (size t1 < 2^height t2)%nat by have H := Nat.pow_lt_mono_r _ _ _ one_lt_two h; lia.
      by crush.
    Qed.

    Lemma log2_size_lt_height t :
      t ≠ Nil →
      (Nat.log2 (size t) < height t)%nat.
    Proof.
      move => t_nonnil.
      rewrite -Nat.log2_lt_pow2.
      destruct t; crush.
      apply size_lt_height.
    Qed.


     Fixpoint perfect_tree x (h : nat) :=
      match h with
      | 0 => Nil
      | S h => Node x (perfect_tree x h) (perfect_tree x h)
      end.

    Lemma perfect_tree_height x h :
      height (perfect_tree x h) = h.
    Proof.
      induction h; by crush.
    Qed.

    Lemma perfect_tree_balanced x h :
      Balanced (perfect_tree x h).
    Proof.
      induction h; constructor; crush.
    Qed.

    (* a tree with 2^h elements must have height at least h + 1  *)
    Lemma min_height_of_size t h :
      2 ^ h ≤ size t → (h < height t)%nat.
    Proof.
      move => t_size.
      apply Classical_Prop.NNPP.
      move=>bad.
      rewrite Nat.nlt_ge in bad.
      have hmmm := size_lt_height t.
      suff : (size t < 2^h)%nat by lia.
      apply (Nat.lt_le_trans (size t) (2^height t) (2 ^ h) hmmm).
      by apply Nat.pow_le_mono_r.
    Qed.

    (* given any height, there exists a Balanced tree with that height.
       (as long as A is not an empty type!)
     *)
    Lemma exists_tree_of_height (nonempty : inhabited A) (h : nat)  :
      ∃ t : tree, Balanced t ∧ height t = h.
    Proof.
      destruct nonempty as [x].
      exists (perfect_tree x h).
      by auto using perfect_tree_height, perfect_tree_balanced.
    Qed.

    Search nat lt ex.
    Search "well".

    Definition is_tree_of_height_size h s : tree → Prop :=
      fun t => Balanced t ∧ height t = h ∧ size t = s.
    Hint Unfold is_tree_of_height_size : core.
    Hint Extern 1 =>
           match goal with
           | [ H : is_tree_of_height_size _ _ _ |- _ ] => destruct H
           end : core.

    Lemma exists_size_of_height (nonempty : inhabited A) (h : nat) :
      ∃ s : nat, ∃ t, is_tree_of_height_size h s t.
    Proof.
      destruct nonempty as [x].
      exists (size (perfect_tree x h)), (perfect_tree x h).
      by auto using perfect_tree_balanced, perfect_tree_height.
    Qed.

    Lemma classical_dec_pred {A} {P : A → Prop} : ∀ x, {P x} + {¬ P x}.
      exact (fun x => excluded_middle_informative _).
    Qed.

    Lemma exists_min_size_of_height (nonempty : inhabited A) (h : nat) :
      ∃ s : nat,
        ((∃ t, is_tree_of_height_size h s t) ∧
        ∀ t', Balanced t' → height t' = h → s ≤ size t').
    Proof.
      pose foundX := nat_findX
                      (fun s => ∃ t, is_tree_of_height_size h s t)
                      classical_dec_pred
                      (exists_size_of_height nonempty h).
      set s := proj1_sig foundX.
      have [t t_spec] := (proj1 (proj2_sig foundX)).
      exists s; split.
      - exists t; assumption.
      - move => t' t'_bal t'_height.
        have solver := nat_find_min'
                      (fun s => ∃ t, is_tree_of_height_size h s t)
                      classical_dec_pred
                      (exists_size_of_height nonempty h).
        have H : is_tree_of_height_size h (size t') t' by crush.
        exact: solver (size t') (ex_intro _ _ H).
    Qed.

    Definition min_size_of_height (nonempty : inhabited A) (h : nat) : nat :=
      nat_find _ classical_dec_pred (exists_min_size_of_height nonempty h).

    Definition min_size_of_height' (nonempty : inhabited A) (h : nat) :=
      nat_findX _ classical_dec_pred (exists_min_size_of_height nonempty h).

    Lemma uninhabited_no_height :
      ¬ inhabited A → ∀ t, height t = 0.
    Proof.
      move=>empty t.
      destruct t; by crush.
    Qed.

    Lemma exists_tree_of_height_of_min_size (nonempty : inhabited A) (h : nat) :
      ∃ t : tree, is_tree_of_height_size h (min_size_of_height nonempty h) t.
    Proof.
      pose found :=
        nat_findX _ classical_dec_pred (exists_min_size_of_height nonempty h).
      replace (min_size_of_height nonempty h) with (proj1_sig found) by reflexivity.
      have t_ex := proj2_sig found.
      by crush.
    Qed.

    Lemma min_size_minimal (nonempty : inhabited A) (h : nat) :
      ∀ t, Balanced t → height t = h → min_size_of_height nonempty h ≤ size t.
    Proof.
      have [solver] :=
      nat_find_spec _ classical_dec_pred (exists_min_size_of_height nonempty h).
      done.
    Qed.

    Lemma min_size_minimal' (nonempty : inhabited A) (h : nat) :
      ∀ t, Balanced t → height t = h → ¬ (size t < min_size_of_height nonempty h)%nat.
    Proof.
      setoid_rewrite Nat.nlt_ge.
      exact: min_size_minimal.
    Qed.

    Lemma min_size_0 (nonempty : inhabited A) :
      min_size_of_height nonempty 0 = 0.
    Proof.
      rewrite nat_find_eq_iff.
      repeat (split; auto).
      - by exists Nil.
      - by crush.
      - lia.
    Qed.

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

    Lemma min_size_1 (nonempty : inhabited A) :
      min_size_of_height nonempty 1 = 1.
    Proof.
      rewrite nat_find_eq_iff.
      have [v] := nonempty.
      repeat (split; auto).
      - exists (perfect_tree v 1); by crush.
      - move => t _ t_height.
        have [t' t'_eq] := height_eq_one_singleton _ t_height.
        by rewrite t'_eq.
      - move => n n_zero [bad_ex _].
        have {}n_zero : n = 0 by lia.
        symmetry in n_zero; destruct n_zero.
        destruct bad_ex as [t [_ [t_height t_size]]].
        rewrite (size_eq_zero_nil _ t_size) in t_height.
        by invert t_height.
    Qed.


    Lemma node_neq_nil {v l r} : Node v l r ≠ Nil.
      by crush.
    Qed.

    Lemma nil_neq_node {v l r} : Nil ≠ Node v l r.
      by crush.
    Qed.

    Fixpoint prune_longest t :=
      match t with
      | Nil => Nil
      | Node _ Nil Nil => Nil
      | Node v l r =>
          if height l <? height r then
            Node v l (prune_longest r)
          else
            Node v (prune_longest l) r
      end.

    Lemma prune_longest_case_lt v l r :
      (height l < height r)%nat →
      prune_longest (Node v l r) = Node v l (prune_longest r).
    Proof.
      move => hlt.
      destruct l, r.
      1,2,3:by crush.
      rewrite {1}/prune_longest; split_ifs; rewrite -/prune_longest.
      2: by crush.
      reflexivity.
    Qed.

    Lemma prune_longest_case_gt v l r :
      (height r < height l)%nat →
      prune_longest (Node v l r) = Node v (prune_longest l) r.
    Proof.
      move => hlt.
      destruct l, r.
      1,2,3:by crush.
      rewrite {1}/prune_longest; split_ifs; rewrite -/prune_longest.
      1: by crush.
      reflexivity.
    Qed.

    Lemma prune_longest_case_eq v l r :
      height l = height r → l ≠ Nil → r ≠ Nil →
      prune_longest (Node v l r) = Node v (prune_longest l) r.
    Proof.
      move => hlt.
      destruct l, r.
      1,2,3:by crush.
      rewrite {1}/prune_longest; split_ifs; rewrite -/prune_longest.
      1: by crush.
      reflexivity.
    Qed.


    Lemma prune_longest_size {t} :
      t ≠ Nil → 1 + size (prune_longest t) = size t.
    Proof.
      induction t.
      - by crush.
      - move => _.
        destruct t1, t2.
        + reflexivity.
        + by crush.
        + by crush.
        + have {}IHt1 := IHt1 node_neq_nil.
          have {}IHt2 := IHt2 node_neq_nil.
          rewrite /prune_longest; split_ifs; rewrite -/prune_longest.
          * by crush.
          * change (1 + size (Node v (prune_longest (Node v0 t1_1 t1_2)) (Node v1 t2_1 t2_2))
                   = size (Node v (Node v0 t1_1 t1_2) (Node v1 t2_1 t2_2))).
            rewrite /size -/size.
            rewrite IHt1.
            replace (size (Node v0 t1_1 t1_2)) with (1 + size t1_1 + size t1_2) by reflexivity.
            ring.
      Qed.

    Lemma prune_longest_height_le t :
      height (prune_longest t) ≤ height t.
    Proof.
      induction t.
      1: by crush.
      destruct t1, t2.
      + simplify; lia.
      + by crush.
      + by crush.
      + rewrite /prune_longest; split_ifs; rewrite -/prune_longest; by crush.
    Qed.

    Lemma prune_longest_height_ge t :
      height t ≤ 1 + height (prune_longest t).
    Proof.
      induction t.
      1: by crush.
      destruct t1, t2.
      + simplify; lia.
      + by crush.
      + by crush.
      + rewrite /prune_longest; split_ifs; rewrite -/prune_longest.
        * change (height (Node v (Node v0 t1_1 t1_2) (Node v1 t2_1 t2_2)) ≤
                    1 + height (Node v (Node v0 t1_1 t1_2) (prune_longest (Node v1 t2_1 t2_2)))).
          rewrite /height -/height in IHt1, IHt2 *.
          lia.
        * change (height (Node v (Node v0 t1_1 t1_2) (Node v1 t2_1 t2_2)) ≤
                    1 + height (Node v (prune_longest (Node v0 t1_1 t1_2)) (Node v1 t2_1 t2_2))).
          rewrite /height -/height in IHt1, IHt2 *.
          lia.
    Qed.

    Lemma prune_longest_height_cases t :
      height (prune_longest t) = height t ∨
      1 + height (prune_longest t) = height t.
    Proof.
      have := prune_longest_height_le t.
      have := prune_longest_height_ge t.
      lia.
    Qed.

    Lemma prune_longest_balanced t :
      Balanced t → Balanced (prune_longest t).
    Proof.
      move => bal.
      induction bal.
      - by crush.
      - destruct l, r.
        1,2,3: by crush.
        rewrite (prune_longest_case_eq v H).
        1,2: by crush.
        destruct (prune_longest_height_cases (Node v0 l1 l2)) as [h|h].
        + apply Balanced_equal; by crush.
        + apply Balanced_right_heavy; by crush.
      - have Hgt : (height r < height l)%nat by lia.
        rewrite (prune_longest_case_gt _ _ _ Hgt).
        destruct (prune_longest_height_cases l).
        + apply Balanced_left_heavy; by crush.
        + apply Balanced_equal; by crush.
      - have Hlt : (height l < height r)%nat by lia.
        rewrite (prune_longest_case_lt _ _ _ Hlt).
        destruct (prune_longest_height_cases r).
        + apply Balanced_right_heavy; by crush.
        + apply Balanced_equal; by crush.
    Qed.

    Lemma prune_longest_height_eq (nonempty : inhabited A) t h :
      t ≠ Nil →
      is_tree_of_height_size h (min_size_of_height nonempty h) t →
      1 + height (prune_longest t) = height t.
    Proof.
      move => t_nonnil t_spec.
      destruct (prune_longest_height_cases t) as [height_eq|].
      2: by crush.
      exfalso.
      have prune_size : 1 + size (prune_longest t) = size t :=
        prune_longest_size t_nonnil.
      have prune_balanced : Balanced (prune_longest t) by
        apply prune_longest_balanced; crush.
      have prune_height : height (prune_longest t) = h by crush.
      have [_ killer] := nat_find_spec _ classical_dec_pred (exists_min_size_of_height nonempty h).
      have {}killer := killer (prune_longest t) prune_balanced prune_height.
      change (min_size_of_height nonempty h ≤ size (prune_longest t)) in killer.
      have t_size : size t = min_size_of_height nonempty h by crush.
      lia.
    Qed.

    Lemma min_size_strict_increasing0 (nonempty : inhabited A) h :
      (min_size_of_height nonempty h < min_size_of_height nonempty (1 + h))%nat.
    Proof.
      rewrite Nat.lt_nge => bad.
      have [t t_spec] := exists_tree_of_height_of_min_size nonempty (1 + h).
      (* if we prune_longest t, then it will still have height h, but a _smaller_ size than
         min_size_of_height h! *)
      have t_nonnil : t ≠ Nil.
      { have [_ [t_height _]] := t_spec.
        move => heq; subst.
        by crush.
      }
      set t' := prune_longest t.
      have t'_height := prune_longest_height_eq nonempty t_nonnil t_spec.
      have t'_size : 1 + size t' = size t := prune_longest_size t_nonnil.
      have t'_balanced : Balanced t' by apply prune_longest_balanced; crush.
      apply (min_size_minimal' nonempty (t := t') (h := h)).
      - by crush.
      - unfold t'; crush.
      - have [_ [_ t_size]] := t_spec.
        lia.
    Qed.

    Lemma add_increasing_of_succ_gt (f : nat → nat) :
      (∀ n, f n < f (S n))%nat → ∀ n m, (0 < m)%nat → (f n < f (m + n))%nat.
    Proof.
      move => succ_inc.
      move => + m; induction m; [lia|].
      move => n _.
      destruct m; [exact: succ_inc|].
      transitivity (f (S m + n)); [|exact: succ_inc].
      apply IHm; lia.
    Qed.

    Lemma strict_increasing_of_succ_gt (f : nat → nat) :
      (∀ n, f n < f (S n))%nat → ∀ n m, (n < m)%nat → (f n < f m)%nat.
    Proof.
      move => succ_inc + m.
      induction m; [lia|].
      move => n Hlt.
      invert Hlt; [auto using succ_inc|].
      transitivity (f m); auto using IHm.
    Qed.

    Lemma min_size_strict_increasing (nonempty : inhabited A) {h1 h2} :
      (h1 < h2)%nat → (min_size_of_height nonempty h1 < min_size_of_height nonempty h2)%nat.
    Proof.
      apply strict_increasing_of_succ_gt.
      by apply min_size_strict_increasing0.
    Qed.
    Hint Rewrite min_size_0 min_size_1 : core.
    Hint Resolve min_size_0 min_size_1 : core.
    Hint Resolve min_size_strict_increasing0 min_size_strict_increasing : core.

    Lemma height_gt_one_nonzero_subtree (nonempty : inhabited A) (h : nat) {v l r}:
      (1 < h)%nat → size (Node v l r) = min_size_of_height nonempty h →
      l ≠ Nil ∨ r ≠ Nil.
    Proof.
      move => h_nonzero t_size.
      apply not_and_or => bad.
      destruct bad as [l_nil r_nil]; subst.
      simpl in t_size.
      have one_size := min_size_1 nonempty.
      have := min_size_strict_increasing nonempty h_nonzero.
      lia.
    Qed.

    Lemma balanced_uneven (nonempty : inhabited A) (h : nat) {v l r} :
      (1 < h)%nat →
      is_tree_of_height_size h (min_size_of_height nonempty h) (Node v l r) →
      height l ≠ height r.
    Proof.
      move => h_gt_0 t_spec bad.
      (* then we can prune either subtree and still get a tree of the same height *)
      have t_nonnil : (Node v l r) ≠ Nil by crush.
      have l_nonnil : l ≠ Nil.
      { move => l_nil; subst.
        simpl in bad.
        have [_ [t_size _]] := t_spec.
        rewrite (height_eq_zero_nil _ (Nat.eq_sym bad))/= in t_size.
        have := min_size_strict_increasing nonempty h_gt_0.
        have := min_size_1 nonempty.
        lia.
      }
      have r_nonnil : r ≠ Nil.
      {
        move => r_nil; subst.
        simpl in bad.
        by have := height_eq_zero_nil _ bad.
      }
      have prune_height := prune_longest_height_eq nonempty t_nonnil t_spec.
      have prune_eq := prune_longest_case_eq v bad l_nonnil r_nonnil.
      rewrite prune_eq in prune_height.
      rewrite /height -/height in prune_height.
      lia.
    Qed.

    Lemma child_of_min_size_is_min_size_l (nonempty : inhabited A) (h : nat) {v l r} :
      is_tree_of_height_size h (min_size_of_height nonempty h) (Node v l r) →
      size l = min_size_of_height nonempty (height l).
    Proof.
      move => t_spec.
      have [t_bal [t_height t_size]] := t_spec.
      apply Nat.le_antisymm.
      2: apply min_size_minimal; by invert t_bal.
      rewrite Nat.le_ngt => Hlt.
      have [l' l'_spec] := exists_tree_of_height_of_min_size nonempty (height l).
      (* consider now the smaller tree, Node v l' r *)
      have solver := min_size_minimal' nonempty.
      apply (solver h (Node v l' r)).
      -
        rewrite /is_tree_of_height_size in l'_spec.
        invert t_bal; by crush.
      -
        rewrite -t_height /height -/height .
        rewrite /is_tree_of_height_size in l'_spec.
        lia.
      -
        rewrite -t_size.
        rewrite /size -/size.
        suff : (size l' < size l)%nat by lia.
        have [_ [_ l'_size]] := l'_spec.
        by rewrite l'_size.
    Qed.

    Lemma child_of_min_size_is_min_size_r (nonempty : inhabited A) (h : nat) {v l r} :
      is_tree_of_height_size h (min_size_of_height nonempty h) (Node v l r) →
      size r = min_size_of_height nonempty (height r).
    Proof.
      move => t_spec.
      have [t_bal [t_height t_size]] := t_spec.
      apply Nat.le_antisymm.
      2: apply min_size_minimal; by invert t_bal.
      rewrite Nat.le_ngt => Hlt.
      have [r' r'_spec] := exists_tree_of_height_of_min_size nonempty (height r).
      (* consider now the smaller tree, Node v l' r *)
      have solver := min_size_minimal' nonempty.
      apply (solver h (Node v l r')).
      -
        rewrite /is_tree_of_height_size in r'_spec.
        invert t_bal; by crush.
      -
        rewrite -t_height /height -/height .
        rewrite /is_tree_of_height_size in r'_spec.
        lia.
      -
        rewrite -t_size.
        rewrite /size -/size.
        suff : (size r' < size r)%nat by lia.
        have [_ [_ r'_size]] := r'_spec.
        by rewrite r'_size.
    Qed.

    Fixpoint mincard n :=
      match n with
      | 0 => 0
      | 1 => 1
      | 2 => 2
      | S (S (S n) as p) => S (mincard n + mincard p)
      end.

    Lemma mincard_eqn n :
 mincard (S (S (S n))) = S (mincard n + mincard (2+n)).
Proof.
 reflexivity.
Qed.

Lemma mincard_incr n : (mincard n < mincard (S n))%nat.
Proof.
 induction n using lt_wf_ind.
 do 3 (destruct n; auto).
 rewrite 2! mincard_eqn.
 apply -> Nat.succ_lt_mono.
 apply Nat.add_lt_mono; eauto.
Qed.

Lemma mincard_lt_mono n m : (n < m -> mincard n < mincard m)%nat.
Proof.
 induction m; inversion_clear 1.
 - apply mincard_incr.
 - transitivity (mincard m); auto using mincard_incr.
Qed.

Lemma mincard_le_mono n m : n <= m -> mincard n <= mincard m.
Proof.
 induction 1; auto.
 transitivity (mincard m); auto using mincard_incr with arith.
Qed.

Lemma mincard_bound n m : m <= 2+n ->
 mincard (S m) <= S (mincard n + mincard m).
Proof.
 intros H.
 destruct m as [|[|m]].
 - simpl. auto with arith.
 - simpl. auto with arith.
 - rewrite mincard_eqn.
   apply -> Nat.succ_le_mono.
   apply Nat.add_le_mono; eauto.
   apply mincard_le_mono; lia.
Qed.

(** [mincard] has an exponential behavior *)

Lemma mincard_twice n : (2 * mincard n < mincard (2+n))%nat.
Proof.
 induction n as [n IH] using lt_wf_ind.
 do 3 (destruct n; [simpl; auto with arith|]).
 change (2 + S (S (S n))) with (S (S (S (2+n)))).
 rewrite 2! mincard_eqn.
 generalize (IH n) (IH (2+n)). lia.
Qed.

Lemma mincard_even n : n<>0 -> 2^n <= mincard (2*n).
Proof.
 induction n.
 - now destruct 1.
 - intros _.
   destruct (Nat.eq_dec n 0).
   * subst; simpl; auto.
   * rewrite Nat.pow_succ_r' Nat.mul_succ_r Nat.add_comm.
     transitivity (2 * mincard (2*n)).
     + apply Nat.mul_le_mono_l; auto.
     + apply Nat.lt_le_incl. apply mincard_twice.
Qed.

Lemma mincard_odd n : 2^n <= mincard (2*n+1).
Proof.
 destruct (Nat.eq_dec n 0).
 - subst; auto.
 - transitivity (mincard (2*n)).
   * now apply mincard_even.
   * apply mincard_le_mono. lia.
Qed.

Lemma mincard_log n : n <= 2 * Nat.log2 (mincard n) + 1.
Proof.
 rewrite (Nat.div2_odd n).
 set (m := Nat.div2 n); clearbody m.
 destruct (Nat.odd n); simpl Nat.b2n; rewrite ?Nat.add_0_r; clear n.
 + apply Nat.add_le_mono_r, Nat.mul_le_mono_l.
   apply Nat.log2_le_pow2.
   apply (mincard_lt_mono (n := 0)); auto with arith.
   apply mincard_odd.
 + destruct (Nat.eq_dec m 0); [subst; simpl; auto|].
   transitivity (2*Nat.log2 (mincard (2*m))); [|lia].
   apply Nat.mul_le_mono_l.
   apply Nat.log2_le_pow2.
   apply (mincard_lt_mono (n := 0)); lia.
   now apply mincard_even.
Qed.

Lemma mincard_le_size t :
  Balanced t → mincard (height t) ≤ size t.
  Proof.
    induction 1.
    - done.
    - rewrite /height -/height.
      destruct (Nat.max_spec (height l) (height r)) as [(U, ->)|(U, ->)].
      + rewrite -> mincard_bound.
        apply -> Nat.succ_le_mono.
        apply Nat.add_le_mono; eauto.
        lia.
      + rewrite -> mincard_bound.
        apply -> Nat.succ_le_mono.
        apply Nat.add_le_mono; eauto.
        fold size.
        by rewrite H1.
        lia.
    - rewrite /height -/height.
      destruct (Nat.max_spec (height l) (height r)) as [(U, ->)|(U, ->)].
      + rewrite -> mincard_bound.
        apply -> Nat.succ_le_mono.
        apply Nat.add_le_mono; eauto.
        lia.
      +
        rewrite -> mincard_bound.
        rewrite Nat.add_comm.
        apply -> Nat.succ_le_mono.
        apply Nat.add_le_mono; eauto.
        lia.
    - rewrite /height -/height; destruct (Nat.max_spec (height l) (height r)) as [(U, ->)|(U, ->)].
      +
        rewrite -> mincard_bound.
        apply -> Nat.succ_le_mono.
        apply Nat.add_le_mono; eauto.
        lia.
      + rewrite -> mincard_bound.
        apply -> Nat.succ_le_mono.
        apply Nat.add_le_mono; eauto.
        lia.
        lia.
    Qed.

  Lemma height_upperbound t :
    Balanced t → height t ≤ 2 * Nat.log2 (size t) + 1.
  Proof.
    intros.
    transitivity  (2 * Nat.log2 (mincard (height t)) + 1).
    apply mincard_log.
    apply Nat.add_le_mono_r, Nat.mul_le_mono_l, Nat.log2_le_mono.
    now apply mincard_le_size.
  Qed.

  Lemma height_lowerbound s : s<>Nil ->
  (Nat.log2 (size s) < height s)%nat.
  Proof.
  apply log2_size_lt_height.
  Qed.

  End MaxHeight.

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

