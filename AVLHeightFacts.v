Require Import ssreflect FrapWithoutSets Utf8 CpdtTactics Util FunInd Psatz.
Require Import Classical ClassicalDescription IndefiniteDescription.
Require Import Arith Orders OrdersTac OrdersFacts.
Require Import AVL.

Set Implicit Arguments.
Close Scope string_scope.
Close Scope boolean_if_scope.
Open Scope general_if_scope.
Close Scope Z_scope.

Module AVLHeightFacts (OT : UsualOrderedType').
  Include AVL OT.
  Local Notation A := OT.t.

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

  Lemma min_size_strict_mono0 (nonempty : inhabited A) h :
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

  Lemma min_size_add_strict_mono nonempty n m :
    (0 < m → min_size_of_height nonempty n < min_size_of_height nonempty (m + n))%nat.
  Proof.
    have := min_size_strict_mono0; have := add_increasing_of_succ_gt; by auto.
  Qed.

  Lemma min_size_add_mono nonempty n m :
    (0 ≤ m → min_size_of_height nonempty n ≤ min_size_of_height nonempty (m + n))%nat.
  Proof.
    destruct (Nat.eq_dec m 0); [by subst|].
    have := min_size_add_strict_mono; by crush.
  Qed.

  Lemma min_size_strict_mono (nonempty : inhabited A) {h1 h2} :
    (h1 < h2)%nat → (min_size_of_height nonempty h1 < min_size_of_height nonempty h2)%nat.
  Proof.
    apply strict_increasing_of_succ_gt.
    by apply min_size_strict_mono0.
  Qed.
  Hint Rewrite min_size_0 min_size_1 : core.
  Hint Resolve min_size_0 min_size_1 : core.
  Hint Resolve min_size_strict_mono0 min_size_strict_mono : core.

  Lemma min_size_mono (nonempty : inhabited A) {h1 h2} :
    (h1 ≤ h2) → (min_size_of_height nonempty h1 ≤ min_size_of_height nonempty h2).
  Proof.
    move => Hle.
    Search "le" "lt" "eq" nat.
    About Nat.le_lteq.
    rewrite Nat.le_lteq in Hle.
    destruct Hle as [Hlt|]; [|by subst].
    apply Nat.lt_le_incl.
    by apply: min_size_strict_mono.
  Qed.

  Lemma height_gt_one_nonzero_subtree (nonempty : inhabited A) (h : nat) {v l r}:
    (1 < h)%nat → size (Node v l r) = min_size_of_height nonempty h →
    l ≠ Nil ∨ r ≠ Nil.
  Proof.
    move => h_nonzero t_size.
    apply not_and_or => bad.
    destruct bad as [l_nil r_nil]; subst.
    simpl in t_size.
    have one_size := min_size_1 nonempty.
    have := min_size_strict_mono nonempty h_nonzero.
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
      have := min_size_strict_mono nonempty h_gt_0.
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

  Lemma min_size_eqn (nonempty : inhabited A) (h : nat) :
    min_size_of_height nonempty (2 + h) =
      1 + min_size_of_height nonempty (1 + h)
        + min_size_of_height nonempty h.
  Proof.
    have one_lt : (1 < 2 + h)%nat by lia.
    have [t t_spec] := exists_tree_of_height_of_min_size nonempty (2 + h).
    destruct t as [|v l r]; [invert t_spec; crush|].
    have l_size := child_of_min_size_is_min_size_l nonempty t_spec.
    have r_size := child_of_min_size_is_min_size_r nonempty t_spec.
    have [t_bal [t_height t_size]] := t_spec.
    invert t_bal.
    - exfalso.
      by have := balanced_uneven nonempty one_lt t_spec.
    - have l_height : height l = 1 + h by rewrite /height -/height in t_height; lia.
      have r_height : height r = h by lia.
      rewrite -{1}l_height -{2}r_height.
      by rewrite -t_size -l_size -r_size.
    - have r_height : height r = 1 + h by rewrite /height -/height in t_height; lia.
      have l_height : height l = h by lia.
      rewrite -{1}r_height -{2}l_height.
      rewrite -t_size -l_size -r_size /size -/size; lia.
  Qed.

  Fixpoint min_size' n :=
    match n with
    | 0 => 0
    | 1 => 1
    | S (S n as p) => S (min_size' p + min_size' n)
    end.

  Lemma min_size_eq_min_size' (nonempty : inhabited A) n :
    min_size_of_height nonempty n = min_size' n.
  Proof.
    induction n using lt_wf_ind.
    do 2 (destruct n; auto).
    rewrite min_size_eqn.
    by do 2 (rewrite H; auto).
  Qed.

  Lemma min_size'_eqn n :
    min_size' (S (S n)) = S (min_size' (S n) + min_size' n).
  Proof.
    reflexivity.
  Qed.

  Lemma min_size_bound (nonempty : inhabited A) n m :
    m ≤ 1 + n →
    min_size_of_height nonempty (1 +  m) ≤ 1 + min_size_of_height nonempty n + min_size_of_height nonempty m.
  Proof.
    move => Hle.
    destruct m as [|[|m]].
    - simpl; rewrite min_size_0 min_size_1; lia.
    - simpl; rewrite min_size_eqn !min_size_1 min_size_0; lia.
    - rewrite min_size_eqn.
      suff : (min_size_of_height nonempty (1 + m) ≤ min_size_of_height nonempty n)%nat.
      move => H; ring_simplify; apply Nat.add_le_mono; lia.
      apply min_size_mono; lia.
  Qed.

  Lemma min_size_twice (nonempty : inhabited A) n :
    (2 * n < min_size_of_height nonempty (2 + n))%nat.
  Proof.
    induction n as [n IH] using lt_wf_ind.
    do 2 (destruct n; [simpl; rewrite ?min_size_eqn ?min_size_1 ?min_size0; lia|]).
    change (2 + S (S n)) with (S (S (2 + n))).
    rewrite 2!min_size_eqn.
    have := IH (S n); have := IH n; simpl; lia.
  Qed.

  Lemma min_size_even nonempty n :
    n ≠ 0 -> 2 ^ n ≤ min_size_of_height nonempty (2 * n).
  Proof.
    induction n; [by crush|].
    move => _.
    destruct (Nat.eq_dec n 0).
    - subst; simplify.
      rewrite min_size_eqn; by autorewrite with core.
    - transitivity (2 * min_size_of_height nonempty (2 * n)).
      crush.
      replace (2 * S n) with (S (S (2 * n))) by lia.
      rewrite min_size_eqn.
      suff : min_size_of_height nonempty (2 * n) ≤ min_size_of_height nonempty (1 + 2 * n) by lia.
      have := min_size_mono; by auto.
  Qed.

  Lemma min_size_odd nonempty n :
    2 ^ n ≤ min_size_of_height nonempty (2 * n + 1).
  Proof.
    destruct (Nat.eq_dec n 0);
      [subst; by autorewrite with core|].
    have := min_size_even; by crush.
  Qed.

  Lemma min_size_log nonempty n :
    n ≤ 2 * Nat.log2 (min_size_of_height nonempty n) + 1.
  Proof.
    rewrite (Nat.div2_odd n).
    set (m := Nat.div2 n); clearbody m.
    destruct (Nat.odd n); simpl Nat.b2n; rewrite ?Nat.add_0_r; clear n.
    - suff : m ≤ Nat.log2 (min_size_of_height nonempty (2 * m + 1)) by lia.
      apply Nat.log2_le_pow2.
      + rewrite -{1}min_size_0.
        apply min_size_strict_mono; lia.
      + by apply min_size_odd.
    - suff : m ≤ Nat.log2 (min_size_of_height nonempty (2 * m)) by lia.
      destruct (Nat.eq_dec m 0); [lia|].
      apply Nat.log2_le_pow2.
      + rewrite -{1}min_size_0.
        apply min_size_strict_mono; lia.
      + by apply min_size_even.
  Qed.

  Lemma height_upperbound0 (nonempty : inhabited A) t :
    Balanced t → height t ≤ 2 * Nat.log2 (size t) + 1.
  Proof.
    move => t_bal.
    transitivity (2 * Nat.log2 (min_size_of_height nonempty (height t)) + 1).
    by apply min_size_log.
    suff : Nat.log2 (min_size_of_height nonempty (height t)) ≤ Nat.log2 (size t) by lia.
    apply Nat.log2_le_mono.
    by apply min_size_minimal.
  Qed.

  Lemma height_upperbound t :
    Balanced t → height t ≤ 2 * Nat.log2 (size t) + 1.
  Proof.
    destruct t; [by crush|].
    have nonempty : inhabited A by constructor.
    by apply height_upperbound0.
  Qed.

End AVLHeightFacts.
