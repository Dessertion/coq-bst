Require Import ssreflect Utf8 CpdtTactics ZArith Psatz FrapWithoutSets.

Require Import Classical.
Require Export ConstructiveEpsilon.

Set Implicit Arguments.

Section find.
Variable (P : nat → Prop).
Hypothesis P_decidable : forall n, {P n} + {¬ P n}.
Variable (H : ∃ n, P n).

Local Definition lbp (m n : nat) : Prop :=
  m = n + 1 ∧ ∀ k, k ≤ n → ¬ P k.

Print well_founded.
Lemma wf_lbp : well_founded lbp.
  unfold well_founded.
  destruct H as [n Pn].
  have : ∀ m k, n ≤ k + m → Acc lbp k.
  { induction m.
    - move => k n_le_k.
      rewrite Nat.add_0_r in n_le_k.
      constructor.
      move => y [y_def Hy].
      exfalso.
      have {}Hy := Hy n n_le_k.
      done.
    - move => k n_le_k.
      constructor.
      move => y [y_def Hy].
      apply IHm.
      lia.
  }
  move => hyp a.
  have h : ∀ k, n ≤ k + n by lia.
  have {}hyp := hyp n _ (h _).
  apply hyp.
Qed.

Definition nat_findX : {n | P n ∧ ∀ m, m < n → ¬ P m}.
  have rec := well_founded_induction_type wf_lbp.
  pose p k := (∀ n, n < k → ¬ P n) → {n | P n ∧ ∀ m, m < n → ¬ P m}.
  specialize (rec p).
  refine (rec _ 0 (fun _ h => _)).
  - refine (fun m IH al => _).
    refine (match P_decidable m with
          | left Pm => exist _ m (conj Pm al)
          | right Pm => _
            end).
    have this : ∀ n, n ≤ m → ¬ P n.
    { move => n h.
      destruct (le_lt_eq_dec _ _ h) as [|e].
      - by apply al.
      - by destruct e.
    }
    apply: IH _ (conj eq_refl this) _.
    move => n h.
    apply this.
    apply Nat.lt_succ_r.
    by rewrite -Nat.add_1_r.
  - exfalso; apply: Nat.nlt_0_r _ h.
Qed.

Definition nat_find : nat :=
  (proj1_sig nat_findX).

Theorem nat_find_eq : proj1_sig nat_findX = nat_find.
  reflexivity.
Qed.

Theorem nat_find_spec : P (nat_find).
  exact: proj1 (proj2_sig nat_findX).
Qed.

Theorem nat_find_min : ∀ m, m < nat_find → ¬ P m.
  exact: proj2 (proj2_sig nat_findX).
Qed.

Theorem nat_find_min' {m} (h : P m) : nat_find ≤ m.
Proof.
  rewrite Nat.le_ngt.
  move => bad; exact: nat_find_min _ bad h.
Qed.

Lemma nat_find_eq_iff {m} : nat_find = m ↔ P m ∧ ∀ n, n < m → ¬ P n.
Proof.
  split.
  - intros [].
    by auto using nat_find_spec, nat_find_min.
  - intros [hm hlt].
    Print Nat.le_antisymm.
    apply: Nat.le_antisymm _ _ (nat_find_min' hm) _.
    rewrite Nat.le_ngt => bad.
    by apply: hlt _ bad (nat_find_spec).
Qed.



End find.

Lemma eq_or_succ_cases {a b} : a ≤ b → b ≤ 1 + a → b = a ∨ b = 1 + a.
Proof.
  lia.
Qed.

Ltac lia' := simplify; try lia.
