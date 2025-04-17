Require Import ssreflect Utf8 CpdtTactics Util FunInd FrapWithoutSets.
Require Import Arith Orders OrdersTac OrdersFacts.
Require Import AVLHeightFacts.

Module AVLFactsFull (OT : UsualOrderedType').
  Include AVLHeightFacts OT.

  (* an AVL tree is a BST which is AVL-balanced *)

  Inductive AVL t : Prop :=
  | AVL_intro : Ordered t → Balanced t → AVL t.
  Hint Constructors AVL : core.

  Lemma AVL_Ordered t :
    AVL t → Ordered t.
  Proof.
    by destruct 1.
  Qed.

  Lemma AVL_Ordered' t :
    AVL t → Ordered' t.
  Proof.
    destruct 1; by rewrite -Ordered_iff_Ordered'.
  Qed.

  Lemma AVL_Balanced t :
    AVL t → Balanced t.
  Proof.
    by destruct 1.
  Qed.

  Hint Resolve AVL_Ordered AVL_Ordered' AVL_Balanced : core.

  Lemma AVL_left v l r :
    AVL (Node v l r) → AVL l.
  Proof.
    constructor; by eauto.
  Qed.

  Lemma AVL_right v l r :
    AVL (Node v l r) → AVL r.
  Proof.
    constructor; by eauto.
  Qed.

  Hint Resolve AVL_left AVL_right : core.

  (* CONTAINS *)

  (* Contains behaves exactly like In in an AVL tree;
     so checking set membership is O(h), where h is the height of the tree *)
  Theorem AVL_In_iff_Contains t :
    AVL t → (∀ x, In x t ↔ Contains x t).
  Proof.
    move => [t_ord t_bal] x.
    by rewrite Ordered_In_iff_Contains.
  Qed.

  (* INSERTION *)

  (* an AVL tree remains an AVL tree after insertion *)
  Theorem AVL_insert x t :
    AVL t → AVL (insert x t).
  Proof.
    constructor; by eauto.
  Qed.

  (* insertion preserves all prior elements *)
  Theorem In_insert_of_In x y t :
    In x t → In x (insert y t).
  Proof.
    exact: insert_In_complete1.
  Qed.

  (* the inserted element is in the new tree *)
  Theorem In_insert x t :
    In x (insert x t).
  Proof.
    exact: insert_In_complete2.
  Qed.

  (* the only elements in `insert y t` are `y` and the elements in `t` *)
  Theorem eq_or_In_of_In_insert x y t :
    In x (insert y t) → x = y ∨ In x t.
  Proof.
    exact: insert_In_correct.
  Qed.

  Theorem In_insert_iff x y t :
    In x (insert y t) ↔ x = y ∨ In x t.
  Proof.
    split.
    - exact: eq_or_In_of_In_insert.
    - destruct 1; subst; by eauto using In_insert_of_In, In_insert.
  Qed.

  (* if an element is already present in an AVL tree, it is unchanged by insert *)
  Theorem AVL_insert_eq_of_In x t :
    AVL t → In x t → insert x t = t.
  Proof.
    move => avl.
    rewrite AVL_In_iff_Contains; [assumption|].
    apply insert_do_nothing; by eauto.
  Qed.

  (* AVL trees are idempotent under insert *)
  Theorem AVL_insert_idempotent x t :
    AVL t → insert x (insert x t) = insert x t.
  Proof.
    move => avl.
    apply insert_idempotent; by eauto.
  Qed.

  (* the tree size grows by 1 if x is not already present *)
  Theorem AVL_insert_size_of_not_In x t :
    AVL t → ¬ In x t → size (insert x t) = 1 + size t.
  Proof.
    move => avl x_not_in.
    apply insert_not_Contains_size.
    rewrite -AVL_In_iff_Contains; by eauto.
  Qed.

  (* the tree size stays the same if x is already present *)
  Theorem AVL_insert_size_of_In x t :
    AVL t → In x t → size (insert x t) = size t.
  Proof.
    move => avl x_in.
    apply insert_Contains_size.
    by rewrite -AVL_In_iff_Contains.
  Qed.

  (* DELETION *)

  (* an AVL tree remains an AVL tree after deletion *)
  Theorem AVL_delete x t :
    AVL t → AVL (delete x t).
  Proof.
    constructor; by eauto.
  Qed.

  (* the elements after deletion is a subset *)
  Theorem AVL_In_of_In_delete x y t :
    AVL t → In x (delete y t) → In x t ∧ x ≠ y.
  Proof.
    move => avl x_in.
    split; move: x_in.
    - exact: delete_subset.
    - apply: delete_In_correct; by eauto.
  Qed.

  (* the deleted element is not in the new tree *)
  Theorem AVL_not_In_delete x t :
    AVL t → ¬ In x (delete x t).
  Proof.
    move => avl bad.
    Search delete.
    suff : x ~= x by tauto.
    move: bad.
    eapply delete_In_correct; by eauto.
  Qed.

  (* if x was already In t, and x is not equal to the deleted element, then x is in the new tree *)
  Theorem AVL_In_delete_of_In_of_neq x y t :
    AVL t → In x t → x ≠ y → In x (delete y t).
  Proof.
    move => avl x_in neq.
    functional induction (delete y t); simpl'; eauto 2.
    - repeat_destruct x_in; subst; tauto.
    - repeat_destruct x_in; subst; try tauto.
      right; right; by eauto.
    - repeat_destruct x_in; subst; try tauto.
      right; left; by eauto.
  Qed.

  Theorem AVL_In_delete_iff x y t :
    AVL t → In x (delete y t) ↔ In x t ∧ x ≠ y.
  Proof.
    move => avl.
    split; [exact: AVL_In_of_In_delete|].
    move => [x_in neq].
    exact: AVL_In_delete_of_In_of_neq.
  Qed.

  (* if the element was not In the tree, then delete does nothing *)
  Theorem AVL_delete_eq_of_not_In x t :
    AVL t → ¬ In x t → delete x t = t.
  Proof.
    move => avl x_not_in.
    rewrite AVL_In_iff_Contains in x_not_in; [done|].
    apply delete_do_nothing; by eauto.
  Qed.

  (* AVL trees are idempotent under delete *)
  Theorem AVL_delete_idempotent x t :
    AVL t → delete x (delete x t) = delete x t.
  Proof.
    move => avl.
    apply delete_idempotent; by eauto.
  Qed.

  (* the tree size decreases by 1 if x is in, otherwise it stays the same *)
  Theorem AVL_delete_size_of_In x t :
    AVL t → In x t → 1 + size (delete x t) = size t.
  Proof.
    move => avl x_in.
    apply delete_Contains_size.
    by rewrite -AVL_In_iff_Contains.
  Qed.

  Theorem AVL_delete_size_of_not_In x t :
    AVL t → ¬ In x t → size (delete x t) = size t.
  Proof.
    move => avl x_in.
    apply delete_not_Contains_size.
    by rewrite -AVL_In_iff_Contains.
  Qed.

  (* LOGARITHMIC HEIGHT *)

  (* AVL trees have logarithmic height *)
  Theorem AVL_height_upperbound t :
    AVL t → height t ≤ 2 * Nat.log2 (size t) + 1.
  Proof.
    move => avl.
    apply height_upperbound; by eauto.
  Qed.
