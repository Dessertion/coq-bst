- functional induction saves a lot of time over using just `crush` to brute force things;
  while `crush` is often powerful enough to just get the job done anyways, proof involving functional induction
  is more than 10x faster

-- eg., take this snippet
```coq
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
```

the line `split_ifs; invert Hbal; by crush` took 3.211 secs:
```
Tactic call ran for 3.211 secs (3.197u,0.013s) (success)
```

This was replaced by the following proof:
```coq
  Lemma balance_right_preserves_Balanced v l r : Balanced (Node v l r) → Balanced (balance_right v l r).
    Proof.
      move => Hbal.
      functional induction (balance_right v l r); simplify; eauto; invert Hbal; by crush.
    Qed.
```
In particular, the second line --- the bulk of the proof -- took only 0.316 secs to run:
```
Tactic call ran for 0.316 secs (0.312u,0.003s) (success)
```

To prove that `insert` preserved AVL `Balanced`, we needed a _very_ strong induction hypothesis.
This was the final one we settled with:
```coq
Lemma insert_preserves_Balanced0 x t :
  Balanced t →
  Balanced (insert x t) ∧
  height t ≤ height (insert x t) ∧
  (t ≠ Nil → 1 + height t = height (insert x t) → height (left_child (insert x t)) ≠ height (right_child (insert x t))).
```

An example of `Hint Rewrite` coming into play:
We've proven these two lemmas:
```coq
    Lemma rotate_left_preserves_size v l r : size (rotate_left v l r) = size (Node v l r).

    Lemma rotate_right_preserves_size v l r : size (rotate_right v l r) = size (Node v l r).
```
We now wish to prove this lemma:
```coq
    Lemma balance_left_preserves_size v l r : size (balance_left v l r) = size (Node v l r).
```
An initial thought would be to do something like this: 

```coq
    Lemma balance_left_preserves_size v l r : size (balance_left v l r) = size (Node v l r).
    Proof.
      functional induction (balance_left v l r); simplify; lia.
```
But this fails -- `lia` can't find a witness somehow. 
If we hedge our bets with `try lia` instead, we see that the proof is left in this state: 
```coq-goals
  v : A
  r : tree
  lv : A
  ll, lr : tree
  e : (S (height r) < S (Nat.max (height ll) (height lr)))%nat
  e1 : height ll ≤ height lr
  ============================
  size (rotate_right v (rotate_left lv ll lr) r) = S (S (size ll + size lr + size r))
```
But our previous two lemmas should be exactly sufficient to solve this!
Thus, simply adding `Hint Rewrite rotate_left_preserves_size rotate_right_preserves_size : core` lets `simplify`, well, simplify enough for `lia` to do the rest.

We may or may not have had a major bug with our balancing rotation _this entire time_; 
in fact, this "bugged" balance _still provably maintains balance_ for `insert`s.

However, it fails to balance properly during deletes.

