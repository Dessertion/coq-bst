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
