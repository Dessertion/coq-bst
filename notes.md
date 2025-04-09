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

  Tactic call ran for 3.211 secs (3.197u,0.013s) (success)
