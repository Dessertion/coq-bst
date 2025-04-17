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



A case where the Inductive form of a predicate results in far better performance: 

During the proof of this Lemma:
```coq
  Lemma merge_In_complete_left x l r :
    In x l → In x (merge l r).
```
We arrive at this proof state: 
```coq-goals
1 goal (ID 10088)
  
  x : A
  r : tree
  v : A
  l : tree
  rv : A
  rl, rr : tree
  x_in_r' : In x (Node rv rl rr)
  x0 : A
  e : find_max (Node rv rl rr) = Some x0
  IHP0 : x0 = x ∨ In x (prune_max (Node rv rl rr))
  ============================
  x0 = x ∨ In x (Node v l (prune_max (Node rv rl rr)))
```
If we replace all the `In`s with their Inductive counterpart, `In'`, `eauto` is able to find the proof blazingly fast
(in fact, just `eauto 2` suffices): 
```coq
  time (rewrite <- In'_iff_In in *; destruct IHP0; by eauto 3).
```
```coq-response
Tactic call ran for 0.013 secs (0.013u,0.s) (success)

No more goals.
```
On the other hand, if we directly try attacking the goal at hand with just `eauto`, we fail to produce any results, 
even on very high depth numbers such as `eauto 10` -- this is because `eauto` doesn't know to Unfold the definition of `In` by itself.
If we give it some help by adding `Hint Unfold In : core`, it _can_ figure it out -- but it is far slower:
```coq
  time (destruct IHP0; by eauto)
```
```coq-response
Tactic call ran for 0.181 secs (0.181u,0.s) (success)

No more goals.
```
Indeed, we see that `eauto 5` is the smallest depth at which `eauto` success -- this is contrasted with the earlier
success at only `eauto 3`.
We can manually give it some help by adding a `simpl` call before `eauto`, which cuts the search depth requirement
from `eauto 5` to `eauto 4`: 
```coq
  time (destruct IHP0; simpl; eauto 4).
```
```coq-response
Tactic call ran for 0.048 secs (0.048u,0.s) (success)

No more goals.
```
But this is _still_ slower than what we had earlier, by a factor of 3!


`crush` is great for prototyping and saving thinking time on the part of the human, but it has a heavy price in terms of 
computation time. 
Here is an example of something where we originally made heavy use of `crush` in the initial proof, and came back later
to refine it with faster tactics. 
Original:
```coq
  Lemma rotate_right_preserves_Ordered v l r : Ordered (Node v l r) → Ordered (rotate_right v l r).
  Proof.
    rewrite !Ordered_iff_Ordered' /rotate_right.
    intros; destruct l; invert_ordered'; try by constructor.
    constructor; crush.
    apply (All_imp (fun x => v < x)); by crush.
  Qed.
```
New:
```coq
  Lemma rotate_right_preserves_Ordered v l r : Ordered (Node v l r) → Ordered (rotate_right v l r).
  Proof.
    rewrite !Ordered_iff_Ordered' /rotate_right.
    intros; destruct l; invert_ordered'; try by constructor.
    constructor; simpl'; eauto 2.
    apply (All_imp (fun x => v < x)); by eauto 2.
  Qed.
```

The line `constructor; crush` took 3.159s to run: 
```
Tactic call ran for 3.159 secs (3.152u,0.006s) (success)
```
In contrast, `constructor; simpl'; eauto 2` took only 0.273s to run:
```
Tactic call ran for 0.273 secs (0.273u,0.s) (success)
```

We took the proof for height from
https://people.csail.mit.edu/alinush/6.006-spring-2014/avl-height-proof.pdf
