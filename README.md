# README

All work is done with Rocq v8.20.

This work is also being hosted at https://github.com/Dessertion/coq-bst

The filestructure is as follows:
- `AVL.v` contains most of the work.
- `Util.v` contains a few utilities -- why something is in `AVL.v` instead of `Util.v` is usually just sloppiness.
- `AVLHeightFacts.v` contains the development of logarithmic height for AVL trees.
- `AVLResults.v` contains all the key results.
- `AVL_incorrect.v` contains an older version of `AVL.v`, developed with incorrect rebalancing functions. It culminates in a proof that insertion still preserves AVL balance despite the incorrect definition.
- `avl.cc` an implementation of AVL trees, based on the implementation in `AVL.v`, which correctly solves the problem `ds4` on the online judge [DMOJ](https://dmoj.ca/problem/ds4). See this submission: https://dmoj.ca/submission/7120643

# COMPILATION

Just run `make`.

Note that this process takes 70s on my Ryzen 5 5600X, so expect it to take a while.
On another classmate's laptop, it took an entire 5 minutes.

