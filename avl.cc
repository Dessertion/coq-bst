#include <bits/stdc++.h>

struct Node {
  int val;
  Node *l = nullptr, *r = nullptr;
  int size = 1, height = 1;
  ~Node() {
    delete l, delete r;
  }
};

int size(Node* t) { return t? t->size : 0; }
int height(Node* t) { return t? t->height : 0; }

void update(Node* t) {
  if (!t) return;
  t->size = 1 + size(t->l) + size(t->r);
  t->height = 1 + std::max(height(t->l), height(t->r));
}

// rotate towards the left; assumes `t` nonnull.
void rotate_left(Node*& t) {
  Node* r = t->r;
  if (!r) return;
  t->r = r->l;
  r->l = t;
  update(t), update(r);
  std::swap(t, r);
}

void rotate_right(Node*& t) {
  Node* l = t->l;
  if (!l) return;
  t->l = l->r;
  l->r = t;
  update(t), update(l);
  std::swap(t, l);
}

// we suspect the left side is heavy and rebalance accordingly
void bal_left(Node*& t) {
  if (!t) return;
  if (1 + height(t->r) >= height(t->l)) return;
  if (height(t->l->r) <= height(t->l->l))
    rotate_right(t);
  else
    rotate_left(t->l), rotate_right(t);
}

void bal_right(Node*& t) {
  if (!t) return;
  if (1 + height(t->l) >= height(t->r)) return;
  if (height(t->r->l) <= height(t->r->r))
    rotate_left(t);
  else
    rotate_right(t->r), rotate_left(t);
}

void insert(Node*& t, int x) {
  if (!t) {
    t = new Node{x};
    return;
  }
  if (x < t->val)
    insert(t->l, x), bal_left(t);
  else
    insert(t->r, x), bal_right(t);
  update(t);
}

Node* prune_max(Node*& t) {
  if (!t) return nullptr;
  Node* ret = prune_max(t->r);
  if (ret) {
    bal_left(t), update(t);
    return ret;
  }
  else {
    ret = t;
    t = t->l;
    return ret;
  }
}

Node* merge(Node* l, Node* r) {
  Node* ret = prune_max(l);
  if (!ret) return r;
  ret->l = l, ret->r = r;
  bal_right(ret), update(ret);
  return ret;
}

void erase(Node*& t, int x) {
  if (!t) return;
  if (x == t->val) {
    auto kill = t;
    t = merge(t->l, t->r);
    kill->l = kill->r = nullptr;
    delete kill;
  }
  else if (x < t->val)
    erase(t->l, x), bal_right(t), update(t);
  else
    erase(t->r, x), bal_left(t), update(t);
}

// x is 1-indexed
// x is guaranteed to be within the size of the array
int select(Node* t, int x, int acc = 0) {
  if (acc + size(t->l) + 1 == x)
    return t->val;
  else if (acc + size(t->l) + 1 < x)
    return select(t->r, x, acc + size(t->l) + 1);
  else
    return select(t->l, x, acc);
}

// locate return a dummy value of `-1` if it could not find the key `x`
int locate(Node* t, int x, int acc = 0) {
  if (!t) return -1;
  if (x < t->val) return locate(t->l, x, acc);
  else if (x > t->val) return locate(t->r, x, acc + size(t->l) + 1);
  else {
    // we have found a node with value == x
    // we now need to look for the _first_ node such that this still holds
    int ret = locate(t->l, x, acc);
    if (ret == -1) // no smaller result found
      return acc + size(t->l) + 1;
    else
      return ret;
  }
}

void print_tree(Node* t) {
  if (!t) return;
  print_tree(t->l);
  std::cout << t->val << ' ';
  print_tree(t->r);
}

void pretty_print(Node* t) {
  if (!t) {
    std::cout << "() ";
    return;
  }
  std::cout << "( ";
  pretty_print(t->l);
  std::cout << t->val << " ";
  pretty_print(t->r);
  std::cout << ") ";
}

bool check_balance (Node* t) {
  if (!t) return true;
  auto hl = height(t->l), hr = height(t->r);
  if (not (-1 <= hl - hr && hl - hr <= 1)) {
    std :: cerr << "AAAAAAAAA: " << t->val << ", DIFF: " << hl - hr << std::endl;
    return false;
  }
  return
    check_balance(t->l) && check_balance(t->r);
}

int main() {
  std::cin.tie(nullptr);
  std::ios_base::sync_with_stdio(false);

  Node* tree = nullptr;

  int N, M;
  std::cin >> N >> M;

  for (int i = 0; i < N; ++i) {
    int a;
    std::cin >> a;
    insert(tree, a);
  }

  int last_answer = 0;
  for (int i = 0; i < M; ++i) {
    char cmd;
    int x;
    std::cin >> cmd >> x;
    x ^= last_answer;
    if (cmd == 'I') {
      insert(tree, x);
    }
    else if (cmd == 'R') {
      erase(tree, x);
    }
    else if (cmd == 'S') {
      int ret = select(tree, x);
      last_answer = ret;
      std::cout << ret << '\n';
    }
    else {
      int ret = locate(tree, x);
      last_answer = ret;
      std::cout << ret << '\n';
    }
  }
  // pretty_print(tree);
  assert(check_balance(tree));
  print_tree(tree);
  std::cout << '\n';
  delete tree;
}

// https://dmoj.ca/submission/7111201
// this is the correct AVL tree

// https://dmoj.ca/submission/7111202
// this is the incorrect AVL tree

// despite being incorrect, it _still_ passes DS4
