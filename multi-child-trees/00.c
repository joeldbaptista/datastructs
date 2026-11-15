#include <stdio.h>
#include <stdlib.h>

/*
A 2-3 tree is a tree where every internal (non-leaf) node has either two
or three children, and every leaf sits at the same depth. That equal-depth
property is the balance guarantee, so search, insert and delete are all
O(log n) in the worst case.

A node holding n keys has exactly n+1 children. So:

- a 2-node holds one key  (keys[0])            and two children;
- a 3-node holds two keys (keys[0] < keys[1])  and three children.

Search in a 3-node, given keys[0] < keys[1]:

1. If x <  keys[0], go to children[0];
2. If x >  keys[0] and x < keys[1], go to children[1];
3. If x >  keys[1], go to children[2].

Search in a 2-node, which holds only keys[0]:

1. If x <  keys[0], go to children[0];
2. If x >  keys[0], go to children[1].

A 2-node is locally binary, but the tree as a whole is not a binary tree:
2-nodes and 3-nodes may be mixed freely at any level.

This implementation stores no duplicate keys.
*/

enum {
	MAXKEYS = 2,
	MAXCHILDREN = MAXKEYS + 1
};

struct node {
	size_t n; /* number of keys; 1 or 2 in a live node */
	int keys[MAXKEYS];
	struct node *children[MAXCHILDREN];
};

struct node *
mknode(size_t n)
{
	struct node *t;
	size_t k;

	/* assumption: there's always enough mem */
	t = malloc(sizeof *t);

	t->n = n > MAXKEYS? MAXKEYS:n;
	for (k = 0; k < MAXKEYS; ++k)
		t->keys[k] = 0;
	for (k = 0; k < MAXCHILDREN; ++k)
		t->children[k] = NULL;
	return t;
}

void
freetree(struct node *t)
{
	size_t k;

	if (t) {
		/* a node with n keys has n+1 children */
		for (k = 0; k <= t->n; ++k)
			freetree(t->children[k]);
		free(t);
	}
}

/*
A leaf has no children at all. Because every leaf is at the same depth,
testing children[0] is enough: a node either has all its n+1 children or
none of them.
*/
static int
isleaf(struct node *t)
{
	return t->children[0] == NULL;
}

/*
slot returns the number of keys in t that are smaller than x. So it is
both the index where x would sit among the keys, and the index of the
child to descend into when x is absent from t.
*/
static size_t
slot(struct node *t, int x)
{
	size_t i;

	i = 0;
	while (i < t->n && x > t->keys[i])
		++i;
	return i;
}

/*
search returns the node holding x, and writes the index of x within that
node through pos. It returns NULL when x is absent. pos may be NULL.
*/
struct node *
search(struct node *t, int x, size_t *pos)
{
	size_t i;

	while (t) {
		i = slot(t, x);
		if (i < t->n && x == t->keys[i]) {
			if (pos)
				*pos = i;
			return t;
		}
		if (isleaf(t))
			return NULL;
		t = t->children[i];
	}
	return NULL;
}

/* ------------------------------------------------------------------ *
 * Insertion
 *
 * Insertion always happens at a leaf. If that leaf has room, the key
 * just goes in. If the leaf is already a 3-node, it has no room, so the
 * node splits: of the three keys involved, the median moves up to the
 * parent and the other two become two separate nodes. The parent may be
 * full in turn, so the split can propagate upward.
 *
 * If the split reaches the root, a new root is made holding the single
 * promoted key. That is the only way the tree gains height, and it adds
 * a level above every leaf at once, which is exactly why all leaves stay
 * at the same depth.
 * ------------------------------------------------------------------ */

/*
insertat puts key k at index i of t, and child c at index i+1, assuming
t has room. For a leaf, c is NULL and the child shuffling is a no-op.
*/
static void
insertat(struct node *t, size_t i, int k, struct node *c)
{
	size_t j;

	for (j = t->n; j > i; --j)
		t->keys[j] = t->keys[j-1];
	t->keys[i] = k;
	for (j = t->n + 1; j > i + 1; --j)
		t->children[j] = t->children[j-1];
	t->children[i+1] = c;
	++t->n;
}

/*
splitnode handles the full case. t already holds MAXKEYS keys, and key k
with child c still have to go in, at index i and i+1. Widening t by one
slot gives three keys and four children; the median key tk[1] is promoted
through pkey, the low key stays in t, and the high key moves to a fresh
node returned through pright.
*/
static void
splitnode(struct node *t, size_t i, int k, struct node *c,
	int *pkey, struct node **pright)
{
	int tk[MAXKEYS + 1];
	struct node *tc[MAXCHILDREN + 1];
	struct node *r;
	size_t j;

	for (j = 0; j < MAXKEYS; ++j)
		tk[j] = t->keys[j];
	for (j = 0; j < MAXCHILDREN; ++j)
		tc[j] = t->children[j];

	for (j = MAXKEYS; j > i; --j)
		tk[j] = tk[j-1];
	tk[i] = k;
	for (j = MAXCHILDREN; j > i + 1; --j)
		tc[j] = tc[j-1];
	tc[i+1] = c;

	r = mknode(1);
	r->keys[0] = tk[2];
	r->children[0] = tc[2];
	r->children[1] = tc[3];

	t->n = 1;
	t->keys[0] = tk[0];
	t->keys[1] = 0;
	t->children[0] = tc[0];
	t->children[1] = tc[1];
	t->children[2] = NULL;

	*pkey = tk[1];
	*pright = r;
}

/*
ins inserts x into the subtree t. It returns 0 when the subtree absorbed
x without changing shape, and 1 when t split, in which case the promoted
key comes back through pkey and the new right sibling through pright.
*/
static int
ins(struct node *t, int x, int *pkey, struct node **pright)
{
	size_t i;
	int k;
	struct node *c;

	i = slot(t, x);
	if (i < t->n && x == t->keys[i])
		return 0; /* already present */

	if (isleaf(t)) {
		if (t->n < MAXKEYS) {
			insertat(t, i, x, NULL);
			return 0;
		}
		splitnode(t, i, x, NULL, pkey, pright);
		return 1;
	}

	if (!ins(t->children[i], x, &k, &c))
		return 0;

	/* the child split, so (k, c) must land in this node */
	if (t->n < MAXKEYS) {
		insertat(t, i, k, c);
		return 0;
	}
	splitnode(t, i, k, c, pkey, pright);
	return 1;
}

/* insert returns the root of the tree, which changes when the root splits */
struct node *
insert(struct node *t, int x)
{
	struct node *root, *right;
	int k;

	if (t == NULL) {
		root = mknode(1);
		root->keys[0] = x;
		return root;
	}
	if (!ins(t, x, &k, &right))
		return t;

	/* the root split, so the tree grows upward by one level */
	root = mknode(1);
	root->keys[0] = k;
	root->children[0] = t;
	root->children[1] = right;
	return root;
}

/* ------------------------------------------------------------------ *
 * Deletion
 *
 * Deletion always happens at a leaf too. A key found in an internal node
 * is first swapped with its in-order predecessor, which always lives in
 * a leaf, and that leaf copy is the one removed.
 *
 * Removing a key from a 2-node leaf leaves it with no keys, which is an
 * underflow. Two repairs exist, and they are mutually exclusive:
 *
 * 1. redistribute: an adjacent sibling that is a 3-node lends a key,
 *    rotating it through the parent's separator key;
 * 2. merge: when no adjacent sibling can lend, the empty node and a
 *    sibling are joined, pulling the parent's separator key down between
 *    them. The parent loses a key, so it may underflow in turn and the
 *    repair propagates upward.
 *
 * If the root underflows, its only child becomes the new root and the
 * tree loses a level, again across every leaf at once.
 * ------------------------------------------------------------------ */

/* rmkey removes keys[i] from t without touching its children */
static void
rmkey(struct node *t, size_t i)
{
	size_t j;

	for (j = i; j + 1 < t->n; ++j)
		t->keys[j] = t->keys[j+1];
	--t->n;
	t->keys[t->n] = 0;
}

/*
mergechildren joins children[j] and children[j+1] of t, with t->keys[j]
pulled down to sit between them. One of the two children holds no keys
and the other holds one, so the merged node holds exactly MAXKEYS keys
and MAXCHILDREN children. It returns 1 if t itself now underflows.
*/
static int
mergechildren(struct node *t, size_t j)
{
	struct node *a, *b;
	int tk[MAXKEYS];
	struct node *tc[MAXCHILDREN];
	size_t k, nk, nc;

	a = t->children[j];
	b = t->children[j+1];

	nk = 0;
	nc = 0;
	for (k = 0; k < a->n; ++k)
		tk[nk++] = a->keys[k];
	tk[nk++] = t->keys[j];
	for (k = 0; k < b->n; ++k)
		tk[nk++] = b->keys[k];
	for (k = 0; k <= a->n; ++k)
		tc[nc++] = a->children[k];
	for (k = 0; k <= b->n; ++k)
		tc[nc++] = b->children[k];

	a->n = nk;
	for (k = 0; k < nk; ++k)
		a->keys[k] = tk[k];
	for (k = 0; k < nc; ++k)
		a->children[k] = tc[k];
	for (k = nc; k < MAXCHILDREN; ++k)
		a->children[k] = NULL;
	free(b);

	/* t loses the separator key and the right half of the merged pair */
	for (k = j + 1; k < t->n; ++k)
		t->children[k] = t->children[k+1];
	rmkey(t, j);
	t->children[t->n + 1] = NULL;

	return t->n == 0;
}

/*
fixchild repairs t->children[i], which holds no keys. It returns 1 if the
repair cost t its last key, pushing the underflow one level up.
*/
static int
fixchild(struct node *t, size_t i)
{
	struct node *c, *s;

	c = t->children[i];

	/* 1. a left sibling that is a 3-node can lend its largest key */
	if (i > 0 && t->children[i-1]->n == MAXKEYS) {
		s = t->children[i-1];
		c->children[1] = c->children[0];
		c->children[0] = s->children[s->n];
		c->keys[0] = t->keys[i-1];
		c->n = 1;
		t->keys[i-1] = s->keys[s->n - 1];
		s->children[s->n] = NULL;
		rmkey(s, s->n - 1);
		return 0;
	}
	/* 2. a right sibling that is a 3-node can lend its smallest key */
	if (i < t->n && t->children[i+1]->n == MAXKEYS) {
		s = t->children[i+1];
		c->children[1] = s->children[0];
		c->keys[0] = t->keys[i];
		c->n = 1;
		t->keys[i] = s->keys[0];
		s->children[0] = s->children[1];
		s->children[1] = s->children[2];
		s->children[2] = NULL;
		rmkey(s, 0);
		return 0;
	}
	/* 3. neither sibling can lend, so merge with one of them */
	return mergechildren(t, i > 0? i - 1 : 0);
}

/* delmax removes the largest key of t, returning it through pmax */
static int
delmax(struct node *t, int *pmax)
{
	if (isleaf(t)) {
		*pmax = t->keys[t->n - 1];
		rmkey(t, t->n - 1);
		return t->n == 0;
	}
	if (delmax(t->children[t->n], pmax))
		return fixchild(t, t->n);
	return 0;
}

/* del removes x from the subtree t, returning 1 if t underflowed */
static int
del(struct node *t, int x)
{
	size_t i;
	int m;

	i = slot(t, x);

	if (isleaf(t)) {
		if (i == t->n || x != t->keys[i])
			return 0; /* x is not in the tree */
		rmkey(t, i);
		return t->n == 0;
	}
	if (i < t->n && x == t->keys[i]) {
		/* swap x with its in-order predecessor, which is the largest
		 * key of the subtree to its left, and delete that instead */
		if (delmax(t->children[i], &m)) {
			t->keys[i] = m;
			return fixchild(t, i);
		}
		t->keys[i] = m;
		return 0;
	}
	if (del(t->children[i], x))
		return fixchild(t, i);
	return 0;
}

/* delete returns the root, which changes when the tree loses a level */
struct node *
delete(struct node *t, int x)
{
	struct node *root;

	if (t == NULL)
		return NULL;
	if (del(t, x)) {
		/* the root lost its last key, so its only child takes over.
		 * That child is NULL when the root was a leaf, i.e. when the
		 * tree is now empty. */
		root = t->children[0];
		free(t);
		return root;
	}
	return t;
}

/* ------------------------------------------------------------------ *
 * Traversal and inspection
 * ------------------------------------------------------------------ */

/*
inorder visits every key in ascending order: subtree, key, subtree, key,
subtree. A 3-node therefore interleaves two keys with three subtrees.
*/
void
inorder(struct node *t, void (*visit)(int))
{
	size_t i;

	if (t == NULL)
		return;
	for (i = 0; i < t->n; ++i) {
		if (!isleaf(t))
			inorder(t->children[i], visit);
		visit(t->keys[i]);
	}
	if (!isleaf(t))
		inorder(t->children[t->n], visit);
}

/* dump prints the shape of the tree, one node per line, indented by depth */
void
dump(struct node *t, int depth)
{
	size_t i;
	int j;

	if (t == NULL) {
		printf("(empty)\n");
		return;
	}
	for (j = 0; j < depth; ++j)
		printf("    ");
	printf("[");
	for (i = 0; i < t->n; ++i)
		printf("%s%d", i? " ":"", t->keys[i]);
	printf("]\n");
	if (!isleaf(t))
		for (i = 0; i <= t->n; ++i)
			dump(t->children[i], depth + 1);
}

/*
checknode verifies every invariant of the subtree t and returns its
height, or -1 if any invariant fails. lo and hi bound the keys the
subtree may contain; a NULL bound means unbounded on that side.
*/
static int
checknode(struct node *t, const int *lo, const int *hi)
{
	const int *l, *r;
	size_t i;
	int h, hc;

	if (t == NULL)
		return 0;
	if (t->n < 1 || t->n > MAXKEYS)
		return -1;
	if (t->n == MAXKEYS && t->keys[0] >= t->keys[1])
		return -1;
	if (lo && t->keys[0] <= *lo)
		return -1;
	if (hi && t->keys[t->n - 1] >= *hi)
		return -1;

	if (isleaf(t)) {
		for (i = 0; i < MAXCHILDREN; ++i)
			if (t->children[i])
				return -1;
		return 1;
	}
	for (i = 0; i <= t->n; ++i)
		if (t->children[i] == NULL)
			return -1;
	for (i = t->n + 1; i < MAXCHILDREN; ++i)
		if (t->children[i])
			return -1;

	h = -1;
	for (i = 0; i <= t->n; ++i) {
		l = (i == 0)? lo : &t->keys[i-1];
		r = (i == t->n)? hi : &t->keys[i];
		hc = checknode(t->children[i], l, r);
		if (hc < 0)
			return -1;
		if (h < 0)
			h = hc;
		else if (h != hc)
			return -1; /* leaves at unequal depth */
	}
	return h + 1;
}

/* checktree returns the height of t, or -1 if t is not a valid 2-3 tree */
int
checktree(struct node *t)
{
	return checknode(t, NULL, NULL);
}

/* ------------------------------------------------------------------ *
 * Demonstration
 * ------------------------------------------------------------------ */

static void
printkey(int x)
{
	printf("%d ", x);
}

static void
report(struct node *t, const char *what)
{
	printf("--- %s (height %d)\n", what, checktree(t));
	dump(t, 0);
	printf("in order: ");
	inorder(t, printkey);
	printf("\n\n");
}

int main(void)
{
	static const int xs[] = {
		50, 30, 70, 10, 40, 60, 80, 20, 35, 45, 55, 65, 75, 85, 5
	};
	struct node *t;
	size_t i, pos;

	/* watch the height grow: each jump is a split reaching the root */
	t = NULL;
	for (i = 0; i < sizeof xs / sizeof xs[0]; ++i) {
		t = insert(t, xs[i]);
		printf("after inserting %2d: height %d\n", xs[i], checktree(t));
	}
	printf("\n");
	report(t, "built");

	/* three search hits and one miss */
	for (i = 0; i < 3; ++i) {
		pos = 0;
		search(t, xs[i], &pos);
		printf("search %2d: found at key index %zu of its node\n",
			xs[i], pos);
	}
	printf("search 99: %s\n\n", search(t, 99, NULL)? "found":"absent");

	t = delete(t, 5);
	report(t, "after deleting 5 (a leaf key)");

	t = delete(t, 50);
	report(t, "after deleting 50 (an internal key)");

	/* empty the tree, watching the height shrink */
	for (i = 0; i < sizeof xs / sizeof xs[0]; ++i) {
		t = delete(t, xs[i]);
		printf("after deleting %2d: height %d\n", xs[i], checktree(t));
	}
	printf("\n");
	report(t, "emptied");

	freetree(t);
	return 0;
}
