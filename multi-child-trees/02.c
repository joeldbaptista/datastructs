#include <stdio.h>
#include <stdlib.h>

/*
A B+ tree stores every record in a leaf. The internal nodes hold no
records at all: their keys are separators used only to route a search
downward, and each separator is a copy of a key that also lives in a
leaf. The leaves are chained left to right, so a range of keys is read by
finding one leaf and then following the chain.

HOW THIS DIFFERS FROM THE B-TREE IN 01.c

1. Two node kinds. An internal node has n keys and n+1 children. A leaf
   has n keys paired with n values, no children, and a next pointer.

2. Search never stops early. In 01.c a key found in an internal node was
   the record itself, so the descent could stop there. Here a separator
   equal to x is not a record, so every search runs the full root-to-leaf
   path. That costs more comparisons, but it makes every lookup the same
   depth and it is what lets the leaves be scanned.

3. Two split rules, and the difference between them matters:
   - a full leaf splits and COPIES the smallest key of its new right half
     up as the separator. The record itself stays in the leaf;
   - a full internal node splits and PUSHES its median key up. The key
     leaves the node, exactly as in 01.c.

4. Deletion never swaps with a predecessor. In 01.c a key held by an
   internal node had to be exchanged with a leaf key first. Here records
   are already only in leaves, so there is nothing to swap.

5. Merging two leaves DISCARDS the separator above them instead of
   pulling it down, because that separator is only a copy. Merging two
   internal nodes still pulls the separator down.

THE ROUTING INVARIANT, AND WHY SEPARATORS GO STALE

A separator keys[i] satisfies

	every key in the subtree of children[i]    <  keys[i], and
	every key in the subtree of children[i+1] >=  keys[i]

so the subtree of children[i] covers a half-open range, bounded below by
keys[i-1] and above by keys[i].

Right after a leaf split, keys[i] equals the smallest key in the subtree
of children[i+1]. But that equality does not survive deletion: deleting
that smallest record from its leaf leaves the separator naming a key that
no longer exists. The separator is still a correct bound, so routing
still works, and no repair is performed. The demo at the bottom counts
these stale separators to show that they are normal rather than
corruption.

ORDER is the maximum number of children of an internal node. Define it on
the compiler command line to pick another order.

Inserting a key that is already present overwrites its value.
*/

#ifndef ORDER
#define ORDER 4
#endif

enum {
	MAXCHILDREN = ORDER,
	MAXKEYS = ORDER - 1,

	/* fewest keys a non-root internal node may hold */
	MINKEYS = (ORDER + 1) / 2 - 1,

	/* fewest records a non-root leaf may hold */
	MINRECS = (MAXKEYS + 1) / 2,

	/* index of the key pushed up when an internal node splits */
	SPLITMID = MAXKEYS / 2,

	/* number of records left behind when a leaf splits */
	LEAFSPLIT = MINRECS
};

/*
One struct serves both node kinds, so that the leaf flag is the only
thing distinguishing them. A real implementation would use two structs,
or a union, because a leaf wastes the children array while an internal
node wastes vals and next.
*/
struct node {
	int leaf;                           /* 1 for a leaf, 0 for internal */
	size_t n;                           /* keys, or records in a leaf */
	int keys[MAXKEYS];
	int vals[MAXKEYS];                  /* leaves only */
	struct node *children[MAXCHILDREN]; /* internal nodes only */
	struct node *next;                  /* leaves only: the next leaf */
};

struct node *
mknode(int leaf, size_t n)
{
	struct node *t;
	size_t k;

	/* assumption: there's always enough mem */
	t = malloc(sizeof *t);

	t->leaf = leaf;
	t->n = n > MAXKEYS? MAXKEYS:n;
	for (k = 0; k < MAXKEYS; ++k) {
		t->keys[k] = 0;
		t->vals[k] = 0;
	}
	for (k = 0; k < MAXCHILDREN; ++k)
		t->children[k] = NULL;
	t->next = NULL;
	return t;
}

/* freetree follows children only. Following next as well would visit
 * every leaf twice. */
void
freetree(struct node *t)
{
	size_t k;

	if (t == NULL)
		return;
	if (!t->leaf)
		for (k = 0; k <= t->n; ++k)
			freetree(t->children[k]);
	free(t);
}

/*
childslot returns the index of the child whose subtree may hold x. Since
keys[i] is a lower bound on the subtree of children[i+1], x belongs there
as soon as x >= keys[i]. Note the >= : in 01.c the test was > , because
there an equal key was the record itself.
*/
static size_t
childslot(struct node *t, int x)
{
	size_t i;

	i = 0;
	while (i < t->n && x >= t->keys[i])
		++i;
	return i;
}

/* recslot returns the number of records in the leaf t with key below x */
static size_t
recslot(struct node *t, int x)
{
	size_t i;

	i = 0;
	while (i < t->n && x > t->keys[i])
		++i;
	return i;
}

/* leaffor descends from t to the one leaf whose range covers x */
static struct node *
leaffor(struct node *t, int x)
{
	while (t && !t->leaf)
		t = t->children[childslot(t, x)];
	return t;
}

/*
search returns the leaf holding x, the index of x within it through pos,
and its value through val. It returns NULL when x is absent. Either out
parameter may be NULL.
*/
struct node *
search(struct node *t, int x, size_t *pos, int *val)
{
	struct node *l;
	size_t i;

	l = leaffor(t, x);
	if (l == NULL)
		return NULL;
	i = recslot(l, x);
	if (i < l->n && l->keys[i] == x) {
		if (pos)
			*pos = i;
		if (val)
			*val = l->vals[i];
		return l;
	}
	return NULL;
}

/* ------------------------------------------------------------------ *
 * Insertion
 * ------------------------------------------------------------------ */

/* putrec inserts the record (x, v) at index i of the leaf t, which has room */
static void
putrec(struct node *t, size_t i, int x, int v)
{
	size_t j;

	for (j = t->n; j > i; --j) {
		t->keys[j] = t->keys[j-1];
		t->vals[j] = t->vals[j-1];
	}
	t->keys[i] = x;
	t->vals[i] = v;
	++t->n;
}

/*
putsep inserts separator k at index i of the internal node t, and child c
at index i+1. t has room.
*/
static void
putsep(struct node *t, size_t i, int k, struct node *c)
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
splitleaf handles a full leaf that must still take (x, v) at index i.
LEAFSPLIT records stay behind and the rest move to a new leaf, which is
spliced into the chain after t. The smallest key of that new leaf is
COPIED up through pkey, and it remains a record in the new leaf.
*/
static void
splitleaf(struct node *t, size_t i, int x, int v,
	int *pkey, struct node **pright)
{
	int tk[MAXKEYS + 1], tv[MAXKEYS + 1];
	struct node *r;
	size_t j;

	for (j = 0; j < MAXKEYS; ++j) {
		tk[j] = t->keys[j];
		tv[j] = t->vals[j];
	}
	for (j = MAXKEYS; j > i; --j) {
		tk[j] = tk[j-1];
		tv[j] = tv[j-1];
	}
	tk[i] = x;
	tv[i] = v;

	r = mknode(1, MAXKEYS + 1 - LEAFSPLIT);
	for (j = 0; j < r->n; ++j) {
		r->keys[j] = tk[LEAFSPLIT + j];
		r->vals[j] = tv[LEAFSPLIT + j];
	}
	r->next = t->next;

	t->n = LEAFSPLIT;
	for (j = 0; j < LEAFSPLIT; ++j) {
		t->keys[j] = tk[j];
		t->vals[j] = tv[j];
	}
	for (j = LEAFSPLIT; j < MAXKEYS; ++j) {
		t->keys[j] = 0;
		t->vals[j] = 0;
	}
	t->next = r;

	*pkey = r->keys[0]; /* copied up, and still a record in r */
	*pright = r;
}

/*
splitinternal handles a full internal node that must still take separator
k at index i and child c at index i+1. The key at SPLITMID is PUSHED up,
so it leaves this level entirely.
*/
static void
splitinternal(struct node *t, size_t i, int k, struct node *c,
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

	r = mknode(0, MAXKEYS - SPLITMID);
	for (j = 0; j < r->n; ++j)
		r->keys[j] = tk[SPLITMID + 1 + j];
	for (j = 0; j <= r->n; ++j)
		r->children[j] = tc[SPLITMID + 1 + j];

	t->n = SPLITMID;
	for (j = 0; j < SPLITMID; ++j)
		t->keys[j] = tk[j];
	for (j = SPLITMID; j < MAXKEYS; ++j)
		t->keys[j] = 0;
	for (j = 0; j <= SPLITMID; ++j)
		t->children[j] = tc[j];
	for (j = SPLITMID + 1; j < MAXCHILDREN; ++j)
		t->children[j] = NULL;

	*pkey = tk[SPLITMID]; /* pushed up, and gone from this node */
	*pright = r;
}

/*
ins inserts (x, v) into the subtree t. It returns 0 when the subtree
absorbed the record, and 1 when t split, in which case the separator for
the parent comes back through pkey and the new right sibling through
pright.
*/
static int
ins(struct node *t, int x, int v, int *pkey, struct node **pright)
{
	size_t i;
	int k;
	struct node *c;

	if (t->leaf) {
		i = recslot(t, x);
		if (i < t->n && t->keys[i] == x) {
			t->vals[i] = v; /* already present, so update */
			return 0;
		}
		if (t->n < MAXKEYS) {
			putrec(t, i, x, v);
			return 0;
		}
		splitleaf(t, i, x, v, pkey, pright);
		return 1;
	}

	i = childslot(t, x);
	if (!ins(t->children[i], x, v, &k, &c))
		return 0;

	/* the child split, so (k, c) must land in this node */
	if (t->n < MAXKEYS) {
		putsep(t, i, k, c);
		return 0;
	}
	splitinternal(t, i, k, c, pkey, pright);
	return 1;
}

/* insert returns the root, which changes when the root splits */
struct node *
insert(struct node *t, int x, int v)
{
	struct node *root, *right;
	int k;

	if (t == NULL) {
		root = mknode(1, 1);
		root->keys[0] = x;
		root->vals[0] = v;
		return root;
	}
	if (!ins(t, x, v, &k, &right))
		return t;

	/* the root split, so a new internal root sits above both halves */
	root = mknode(0, 1);
	root->keys[0] = k;
	root->children[0] = t;
	root->children[1] = right;
	return root;
}

/* ------------------------------------------------------------------ *
 * Deletion
 *
 * The record always sits in a leaf, so removal is direct. A non-root leaf
 * left with fewer than MINRECS records, or a non-root internal node left
 * with fewer than MINKEYS keys, has underflowed and is repaired either by
 * borrowing from an adjacent sibling or by merging with one. Both repairs
 * differ between the two node kinds, which is why there are two repair
 * functions below.
 * ------------------------------------------------------------------ */

/* rmkey removes keys[i] from an internal node, leaving its children alone */
static void
rmkey(struct node *t, size_t i)
{
	size_t j;

	for (j = i; j + 1 < t->n; ++j)
		t->keys[j] = t->keys[j+1];
	--t->n;
	t->keys[t->n] = 0;
}

/* rmrec removes the record at index i of a leaf */
static void
rmrec(struct node *t, size_t i)
{
	size_t j;

	for (j = i; j + 1 < t->n; ++j) {
		t->keys[j] = t->keys[j+1];
		t->vals[j] = t->vals[j+1];
	}
	--t->n;
	t->keys[t->n] = 0;
	t->vals[t->n] = 0;
}

/*
mergeleaves joins the leaves children[j] and children[j+1] of t. The
separator t->keys[j] is discarded rather than pulled down, because it is
only a copy of a key that still lives in a leaf. It returns 1 if t
underflows.
*/
static int
mergeleaves(struct node *t, size_t j)
{
	struct node *a, *b;
	size_t k;

	a = t->children[j];
	b = t->children[j+1];

	/* one leaf holds MINRECS-1 records and the other MINRECS, so the
	 * total is at most MAXKEYS and b appends to a without overflow */
	for (k = 0; k < b->n; ++k) {
		a->keys[a->n] = b->keys[k];
		a->vals[a->n] = b->vals[k];
		++a->n;
	}
	a->next = b->next; /* keep the chain intact */
	free(b);

	for (k = j + 1; k < t->n; ++k)
		t->children[k] = t->children[k+1];
	rmkey(t, j);
	t->children[t->n + 1] = NULL;

	return t->n < MINKEYS;
}

/*
mergeinternal joins the internal nodes children[j] and children[j+1] of
t, pulling the separator t->keys[j] DOWN to sit between them, because at
this level the separator is the only copy of that boundary.
*/
static int
mergeinternal(struct node *t, size_t j)
{
	struct node *a, *b;
	size_t k, an;

	a = t->children[j];
	b = t->children[j+1];

	/* the two hold 2*MINKEYS-1 keys between them, plus the separator,
	 * which is at most MAXKEYS for every ORDER */
	an = a->n;
	a->keys[an] = t->keys[j];
	for (k = 0; k < b->n; ++k)
		a->keys[an + 1 + k] = b->keys[k];
	for (k = 0; k <= b->n; ++k)
		a->children[an + 1 + k] = b->children[k];
	a->n = an + 1 + b->n;
	free(b);

	for (k = j + 1; k < t->n; ++k)
		t->children[k] = t->children[k+1];
	rmkey(t, j);
	t->children[t->n + 1] = NULL;

	return t->n < MINKEYS;
}

/* fixleaf repairs t->children[i], a leaf short of records */
static int
fixleaf(struct node *t, size_t i)
{
	struct node *c, *s;
	size_t j;

	c = t->children[i];

	/* 1. the left leaf lends its largest record */
	if (i > 0 && t->children[i-1]->n > MINRECS) {
		s = t->children[i-1];
		for (j = c->n; j > 0; --j) {
			c->keys[j] = c->keys[j-1];
			c->vals[j] = c->vals[j-1];
		}
		c->keys[0] = s->keys[s->n - 1];
		c->vals[0] = s->vals[s->n - 1];
		++c->n;
		rmrec(s, s->n - 1);
		/* the separator is the lower bound of c, which just changed */
		t->keys[i-1] = c->keys[0];
		return 0;
	}
	/* 2. the right leaf lends its smallest record */
	if (i < t->n && t->children[i+1]->n > MINRECS) {
		s = t->children[i+1];
		c->keys[c->n] = s->keys[0];
		c->vals[c->n] = s->vals[0];
		++c->n;
		rmrec(s, 0);
		/* the separator is the lower bound of s, which just changed */
		t->keys[i] = s->keys[0];
		return 0;
	}
	/* 3. neither leaf can lend, so merge with one */
	return mergeleaves(t, i > 0? i - 1 : 0);
}

/* fixinternal repairs t->children[i], an internal node short of keys */
static int
fixinternal(struct node *t, size_t i)
{
	struct node *c, *s;
	size_t j;

	c = t->children[i];

	/* 1. rotate a key in from the left sibling, through the separator */
	if (i > 0 && t->children[i-1]->n > MINKEYS) {
		s = t->children[i-1];
		for (j = c->n; j > 0; --j)
			c->keys[j] = c->keys[j-1];
		for (j = c->n + 1; j > 0; --j)
			c->children[j] = c->children[j-1];
		c->keys[0] = t->keys[i-1];
		c->children[0] = s->children[s->n];
		++c->n;
		t->keys[i-1] = s->keys[s->n - 1];
		s->children[s->n] = NULL;
		rmkey(s, s->n - 1);
		return 0;
	}
	/* 2. rotate a key in from the right sibling, through the separator */
	if (i < t->n && t->children[i+1]->n > MINKEYS) {
		s = t->children[i+1];
		c->keys[c->n] = t->keys[i];
		c->children[c->n + 1] = s->children[0];
		++c->n;
		t->keys[i] = s->keys[0];
		for (j = 0; j < s->n; ++j)
			s->children[j] = s->children[j+1];
		s->children[s->n] = NULL;
		rmkey(s, 0);
		return 0;
	}
	/* 3. neither sibling can lend, so merge with one */
	return mergeinternal(t, i > 0? i - 1 : 0);
}

static int
fixchild(struct node *t, size_t i)
{
	return t->children[i]->leaf? fixleaf(t, i) : fixinternal(t, i);
}

/* del removes x from the subtree t, returning 1 if t underflowed */
static int
del(struct node *t, int x)
{
	size_t i;

	if (t->leaf) {
		i = recslot(t, x);
		if (i == t->n || t->keys[i] != x)
			return 0; /* x is not in the tree */
		rmrec(t, i);
		return t->n < MINRECS;
	}
	i = childslot(t, x);
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

	/*
	The underflow flag is ignored here, because the root is exempt from
	both minimums. Only an empty root matters.
	*/
	del(t, x);
	if (t->n > 0)
		return t;
	if (t->leaf) {
		free(t); /* the last record is gone, so the tree is empty */
		return NULL;
	}
	root = t->children[0]; /* the root's only child takes over */
	free(t);
	return root;
}

/* ------------------------------------------------------------------ *
 * Scanning
 *
 * This is what the leaf chain buys. A range query costs one descent to
 * find the first leaf, then a walk along the chain. No part of the
 * internal structure is touched again, and the records come out in key
 * order with no recursion and no backtracking.
 * ------------------------------------------------------------------ */

struct node *
firstleaf(struct node *t)
{
	while (t && !t->leaf)
		t = t->children[0];
	return t;
}

/* scanall visits every record in ascending key order along the chain */
void
scanall(struct node *t, void (*visit)(int, int))
{
	struct node *l;
	size_t i;

	for (l = firstleaf(t); l; l = l->next)
		for (i = 0; i < l->n; ++i)
			visit(l->keys[i], l->vals[i]);
}

/* rangescan visits every record whose key lies in [lo, hi] */
void
rangescan(struct node *t, int lo, int hi, void (*visit)(int, int))
{
	struct node *l;
	size_t i;

	l = leaffor(t, lo);
	if (l == NULL)
		return;
	i = recslot(l, lo);
	while (l) {
		while (i < l->n) {
			if (l->keys[i] > hi)
				return;
			visit(l->keys[i], l->vals[i]);
			++i;
		}
		l = l->next;
		i = 0;
	}
}

/* ------------------------------------------------------------------ *
 * Inspection
 * ------------------------------------------------------------------ */

/* dump prints internal separators as [...] and leaf records as {k:v ...} */
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
	if (t->leaf) {
		printf("{");
		for (i = 0; i < t->n; ++i)
			printf("%s%d:%d", i? " ":"", t->keys[i], t->vals[i]);
		printf("}\n");
		return;
	}
	printf("[");
	for (i = 0; i < t->n; ++i)
		printf("%s%d", i? " ":"", t->keys[i]);
	printf("]\n");
	for (i = 0; i <= t->n; ++i)
		dump(t->children[i], depth + 1);
}

/*
checknode verifies every invariant of the subtree t and returns its
height, or -1 if any invariant fails. The bounds are half-open: every key
in the subtree must satisfy *lo <= key < *hi, and a NULL bound means
unbounded on that side. isroot marks the one node exempt from the
minimums.
*/
static int
checknode(struct node *t, int isroot, const int *lo, const int *hi)
{
	const int *l, *r;
	size_t i;
	int h, hc;

	if (t == NULL)
		return 0;
	if (t->n < 1 || t->n > MAXKEYS)
		return -1;
	for (i = 1; i < t->n; ++i)
		if (t->keys[i-1] >= t->keys[i])
			return -1;
	if (lo && t->keys[0] < *lo)
		return -1;
	if (hi && t->keys[t->n - 1] >= *hi)
		return -1;

	if (t->leaf) {
		if (!isroot && t->n < MINRECS)
			return -1;
		for (i = 0; i < MAXCHILDREN; ++i)
			if (t->children[i])
				return -1;
		return 1;
	}

	if (!isroot && t->n < MINKEYS)
		return -1;
	if (t->next)
		return -1; /* only leaves belong to the chain */
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
		hc = checknode(t->children[i], 0, l, r);
		if (hc < 0)
			return -1;
		if (h < 0)
			h = hc;
		else if (h != hc)
			return -1; /* leaves at unequal depth */
	}
	return h + 1;
}

/* checktree returns the height of t, or -1 if t is not a valid B+ tree */
int
checktree(struct node *t)
{
	return checknode(t, 1, NULL, NULL);
}

static size_t
countrecs(struct node *t)
{
	size_t i, c;

	if (t == NULL)
		return 0;
	if (t->leaf)
		return t->n;
	c = 0;
	for (i = 0; i <= t->n; ++i)
		c += countrecs(t->children[i]);
	return c;
}

/*
checkchain verifies that the leaf chain reaches every leaf exactly once,
in ascending key order, and ends at NULL. It returns 1 on success. This
is a separate invariant from checktree, because the chain is redundant
structure: the tree can be shaped correctly while the chain is broken.
*/
int
checkchain(struct node *t)
{
	struct node *l;
	size_t i, seen;
	int prev, first;

	seen = 0;
	first = 1;
	prev = 0;
	for (l = firstleaf(t); l; l = l->next) {
		if (!l->leaf)
			return 0;
		for (i = 0; i < l->n; ++i) {
			if (!first && prev >= l->keys[i])
				return 0;
			prev = l->keys[i];
			first = 0;
			++seen;
		}
	}
	return seen == countrecs(t);
}

/*
staleseps counts the separators that no longer match any record. They are
expected after deletions and are harmless, since a separator only has to
bound the subtrees on either side of it.
*/
int
staleseps(struct node *root, struct node *t)
{
	size_t i;
	int c;

	if (t == NULL || t->leaf)
		return 0;
	c = 0;
	for (i = 0; i < t->n; ++i)
		if (search(root, t->keys[i], NULL, NULL) == NULL)
			++c;
	for (i = 0; i <= t->n; ++i)
		c += staleseps(root, t->children[i]);
	return c;
}

/* ------------------------------------------------------------------ *
 * Demonstration
 * ------------------------------------------------------------------ */

static void
printrec(int k, int v)
{
	printf("%d:%d ", k, v);
}

static void
report(struct node *t, const char *what)
{
	int stale = staleseps(t, t);

	printf("--- %s (height %d, chain %s, %d stale separator%s)\n",
		what, checktree(t), checkchain(t)? "ok":"BROKEN",
		stale, stale == 1? "":"s");
	dump(t, 0);
	printf("chain: ");
	scanall(t, printrec);
	printf("\n\n");
}

int main(void)
{
	static const int xs[] = {
		50, 30, 70, 10, 40, 60, 80, 20, 35, 45, 55, 65, 75, 85, 5
	};
	struct node *t;
	size_t i, pos;
	int v;

	printf("ORDER %d: internal nodes hold %d..%d keys, "
		"leaves hold %d..%d records\n",
		ORDER, MINKEYS, MAXKEYS, MINRECS, MAXKEYS);
	printf("          an internal split pushes up key index %d of %d; "
		"a leaf split copies up and leaves %d behind\n\n",
		SPLITMID, MAXKEYS + 1, LEAFSPLIT);

	/* the value is ten times the key, to make the mapping visible */
	t = NULL;
	for (i = 0; i < sizeof xs / sizeof xs[0]; ++i) {
		t = insert(t, xs[i], xs[i] * 10);
		printf("after inserting %2d: height %d\n", xs[i], checktree(t));
	}
	printf("\n");
	report(t, "built");

	/* a separator may equal a key, yet the record is still in a leaf */
	for (i = 0; i < 3; ++i) {
		pos = 0;
		v = 0;
		search(t, xs[i], &pos, &v);
		printf("search %2d: value %d, at index %zu of its leaf\n",
			xs[i], v, pos);
	}
	printf("search 99: %s\n\n", search(t, 99, NULL, NULL)? "found":"absent");

	/* the range query that the leaf chain exists for */
	printf("range [33, 66]: ");
	rangescan(t, 33, 66, printrec);
	printf("\n");
	printf("range [1, 12]:  ");
	rangescan(t, 1, 12, printrec);
	printf("\n\n");

	/* re-inserting a key must replace its value, not add a record */
	t = insert(t, 40, 4444);
	v = 0;
	search(t, 40, NULL, &v);
	printf("after re-inserting 40: value %d, height %d, chain %s\n\n",
		v, checktree(t), checkchain(t)? "ok":"BROKEN");

	/* deleting 50 empties its leaf below MINRECS, so a repair runs and
	 * the separator naming 50 disappears with it */
	t = delete(t, 50);
	report(t, "after deleting 50, which forced a leaf repair");

	/* 40 is a separator in the root, and its leaf has a record to
	 * spare, so no repair runs and the separator is left naming a key
	 * that no longer exists. Routing still works, so it is not fixed. */
	t = delete(t, 40);
	report(t, "after deleting 40, leaving its separator stale");

	t = delete(t, 5);
	report(t, "after deleting 5");

	/* empty the tree, watching the height shrink */
	for (i = 0; i < sizeof xs / sizeof xs[0]; ++i) {
		t = delete(t, xs[i]);
		printf("after deleting %2d: height %d, chain %s\n",
			xs[i], checktree(t), checkchain(t)? "ok":"BROKEN");
	}
	printf("\n");
	report(t, "emptied");

	freetree(t);
	return 0;
}
