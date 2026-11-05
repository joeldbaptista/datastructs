#include <stdio.h>
#include <stdlib.h>
#include <time.h>

/*
 * 01.c: the treap of 00.c with every recursive function rewritten as a
 * loop.  The data structure and the printed results are identical; only
 * the control flow differs.  Three techniques replace the recursion:
 * - a pointer to the link that must be filled in (struct node **), which
 *   carries the "where does my result go" part of a recursive call
 *   without a stack frame; used by split, merge and erase;
 * - repeated rotation, which flattens the tree as it is consumed; used
 *   by freenode;
 * - temporary threads, which borrow the empty child pointers to remember
 *   the way back up; used by inorder (a Morris traversal).
 * This list covers every function that was recursive, except dump, which
 * still needs an explicit stack because it has to know the depth of each
 * node at the moment it prints it.
 */

struct node {
	struct node *l, *r;
	int key, prior;
};

struct node *
mknode(int key)
{
	struct node *n;

	/* assumption: there's always enough mem */
	n = malloc(sizeof *n);
	n->l = NULL;
	n->r = NULL;
	n->key = key;
	n->prior = rand() % 1234;
	return n;
}

/*
 * freenode: free the whole treap without a stack.  While the current
 * root has a left child, rotate that child up; this strictly shortens
 * the left spine.  Otherwise the root has no left child, so it can be
 * freed and replaced by its right child.  Each step either rotates or
 * frees, so the loop ends after O(n) steps.
 *
 * The rotation is the usual right rotation, which moves the left child
 * up and the old root down to the right:
 *
 *          n                       t
 *         / \                     / \
 *        t   C      ------>      A   n
 *       / \                         / \
 *      A   B                       B   C
 *
 *      t = n->l                A = t->l   B = t->r   C = n->r
 *
 * The four assignments in the loop body perform it:
 *      t = n->l;       remember the left child, which moves up
 *      n->l = t->r;    B changes parent: it is now n's left subtree
 *      t->r = n;       n becomes t's right child
 *      n = t;          t is the new root
 *
 * The in-order sequence is the same on both sides, A t B n C, so the
 * binary search tree property survives the rotation.  The heap property
 * on `prior` does not, but that does not matter here, because the tree
 * is being destroyed.
 *
 * Rotating makes the left subtree of the root strictly smaller: it was
 * the whole subtree of t, and afterwards it is only A.  So a rotation
 * cannot repeat forever, and the node reached when the left child is
 * finally NULL is freed.
 */
void
freenode(struct node *n)
{
	struct node *t;

	while (n) {
		if (n->l) {
			t = n->l;	/* rotate right */
			n->l = t->r;
			t->r = n;
			n = t;
		} else {
			t = n->r;
			free(n);
			n = t;
		}
	}
}

/*
 * search: plain binary search tree lookup; the priorities play no part.
 * Returns the node holding `key`, or NULL if there is none.
 * It was already a loop in 00.c, so it is unchanged.
 */
struct node *
search(struct node *n, int key)
{
	while (n && n->key != key)
		n = key < n->key ? n->l : n->r;
	/* n == NULL || n->key == key */
	return n;
}

/*
 * split: cut the treap rooted at `n` into two treaps by `key`.
 * - *l receives every node with a key strictly less than `key`;
 * - *r receives every node with a key greater than or equal to `key`.
 * `pl` and `pr` always hold the address of the link that the next node
 * taken for the left, respectively the right, result must be written to.
 * The recursive version passed that address down as a parameter instead.
 */
void
split(struct node *n, int key, struct node **l, struct node **r)
{
	struct node **pl, **pr;

	pl = l;
	pr = r;
	while (n) {
		if (n->key < key) {
			/* n and its whole left subtree belong to *l. */
			*pl = n;
			pl = &n->r;
			n = n->r;
		} else {
			/* n and its whole right subtree belong to *r. */
			*pr = n;
			pr = &n->l;
			n = n->l;
		}
	}
	*pl = NULL;
	*pr = NULL;
}

/*
 * merge: join two treaps into one.  It assumes every key in `l` is
 * smaller than every key in `r`, so no comparison of keys is needed and
 * only the priorities decide the shape: the node with the larger
 * priority becomes the root.
 * `slot` holds the address of the link awaiting the merge of whatever is
 * left of the two inputs; when one input runs out, the other is hung
 * there whole.
 */
struct node *
merge(struct node *l, struct node *r)
{
	struct node *root, **slot;

	slot = &root;
	while (l && r) {
		if (l->prior > r->prior) {
			*slot = l;
			slot = &l->r;
			l = l->r;
		} else {
			*slot = r;
			slot = &r->l;
			r = r->l;
		}
	}
	*slot = l ? l : r;
	return root;
}

/*
 * insert: split at `key`, then merge the three pieces back in order.
 * Duplicate keys are ignored, so the treap behaves as a set.
 * Returns the new root.  The code is the same as in 00.c; it is
 * iterative here because split and merge are.
 */
struct node *
insert(struct node *root, int key)
{
	struct node *n, *l, *r;

	if (search(root, key))
		return root;
	n = mknode(key);
	split(root, key, &l, &r);
	return merge(merge(l, n), r);
}

/*
 * erase: descend to the node holding `key`, then replace it by the merge
 * of its two children and free it.  Merging is legal there because all
 * left-subtree keys are below all right-subtree keys.
 * The walk holds the address of the link that points at the current
 * node, so the replacement can be written through it without returning
 * up a call chain; `&root` is that link for the root itself.
 * Erasing an absent key is a no-op.  Returns the new root.
 */
struct node *
erase(struct node *root, int key)
{
	struct node **slot, *n;

	slot = &root;
	while ((n = *slot) && n->key != key)
		slot = key < n->key ? &n->l : &n->r;
	/* n == NULL || n->key == key */
	if (n) {
		*slot = merge(n->l, n->r);
		free(n);
	}
	return root;
}

/*
 * inorder: a Morris traversal.  Before descending into a left subtree,
 * make the rightmost node of that subtree point back at the current
 * node, so the traversal can climb again without a stack.  Meeting that
 * thread a second time means the left subtree is done: remove the
 * thread, print, and go right.  The tree is restored by the time the
 * loop ends.
 */
void
inorder(struct node *n)
{
	struct node *p;

	while (n) {
		if (!n->l) {
			printf(" %d", n->key);
			n = n->r;
			continue;
		}
		p = n->l;
		while (p->r && p->r != n)
			p = p->r;
		if (!p->r) {
			p->r = n;	/* lay the thread down */
			n = n->l;
		} else {
			p->r = NULL;	/* take the thread back up */
			printf(" %d", n->key);
			n = n->r;
		}
	}
}

/* A stack entry for dump: a node together with its depth. */
struct frame {
	struct node *n;
	int depth;
};

/* push: append one frame, doubling the array when it is full. */
void
push(struct frame **st, int *cap, int *top, struct node *n, int depth)
{
	if (*top == *cap) {
		*cap *= 2;
		/* assumption: there's always enough mem */
		*st = realloc(*st, *cap * sizeof **st);
	}
	(*st)[*top].n = n;
	(*st)[*top].depth = depth;
	(*top)++;
}

/*
 * dump: print the tree rotated 90 degrees, root at the left margin.
 * This is the recursion of 00.c with the call stack made explicit:
 * descend the right spine pushing each node, then pop, print, and turn
 * left.  The depth travels inside the stack entry.
 */
void
dump(struct node *root)
{
	struct frame *st;
	struct node *n;
	int cap, top, depth, i;

	cap = 16;
	top = 0;
	/* assumption: there's always enough mem */
	st = malloc(cap * sizeof *st);
	n = root;
	depth = 0;
	for (;;) {
		while (n) {
			push(&st, &cap, &top, n, depth);
			n = n->r;
			depth++;
		}
		if (!top)
			break;
		top--;
		n = st[top].n;
		depth = st[top].depth;
		for (i = 0; i < depth; i++)
			printf("    ");
		printf("%d (p=%d)\n", n->key, n->prior);
		n = n->l;
		depth++;
	}
	free(st);
}

int
main(void)
{
	struct node *root;
	int keys[] = {5, 3, 8, 1, 9, 7, 2, 6, 4};
	int i, n;

	srand(29420349);
	root = NULL;
	n = sizeof keys / sizeof *keys;

	for (i = 0; i < n; i++)
		root = insert(root, keys[i]);

	printf("inorder:");
	inorder(root);
	printf("\n\nshape (right subtree on top):\n");
	dump(root);

	printf("\nsearch 7: %s\n", search(root, 7) ? "found" : "absent");
	printf("search 42: %s\n", search(root, 42) ? "found" : "absent");

	root = erase(root, 1);
	root = erase(root, 5);
	root = erase(root, 42);	/* absent, so nothing happens */
	printf("\nafter erasing 1, 5, 42:");
	inorder(root);
	printf("\n");

	freenode(root);
	return 0;
}
