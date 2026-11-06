/*
 * Treap - tree + heap
 *
 * I used a treap in the latest version of `vic`. In this short scratch file
 * we explore the concept of a treap; that is, how to create, add and remove
 * nodes while keeping their invariant conditions.
 *
 * What's the idea behind treaps? A traditional binary search tree may
 * degenerate into a linked list. In other words, if a binary search tree is
 * not balanced, the advantage of using it (i.e. O(log n) operations) is lost.
 * Treaps fix that by adding an additional parameter to the node, called
 * 'priority'. This parameter is used to enforce a max-heap condition; that is,
 * the priority of the parent node must be larger than the priority of its
 * child nodes. The particularity of this parameter is that it is randomly
 * assigned at the moment the node is created, so the shape of the tree does
 * not depend on the order in which the keys are inserted.
 *
 * Two parameters per node mean two invariant conditions to keep at the same
 * time: the binary search tree condition on the key, and the max-heap
 * condition on the priority. There are two equivalent ways of keeping both.
 * The classic one inserts the node as a leaf, traversing the tree with the
 * binary search tree rule, and then rotates the node upwards while its
 * priority is larger than the priority of its parent; the rotations stop when
 * the parent has a larger priority, or when the new node reaches the root.
 * Note that a rotation preserves the binary search tree condition, so only
 * the heap condition has to be repaired. The other way, the one used in this
 * file, builds every operation out of two primitives, split and merge.
 */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

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

void
freenode(struct node *n)
{
	if (n) {
		freenode(n->l);
		freenode(n->r);
		free(n);
	}
}

/*
 * search: plain binary search tree lookup; the priorities play no part.
 * Returns the node holding `key`, or NULL if there is none.
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
 * Both results keep the heap property, because split never changes which
 * node is above which: it only drops the edges that straddle `key`.
 */
void
split(struct node *n, int key, struct node **l, struct node **r)
{
	if (!n) {
		*l = NULL;
		*r = NULL;
		return;
	}
	if (n->key < key) {
		/* n and its whole left subtree belong to *l. */
		split(n->r, key, &n->r, r);
		*l = n;
	} else {
		/* n and its whole right subtree belong to *r. */
		split(n->l, key, l, &n->l);
		*r = n;
	}
}

/*
 * merge: join two treaps into one.  It assumes every key in `l` is
 * smaller than every key in `r`, so no comparison of keys is needed and
 * only the priorities decide the shape: the node with the larger
 * priority becomes the root.
 */
struct node *
merge(struct node *l, struct node *r)
{
	if (!l)
		return r;
	if (!r)
		return l;
	if (l->prior > r->prior) {
		l->r = merge(l->r, r);
		return l;
	}
	r->l = merge(l, r->l);
	return r;
}

/*
 * insert: split at `key`, then merge the three pieces back in order.
 * Duplicate keys are ignored, so the treap behaves as a set.
 * Returns the new root.
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
 * Erasing an absent key is a no-op.  Returns the new root.
 */
struct node *
erase(struct node *root, int key)
{
	struct node *t;

	if (!root)
		return NULL;
	if (key < root->key)
		root->l = erase(root->l, key);
	else if (key > root->key)
		root->r = erase(root->r, key);
	else {
		t = merge(root->l, root->r);
		free(root);
		return t;
	}
	return root;
}

void
inorder(struct node *n)
{
	if (n) {
		inorder(n->l);
		printf(" %d", n->key);
		inorder(n->r);
	}
}

/* dump: print the tree rotated 90 degrees, root at the left margin. */
void
dump(struct node *n, int depth)
{
	int i;

	if (!n)
		return;
	dump(n->r, depth + 1);
	for (i = 0; i < depth; i++)
		printf("    ");
	printf("%d (p=%d)\n", n->key, n->prior);
	dump(n->l, depth + 1);
}

int
main(void)
{
	struct node *root;
	int keys[] = {5, 3, 8, 1, 9, 7, 2, 6, 4};
	int i, n;

	srand(10349);
	root = NULL;
	n = sizeof keys / sizeof *keys;

	for (i = 0; i < n; i++)
		root = insert(root, keys[i]);

	printf("inorder:");
	inorder(root);
	printf("\n\nshape (right subtree on top):\n");
	dump(root, 0);

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
