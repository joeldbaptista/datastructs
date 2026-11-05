#include <stdio.h>
#include <stdlib.h>

struct node {
	int key;
	struct node *left, *right;
};

struct node *
mknode(int key)
{
	struct node *n;

	n = malloc(sizeof *n);
	n->key = key;
	n->left = NULL;
	n->right = NULL;
	return n;
}

void
freetree(struct node *t)
{
	if (t) {
		freetree(t->left);
		freetree(t->right);
		free(t);
	}
}

void
_printtree(struct node *t, int level)
{
	int k;

	if (t) {
		_printtree(t->right, level+1);
		putchar('|');
		for (k = 0; k < (level == 1? level: 3*level); ++k)		
			putchar('-');
		printf(" %d (%d)", t->key, level);
		putchar('\n');
		_printtree(t->left, level+1);
	}
}

void
printtree(struct node *t)
{
	_printtree(t, 1);
}

struct node *
insert(struct node *t, struct node *n)
{
	int done;
	struct node *tt;

	if (!t)
		return n;
	if (!n)
		return t;	

	tt = t;
	done = 0;
	while (!done) {
		if (tt->key < n->key) {
			if (tt->right) {
				tt = tt->right;
			} else {
				tt->right = n;
				done = 1;
			}
		} else {
			if (tt->left) {
				tt = tt->left;
			} else {
				tt->left = n;
				done = 1;
			}
		}
	}
	return t;
}

int main(void)
{
	int k;
	int keys[] = {10, 15, 8, 12, 17, 2, 9, 1, 5};
	int nkeys = sizeof(keys) / sizeof(keys[0]);
	struct node *t = NULL;

	for (k = 0; k < nkeys; ++k)
		t = insert(t, mknode(keys[k]));

	printtree(t);
	freetree(t);
	return 0;
}
