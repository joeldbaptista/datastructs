#include <stdio.h>
#include <stdlib.h>

/* --- Interface --- */

struct node {
	int data;
	struct node *next;
};

struct node *mknode(int data);
void freelist(struct node *h);
void printlist(const char *title, struct node *h);

struct node *append(struct node *h, struct node *n);
struct node *prepend(struct node *h, struct node *n);
struct node *reverse(struct node *h);
struct node *middle(struct node *h);
void cutinhalves(struct node *h, struct node **l, struct node **r);
struct node *sort(struct node *h, int (*cmp_mode)(struct node *, struct node *));

/* --- Implementation --- */

struct node *
mknode(int data)
{
	struct node *n;

	/* assumption: there's always enough mem */
	n = malloc(sizeof *n);
	n->data = data;
	n->next = NULL;
	return n;
}

void
freelist(struct node *h)
{
	struct node *t;

	if (!h)
		return;

	t = h;
	while (t) {
		h = t;
		t = t->next;
		free(h)	;
	}
}

void
printlist(const char *title, struct node *h)
{
	int k;

	printf("== %s ==\n", title);
	for (k = 0; h; h=h->next)
		printf("%3d. %3d\n", ++k, h->data);	
}

struct node *
append(struct node *h, struct node *n)
{
	struct node *t;

	if (!h)
		return n;
	if (!n)	
		return h;

	for (t=h; t->next; t=t->next)
		;
	t->next = n;
	return h;
}

struct node *
prepend(struct node *h, struct node *n)
{
	if (!n)
		return h;

	n->next = h;
	return n;
}

/*
         p   h    
 1.      0   A -> B -> C -> D -> 0

         p    h    n 
 2.      0    A -> B -> C -> D -> 0

         p    h   n 
 3.      0 <- A   B -> C -> D -> 0

             p,h  n
 4.      0 <- A   B -> C -> D -> 0

              p  h,n
 5.      0 <- A   B -> C -> D -> 0 

              p   h    n
 6.      0 <- A   B -> C -> D -> 0

              p    h   n
 7.      0 <- A <- B   C -> D -> 0

                  h,p  n
 8.      0 <- A <- B   C -> D -> 0

                   p  h,n
 9.      0 <- A <- B   C -> D -> 0

                   p   h    n
10.      0 <- A <- B   C -> D -> 0

 etc...
*/
struct node *
reverse(struct node *h)
{
	/* assumption: h != NULL */
	struct node *p, *n;

	p = NULL; /* 1. */

	while (h) {
		n = h->next; /* 2., 6. */
		h->next = p; /* 3., 7. */
		p = h; /* 4., ... */
		h = n; /* 5., ... */
	}
	return p;
}

struct node *
middle(struct node *h)
{
	struct node *t, *tt;

	t = h;
	tt = h;

	while (tt && tt->next) {
		t = t->next;
		tt = (tt->next)->next;
	}
	return t;
}

void
cutinhalves(struct node *h, struct node **l, struct node **r)
{
	struct node *t, *tt;

	/* split the list in two */
	t = h;
	tt = h;

	/* stop one before the middle */
	while (tt && tt->next && (tt->next)->next) {
		t = t->next;
		tt = (tt->next)->next;
	}

	*l = h;
	*r = t->next;
	t->next = NULL; /* break the link */
}

struct node *
merge(struct node *l, struct node *r, int (*cmp_node)(struct node *, struct node *))
{
	struct node *h, *t;

	if (cmp_node(l, r) < 0) {
		h = l;
		l = l->next;
	} else {
		h = r;
		r = r->next;
	}
	for (t=h; l && r; t=t->next) {
		if (cmp_node(l, r) < 0) {
			t->next = l;
			l = l->next;
		} else {
			t->next = r;
			r = r->next;
		}
	}
	if (l) {
		t->next = l;	
	}
	if (r) {
		t->next = r;	
	}
	return h;
}

struct node *
sort(struct node *h, int (*cmp_node)(struct node *, struct node *))
{
	struct node *l, *r;

	if (!h->next)
		return h;

	cutinhalves(h, &l, &r);
	l = sort(l, cmp_node);
	r = sort(r, cmp_node);
	h = merge(l, r, cmp_node);
	return h;	
}

/* --- Entry point --- */

int
cmp_node(struct node *m, struct node *n)
{
	return m->data - n->data;
}

int main(void)
{
	int k;
	struct node *h;

	srand(23479);

	h = NULL;
	for (k = 0; k < 10; ++k)
		h = prepend(h, mknode(rand() % 1234));
	printlist("Original", h);

	h = reverse(h);
	printlist("Reversed", h);

	h = sort(h, cmp_node);
	printlist("Sorted", h);

	freelist(h);
	return 0;
}
