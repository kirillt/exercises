#include <stdio.h>
#include <stdbool.h>

const int inf = -1;

struct request {
    int distance;
    int node;
};

struct list {
    int   value;
    void* next;
};

struct list* append(struct list *l, int v) {
    struct list *result = malloc(sizeof(struct list));
    (*result).value = v;
    (*result).next  = l;
    return result;
}

void solve() {
    int i, n, s, m;
    void  free(void*);
    void* malloc(size_t);

    FILE  *in   = fopen("bfsrev.in" ,"r");
    fscanf(in ,"%d %d %d",&n,&s,&m);

    int  distances[n];
    for (i = 0; i < n; i++) {
        distances[i] = inf;
    }

    struct list **edges = malloc(sizeof(struct list*)*n);
    for (i = 0; i < n; i++) {
        edges[i] = 0;
    }

    for (i = 0; i < m; i++) {
        int from,to;
        fscanf(in,"%d %d",&from,&to);
        edges[to-1] = append(
            edges[to-1],
            from-1);
    }

    fclose(in );

    struct request *queue  = malloc(sizeof(struct request)*m);

    struct request *top    = queue;
    struct request *bottom = top + 1;
    (*top).distance = 0;
    (*top).node = s-1;

    while (top != bottom) {

        int currNode = (*top).node;
        int currDist = (*top).distance;
        int lastDist = distances[currNode];
        if (lastDist == -1 || lastDist > currDist) {

            distances[currNode] = currDist;
            struct list *nextNode = edges[currNode];
            while(nextNode != 0) {
                (*bottom).distance = currDist + 1;
                (*bottom).node = (*nextNode).value;
                nextNode = (*nextNode).next;
                bottom++;
            }
        }
        top++;
    }

    FILE   *out = fopen("bfsrev.out","w");
    for (i = 0; i < n; i++) {
        fprintf(out,"%d ",distances[i]);
    }
    fclose(out);
}

void generateTest() {
    int n = 100000;
    int s = n - 1;
    int m = n;
    FILE   *out = fopen("bfsrev.in","w");
    fprintf(out,"%d %d %d\n",n,s,m);

    int i;
    int a = 1; int b = 2;
    for (i = 0; i < m; i++) {
        if (b > n) {
            b = 1;
        }
        fprintf(out,"%d %d\n",a++,b++);
    }
    fclose(out);
}

int main() {
    solve();
    return 0;
}
