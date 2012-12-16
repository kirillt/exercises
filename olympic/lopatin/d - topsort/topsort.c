#include <stdio.h>
#include <stdbool.h>

int                 n;
bool            cycle;
bool         *visited;
bool         *inside;
struct list  *order;
struct list **edges;

extern void* malloc(size_t);
extern void  free(void*);

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

void dfs(int curr) {
    if (cycle) {
        return;
    } else {
        if (visited[curr]) {
            if (inside[curr]) {
                cycle = true;
            }
            return;
        } else {

            inside[curr] = true;
            visited[curr] = true;

            struct list *next = edges[curr];
            while (next != 0) {
                dfs((*next).value);
                next = (*next).next;
                if (cycle) {
                    return;
                }
            }

            inside[curr] = false;
            order = append(order,curr);
            return;

        }
    }
}

void solve() {
    int i, m;

    FILE  *in   = fopen("topsort.in" ,"r");
    fscanf(in ,"%d %d",&n,&m);

    inside  = malloc(sizeof(bool)*n);
    visited = malloc(sizeof(bool)*n);
    edges   = malloc(sizeof(struct list*)*n);
    for (i = 0; i < n; i++) {
        visited[i] = false;
        inside[i] = false;
        edges[i] = 0;
    }

    for (i = 0; i < m; i++) {
        int from,to;
        fscanf(in,"%d %d",&from,&to);
        edges[from-1] = append(
            edges[from-1],
            to-1);
    }

    fclose(in );

    order  = 0;
    for (i = 0; i < n; i++) {
        if (!visited[i]) {
            dfs(i);
        }
    }

    FILE   *out = fopen("topsort.out","w");
    if (cycle) {
        fprintf(out,"-1");
    } else {
        while (order != 0) {
            fprintf(out,"%d ",(*order).value+1);
            order = (*order).next;
        }
    }
    fclose(out);
}

int main() {
    solve();
    return 0;
}
