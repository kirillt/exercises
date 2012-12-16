#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

extern void* malloc(size_t);
extern void  free(void*);

struct edge_raw {
    int id;
    int to;
};
#define edge struct edge_raw

struct list_raw {
    edge  value;
    void* next;
};
#define list struct list_raw

list* append(list *l, edge v) {
    list *result = (list*)malloc(sizeof(list));
    (*result).value = v;
    (*result).next  = l;
    return result;
}

int  compare(const void *left, const void *right) {
    return (*(int *)left) - (*(int *)right);
}

int  min(const int left, const int right) {
    if (left < right) {
        return left;
    } else {
        return right;
    }
}

int *init(int size) {
    int  i;
    int *array = (int*)malloc(sizeof(int)*size);
    for (i = 0; i < size; i++) {
        array[i] = 0;
    }
    return array;
}

int          k;
int          n;
int      timer;
int   *time_in;
int   *time_up;
bool  *visited;
list  *bridges;
list **edges;

void dfs(int curr, int prev) {
    visited[curr] = true;

    timer++;
    time_in[curr] = timer;
    time_up[curr] = timer;

    list  *children  = edges[curr];
    while (children != 0) {
        edge next = (*children).value;

        if (next.to != prev) {
            if (visited[next.to]) {
                time_up[curr] = min(
                    time_up[curr],
                    time_in[next.to]
                );
            } else {
                dfs(next.to, curr);
                time_up[curr] = min(
                    time_up[curr],
                    time_up[next.to]
                );
                if (time_up[next.to] > time_in[curr]) {
                    bridges = append(bridges,next);
                    k++;
                }
            }
        }

        children  = (*children).next;
    }
}

void solve() {
    int i, m;

    FILE  *in   = fopen("bridges.in" ,"r");
    fscanf(in ,"%d %d",&n,&m);

    visited = (bool* )malloc(sizeof(bool )*n);
    edges   = (list**)malloc(sizeof(list*)*n);
    for (i = 0; i < n; i++) {
        visited[i] = false;
        edges[i]   = 0;
    }

    for (i = 1; i < m+1; i++) {
        int  from,to;
        fscanf(in,"%d %d",&from,&to);

        edge temp;
        temp.id = i;

        temp.to = to  -1;
        edges[from-1] = append(
            edges[from-1],
            temp);

        temp.to = from-1;
        edges[to  -1] = append(
            edges[to  -1],
            temp);
    }

    fclose(in );

    k       = 0;
    bridges = 0;

    timer   = 0;
    time_in = init(n);
    time_up = init(n);

    for (i = 0; i < n; i++) {
        if (!visited[i]) {
            dfs(i, -1);
        }
    }

    i = 0;
    int ids[k];
    while (bridges != 0) {
        ids[i]  = (*bridges).value.id;
        bridges = (*bridges).next;
        i++;
    }

    qsort(ids,k,sizeof(int),&compare);

    FILE   *out = fopen("bridges.out","w");
    fprintf(out,"%d\n",k);
    for (i = 0; i < k; i++) {
        fprintf(out,"%d ",ids[i]);
    }
    fclose(out);
}

int main() {
    solve();
    return 0;
}
