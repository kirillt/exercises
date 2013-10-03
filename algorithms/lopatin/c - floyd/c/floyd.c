#include <stdio.h>

#define o(row,column) (row + column*n)

void solve() {
    int n;
    FILE  *in  = fopen("floyd.in" ,"r");
    fscanf(in ,"%d",&n);

    int edges[n*n];

    int  i;
    for (i = 0; i < n; i++) {
        int  j;
        for (j = 0; j < n; j++) {
            fscanf(in,"%d",&edges[o(i,j)]);
        }
    }
    fclose(in );

    int  k;
    for (k = 0; k < n; k++) {
        for (i = 0; i < n; i++) {
            int  j;
            for (j = 0; j < n; j++) {
                int  w = edges[o(i,k)] + edges[o(k,j)];
                if  (w < edges[o(i,j)]) {
                    edges[o(i,j)] = w;
                }
            }
        }
    }

    FILE   *out = fopen("floyd.out","w");
    for (i = 0; i < n; i++) {
        int  j;
        for (j = 0; j < n; j++) {
            fprintf(out,"%d ",edges[o(i,j)]);
        }
        fprintf(out,"\n");
    }
    fclose(out);
}

int main() {
    solve();
    return 0;
}
