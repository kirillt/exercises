#include <math.h>
#include <stdio.h>
#include <stdbool.h>

#define small unsigned char

struct point_raw {
    short x;
    short y;
};

struct edge_raw {
    small from;
    small to;
};

typedef struct point_raw point;
typedef struct  edge_raw edge ;

#define  o(row,column,n) (row*n + column)
#define sq(x)            ((x)*(x))

const double MAX_DISTANCE = 3000;
//it is more than sqrt(2*2000^2)

small   n;
void solve() {
    small i,j;

    FILE *in = fopen("connect.in","r");

    fscanf(in,"%d\n",&n);
    point points[n];
    for (i = 0; i < n; i++) {
        fscanf(in,"%d %d\n",
            &points[i].x,
            &points[i].y
        );
    }

    fclose(in );

    double edges[n*n];
    for (i = 0; i < n; i++) {
        for (j = i; j < n; j++) {
            point pi, pj;
            pi = points[i];
            pj = points[j];
            double dist = sqrt(
                sq(pi.x - pj.x) +
                sq(pi.y - pj.y)
            );
            edges[o(i,j,n)] = dist;
            edges[o(j,i,n)] = dist;
        }
    }

    bool rest[n];
    for (i = 0; i < n; i++) {
        rest[i] = true;
    }

    int count  = 0;
    double sum = 0;
    rest[0]    = false;
    edge included[n-1];

    while (true) {
        small  to;
        small  from;
        bool   stop = true;
        double min  = MAX_DISTANCE;

        for (i = 0; i < n; i++)     { if (!rest[i]) {
            for (j = 0; j < n; j++) { if ( rest[j]) {
                double dist = edges[o(i,j,n)];
                if (min  > dist) {
                    min  = dist;
                    from = i;
                    to   = j;
                }

                stop = false;
            }}
        }}

        if (stop) {
            break;
        } else {
            rest[to] = false;
            included[count].from = from;
            included[count].to   = to;
            sum += min;
            count++;
        }
    }

    FILE *out = fopen("connect.out","w");
    fprintf(out,"%f\n%d\n",sum,count);
    for (i = 0; i < count; i++) {
        fprintf(out,"%d %d\n",
            included[i].from+1,
            included[i].to+1);
    }
    fclose(out);
}

void generateTest() {
    int i,n = 200;
    FILE *out = fopen("connect.in","w");
    fprintf(out,"%d\n",n);
    for (i = 0; i < n; i++) {
        fprintf(out,"%d %d\n",
            -1000+2*i,
             1000-i);
    }
    fclose(out);
}

int main() {
    solve();
    return 0;
}
