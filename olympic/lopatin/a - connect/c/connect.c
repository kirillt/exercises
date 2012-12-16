#include <stdio.h>
#include <stdbool.h>

int min(int a, int b) {
    if (a > b) {
        return b;
    } else {
        return a;
    }
}

void init(int* array, int i) {
    i--;
    for(; i > 0; i--) {
        array[i] = i;
    }
}

int assign(int* components, int i, int j) {
    int a,b,c,d,m;
    a = components[i];
    b = components[j];
    if (a == i && b == j) {
        m = min(a,b);
    } else {
        m = assign(components,a,b);
    }
    components[i] = m;
    components[j] = m;
    return m;
}

bool update(int* components, int i) {
    int right = components[i];
    int left  = components[right];
    if (left == right) {
        return false;
    } else {
        components[i] = left;
        return true;
    }
}

int normalize(int* components, int n) {
    int k = 0;
    int nums[n];

    int  i;
    for (i = 1; i < n+1; i++) {
        nums[i] = 0;
    }

    for (i = 1; i < n+1; i++) {
        int v = components[i];
        if (nums[v] == 0) {
            k++;
            nums[v] = k;
            components[i] = k;
        } else {
            components[i] = nums[v];
        }
    }

    return k;
}

void solve() {
    int n, m;
    FILE  *in  = fopen("connect.in" ,"r");
    fscanf(in ,"%d %d",&n,&m);

    int  components[n+1];
    init(components,n+1);

    for (; m > 0; m--) {
        int i,j;
        fscanf(in,"%d %d",&i,&j);
        assign(components,i,j);
    }
    fclose(in );

    bool   f = true;
    while (f) {
        f = false;

        int  i;
        for (i = n; i > 0; i--) {
             f = f || update(components,i);
        }
    }

    int k = normalize(components,n);

    FILE   *out = fopen("connect.out","w");
    fprintf(out,"%d\n",k);
    int  i;
    for (i = 1; i < n+1; i++) {
        fprintf(out,"%d ",components[i]);
    }
    fclose(out);
}

void generateTest() {
    int n,m;
    n = 20000;
    m = 200000;

    FILE   *out = fopen("connect.in","w");
    fprintf(out,"%d %d\n",n,m);
    int  i,j;
    for (j = 0; j < 20; j++) {
        for (i = 0; i < n; i += 2+j) {
            fprintf(out,"%d %d\n",(i+1) % n,(i+2+j) % n);
        }
    }
    fclose(out);
}

int main() {
    solve();
    return 0;
}
