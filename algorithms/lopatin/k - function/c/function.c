#include <stdio.h>
#include <stdbool.h>

#define two32      4294967296
#define MAX_NUMBER 1000000000000
#define INIT_STACK 16

typedef unsigned long long int64;
typedef unsigned long      int32;

struct request_raw {
    int64 argument;
    int32 counter;
};
typedef struct request_raw request;

void* malloc(size_t);
void  free(void*);

int32  counter = 0;
int32 *cache;

request create_request(const int64 argument) {
    request result;
    result.argument = argument;
    result.counter  = counter;
    return result;
}

void    putOnStack(const int64 argument, request ***bottom) {
    (  *bottom)++;
    ( **bottom) = (request**)malloc(sizeof(request));
    (***bottom) = create_request(argument);
}

void    processArg(const int64 argument, request ***bottom) {
    if (cache[argument] == 0) {
        putOnStack(argument,bottom);
    }
}

void    incCounter(const int64 argument) {
    int32 result;
    if (argument < 3) {
        result = 1;
        cache[argument] = result;
    } else {
        result = cache[argument];
    }
    counter += result % two32;
}

void solve() {
    int64 argument;
    {
        FILE  *in = fopen("function.in" ,"r");
        fscanf(in,"%lld",&argument);
        fclose(in );
    }

    cache = (int32*)malloc(sizeof(int32*)*(argument+1));
    memset(cache,0,argument+1);

    {
        //todo: realloc
        request **stack  = (request**)malloc(sizeof(request*)*INIT_STACK);
               ( *stack) = (request* )malloc(sizeof(request ));
               (**stack) = create_request(argument);

        request **bottom = stack;
        do {
            request current = **bottom;
            int64   value   = current.argument;

            if (value < 3 || cache[value] != 0) {
                incCounter(value);
                free(*bottom);
                bottom--;
            } else {
                int64 left, right;
                if (value % 2 == 0) {
                    left  = value - 1;
                    right = value - 3;
                } else {
                    left  = (value / 7)*6 + ((value % 7)*6)/7;
                    right = (value / 3)*2 + ((value % 3)*2)/3;
                }
                if (cache[left] == 0 || cache[right] == 0) {
                    //left and right will be computed twice =/
                    processArg(left, &bottom);
                    processArg(right,&bottom);
                } else {
                    cache[value] = (cache[left] + cache[right]) % two32;
                }
            }
        } while (bottom != stack);
    }

    {
        FILE *out = fopen("function.out","w");
        fprintf(out,"%lld",counter);
        fclose(out);
    }
}

int main() {
    solve();
    return 0;
}
