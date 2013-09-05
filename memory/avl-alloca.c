#include <alloca.h>
#include <stdlib.h>
#include <stdio.h>

#define true  1
#define false 0

struct input;

#define COMMAND char
#define ADD     1
#define DEL     0

typedef struct input {
    COMMAND       command;
    int           number;
    struct input* next;
} input;

#define DIRECTION char
#define LT      -1
#define EQ       0
#define RT      +1

DIRECTION invert(DIRECTION dir) {
    return dir * (-1);
}

char dir2id(DIRECTION dir) {
    switch (dir) {
        case LT: return 0;
        case RT: return 1;
        default: exit(-1);
    }
}

#define LEFT       CHILD(LT)
#define RIGHT      CHILD(RT)
#define CHILD(dir) child[dir2id(dir)]

typedef struct tree {
    struct tree* child[2];
    DIRECTION    balance;
    int          root;
} tree;

typedef void (*tree2void)(tree*);

void print(tree* maybe_state) {
    putchar('[');
    if (maybe_state) {
        tree state = *maybe_state;
        printf("%d(%d) ", state.root, state.balance);
        print(state.LEFT);
        putchar(' ');
        print(state.RIGHT);
    }
    putchar(']');
}

void println(tree* maybe_state) {
    print(maybe_state);
    putchar('\n');
}

void work(input* maybe_sequence) {
    void loop(tree* maybe_state) {

        //BTW, it is demonstration of nested function calls by pointers
        //direction and maybe_state are used not as globals but as locals for every function

        #define CHECK    char
        #define DISABLED 0
        #define ENABLED  1

        CHECK balancing;

        void add(tree* maybe_state, const int number, tree2void cont) {
            DIRECTION direction;

            void init(const int root, tree2void cont) {
                tree* node    = alloca(sizeof(tree));
                node->root    = root;
                node->LEFT    = 0;
                node->RIGHT   = 0;
                node->balance = 0;
                return cont(node);
            }
            void append(tree* ptr_node) {
                tree* ptr_state = maybe_state;
                const tree state = *maybe_state;
                if (balancing) {
                    const tree node = *ptr_node;
                    if (!node.LEFT && !node.RIGHT &&
                        state.CHILD(invert(direction))) {
                        //DIRTY: for keeping simple ++ or -- of balance counter
                        //we should handle this case 
                        balancing = DISABLED;

                        ptr_state->balance += direction;
                        goto ok;
                    }
                    if (state.balance == LT || state.balance == RT) {
                        DIRECTION opposite = invert(direction);
                        if (state.balance == invert(node.balance)) {
                            //[x [y L [z A B]] R] and [x L [y [z A B] R]] cases

                            tree* ptr_mid = node.CHILD(opposite);
                            tree  mid = *ptr_mid;

                            tree* a = mid.CHILD(opposite);
                            tree* b = mid.CHILD(direction);

                            ptr_mid->CHILD(opposite)    = ptr_state;
                            ptr_mid->CHILD(direction)   = ptr_node;
                            ptr_node->CHILD(opposite)   = b;
                            ptr_node->balance += direction;
                            ptr_state->CHILD(direction) = a;
                            ptr_state->balance += opposite;

                            maybe_state = ptr_state = ptr_mid;
                            balancing = DISABLED;
                        } else {
                            //[x [y L    C   ] R] and [x L [y    C    R]] cases

                            ptr_node->CHILD(opposite) = ptr_state;
                            ptr_node->balance += opposite;
                            ptr_state->CHILD(direction) = node.CHILD(opposite);
                            ptr_state->balance += opposite;

                            maybe_state = ptr_state = ptr_node;
                            balancing = DISABLED;
                        }
                    } else {
                        ptr_state->balance += direction;
                        goto ok;
                    }
                } else {
                    ok: {
                        ptr_state->CHILD(direction) = ptr_node;
                    }
                }
                return cont(maybe_state);
            }

            if (maybe_state) {
                tree state = *maybe_state;
                int root = state.root;
                if (root == number) {
                    return loop(maybe_state);
                } else {
                    if (root > number) { direction = LT; }
                    else               { direction = RT; }
                    return add(state.CHILD(direction), number, append);
                }
            } else {
                return init(number, cont);
            }
        }

        void del(tree* maybe_state, const int number, tree2void cont) {
            //will not be implemented
            exit(-1);
        }

        balancing = ENABLED;
        if (maybe_sequence) {
            input sequence = *maybe_sequence;
            int number = sequence.number;
            maybe_sequence = sequence.next;
            switch (sequence.command) {
                case ADD: return add(maybe_state, number, &loop);
                case DEL: return del(maybe_state, number, &loop);
            }
        } else {
            println(maybe_state);
        }
    }

    loop(0);
}

int main(int argc, char *argv[]) {
    int i;
    input* ptr_sequence = alloca(sizeof(input));
    input* prev = ptr_sequence;
    input* curr = prev;
    for (i = 0; i < 100; i++) {
        curr->command = ADD;
        curr->number = i < 51 ? 50 - i : i;
        prev->next = curr;
        prev = curr;
        curr = alloca(sizeof(input));
    }

    work(ptr_sequence);
    return 0;
}
