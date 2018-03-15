#ifndef HUFFMAN_SCAN_H
#define HUFFMAN_SCAN_H

#include "code.h"
#include "tree.h"
#include "stack_r.h"

struct scan {

    symbol* input;

    struct stack_r* stack;

    tree* emit() {
        stack = nil_r();

        for (auto s = *input; s != ET; s = *(++input)) {
            if (s == OP) {
                auto right = pop();
                auto left = pop();
                push(merge(left, right));
            } else {
                push(vertex(s, 0));
            }
        }
        input++;

        auto huffman = pop();
        free(stack);
        return huffman;
    }

private:

    inline void push(tree* s) {
        stack = cons_r(s, stack);
    }

    inline tree* pop() {
        auto value = stack->head;
        auto tail = stack->tail;

        free(stack);

        stack = tail;
        return value;
    }
};

#endif //HUFFMAN_SCAN_H