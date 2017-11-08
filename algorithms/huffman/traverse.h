#ifndef HUFFMAN_TRAVERSE_H
#define HUFFMAN_TRAVERSE_H

#include "code.h"
#include "tree.h"
#include "stack_w.h"

struct traverse {
    code codes[ALPHABET_SIZE];

    struct stack_w* stack;

    size_t limit;
    symbol *output;

    void walk(tree* tree) {
        limit = 0;
        stack = nil_w();

        walk(tree, 0, 0);

        while (!empty()) {
            emit(pop());
        }
        free(stack);

        emit(ET);
    }

private:

    inline void emit(symbol s) {
        output[limit++] = s;
    }

    inline int reverse(int code, short length) {
        int result = 0;
        for (short i = 0; i < length; i++) {
            short j = length - i - (short)1;
            if ((code & (1 << i)) != 0) {
                result |= 1 << j;
            }
        }
        return result;
    }

    void walk(tree* tree, int code, short depth) {
        if (tree->terminal) {
            codes[tree->letter].value = reverse(code, depth);
            codes[tree->letter].length = depth;
            emit(tree->letter);
            free(tree);
            return;
        }

        auto d = depth++;

        lp();
        walk(tree->left, code, depth);
        op();
        walk(tree->right, code | (1 << d), depth);
        rp();

        free(tree);
    }

    inline bool empty() {
        return stack->tail == nullptr;
    }

    inline void push(symbol s) {
        stack = cons_w(s, stack);
    }

    inline symbol pop() {
        auto value = stack->head;
        auto tail = stack->tail;

        free(stack);

        stack = tail;
        return value;
    }

    inline void lp() {
        push(LP);
    }

    inline void op() {
        while (stack->head == OP) {
            emit(pop());
        }
        push(OP);
    }

    inline void rp() {
        auto s = pop();
        while (s != LP) {
            emit(s);
            s = pop();
        }
    }
};

#endif //HUFFMAN_TRAVERSE_H
