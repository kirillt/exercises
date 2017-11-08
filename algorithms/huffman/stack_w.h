#ifndef HUFFMAN_STACK_W_H
#define HUFFMAN_STACK_W_H

#include <cstdlib>
#include "code.h"

struct stack_w {

    symbol head;

    stack_w* tail;

};

stack_w* nil_w() {
    auto s = (stack_w*) malloc(sizeof(stack_w));
    s->tail = nullptr;
    return s;
}

stack_w* cons_w(symbol head, stack_w* tail) {
    auto fresh = nil_w();
    fresh->head = head;
    fresh->tail = tail;
    return fresh;
}

#endif //HUFFMAN_STACK_W_H