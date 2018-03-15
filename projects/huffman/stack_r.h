#ifndef HUFFMAN_STACK_R_H
#define HUFFMAN_STACK_R_H

#include "tree.h"

struct stack_r {

    tree* head;

    stack_r* tail;

};

stack_r* nil_r() {
    auto s = (stack_r*) malloc(sizeof(stack_r));
    s->tail = nullptr;
    return s;
}

stack_r* cons_r(tree* head, stack_r* tail) {
    auto fresh = nil_r();
    fresh->head = head;
    fresh->tail = tail;
    return fresh;
}

#endif //HUFFMAN_STACK_R_H
