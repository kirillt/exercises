#ifndef HUFFMAN_TREE_H
#define HUFFMAN_TREE_H

#include <malloc.h>
#include <cassert>
#include "code.h"

struct tree {

    bool terminal;

    long weight;
    symbol letter;

    tree* left;
    tree* right;

};

typedef struct tree tree;

tree* vertex(symbol s, long w) {
    auto t = (tree*) malloc(sizeof(tree));
    t->terminal = true;

    t->left = nullptr;
    t->right = nullptr;
    t->letter = s;
    t->weight = w;
    return t;
}

tree* merge(tree* a, tree* b) {
    auto t = (tree*) malloc(sizeof(tree));
    t->terminal = false;

    auto wa = a->weight;
    auto wb = b->weight;
    if (wa > wb) {
        t->right = a;
        t->left = b;
    } else {
        t->right = b;
        t->left = a;
    }

    t->weight = wa + wb;
    return t;
}

void dealloc(tree* t) {
    if (t->left != nullptr) dealloc(t->left);
    if (t->right != nullptr) dealloc(t->right);
    free(t);
}

#endif //HUFFMAN_TREE_H