#ifndef HUFFMAN_FSM_H
#define HUFFMAN_FSM_H

#include "tree.h"

struct fsm {

    tree* root;
    tree* state;

    symbol emit(char bit) {
        if (bit == 0) state = state->left;
        else state = state->right;

        if (state->terminal) {
            auto result = state->letter;
            state = root;
            return result;
        } else {
            return 0;
        }
    }

};

#endif //HUFFMAN_FSM_H
