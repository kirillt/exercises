#ifndef HUFFMAN_CODE_H
#define HUFFMAN_CODE_H

typedef unsigned char octet;

typedef unsigned char symbol;
#define ALPHABET_SIZE 256

#define LP 0
#define OP 1

#define ET 2

struct code {
    int value;
    short length;
};

typedef struct code code;

#endif //HUFFMAN_CODE_H