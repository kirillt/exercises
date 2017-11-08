#ifndef HUFFMAN_CODER_H
#define HUFFMAN_CODER_H

#include <unistd.h>
#include <cstdio>
#include "code.h"

#include <climits>

struct coder {
    code* codes;
    symbol* input;
    char* output;

    unsigned long from;
    unsigned long limit;

    unsigned long emitted;

    char offset;
    char buffer;
    char tail;

    int value;
    short length;

    char pack() {
        emitted = 0;

        while (from < limit || offset > 0 || length > 0) {
            if (length < 1) {
                if (from < limit) {
                    auto code = codes[input[from]];
                    length = code.length;
                    value = code.value;
                    from++;
                } else {
                    emit();
                    return tail;
                }
            }

            short room = (short)8 - offset;

            if (length > room) {
                short extra = length - room;
                buffer |= value >> extra;
                emit(); //can't be last write

                auto mask = 1;
                for (short k = 1; k < extra; k++) {
                    mask <<= 1;
                    mask |= 1;
                }
                value &= mask;
                length = extra;
            } else {
                buffer |= value << (room - length);
                offset += length;
                length = 0;

                if (offset == 8) {
                    emit();
                }
            }
        }

        return tail;
    }

private:

    void emit() {
        tail = offset;
        *(output++) = buffer;
        emitted++;
        buffer = 0;
        offset = 0;
    }
};

#endif //HUFFMAN_CODER_H
