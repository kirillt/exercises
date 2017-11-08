#include <sys/mman.h>
#include <sys/stat.h>
#include <iostream>
#include <fcntl.h>
#include <unistd.h>

#include "tree.h"
#include "heap.h"
#include "coder.h"
#include "traverse.h"

int main(int argc, const char* argv[]) {
    if (argc < 2) { printf("Provide input file path\n"); return 1; }
    if (argc > 3) { printf("Too much arguments\n"); return 1; }

    auto file_in  = argv[1];
    auto file_out = argc == 3 ? argv[2] : "out.hf";

    struct stat stat;

    auto source = open(file_in, O_RDONLY);
    if (source < 0) {
        printf("Can't open file\n");
        return 1;
    }

    fstat(source, &stat);
    auto target = open(file_out, O_WRONLY | O_CREAT | O_TRUNC, stat.st_mode);

    auto size = (size_t)stat.st_size;
    if (size == 0) {
        close(source);
        close(target);
        return 0;
    }

    auto input = (symbol*) mmap(nullptr, size, PROT_READ, MAP_SHARED, source, 0);
    if (input == nullptr) {
        printf("Can't mmap input file\n");
        return 1;
    }

    auto total = stat.st_size / sizeof(symbol);
    long occurrences[ALPHABET_SIZE] = {0};
    for (auto i = 0; i < total; i++) {
        occurrences[input[i]]++;
    }

    int different = 0;
    symbol letters[ALPHABET_SIZE] = {0};
    for (symbol s = 1; s != 0; s++) {
        long n = occurrences[s];
        if (n > 0) {
            letters[different] = s;
            different++;
        }
    }

    if (different == 1) {
        write(target, letters, 1);
        char stop = ET;
        write(target, &stop, 1);
        write(target, &total, sizeof(unsigned long));
    } else {
        struct heap *heap = create(different);
        for (int i = 0; i < different; i++) {
            symbol l = letters[i];
            heap->push(vertex(l, occurrences[l]));
        }

        tree *t;
        while (heap->limit > 1) {
            t = heap->pop();
            tree *v = heap->pop();
            heap->push(merge(t, v));
        }

        tree *huffman = heap->pop();
        free(heap->array);
        free(heap);

        struct traverse traverse;
        traverse.output = (symbol *) malloc(2 * different * sizeof(symbol));
        traverse.walk(huffman);

        write(target, traverse.output, traverse.limit);
        free(traverse.output);

        auto buffer = (char *) malloc(size + 1);
        struct coder coder = {traverse.codes, input, buffer + 1, 0, total};
        char tail = coder.pack();
        buffer[0] = tail;
        write(target, buffer, coder.emitted + 1);
        free(buffer);
    }

    munmap(input, size);
    close(source);
    close(target);
    return 0;
}