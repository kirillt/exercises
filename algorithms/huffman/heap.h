#ifndef HUFFMAN_HEAP_H
#define HUFFMAN_HEAP_H

#include <cstring>

inline int parent(int i) {
    return (i - 1) / 2;
}

inline int left(int p) {
    return p * 2 + 1;
}

inline int right(int p) {
    return p * 2 + 2;
}

struct heap {
    int size;
    int limit;

    tree** array = nullptr;

    void resize(int k) {
        auto length = sizeof(tree*) * k;
        auto fresh = (tree**) malloc(length);
        if (array != nullptr) {
            memcpy(fresh, array, length);
            free(array);
        }
        array = fresh;
        size = k;
    }

    inline void swap(int i, int j) {
        tree* t = array[i];
        array[i] = array[j];
        array[j] = t;
    }

    inline int lighter(int i, int j) {
        return array[i]->weight < array[j]->weight;
    }

    inline int lightest(int p) {
        int l = left(p);
        int r = right(p);
        int x = p;
        if (l < limit && lighter(l,x)) {
            x = l;
        }
        if (r < limit && lighter(r,x)) {
            x = r;
        }
        return x;
    }

    heap* push(tree* t) {
        if (limit >= size) {
            resize(size * 2);
        }
        int i = limit;
        array[i] = t;
        limit++;

        int p = parent(i);
        while (i > 0 && lighter(i,p)) {
            swap(i, p);
            i = p;
            p = parent(i);
        }

        return this;
    }

    tree* pop() {
        tree* t = array[0];
        array[0] = array[--limit];

        int p = 0;
        int i = lightest(p);
        while (i < limit && i != p) {
            swap(i, p);
            p = i;
            i = lightest(p);
        }

        return t;
    }
};

heap* create(int size) {
    auto h = (heap*) malloc(sizeof(heap));
    h->array = nullptr;
    h->resize(size);
    h->limit = 0;
}

typedef struct heap heap;

#endif //HUFFMAN_HEAP_H