#include <cstdio>
#include <unistd.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include "code.h"
#include "scan.h"
#include "fsm.h"

int main(int argc, const char* argv[]) {
    if (argc < 2) { printf("Provide input file path\n"); return 1; }
    if (argc > 3) { printf("Too much arguments\n"); return 1; }

    auto file_in  = argv[1];
    auto file_out = argc == 3 ? argv[2] : "out.txt";

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

    struct scan scan = { input };
    auto huffman = scan.emit();

    if (huffman->terminal) {
        auto repeats = *(unsigned long*)scan.input;
        for (auto i = 0; i < repeats; i++) {
            write(target, &huffman->letter, 1);
        }
    } else {
        auto data = (octet *) scan.input;
        char tail = *(data++);

        struct fsm fsm;
        fsm.root = huffman;
        fsm.state = fsm.root;
        int i = 0;
        octet *limit = (octet *) input + size;
        for (octet *byte = data; byte != limit; byte++) {
            octet mask = 1 << 7;
            auto stop = byte == limit - 1 ? tail : 8;
            for (char bit = 0; bit < stop; bit++, mask >>= 1) {
                octet x = *byte & mask;
                auto s = fsm.emit(x);
                if (s != 0) {
                    write(target, &s, 1);
                }
            }
        }
        dealloc(huffman);
    }

    munmap(input, size);
    close(source);
    close(target);
    return 0;
}