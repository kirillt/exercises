cmake_minimum_required(VERSION 3.8)
project(huffman)

set(CMAKE_CXX_STANDARD 11)

set(COMMON_SOURCES tree.h code.h)
set(ENCODER_SOURCES encode.cpp heap.h coder.h stack_w.h traverse.h)
set(DECODER_SOURCES decode.cpp stack_r.h scan.h fsm.h)

set(SOURCE_FILES ${COMMON_SOURCES} ${ENCODER_SOURCES} ${DECODER_SOURCES})
add_executable(encode ${ENCODER_SOURCES} ${COMMON_SOURCES})
add_executable(decode ${DECODER_SOURCES} ${COMMON_SOURCES})