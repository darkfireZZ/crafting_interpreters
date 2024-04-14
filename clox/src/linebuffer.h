
#ifndef clox_linebuffer_h
#define clox_linebuffer_h

#include "common.h"

typedef struct {
    int line;
    int nextLineOffset;
} LineInfo;

typedef struct {
    int count;
    int capacity;
    LineInfo* lines;
} LineBuffer;

void initLineBuffer(LineBuffer* buffer);
void writeLineBuffer(LineBuffer* buffer, int line);
void freeLineBuffer(LineBuffer* buffer);
int lineBufferGet(LineBuffer* buffer, int offset);

#endif
