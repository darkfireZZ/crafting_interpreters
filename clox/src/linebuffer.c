
#include "linebuffer.h"
#include "memory.h"

void initLineBuffer(LineBuffer* buffer) {
    buffer->count = 0;
    buffer->capacity = 0;
    buffer->lines = NULL;
}

void writeLineBuffer(LineBuffer* buffer, int line) {
    LineInfo* lastLineInfo = buffer->count > 0 ? (buffer->lines + buffer->count - 1) : NULL;

    assert(!lastLineInfo || line >= lastLineInfo->line);

    if (lastLineInfo && line == lastLineInfo->line) {
        lastLineInfo->nextLineOffset++;
        return;
    }

    if (buffer->capacity < buffer->count + 1) {
        int oldCapacity = buffer->capacity;
        buffer->capacity = GROW_CAPACITY(oldCapacity);
        buffer->lines = GROW_ARRAY(LineInfo, buffer->lines, oldCapacity, buffer->capacity);
    }

    buffer->lines[buffer->count].line = line;
    int prevLineOffset = lastLineInfo ? lastLineInfo->nextLineOffset : 0;
    buffer->lines[buffer->count].nextLineOffset = prevLineOffset + 1;
    buffer->count++;
}

void freeLineBuffer(LineBuffer* buffer) {
    FREE_ARRAY(LineInfo, buffer->lines, buffer->capacity);
    initLineBuffer(buffer);
}

static int numBytesLineBuffer(LineBuffer* buffer) {
    if (buffer->count > 0) {
        return buffer->lines[buffer->count - 1].nextLineOffset;
    } else {
        return 0;
    }
}

int lineBufferGet(LineBuffer* buffer, int offset) {
    assert(offset < numBytesLineBuffer(buffer));

    // TODO: This should perform a binary search
    for (int i = 0; i < buffer->count; ++i) {
        LineInfo lineInfo = buffer->lines[i];
        if (offset < lineInfo.nextLineOffset) {
            return lineInfo.line;
        }
    }

    // This is unreachable
    return -1;
}
