
CC = gcc
CFLAGS = -O1 -std=c99 -Wall -Wextra -Wpedantic -Werror -Wno-unused-parameter \
		 -g \
		 -Wno-unused-function # TODO: enable this again

SRC_DIR = ./src
BUILD_DIR = ./build

SRCS = $(shell find $(SRC_DIR) -name '*.c' -or -name '*.h')

.PHONY: all
all: $(BUILD_DIR)/clox

$(BUILD_DIR)/clox: $(SRCS)
	mkdir -p $(BUILD_DIR)
	$(CC) $(CFLAGS) -o $@ $^

.PHONY: clean
clean:
	rm -rf $(BUILD_DIR)
