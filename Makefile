.PHONY: all clean

# --- Configuration Variables ---
# Define the build directory. Default is _build/default/src/
COQMODULE := sflib
BUILD_DIR ?= _build/default/src/

COQFILES := $(wildcard src/*.v)

# --- Main Targets ---
# Default target: creates the _CoqProject file
all: _CoqProject

# Rule to create the _CoqProject file
_CoqProject:
	@echo "-R $(BUILD_DIR) $(COQMODULE)" > _CoqProject
	@echo "$(COQFILES)" >> _CoqProject

# Rule to clean up the generated _CoqProject file
clean:
	@rm -f _CoqProject