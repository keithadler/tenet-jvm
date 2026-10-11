JAVAC ?= javac
SRC := $(wildcard src/main/java/tenet/*.java)

all: out/.built

out/.built: $(SRC)
	mkdir -p out
	$(JAVAC) -Xlint:all -d out $(SRC)
	touch out/.built

clean:
	rm -rf out

test: all
	python3 tests/negative.py
	bin/tenet-jvm tests/exports/nat_add_comm.ndjson

.PHONY: all clean test
