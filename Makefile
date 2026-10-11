JAVAC ?= javac
SRC := $(wildcard src/main/java/tenet/*.java)

all: out/.built

out/.built: $(SRC)
	mkdir -p out
	$(JAVAC) -Xlint:all -d out $(SRC)
	touch out/.built

clean:
	rm -rf out
