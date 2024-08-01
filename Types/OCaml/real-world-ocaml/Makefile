TARGETS = ch01 ch02 ch04 ch05 ch17 ch19 ch21

DUNE = dune

all: $(TARGETS)
	for t in $(TARGETS); do \
		(echo "making $$t:" && $(DUNE) build --root=$$t) || exit 1; \
	done

format: $(TARGETS)
	for t in $(TARGETS); do \
		(echo "making $$t:" && $(DUNE) fmt --root=$$t) || exit 1; \
	done

doc: $(TARGETS)
	for t in $(TARGETS); do \
		(echo "making $$t:" && $(DUNE) build @doc --root=$$t) || exit 1; \
	done

test: $(TARGETS)
	for t in $(TARGETS); do \
		(echo "making $$t:" && $(DUNE) runtest --root=$$t) || exit 1; \
	done

clean: $(TARGETS)
	for t in $(TARGETS); do \
		(echo "cleaing $$t:" && $(DUNE) clean --root=$$t) || true; \
	done
