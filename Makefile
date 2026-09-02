PYTHON ?= python3
BOOK ?=
SLUG ?=
TITLE ?=
empty :=
space := $(empty) $(empty)
TREE_IGNORE_PATTERNS ?= \
	vscode-build build tree.txt .git .vscode .lake \
	.latexindent_cache .ruff_cache __pycache__ \
	*.pdf *.run.xml *.synctex.gz *.toc *.xdv \
	*.idx *.ilg *.ind *.lof *.log *.lot *.out \
	*.aux *.bbl *.bcf *.blg *.fdb_latexmk *.fls \
	*.orig *.rej *.bak *.backup *.save *.swp *.swo *~ \
	.books.yml.*.tmp .DS_Store ._* __MACOSX/
TREE_IGNORE ?= $(subst $(space),|,$(strip $(TREE_IGNORE_PATTERNS)))

COMMAND_GOALS := books lean contents site generated format config
CHECK_REQUESTED := $(filter check,$(MAKECMDGOALS))
CONTENTS_SCOPE := $(filter chap sec all,$(MAKECMDGOALS))
CHECK_SCOPE := $(filter all source manifest proof-links,$(MAKECMDGOALS))
FORMAT_SCOPE := $(filter tex py sh all,$(MAKECMDGOALS))
DOCTOR_SCOPE := $(filter env books,$(MAKECMDGOALS))
CLEAN_SCOPE := $(filter build source cache,$(MAKECMDGOALS))
CACHE_SCOPE := $(filter lake tex ruff py all,$(MAKECMDGOALS))
STRICT_REQUESTED := $(filter strict,$(MAKECMDGOALS))

.PHONY: \
	help \
	report \
	clean build source \
	cache lake ruff all \
	tree \
	format tex py sh \
	books \
	lean \
	test \
	check manifest proof-links strict \
	doctor env \
	contents chap sec \
	site \
	config \
	generated \
	new-book \
	publish \
	image-pin

help:
	@printf '%s\n' \
		'Textbook repository commands:' \
		'' \
		'  make help                                  Show this help' \
		'  make report                                Print an informational repository report' \
		'  make clean {build|source}                  Remove build output or disposable source-tree artifacts' \
		'  make clean cache {lake|tex|ruff|py|all}    Remove selected local caches' \
		'  make tree                                  Write the local tree.txt listing' \
		'' \
		'  make format {tex|py|sh|all} [check]        Format or check source formatting' \
		'  make books [BOOK=<slug>]                   Build all enabled books or one book' \
		'  make books [BOOK=<slug>] check [strict]    Build and check selected books' \
		'  make lean [check]                          Build Lean, or check proofs and links' \
		'' \
		'  make test                                  Run the Python test suite (run with full checks)' \
		'  make check {manifest|source|proof-links}   Run a focused repository check' \
		'  make check all [strict]                    Run Lean and LaTeX validation (separate from tests)' \
		'  make doctor env                            Check the development environment' \
		'  make doctor books [BOOK=<slug>]            Inspect all textbooks or one textbook' \
		'' \
		'  make contents {chap|sec|all} [check]       Regenerate or check LaTeX assembly' \
		'  make site [BOOK=<slug>] [check]            Regenerate or check site content' \
		'  make config [check]                        Synchronize or check shared configuration' \
		'  make generated [check]                     Regenerate or check all generated content' \
		'' \
		'  make new-book SLUG=<slug> TITLE="<title>"  Scaffold and register a new textbook' \
		'  make publish BOOK=<slug>                   Publish an eligible textbook release' \
		'  make image-pin DIGEST=<sha256>             Automation/recovery: pin a tested image' \
		'' \
		'Variables:' \
		'  BOOK=<slug>                                Select one registered textbook' \
		'  SLUG=<slug>                                Set the slug for make new-book' \
		'  TITLE=<title>                              Set the title for make new-book' \
		'  BOOK_BUILD_JOBS=<n>                        Limit parallel bulk builds' \
		'  PYTHON=<command>                           Override the Python interpreter' \
		'  TREE_IGNORE=<pattern>                      Customize exclusions for make tree' \
		'' \
		'See README.md and docs/CONTRIBUTING.md for details.'

report:
	@$(PYTHON) scripts/repository-report.py

clean:
	@if [ "$(words $(CLEAN_SCOPE))" -ne 1 ]; then \
		printf '%s\n' \
			"usage: make clean {build|source}" \
			"usage: make clean cache {lake|tex|ruff|py|all}" >&2; \
		exit 2; \
	fi
	@if [ -n "$(filter build,$(CLEAN_SCOPE))" ]; then \
		./scripts/clean.sh; \
	elif [ -n "$(filter source,$(CLEAN_SCOPE))" ]; then \
		./scripts/clean-artifacts.sh; \
	elif [ "$(words $(CACHE_SCOPE))" -ne 1 ]; then \
		printf '%s\n' \
			"usage: make clean {build|source}" \
			"usage: make clean cache {lake|tex|ruff|py|all}" >&2; \
		exit 2; \
	else \
		./scripts/clean-cache.sh "$(CACHE_SCOPE)"; \
	fi

build source cache lake ruff all:
	@:

tree:
	@rm -f tree.txt
	@tree \
		--dirsfirst \
		-a \
		-I "$(TREE_IGNORE)" \
		> tree.txt

format:
	@if [ "$(words $(FORMAT_SCOPE))" -ne 1 ]; then \
		echo "usage: make format {tex|py|sh|all} [check]" >&2; \
		exit 2; \
	fi
	@if [ -n "$(filter tex all,$(FORMAT_SCOPE))" ]; then \
		./scripts/format-tex.sh $(if $(CHECK_REQUESTED),--check); \
	fi
	@if [ -n "$(filter py all,$(FORMAT_SCOPE))" ]; then \
		./scripts/format-python.sh $(if $(CHECK_REQUESTED),--check); \
	fi
	@if [ -n "$(filter sh all,$(FORMAT_SCOPE))" ]; then \
		./scripts/format-shell.sh $(if $(CHECK_REQUESTED),--check); \
	fi
	@if [ "$(FORMAT_SCOPE)" = "all" ]; then \
		./scripts/normalize-eof.sh $(if $(CHECK_REQUESTED),--check); \
	fi

tex py sh:
	@:

books:
	@if [ -n "$(filter doctor,$(MAKECMDGOALS))" ]; then \
		:; \
	elif [ -n "$(STRICT_REQUESTED)" ] && [ -z "$(CHECK_REQUESTED)" ]; then \
		printf '%s\n' \
			"error: strict requires check for a book build" \
			"usage: make books [BOOK=<slug>]" \
			"usage: make books [BOOK=<slug>] check [strict]" >&2; \
		exit 2; \
	elif [ -n "$(strip $(BOOK))" ]; then \
		./scripts/build-book.sh "$(BOOK)"; \
		if [ -n "$(CHECK_REQUESTED)" ]; then \
			$(PYTHON) scripts/check-log.py $(if $(STRICT_REQUESTED),--strict) \
				"build/$(BOOK)/book.log"; \
		fi; \
	else \
		if [ -n "$(CHECK_REQUESTED)" ]; then \
			$(if $(STRICT_REQUESTED),env CHECK_LOG_STRICT=1 )./scripts/build-all.sh check; \
		else \
			./scripts/build-all.sh; \
		fi; \
	fi

lean:
	@if [ -n "$(CHECK_REQUESTED)" ]; then \
		./scripts/check-lean.sh; \
	else \
		cd lean && lake build; \
	fi

test:
	@$(PYTHON) -m unittest discover -s tests -p 'test_*.py' -v

check:
	@if [ -z "$(filter $(COMMAND_GOALS),$(MAKECMDGOALS))" ] && \
		[ "$(words $(CHECK_SCOPE))" -ne 1 ]; then \
		printf '%s\n' \
			"usage: make check {manifest|source|proof-links}" \
			"usage: make check all [strict]" >&2; \
		exit 2; \
	fi
	@if [ -n "$(STRICT_REQUESTED)" ] && \
		[ -n "$(filter-out all,$(CHECK_SCOPE))" ]; then \
		echo "error: strict is only valid for the full check" >&2; \
		exit 2; \
	fi
	@if [ -n "$(filter $(COMMAND_GOALS),$(MAKECMDGOALS))" ]; then \
		:; \
	else \
		case "$(CHECK_SCOPE)" in \
			source) \
				./scripts/check-repository.sh; \
				;; \
			manifest) \
				$(PYTHON) scripts/books.py validate; \
				;; \
			proof-links) \
				$(PYTHON) scripts/check-proof-links.py; \
				;; \
			all) \
				if [ -n "$(STRICT_REQUESTED)" ]; then \
					env CHECK_LOG_STRICT=1 ./scripts/check.sh; \
				else \
					./scripts/check.sh; \
				fi; \
				;; \
		esac; \
	fi

manifest proof-links strict:
	@:

doctor:
	@if [ "$(words $(DOCTOR_SCOPE))" -ne 1 ]; then \
		printf '%s\n' \
			"usage: make doctor env" \
			"usage: make doctor books [BOOK=<slug>]" >&2; \
		exit 2; \
	fi
	@if [ -n "$(filter env,$(DOCTOR_SCOPE))" ]; then \
		if [ -n "$(strip $(BOOK))" ]; then \
			echo "error: BOOK is only valid with 'make doctor books'" >&2; \
			exit 2; \
		fi; \
		./scripts/check-environment.sh; \
	elif [ -n "$(strip $(BOOK))" ]; then \
		$(PYTHON) scripts/books.py require "$(BOOK)" >/dev/null; \
		$(PYTHON) scripts/book-doctor.py "$(BOOK)"; \
	else \
		$(PYTHON) scripts/books.py list | while IFS= read -r slug; do \
			$(PYTHON) scripts/book-doctor.py "$$slug"; \
		done; \
	fi

env:
	@:

contents:
	@if [ "$(words $(CONTENTS_SCOPE))" -ne 1 ]; then \
		echo "usage: make contents {chap|sec|all} [check] [BOOK=<slug>]" >&2; \
		exit 2; \
	fi
	@$(PYTHON) scripts/generate-contents.py "$(CONTENTS_SCOPE)" \
		$(if $(strip $(BOOK)),--book "$(BOOK)") \
		$(if $(CHECK_REQUESTED),--check)

chap sec:
	@:

site:
	@$(PYTHON) scripts/generate-site-pages.py \
		$(if $(strip $(BOOK)),--book "$(BOOK)") \
		$(if $(CHECK_REQUESTED),--check)

config:
	@$(PYTHON) scripts/config_sync.py $(if $(CHECK_REQUESTED),--check)

generated:
	@$(PYTHON) scripts/generate-contents.py all \
		$(if $(strip $(BOOK)),--book "$(BOOK)") \
		$(if $(CHECK_REQUESTED),--check)
	@$(PYTHON) scripts/generate-site-pages.py \
		$(if $(strip $(BOOK)),--book "$(BOOK)") \
		$(if $(CHECK_REQUESTED),--check)

new-book:
	@test -n "$(strip $(SLUG))" || \
		(echo "error: SLUG is required" >&2; exit 2)
	@test -n "$(strip $(TITLE))" || \
		(echo "error: TITLE is required" >&2; exit 2)
	@PYTHON="$(PYTHON)" ./scripts/new-book.sh "$(SLUG)" "$(TITLE)"

publish:
	@test -n "$(BOOK)" || \
		(echo "error: BOOK is required \
		(example: make publish BOOK=mathematical-analysis-1)" >&2; \
		exit 2)
	@./scripts/publish-release.sh "$(BOOK)"

image-pin:
	@test -n "$(DIGEST)" || \
		(echo "error: DIGEST is required" >&2; exit 2)
	@$(PYTHON) scripts/check-image-reference.py --set-digest "$(DIGEST)"
