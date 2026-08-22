PYTHON ?= python3
BOOK ?=
SLUG ?=
TITLE ?=
TREE_IGNORE ?= vscode-build|build|context.tex|tree.txt|.git|.vscode|.lake|__pycache__

COMMAND_GOALS := lean readme site generated format
CHECK_REQUESTED := $(filter check,$(MAKECMDGOALS))
README_SCOPE := $(filter root books,$(MAKECMDGOALS))
CHECK_SCOPE := $(filter all source manifest proof-links,$(MAKECMDGOALS))
FORMAT_SCOPE := $(filter tex py all,$(MAKECMDGOALS))
DOCTOR_SCOPE := $(filter env books,$(MAKECMDGOALS))
STRICT_REQUESTED := $(filter strict,$(MAKECMDGOALS))

.PHONY: \
	help \
	report \
	clean \
	tree \
	format tex py \
	books \
	lean \
	test \
	check all source manifest proof-links strict \
	doctor env \
	readme root \
	site \
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
		'  make clean                                 Remove generated build output' \
		'  make tree                                  Write the local tree.txt listing' \
		'' \
		'  make format {tex|py|all} [check]           Format or check source formatting' \
		'  make books [BOOK=<slug>]                   Build all enabled books or one book' \
		'  make lean [check]                          Build Lean, or check proofs and links' \
		'' \
		'  make test                                  Run the Python test suite' \
		'  make check {manifest|source|proof-links}   Run a focused repository check' \
		'  make check all [strict]                    Run the complete validation suite' \
		'  make doctor env                            Check the development environment' \
		'  make doctor books [BOOK=<slug>]            Inspect all textbooks or one textbook' \
		'' \
		'  make readme {root|books} [check]           Regenerate or check README content' \
		'  make site [BOOK=<slug>] [check]            Regenerate or check site content' \
		'  make generated [check]                     Regenerate or check all generated content' \
		'' \
		'  make new-book SLUG=<slug> TITLE="<title>"  Scaffold and register a new textbook' \
		'  make publish BOOK=<slug>                   Publish an eligible textbook release' \
		'  make image-pin DIGEST=<sha256>             Update the pinned build image' \
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
	@./scripts/clean.sh

tree:
	@rm -f tree.txt
	@tree \
		--dirsfirst \
		-a \
		-I "$(TREE_IGNORE)" \
		> tree.txt

format:
	@if [ "$(words $(FORMAT_SCOPE))" -ne 1 ]; then \
		echo "usage: make format {tex|py|all} [check]" >&2; \
		exit 2; \
	fi
	@if [ -n "$(filter tex all,$(FORMAT_SCOPE))" ]; then \
		./scripts/format-tex.sh $(if $(CHECK_REQUESTED),--check); \
	fi
	@if [ -n "$(filter py all,$(FORMAT_SCOPE))" ]; then \
		./scripts/format-python.sh $(if $(CHECK_REQUESTED),--check); \
	fi

tex py:
	@:

books:
	@if [ -n "$(filter readme doctor,$(MAKECMDGOALS))" ]; then \
		:; \
	elif [ -n "$(strip $(BOOK))" ]; then \
		./scripts/build-book.sh "$(BOOK)"; \
	else \
		./scripts/build-all.sh; \
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
		echo "usage: make check {all|source|manifest|proof-links} [strict]" >&2; \
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

all source manifest proof-links strict:
	@:

doctor:
	@if [ "$(words $(DOCTOR_SCOPE))" -ne 1 ]; then \
		echo "usage: make doctor {env|books} [BOOK=<slug>]" >&2; \
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

readme:
	@if [ "$(words $(README_SCOPE))" -ne 1 ]; then \
		echo "usage: make readme {root|books} [check] [BOOK=<slug>]" >&2; \
		exit 2; \
	fi
	@if [ -n "$(filter root,$(README_SCOPE))" ]; then \
		$(PYTHON) scripts/generate-readme-books.py \
			--root \
			$(if $(CHECK_REQUESTED),--check); \
	else \
		$(PYTHON) scripts/generate-readme-books.py \
			--books \
			$(if $(strip $(BOOK)),--book "$(BOOK)") \
			$(if $(CHECK_REQUESTED),--check); \
	fi

root:
	@:

site:
	@$(PYTHON) scripts/generate-site-pages.py \
		$(if $(strip $(BOOK)),--book "$(BOOK)") \
		$(if $(CHECK_REQUESTED),--check)

generated:
	@$(PYTHON) scripts/generate-readme-books.py \
		--root \
		$(if $(CHECK_REQUESTED),--check)
	@$(PYTHON) scripts/generate-readme-books.py \
		--books \
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
		(example: make publish BOOK=mathematical-analysis)" >&2; \
		exit 2)
	@./scripts/publish-release.sh "$(BOOK)"

image-pin:
	@test -n "$(DIGEST)" || \
		(echo "error: DIGEST is required" >&2; exit 2)
	@$(PYTHON) scripts/check-image-reference.py --set-digest "$(DIGEST)"
