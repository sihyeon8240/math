PYTHON ?= python3
BOOK ?=
SLUG ?=
TITLE ?=
VERSION ?=
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

COMMAND_GOALS := book lean contents site generated format config
CHECK_REQUESTED := $(filter check,$(MAKECMDGOALS))
CONTENTS_SCOPE := $(filter chap sec all,$(MAKECMDGOALS))
CHECK_SCOPE := $(filter all source manifest proof-links docs,$(MAKECMDGOALS))
FORMAT_SCOPE := $(filter tex py sh all,$(MAKECMDGOALS))
DOCTOR_SCOPE := $(filter env book,$(MAKECMDGOALS))
CLEAN_SCOPE := $(filter build source cache,$(MAKECMDGOALS))
CACHE_SCOPE := $(filter lake tex ruff py all,$(MAKECMDGOALS))
BOOK_ACTION := $(filter new release,$(MAKECMDGOALS))
IMAGE_ACTION := $(filter pin build run,$(MAKECMDGOALS))
override CMD := $(value CMD)
export IMAGE CMD

ifneq ($(filter image,$(MAKECMDGOALS)),)
ifneq ($(filter-out image pin build run,$(MAKECMDGOALS)),)
$(error usage: make image {pin|build|run})
endif
endif

STRICT_REQUESTED := $(filter strict,$(MAKECMDGOALS))

.PHONY: \
	help report tree \
	clean build source cache lake ruff all \
	book new release \
	contents chap sec \
	image pin run \
	test \
	check manifest proof-links docs strict \
	lean \
	format tex py sh \
	doctor env \
	config site generated

help:
	@printf '%s\n' \
		'Textbook repository commands:' \
		'' \
		'Maintenance:' \
		'  make help                                         Show this help' \
		'  make report                                       Print an informational repository report' \
		'  make tree                                         Write the local tree.txt listing' \
		'  make clean {build|source}                         Remove build output or source artifacts' \
		'  make clean cache {lake|tex|ruff|py|all}           Remove selected local caches' \
		'' \
		'Books:' \
		'  make book [BOOK=<slug>]                           Build all enabled books or one book' \
		'  make book [BOOK=<slug>] check [strict]            Build and check selected books' \
		'  make book new SLUG=<slug> TITLE="<title>"         Scaffold and register a textbook' \
		'  make book release BOOK=<slug> VERSION=<version>   Prepare a release for review' \
		'  make contents {chap|sec|all} [check]              Regenerate or check LaTeX assembly' \
		'' \
		'Images and environment:' \
		'  make image build [IMAGE=<tag>]                    Build a local development image' \
		'  make image run [IMAGE=<ref>] [CMD="<command>"]    Open a shell or run a container command' \
		'  make image pin DIGEST=<sha256>                    Automation/recovery: pin a tested image' \
		'' \
		'Validation and formatting:' \
		'  make test                                         Run the Python test suite' \
		'  make check {manifest|source|proof-links|docs}     Run a focused repository check' \
		'  make check all [strict]                           Run Lean and LaTeX validation' \
		'  make lean [check]                                 Build Lean, or check proofs and links' \
		'  make format {tex|py|sh|all} [check]               Format or check source formatting' \
		'  make doctor env                                   Check the development environment' \
		'  make doctor book [BOOK=<slug>]                    Inspect all textbooks or one textbook' \
		'' \
		'Generated content:' \
		'  make config [check]                               Synchronize or check shared configuration' \
		'  make site [BOOK=<slug>] [check]                   Regenerate or check site content' \
		'  make generated [check]                            Regenerate or check all generated content' \
		'' \
		'Variables:' \
		'  BOOK=<slug>             Select one registered textbook' \
		'  SLUG=<slug>             Set the slug for make book new' \
		'  TITLE=<title>           Set the title for make book new' \
		'  VERSION=<version>       Set the version for make book release' \
		'  IMAGE=<ref>             Override the image to build or run' \
		'  CMD=<command>           Run a shell command with make image run' \
		'  DIGEST=<sha256>         Pin a tested image with make image pin' \
		'  BOOK_BUILD_JOBS=<n>     Limit parallel bulk builds' \
		'  PYTHON=<command>        Override the Python interpreter' \
		'  TREE_IGNORE=<pattern>   Customize exclusions for make tree' \
		'' \
		'See README.md and docs/CONTRIBUTING.md for details.'

report:
	@$(PYTHON) scripts/repository-report.py

tree:
	@rm -f tree.txt
	@tree \
		--dirsfirst \
		-a \
		-I "$(TREE_IGNORE)" \
		> tree.txt

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

book:
	@if [ "$(words $(BOOK_ACTION))" -gt 1 ] || \
		{ [ -n "$(BOOK_ACTION)" ] && [ -n "$(filter check strict doctor,$(MAKECMDGOALS))" ]; }; then \
		echo "usage: make book [new|release] (check/strict apply only to builds)" >&2; \
		exit 2; \
	fi
	@if [ -n "$(filter doctor,$(MAKECMDGOALS))" ]; then \
		:; \
	elif [ "$(BOOK_ACTION)" = "new" ]; then \
		test -n "$$SLUG" && test -n "$$TITLE" || \
			{ echo 'usage: make book new SLUG=<slug> TITLE="<title>"' >&2; exit 2; }; \
		PYTHON="$(PYTHON)" ./scripts/new-book.sh "$$SLUG" "$$TITLE"; \
	elif [ "$(BOOK_ACTION)" = "release" ]; then \
		test -n "$$BOOK" && test -n "$$VERSION" || \
			{ echo 'usage: make book release BOOK=<slug> VERSION=<version>' >&2; exit 2; }; \
		$(PYTHON) scripts/releases.py prepare --book "$$BOOK" --version "$$VERSION"; \
	elif [ -n "$(STRICT_REQUESTED)" ] && [ -z "$(CHECK_REQUESTED)" ]; then \
		printf '%s\n' \
			"error: strict requires check for a book build" \
			"usage: make book [BOOK=<slug>]" \
			"usage: make book [BOOK=<slug>] check [strict]" >&2; \
		exit 2; \
	elif [ -n "$(strip $(BOOK))" ]; then \
		./scripts/build-book.sh "$(BOOK)" || exit $$?; \
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

new release:
	@test -n "$(filter book,$(MAKECMDGOALS))" || \
		{ echo "usage: make book $@" >&2; exit 2; }

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

image:
	@if [ "$(words $(IMAGE_ACTION))" -ne 1 ]; then \
		echo "usage: make image {pin|build|run}" >&2; \
		exit 2; \
	fi
	@if [ "$(IMAGE_ACTION)" = "pin" ]; then \
		test -n "$(DIGEST)" || { echo "error: DIGEST is required" >&2; exit 2; }; \
		$(PYTHON) scripts/check-image-reference.py --set-digest "$(DIGEST)"; \
	elif [ "$(IMAGE_ACTION)" = "build" ]; then \
		./scripts/build-image.sh; \
	else \
		./scripts/run-container.sh; \
	fi

pin run:
	@test -n "$(filter image,$(MAKECMDGOALS))" || \
		{ echo "usage: make image $@" >&2; exit 2; }

test:
	@$(PYTHON) -m unittest discover -s tests -p 'test_*.py' -v

check:
	@if [ -z "$(filter $(COMMAND_GOALS),$(MAKECMDGOALS))" ] && \
		[ "$(words $(CHECK_SCOPE))" -ne 1 ]; then \
		printf '%s\n' \
			"usage: make check {manifest|source|proof-links|docs}" \
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
			docs) \
				$(PYTHON) scripts/check-docs.py; \
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

manifest proof-links docs strict:
	@:

lean:
	@if [ -n "$(CHECK_REQUESTED)" ]; then \
		./scripts/check-lean.sh; \
	else \
		cd lean && lake build; \
	fi

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

doctor:
	@if [ "$(words $(DOCTOR_SCOPE))" -ne 1 ]; then \
		printf '%s\n' \
			"usage: make doctor env" \
			"usage: make doctor book [BOOK=<slug>]" >&2; \
		exit 2; \
	fi
	@if [ -n "$(filter env,$(DOCTOR_SCOPE))" ]; then \
		if [ -n "$(strip $(BOOK))" ]; then \
			echo "error: BOOK is only valid with 'make doctor book'" >&2; \
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

config:
	@$(PYTHON) scripts/config_sync.py $(if $(CHECK_REQUESTED),--check)

site:
	@$(PYTHON) scripts/generate-site-pages.py \
		$(if $(strip $(BOOK)),--book "$(BOOK)") \
		$(if $(CHECK_REQUESTED),--check)

generated:
	@$(PYTHON) scripts/generate-contents.py all \
		$(if $(strip $(BOOK)),--book "$(BOOK)") \
		$(if $(CHECK_REQUESTED),--check)
	@$(PYTHON) scripts/generate-site-pages.py \
		$(if $(strip $(BOOK)),--book "$(BOOK)") \
		$(if $(CHECK_REQUESTED),--check)
