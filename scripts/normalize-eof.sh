#!/usr/bin/env bash
set -euo pipefail

mode="format"
collapse_blank_lines=0
while [[ "${1:-}" == --* ]]; do
  case "$1" in
  --check) mode="check" ;;
  --collapse-blank-lines) collapse_blank_lines=1 ;;
  *)
    echo "usage: $0 [--check] [--collapse-blank-lines] [FILE...]" >&2
    exit 2
    ;;
  esac
  shift
done

files=("$@")
if [[ "${#files[@]}" -eq 0 ]]; then
  while IFS= read -r -d '' file; do
    [[ -f "$file" ]] || continue
    grep -Iq '' "$file" || continue
    files+=("$file")
  done < <(git ls-files -z --cached)
fi

status=0
for file in "${files[@]}"; do
  if [[ "$mode" == "check" ]]; then
    if ! perl -0777 -sne '
      $normalized = $_;
      $normalized =~ s/\n(?:[ \t]*\n){2,}/\n\n/g if $collapse;
      $normalized =~ s/[\t\r\n ]*\z/\n/;
      exit($normalized eq $_ ? 0 : 1);
    ' -- -collapse="$collapse_blank_lines" "$file"; then
      echo "needs whitespace normalization: $file" >&2
      status=1
    fi
  else
    perl -0777 -spi -e '
      s/\n(?:[ \t]*\n){2,}/\n\n/g if $collapse;
      s/[\t\r\n ]*\z/\n/;
    ' -- -collapse="$collapse_blank_lines" "$file"
  fi
done

exit "$status"
