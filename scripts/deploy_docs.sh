#!/usr/bin/env bash
# Copyright (c) 2026 Cameron Freer. All rights reserved.
# SPDX-License-Identifier: Apache-2.0
#
# Lay out one version of the generated documentation inside a checkout of the `gh-pages`
# branch, within the GitHub Pages budget (1 GB per published site).
#
#   docs/<version>/           the library's pages, search index, and page assets (~40 MB)
#   docs/deps/<deps-key>/     the dependency pages (Mathlib, Init, Lean, Std, ...; ~530 MB),
#                             published once per dependency pin and shared by every version
#   docs/latest/index.html    a redirect to the newest version, never a copy
#   docs/index.html           the list of published versions
#
# Links from the library's pages to dependency pages are rewritten to the shared tree. A
# version directory is replaced whole, so no obsolete page survives a redeploy. The script
# fails if the published tree would exceed SIZE_LIMIT_BYTES; when the dependency pin changes,
# the previous `deps/<key>` tree (and the versions that link into it) must be pruned by hand
# before the new one fits.
#
# Environment:
#   DOCS_SRC          doc-gen4 output directory (docbuild/.lake/build/doc)
#   DOCS_VERSION      version name, e.g. v0.11.0 (validated: [A-Za-z0-9._-], not latest/deps)
#   DEPS_KEY          dependency-pin key, e.g. the Mathlib revision's first 12 characters
#   PAGES_DIR         checkout of the gh-pages branch
#   SIZE_LIMIT_BYTES  optional, default 900000000
set -euo pipefail

: "${DOCS_SRC:?}" "${DOCS_VERSION:?}" "${DEPS_KEY:?}" "${PAGES_DIR:?}"
SIZE_LIMIT_BYTES="${SIZE_LIMIT_BYTES:-900000000}"

case "$DOCS_VERSION" in
  latest|deps|.*|*/*|*..*) echo "deploy_docs: refusing version name '$DOCS_VERSION'" >&2; exit 1 ;;
esac
[[ "$DOCS_VERSION" =~ ^[A-Za-z0-9._-]+$ ]] || { echo "deploy_docs: invalid version name" >&2; exit 1; }
[[ "$DEPS_KEY" =~ ^[A-Za-z0-9._-]+$ ]] || { echo "deploy_docs: invalid deps key" >&2; exit 1; }
[ -d "$DOCS_SRC/RegularityLemmata" ] || { echo "deploy_docs: no library pages under $DOCS_SRC" >&2; exit 1; }

LIB_DIRS=(RegularityLemmata declarations find)
docs="$PAGES_DIR/docs"
ver="$docs/$DOCS_VERSION"
deps="$docs/deps/$DEPS_KEY"
mkdir -p "$docs"

# Dependency directories: every top-level directory of the build that is not the library's own.
dep_names=()
for d in "$DOCS_SRC"/*/; do
  n=$(basename "$d")
  case " ${LIB_DIRS[*]} " in *" $n "*) continue ;; esac
  dep_names+=("$n")
done

# 1. The shared dependency tree, published once per key.
if [ ! -d "$deps" ]; then
  mkdir -p "$deps"
  for n in "${dep_names[@]}"; do cp -r "$DOCS_SRC/$n" "$deps/$n"; done
  find "$DOCS_SRC" -maxdepth 1 -type f -exec cp {} "$deps/" \;
  [ -d "$DOCS_SRC/declarations" ] && cp -r "$DOCS_SRC/declarations" "$deps/declarations"
  echo "deploy_docs: published dependency pages under deps/$DEPS_KEY"
else
  echo "deploy_docs: dependency pages deps/$DEPS_KEY already published; reused"
fi

# 2. The version directory, replaced whole.
rm -rf "$ver"; mkdir -p "$ver"
for n in "${LIB_DIRS[@]}"; do [ -d "$DOCS_SRC/$n" ] && cp -r "$DOCS_SRC/$n" "$ver/$n"; done
find "$DOCS_SRC" -maxdepth 1 -type f -exec cp {} "$ver/" \;

# 3. Rewrite links from the version's pages into the shared dependency tree.
alt=$(IFS='|'; echo "${dep_names[*]}")
find "$ver" -name '*.html' -print0 | xargs -0 perl -pi -e \
  's{(href|src)="((?:\.\./)*)\./?('"$alt"')/}{$1="$2../deps/'"$DEPS_KEY"'/$3/}g'

# 4. `latest` as a redirect, and the version index.
mkdir -p "$docs/latest"
cat > "$docs/latest/index.html" <<HTML
<!DOCTYPE html><html><head><meta charset="utf-8">
<meta http-equiv="refresh" content="0; url=../$DOCS_VERSION/">
<link rel="canonical" href="../$DOCS_VERSION/"><title>RegularityLemmata docs</title></head>
<body><a href="../$DOCS_VERSION/">RegularityLemmata documentation, $DOCS_VERSION</a></body></html>
HTML
{
  echo '<!DOCTYPE html><html><head><meta charset="utf-8"><title>RegularityLemmata docs</title></head><body>'
  echo '<h1>RegularityLemmata generated documentation</h1><ul>'
  for d in "$docs"/*/; do
    n=$(basename "$d"); case "$n" in deps|latest) continue ;; esac
    echo "<li><a href=\"$n/\">$n</a></li>"
  done
  echo '</ul><p><a href="latest/">latest</a> redirects to the newest release.</p></body></html>'
} > "$docs/index.html"

# 5. Budget.
size=$(du -sb "$docs" | cut -f1)
echo "deploy_docs: published tree is $size bytes (limit $SIZE_LIMIT_BYTES); versions: $(ls "$docs" | grep -v -x -e deps -e latest -e index.html | tr '\n' ' '); deps keys: $(ls "$docs/deps" | tr '\n' ' ')"
if [ "$size" -gt "$SIZE_LIMIT_BYTES" ]; then
  echo "deploy_docs: published tree exceeds the budget; prune old versions or an old deps tree" >&2
  exit 1
fi
