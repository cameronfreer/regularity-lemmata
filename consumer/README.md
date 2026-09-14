# External consumer fixture

A separate Lake package that depends on this library **by Git at a full commit**, importing only
advertised entry points: the `RegularityLemmata.Kernel` facade and the modules `Finite.Hedge`
and `Finite.DensityBuckets` directly. It is the release checklist's proof that a downstream
project can build against a published commit with the library's own Mathlib pin, and it is not
a target of the main package (nothing here is imported by the library or built by its gate).

`lakefile.toml` pins `rev` to the release candidate's full SHA; `lake-manifest.json` records the resolved
full SHA. The release checklist rebuilds the fixture against the actual release commit, from a
copy outside the repository:

```
# SCRATCH_DIR must be a disk-backed directory; the build downloads the mathlib cache (several GB)
: "${SCRATCH_DIR:?Set SCRATCH_DIR to a disk-backed directory}"
dir=$(mktemp -d -p "$SCRATCH_DIR" consumer-check-XXXX) && cp -r consumer/. "$dir" && cd "$dir"
sed -i 's/^rev = .*/rev = "<release commit, full SHA>"/' lakefile.toml
rm -f lake-manifest.json && lake update && lake exe cache get && lake build
python3 -c "import json;print([p['rev'] for p in json.load(open('lake-manifest.json'))['packages'] if p['name']=='RegularityLemmata'])"
```

`SCRATCH_DIR` is required: point it at a directory on a disk with room for the dependency
cache. A RAM-backed temporary directory is not suitable for a build of this size.

The printed revision must be the release commit's full SHA. Builds are large (the library's
imported modules are compiled from source; mathlib comes from the cache), so keep them outside
the repository.
