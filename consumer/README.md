# External consumer fixture

A separate Lake package that depends on this library **by Git at a full commit**, importing only
advertised entry points: the `RegularityLemmata.Kernel` facade and the modules `Finite.Hedge`
and `Finite.DensityBuckets` directly. It is the release checklist's proof that a downstream
project can build against a published commit with the library's own Mathlib pin, and it is not
a target of the main package (nothing here is imported by the library or built by its gate).

`lakefile.toml` pins `rev` to the release candidate; `lake-manifest.json` records the resolved
full SHA. The release checklist rebuilds the fixture against the actual release commit, from a
copy outside the repository:

```
cp -r consumer /home/freer/scratch/tmp/consumer-check && cd /home/freer/scratch/tmp/consumer-check
sed -i 's/^rev = .*/rev = "<release commit>"/' lakefile.toml
rm -f lake-manifest.json && lake update && lake exe cache get && lake build
python3 -c "import json;print([p['rev'] for p in json.load(open('lake-manifest.json'))['packages'] if p['name']=='RegularityLemmata'])"
```

The printed revision must be the release commit's full SHA. Builds are large (the library's
imported modules are compiled from source; Mathlib comes from the cache), so keep them outside
the repository.
