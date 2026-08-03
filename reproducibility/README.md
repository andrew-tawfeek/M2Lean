# Reproducibility records

`manifest.json` is the static, in-tree reproducibility manifest. It identifies
the release environment, dependency revisions, release commands, expected
outcomes, and SHA-256 hashes of every generated certificate and checked-in
Lean data module. Once tagged, this file is immutable.

`benchmark.schema.json` defines the machine-readable output of:

```sh
bash scripts/bench.sh --output reproducibility/benchmarks/local.json
```

Benchmark files record the source commit and dirty state, commands, raw
stdout/stderr, wall time, peak resident memory, exit status, and timeout state.
Only a record produced from the clean release commit is evidence for the
paper's table. Local exploratory results should not be committed.

The release benchmark must be written outside the checkout so that recording
it does not dirty the tagged tree. It is attached to the GitHub release and
archive rather than committed back into the release tag.

`release-record.schema.json` defines a second, external record generated only
after the annotated tag and permanent archive exist. This post-tag record
binds the tag object, commit and tree, static-manifest hash, clean benchmark
hash, archive permalink/DOI, and any additional release-asset hashes.

The release gate is:

```sh
bash scripts/test-all.sh
```

## Post-tag identity record

The `releaseCommit`, `archive`, and `paperBenchmarkRecord` fields in the
tagged `manifest.json` remain null by design. Filling them after tagging would
change the commit they are meant to identify. Instead:

1. Create the annotated tag from a clean commit.
2. From that exact clean tag commit, write the full benchmark JSON outside the
   worktree.
3. Create the permanent archive and obtain its permalink or DOI.
4. Generate the external record, also outside the worktree:

```sh
python scripts/release-record.py \
  --tag v0.2.0 \
  --benchmark /release-evidence/paper-v0.2.0.json \
  --archive-permalink https://doi.org/10.5281/zenodo.RECORD \
  --archive-doi 10.5281/zenodo.RECORD \
  --asset /release-evidence/M2Lean-v0.2.0.tar.gz \
  --output /release-evidence/m2lean-v0.2.0-release-record.json
```

The generator refuses dirty worktrees, lightweight tags, a tag not selecting
`HEAD`, benchmark records from another or dirty commit, in-worktree output,
duplicate asset names, and overwrites. Publish the benchmark and generated
record as GitHub release/archive assets. The record itself is not committed
back into `v0.2.0`.

## Verifying hashes

On Linux:

```sh
sha256sum -c reproducibility/generated.sha256
```

`generated.sha256` is an exact, sorted view of the same set listed in the JSON
manifest and provides a standard-tool check. The release gate uses
`scripts/check-generated.py` to reject malformed, duplicate, unsafe,
case-conflicting, symlinked, missing, or unlisted paths; it also computes raw
digests without Git or external Python packages. `scripts/test-all.sh` runs
that check before and after regeneration, so it verifies both the shipped
files and producer determinism even in an unpacked source archive.
