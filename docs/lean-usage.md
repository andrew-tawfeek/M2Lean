# Lean package and verifier usage

The repository root is the Lake package root, with Lean sources under
`lean/`. It uses Lean 4.32.0 and pins mathlib to commit
`81a5d257c8e410db227a6665ed08f64fea08e997` through the checked-in root Lake
manifest.

## Build from this repository

On Debian or WSL:

```sh
bash scripts/lean-build.sh
bash scripts/lean-build.sh m2lean-check
```

The helper mirrors the source package into `$HOME/m2lean-lean` because native
Linux builds are substantially faster than builds on a mounted Windows file
system. The repository root remains the source of record.

## Pin as a downstream Lake dependency

For a tagged release:

```toml
[[require]]
name = "m2lean"
git = "https://github.com/andrew-tawfeek/M2Lean.git"
rev = "v0.2.0"
```

For archival reproduction, replace the tag with the full release commit. A
minimal module can import only the proof layers it uses:

```lean
import M2Lean.Certificates.Soundness
import M2Lean.Groebner.Sound

#check M2Lean.checkIdentity_sound
#check M2Lean.checkMembership_sound
#check M2Lean.checkGroebner_sound
#check M2Lean.checkNonMembership_sound
```

Targeted imports avoid compiling case-study modules a downstream project does
not use. The project has not yet been published to Reservoir; use the pinned
Git dependency until a Reservoir release is separately announced.

## Runtime verifier

Build the executable, then run:

```sh
$HOME/m2lean-lean/.lake/build/bin/m2lean-check input.json
$HOME/m2lean-lean/.lake/build/bin/m2lean-check input.json -o report.json
```

Exit status `0` means every claim was accepted. Structural/parse failures and
mathematical rejection use nonzero statuses and diagnostic classes documented
in `protocol/SPEC.md`. Reports echo validated input provenance, but provenance
does not affect assurance.

A `proved` result says a soundness theorem exists for that checker and order;
the report is not a proof object. To establish a concrete theorem, import or
generate Lean data, prove checker acceptance (usually with kernel reduction),
and apply the corresponding soundness theorem as the case studies do.

## Optional live tactic

```lean
import M2Lean.Tactic.Macaulay2

example : toMv 2 f ∈ spanOf 2 generators := by
  macaulay2
```

The tactic currently handles a restricted class of ground sparse-polynomial
membership goals. It launches `M2` while elaborating, receives cofactors, and
closes the goal by applying Lean's checked membership machinery. Macaulay2 is
still untrusted, but it must be installed and on `PATH` for the tactic call.

## Generated data

`scripts/json2lean.py` converts selected JSON documents to literal Lean data
modules. The release gate regenerates four modules and eleven JSON documents,
verifies their raw-byte digests against the committed SHA-256 ledger, and only
then builds the theorem files. Generated syntax has no assurance until Lean
elaborates it and the kernel checks the resulting declarations.
