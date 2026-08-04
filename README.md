# M2Lean

[![CI](https://github.com/andrew-tawfeek/M2Lean/actions/workflows/ci.yml/badge.svg)](https://github.com/andrew-tawfeek/M2Lean/actions/workflows/ci.yml)
[![License: MIT](https://img.shields.io/badge/software%20license-MIT-blue.svg)](LICENSE)

M2Lean is a certificate-based interface between
[Macaulay2](https://macaulay2.com/) and [Lean 4](https://lean-lang.org/).
Macaulay2 discovers algebraic data and emits explicit evidence; a Lean
executable validates that evidence, and selected checker results can be
instantiated as theorems checked by Lean's kernel.

This repository contains M2Lean 0.2.0 and protocol 0.2.0. The public
interface is still experimental: pin the annotated tag `v0.2.0` or the exact
evaluated commit `49f18427957e3a7960971d43c14ea4ce6991e472` instead of following
the default branch.

## Release and archival evidence

The [v0.2.0 release](https://github.com/andrew-tawfeek/M2Lean/releases/tag/v0.2.0)
contains the [raw paper benchmark](https://github.com/andrew-tawfeek/M2Lean/releases/download/v0.2.0/paper-v0.2.0.json),
the [post-tag identity record](https://github.com/andrew-tawfeek/M2Lean/releases/download/v0.2.0/m2lean-v0.2.0-release-record.json),
and the deterministic [source archive](https://github.com/andrew-tawfeek/M2Lean/releases/download/v0.2.0/M2Lean-v0.2.0.tar.gz)
with its [checksum](https://github.com/andrew-tawfeek/M2Lean/releases/download/v0.2.0/M2Lean-v0.2.0.tar.gz.sha256).
The [tag CI run](https://github.com/andrew-tawfeek/M2Lean/actions/runs/30874626074)
completed both the normal release gate and a no-cache clean-room build.

[Software Heritage preserves the tagged Git source](https://archive.softwareheritage.org/swh:1:dir:8354556bb3be6e767b97774ca17f501efd6fbefd;origin=https://github.com/andrew-tawfeek/M2Lean;visit=swh:1:snp:3287142ae38071a07632f96b5887f3284112e764;anchor=swh:1:rel:b14fe2261b9eca1a816b9590ee6edda3d091feb2),
including annotated release SWHID
`swh:1:rel:b14fe2261b9eca1a816b9590ee6edda3d091feb2`. Ordinary Software
Heritage Git ingestion does not preserve separately attached GitHub release
assets; the benchmark, source archive, and checksum file are instead bound to
the tagged commit by the post-tag identity record.

## What is certified

The interchange format covers rational and prime fields, multivariate
polynomial rings with Lex or GRevLex order, ideals, matrices, graded free
modules, and seven claim kinds.

| Claim | Runtime check | Checker soundness theorem in Lean |
|---|---|---|
| Polynomial identity | yes | yes |
| Ideal membership | yes | yes |
| Span inclusion | yes | yes |
| Gröbner basis, GRevLex | yes | yes |
| Gröbner basis, Lex | yes | not yet |
| Non-membership, GRevLex | yes | yes |
| Non-membership, Lex | yes | not yet |
| Chain complex | yes | yes, for composition being zero |
| Graded complex | yes | not yet |

The command-line verifier labels claims `proved` only when the relevant
checker has a soundness theorem. That label describes the library result;
the JSON report is not itself a Lean proof object. A theorem file must still
instantiate the soundness theorem and be elaborated by Lean. See
[`docs/trust-model.md`](docs/trust-model.md) for the exact assurance and
trust boundaries.

## Quick start

The primary reproducibility environment is Debian 13 (including WSL2),
Macaulay2 1.24.11, Lean 4.32.0, and the mathlib revision pinned in
[`lake-manifest.json`](lake-manifest.json). The scripts require
`bash`, `git`, `rsync`, `python3`, `python3-jsonschema`, and `curl`;
Macaulay2 must be available as `M2`.

The Macaulay2 package load, smoke, documentation-check, installation, and
fresh installed-package workflows have also been tested with the official
Macaulay2 1.26.06 Debian packages. Exact compatibility-test provenance is in
[`reproducibility/macaulay2-compatibility.md`](reproducibility/macaulay2-compatibility.md).

```sh
git clone https://github.com/andrew-tawfeek/M2Lean.git
cd M2Lean
bash scripts/lean-build.sh m2lean-check
bash scripts/test-all.sh
```

`test-all.sh` verifies the 15 shipped generated files, regenerates them, checks
their raw-byte digests against the committed SHA-256 ledger, verifies valid
and adversarial protocol documents, builds the theorem files, and runs the
axiom audit.

To inspect one document directly:

```sh
$HOME/m2lean-lean/.lake/build/bin/m2lean-check \
  examples/flagship/flagship.json
```

The process exits `0` only when the document is structurally valid and every
claim is accepted. Use `-o report.json` to retain the verification report.

## From Macaulay2

Load the package directly from a checkout:

```macaulay2
loadPackage("M2Lean", FileName => "m2/M2Lean.m2")

R = QQ[x,y];
I = ideal(x+y, x-y);
D = newM2LeanDocument "demo";
membershipClaim(D, "mem1", x^3 + y^3, I);
writeM2LeanDocument(D, "demo.json")
```

If `m2lean-check` is on `PATH`, or `M2LEAN_CHECK` names the executable,
Macaulay2 can request verification in the same session:

```macaulay2
verifyWithLean D
```

For a user-local installation, run this once from the repository root:

```macaulay2
installPackage("M2Lean", FileName => "m2/M2Lean.m2")
```

In a fresh session the installed form is:

```macaulay2
loadPackage "M2Lean"
```

Package installation, supported versions, and exported functions are
documented in [`docs/macaulay2-usage.md`](docs/macaulay2-usage.md).

## From Lean

The repository root is the Lake package root; Lean source files live under
`lean/`. A downstream Lake project can pin the 0.2.0 tag as follows:

```toml
[[require]]
name = "m2lean"
git = "https://github.com/andrew-tawfeek/M2Lean.git"
rev = "v0.2.0"
```

Use a full commit hash instead of `v0.2.0` when reproducing a particular
artifact. A minimal downstream file is:

```lean
import M2Lean.Certificates.Soundness
import M2Lean.Groebner.Sound

#check M2Lean.checkMembership_sound
#check M2Lean.checkGroebner_sound
```

The optional `by macaulay2` tactic invokes a live `M2` process during
elaboration. Certificate checking and the theorem files do not require a
trusted or live Macaulay2 process. More detail is in
[`docs/lean-usage.md`](docs/lean-usage.md).

## Case studies

- **Twisted cubic:** Macaulay2 supplies membership, Gröbner, complex, and
  unit-ideal evidence. Lean proves the unit-ideal conclusion for the two
  ideals, hence their affine zero sets have no common point.
- **Alpöge–Fable Jacobian example:** Lean verifies the constant determinant,
  applies the membership soundness theorem to all nine exported certificates,
  and proves a rational collision for the announced three-dimensional map. It
  refutes both the explicitly defined rational-point injectivity formulation
  and a polynomial-map inverse formulation over `ℚ`. The final
  noninjectivity step evaluates the displayed points directly, so the
  membership path remains parallel rather than a logical dependency.
- **Graph coloring:** the kernel-checked theorem is the concrete non-
  3-colorability result for the six-vertex wheel. The `K_4` and Grötzsch
  documents currently demonstrate runtime unit-ideal checking only.
- **Additional fixtures:** prime-field arithmetic, separability, toric and
  Stanley--Reisner ideals, symmetric polynomials, and polynomial identities.

## Repository map

| Path | Contents |
|---|---|
| [`protocol/`](protocol/) | Normative 0.2.0 specification, schema, and fixtures |
| [`m2/`](m2/) | Macaulay2 package and package tests |
| [`lean/`](lean/) | Lean library, verifier executable, soundness proofs, and theorem files |
| [`examples/`](examples/) | Reproducible Macaulay2 inputs and certificate documents |
| [`scripts/`](scripts/) | Regeneration, test, audit, and benchmark entry points |
| [`reproducibility/`](reproducibility/) | Environment manifest, expected hashes, and benchmark records |
| [`docs/`](docs/) | Architecture, trust model, usage, decisions, and release notes |
| [`paper/`](paper/) | Preprint source and PDF |

The normative protocol is [`protocol/SPEC.md`](protocol/SPEC.md). Protocol
changes require an architecture decision record and a compatibility review.

## Reproducibility

Run the entire release gate with:

```sh
bash scripts/test-all.sh
```

Regenerate only tracked certificates and Lean data with:

```sh
bash scripts/regenerate-all.sh
```

Record benchmarks as machine-readable JSON with:

```sh
bash scripts/bench.sh --output reproducibility/benchmarks/local.json
```

The recorded environment, expected outcomes, and authoritative artifact hashes
are in [`reproducibility/manifest.json`](reproducibility/manifest.json). The
same artifact hashes are available as the standard-tool
[`reproducibility/generated.sha256`](reproducibility/generated.sha256) ledger.
Benchmark results describe only the named machine and inputs; the project does
not yet make a scaling claim.

## Contributing and citation

Please read [`CONTRIBUTING.md`](CONTRIBUTING.md) before changing the protocol
or trusted semantics. Cite the software using [`CITATION.cff`](CITATION.cff)
and cite the paper separately when referring to the architecture or case
studies. Release history is in [`CHANGELOG.md`](CHANGELOG.md).

The software is MIT-licensed. The paper is separately licensed under
CC BY 4.0; see [`LICENSES.md`](LICENSES.md) for scope and attribution details.
