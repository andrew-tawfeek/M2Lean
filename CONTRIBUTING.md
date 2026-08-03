# Contributing to M2Lean

M2Lean connects untrusted Macaulay2 computations to executable and, for
selected claims, kernel-checked Lean verification. Read the
[`protocol specification`](protocol/SPEC.md),
[`architecture`](docs/architecture.md), and
[`trust model`](docs/trust-model.md) before changing certificate semantics.

## Repository layout

- `protocol/`: normative specification, JSON schema, and shared fixtures.
- `lean/`: parser, semantics, checkers, soundness proofs, executable, and
  theorem examples.
- `m2/`: Macaulay2 producer package and tests.
- `examples/`: source computations and generated certificate documents.
- `scripts/`: release, regeneration, verification, and benchmark automation.
- `reproducibility/`: pinned environment and release evidence.
- `docs/`: usage, architecture decisions, trust model, and release notes.
- `paper/`: the separately licensed preprint.

## Non-negotiable rules

1. **Protocol changes require an ADR.** Any change to the meaning or required
   shape of a document needs an entry in `docs/decisions/` and an explicit
   compatibility decision.
2. **Do not expand trust implicitly.** Macaulay2, transport, generated text,
   and certificate contents remain untrusted. A claim is `proved` only when
   checker acceptance is connected to its advertised mathematical statement
   by a kernel-checked theorem.
3. **Keep theorem-bearing code `sorry`-free.** New soundness and example
   theorems may not add axioms. The axiom audit must remain limited to
   `propext`, `Classical.choice`, and `Quot.sound`.
4. **Test rejection behavior.** Every new claim or validation rule needs a
   valid fixture and targeted corrupt fixtures. Tests should assert the
   diagnostic class as well as failure.
5. **Name assurance levels precisely.** Runtime acceptance, a formal
   soundness theorem, and a theorem instantiated in a case study are distinct
   facts.
6. **Regeneration must be deterministic.** Generated JSON and `*Data.lean`
   files must match the committed SHA-256 ledger byte for byte.

## Development workflow

Use a feature branch and keep changes narrowly scoped. On Debian/WSL, run:

```sh
bash scripts/test-all.sh
```

This is the release gate: it verifies the shipped artifacts, regenerates all
15 outputs, checks their raw-byte digests against the committed SHA-256
ledger, builds the Lean package and verifier, runs valid and adversarial
fixtures, builds theorem files, and performs the axiom audit. When working on
one layer, the narrower commands are:

```sh
bash scripts/regenerate-all.sh
bash scripts/lean-build.sh
bash scripts/lean-build.sh m2lean-check
M2 --script m2/tests/smoke.m2
```

Before submitting a change:

- add or update fixtures and documentation;
- run `git diff --check`;
- run the full release gate from a clean worktree;
- describe any assurance-level or compatibility change explicitly;
- update `CHANGELOG.md` under `Unreleased` for user-visible changes.

Do not commit local build trees, transient reports, or private benchmark
paths. Benchmark records intended for a release belong under
`reproducibility/benchmarks/` and must validate against the checked-in schema.

## Protocol and proof review

Protocol changes should be reviewed from both producer and consumer sides.
The normative mathematical definition belongs in `protocol/SPEC.md`; the JSON
schema is only a structural pre-filter. A checker change is incomplete until
its advertised assurance level, soundness statement, negative fixtures, and
trust-model documentation agree.

Changes to `lean/M2Lean/Protocol/Sparse.lean`,
`lean/M2Lean/Semantics/Interp.lean`, or theorem statements in the soundness
layer deserve particular scrutiny because a mistaken definition can change
the proposition established by an accepted certificate.

## Documentation and releases

Keep examples copy-pasteable and pin all release dependencies. Do not claim a
tag, DOI, arXiv identifier, Reservoir release, or Macaulay2 distribution
status until it exists and is independently reachable. The release procedure
is summarized in [`docs/releases/v0.2.0.md`](docs/releases/v0.2.0.md) and the
environment of record is [`reproducibility/manifest.json`](reproducibility/manifest.json).
