# Contributing to M2Lean

M2Lean connects Macaulay2 (computation) and Lean 4 (formal verification)
through a versioned interchange protocol. Before contributing, read
`README.md` (the project vision) and `protocol/SPEC.md` (the normative
protocol specification).

## Repository layout

- `protocol/` — the versioned interchange format: specification, JSON
  schema, and cross-language fixtures. The spec is normative; both
  implementations must follow it.
- `lean/` — the Lean 4 package: protocol parsing, semantics, certificate
  checkers with soundness theorems, and examples.
- `m2/` — the Macaulay2 bridge package: exporters, certificate
  generation, and tests.
- `examples/` — end-to-end worked examples (each one produces protocol
  documents in `m2/` and checks them in `lean/`).
- `scripts/` — build, test, and pipeline automation.
- `docs/` — architecture, trust model, roadmap, and architecture
  decision records (`docs/decisions/`).
- `paper/` — the preprint sources.

## Ground rules

1. **Protocol changes require an ADR.** Any change that alters the
   mathematical meaning of a protocol document needs a short decision
   record in `docs/decisions/` and a version bump discussion.
2. **No trust expansion.** Lean must never accept a claim merely because
   M2 said so. New checkers need a soundness theorem (or an explicit,
   documented placement at a lower assurance level).
3. **No `sorry` in accepted claims.** Files under
   `lean/M2Lean/Certificates/` and their dependencies must be
   `sorry`-free and must not add axioms.
4. **Fixtures are adversarial.** Every new claim kind needs at least one
   valid fixture and one deliberately corrupted fixture that the checker
   must reject.
5. **Assurance levels are visible.** "Computed", "checked", and
   "formally proved" are different statuses; do not conflate them in
   code, docs, or output.

## Workflow

Work on feature branches; merge to `master` via pull request. Run
`scripts/test-all.sh` (WSL/Linux) before opening a PR.
