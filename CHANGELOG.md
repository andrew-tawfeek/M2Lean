# Changelog

All notable user-facing changes are recorded here. M2Lean follows semantic
versioning for the software package and versions its interchange protocol
separately.

## Unreleased

- No user-facing changes yet.

## 0.2.0 - 2026-08-03

### Added

- `NonMembership` certificates tied to a Gröbner claim in the same document.
- Prime-field execution and soundness over verified prime characteristics.
- A formal GRevLex monomial order, executable comparator bridge, Buchberger
  criterion, and kernel-checked Gröbner/non-membership soundness.
- Graded-complex runtime validation for dimensions, twists, homogeneity, and
  consecutive composition.
- The `m2lean-check` CLI, Macaulay2 `verifyWithLean` integration, and the
  experimental `by macaulay2` tactic.
- Twisted-cubic, Alpöge–Fable Jacobian, graph-coloring, separability,
  finite-field, toric, Stanley--Reisner, and symmetric-polynomial examples.
- Recorded-environment certificate and `Data.lean` byte-for-byte replay,
  structured negative fixtures, axiom auditing, and machine-readable benchmark
  records.

### Changed

- Protocol 0.2.0 requires S-pair evidence for every pair of distinct basis
  elements. Certificates produced under the 0.1.0 coprime-pair omission rule
  must be regenerated.
- Provenance has a validated structure and is echoed in verifier reports, but
  remains informational and never changes mathematical assurance.
- Membership elements and coefficients must be canonical; duplicate IDs and
  object/claim ID collisions are rejected.

### Assurance boundaries

- GRevLex Gröbner and non-membership claims are `proved`; their Lex variants
  remain `checked`.
- `ChainComplex` proves composition zero only. `GradedComplex` remains
  executable-only and neither claim implies exactness or minimality.
