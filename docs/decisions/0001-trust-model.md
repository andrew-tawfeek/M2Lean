# ADR 0001: Small trusted core; M2 is an untrusted oracle

- Status: accepted
- Date: 2026-07-20

## Decision

Macaulay2 (engine, interpreter, our package, all serialization) is
treated as an untrusted oracle. Lean accepts a claim only after an
executable checker verifies its evidence; checkers at assurance level
`proved` carry kernel-checked soundness theorems. `native_decide` is
forbidden in checkers. Provenance never influences acceptance.

## Consequences

Certificates must be *self-contained*: everything needed to verify a
claim is inside the document. This rules out designs where Lean
replays M2 computations or trusts M2's `true`. It also means some M2
results (e.g. primary decomposition) cannot be certified until a
certificate notion exists for them — an accepted limitation.

## Alternatives rejected

- Trusting M2 outputs wholesale ("computer algebra oracle" style à la
  early CAS bridges): incompatible with the project's definition of
  success.
- Verified recomputation inside Lean: too slow, duplicates M2.
