# Roadmap

Milestones follow README §9. Status as of July 2026.

| milestone | status | notes |
|---|---|---|
| M0 vocabulary and design | **done** | SPEC 0.1.0, trust model, ADRs 0001–0004 |
| M1 transport and round-trip | **done** | M2 exporter + Lean parser share `protocol/fixtures/` |
| M2 certified polynomial/module core | **done (partial)** | identity, membership, span-inclusion checkers with soundness theorems; GB checker at `checked` level |
| M3 complexes and resolutions | **partial** | `ChainComplex` (proved) and `GradedComplex` (checked) claims; exactness certificates not yet designed |
| M4 flagship mathematics | **done (first instance)** | certified Nullstellensatz-style disjointness theorem for the twisted cubic; Eagon–Northcott complex certified as graded complex with Betti data |
| M5 ergonomic integration | **not started** | subprocess protocol, caching, editor surface |

## Next steps (post-preprint)

1. Formalize Buchberger's criterion (standard representations) to
   promote `GroebnerBasis` from `checked` to `proved`; upstream to
   mathlib where possible.
2. Exactness certificates: rank + depth data (Buchsbaum–Eisenbud
   criterion) or certified kernel computations via syzygy claims.
3. Prime fields in the Lean semantics (`ZMod p`); the protocol and M2
   side already support them.
4. Compact/binary certificate encoding and streaming for large GB
   certificates.
5. `by macaulay2` tactic invoking M2 as a subprocess from Lean.
6. Negative certificates (non-membership via GB normal forms).
