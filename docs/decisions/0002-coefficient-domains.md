# ADR 0002: Version-0 coefficient domains are ℚ and prime fields

- Status: accepted
- Date: 2026-07-20

## Decision

Protocol 0.1.0 supports exactly `RationalField` and `PrimeField p`
(p prime, verified by the consumer). Encodings: reduced fractions of
decimal strings; residues in `[0, p)`. JSON numbers are never used
for mathematical data.

## Rationale

Both systems have exactly aligned semantics for these domains: M2's
`QQ`/`ZZ/p` and mathlib's `ℚ`/`ZMod p`. Algebraic extensions, towers,
inexact fields, and `ZZ` (non-field Gröbner theory) all introduce
semantic mismatches that would grow the trusted semantics layer before
the vertical slice exists. The Lean semantics currently interprets
only ℚ; prime fields are parsed and validated but their `checked`
claims are not yet promoted to `proved` (roadmap item 3).

## Consequences

M2 users must map their computation into ℚ or a prime field before
certification. Charateristic-dependent behavior (e.g. GB over ℚ vs
F_p) is the producer's responsibility; the certificate is checked in
the declared domain only.
