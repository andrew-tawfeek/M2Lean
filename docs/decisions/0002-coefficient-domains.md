# ADR 0002: Version-0 coefficient domains are ℚ and prime fields

- Status: accepted
- Date: 2026-07-20
- Updated: 2026-08-03 for protocol 0.2.0 implementation status

## Decision

Protocol 0.2.0 supports exactly `RationalField` and `PrimeField p`, with
primality verified by the consumer. Rational coefficients are reduced
fractions of decimal strings; prime-field residues are decimal strings in
`[0, p)`. JSON numbers are never used for mathematical scalar data.

## Rationale

Macaulay2's `QQ`/`ZZ/p` and mathlib's `ℚ`/`ZMod p` have aligned semantics for
the supported operations. Algebraic extensions, towers, inexact fields, and
`ZZ` (non-field Gröbner theory) introduce additional semantic obligations and
are intentionally deferred.

The Lean checkers and soundness theorems are parameterized over the
coefficient field. Prime-field documents are interpreted using `ZMod p` only
after the consumer verifies that `p` is prime.

## Consequences

Users must map a computation into `QQ` or a prime field before certification.
Characteristic-dependent behavior (for example, a Gröbner basis over `QQ`
versus `ZZ/p`) is the producer's responsibility; the certificate is checked
only in its declared coefficient field.
