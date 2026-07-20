# ADR 0005: Protocol 0.2.0 — all S-pairs, NonMembership, prime-field checking

- Status: accepted
- Date: 2026-07-20

## Decision

Protocol 0.2.0 makes three coupled changes:

1. **Gröbner evidence must cover every pair** of basis elements; the
   0.1.0 allowance to omit coprime-leading-monomial pairs is removed.
2. **A `NonMembership` claim kind** is added: division data against a
   Gröbner basis certified in the same document, with a nonzero fully
   reduced remainder.
3. **Prime-field claims are checkable**: the Lean side now runs every
   checker in the declared coefficient field (`ℚ` or `ZMod p`), so
   `PrimeField` documents are no longer parse-only.  As the required
   encoding for residues, bare decimal strings are also accepted
   wherever a coefficient is expected (interpreted as integer
   rationals over `ℚ`).

## Rationale

The coprime-pair omission (Buchberger's first criterion) is a
performance optimization whose formal soundness proof is an extra
theorem with its own delicate degree argument.  Requiring all pairs
keeps the planned soundness theorem for `checkGroebner` within the
standard-representation criterion alone, at the cost of slightly
larger certificates (the flagship certificate grows from 2 to 3
S-pairs).  The first criterion can return as a 0.3.x optimization
*after* it is formalized.

Negative certificates are only sound relative to a Gröbner basis, so
`NonMembership` explicitly references the `GroebnerBasis` claim it
depends on and inherits its assurance level.

## Consequences

- 0.1.0 Gröbner certificates that omitted coprime pairs are rejected
  by 0.2.0 consumers; producers regenerate (`gbClaim` now emits all
  pairs).
- The checkers, semantics, and soundness theorems are parameterized
  over the coefficient field; `ZMod p` requires a primality check at
  the trust boundary (the verifier refuses non-prime characteristics).
