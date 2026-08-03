# ADR 0003: Version-0 monomial orders are Lex and GRevLex

- Status: accepted
- Date: 2026-07-20
- Updated: 2026-08-03 for GRevLex soundness status

## Decision

The protocol supports `Lex` and `GRevLex`, with normative mathematical
definitions in SPEC §3.5 rather than an appeal to an implementation default.
The order is a field of the ring object because a Gröbner claim has no meaning
without it. Variable identity is positional; names are display-only.

## Rationale

GRevLex is Macaulay2's default and a practical workhorse. Lex is useful for
elimination and provides a deliberately different comparator. Cross-system
order mismatch is a silent-corruption risk: tie-breaking conventions vary,
especially about the final variable. Normative definitions and shared pairs
on which Lex and GRevLex disagree make that difference testable.

## Consequences

Weight, elimination, and module orders such as Schreyer order are deferred.
The executable comparators live in `Protocol/Sparse.lean`, and canonical-form
validation uses the declared order. For GRevLex, `Groebner/Bridge.lean` proves
agreement with the abstract `MonomialOrder.degRevLex`, enabling the formal
Gröbner and non-membership soundness theorems. The corresponding Lex bridge is
not yet formalized, so Lex-backed claims remain at assurance level `checked`.
