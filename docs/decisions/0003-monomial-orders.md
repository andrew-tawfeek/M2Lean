# ADR 0003: Version-0 monomial orders are Lex and GRevLex, defined normatively

- Status: accepted
- Date: 2026-07-20

## Decision

The protocol supports `Lex` and `GRevLex`, with normative mathematical
definitions in SPEC §3.5 (not "whatever M2/mathlib does"). The order
is a field of the ring object, since Gröbner claims are meaningless
without it. Variable identity is positional; names are display-only.

## Rationale

GRevLex is M2's default and the practical workhorse; Lex is the
simplest to reason about and useful for elimination later. Cross-system
order mismatch is a classic silent-corruption source: M2 uses
GRevLex with the *last* variable least, and several textbooks differ
in tie-breaking conventions. Making the definition normative and
testing it with adversarial fixtures (pairs ordered differently by
Lex and GRevLex) removes the ambiguity.

## Consequences

Weight orders, elimination orders, and module orders (Schreyer) are
future minor versions. The Lean side implements the two comparators
once, in `Protocol/Sparse.lean`, and the canonical-form validator uses
them; a wrong comparator would be caught by the shared fixtures.
