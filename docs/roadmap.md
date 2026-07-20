# Roadmap

Milestones follow README S9. Status as of July 2026 (bridge v2).

| milestone | status | notes |
|---|---|---|
| M0 vocabulary and design | **done** | SPEC 0.2.0, trust model, ADRs 0001-0005 |
| M1 transport and round-trip | **done** | M2 exporter + Lean parser share `protocol/fixtures/` |
| M2 certified polynomial/module core | **done** | identity, membership, span-inclusion, Groebner (GRevLex), and non-membership checkers all carry soundness theorems |
| M3 complexes and resolutions | **partial** | `ChainComplex` (proved) and `GradedComplex` (checked); exactness certificates not yet designed |
| M4 flagship mathematics | **done** | twisted-cubic disjointness; phi8 separability (mathlib `Polynomial.Separable`); F_101 tier |
| M5 ergonomic integration | **partial** | `verifyWithLean` in-session verification; `by macaulay2` tactic (ground membership goals); CI on every push |

## Formalizations delivered (mathlib-upstream candidates)

- `M2Lean.Groebner.buchberger_criterion` - Buchberger's criterion in
  standard-representation form over any `MonomialOrder` and field.
- `MonomialOrder.degRevLex` - the degree-reverse-lexicographic order
  (WF via finiteness of bounded-degree exponent vectors).
- The comparator-agreement and lead-bridge lemmas connecting an
  executable sparse checker to the abstract theory.

## Next steps

1. Upstream the above to mathlib.
2. Lex agreement lemmas (promotes Lex-order GB claims to proved).
3. Graded-complex soundness (homogeneity semantics).
4. Exactness certificates: syzygy claims or Buchsbaum-Eisenbud data.
5. Reinstate the coprime-pair skip by formalizing Buchberger's first
   criterion.
6. Tactic: symbolic-goal reflection (polyrith-style normalization).
7. Compact/binary certificate encoding and streaming.
