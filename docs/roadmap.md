# Roadmap

Status for the M2Lean 0.2.0 release candidate, August 2026.

| Area | Status | Evidence or boundary |
|---|---|---|
| Protocol and shared semantics | complete for 0.2.0 | normative specification, schema, cross-language fixtures |
| Identity, membership, span inclusion | proved | executable checkers and kernel-checked soundness theorems |
| GRevLex Gröbner and non-membership | proved | comparator bridge, Buchberger criterion, end-to-end soundness |
| Lex Gröbner and non-membership | checked | executable path; formal order bridge remains open |
| Chain complexes | proved, narrow | composition zero only |
| Graded complexes | checked | dimensions, twists, homogeneity, composition; semantic proof open |
| M2 and CLI integration | implemented | direct package loading, installation path, `verifyWithLean` |
| Lean tactic | experimental | ground membership goals; invokes live M2 at elaboration time |
| Public distribution | in progress | GitHub tag/archive, Reservoir, and M2 package review are release tasks |

## Near-term priorities

1. Publish and archive an immutable 0.2.0 artifact, then record its commit and
   DOI in the paper, citation metadata, and reproducibility manifest.
2. Formalize the Lex comparator bridge and promote Lex Gröbner-backed claims.
3. Formalize graded homogeneity and the graded-complex checker.
4. Design separate certificate families for exactness, minimality, cokernel
   identification, and Betti data.
5. Add parameterized scaling benchmarks with memory and phase-level timing.
6. Make tactic reflection work for a documented symbolic-goal fragment.

## Upstream candidates

The following components should be discussed separately with mathlib and the
authors of the contemporary Lean Gröbner developments:

- `MonomialOrder.degRevLex` and its well-foundedness proof;
- the standard-representation form of Buchberger's criterion;
- executable-to-abstract GRevLex comparator and leading-term bridges.

Any upstream proposal should be a small independent contribution, not an
attempt to upstream the whole Macaulay2 bridge.

## Longer-term work

- compact or streaming certificate encodings;
- additional coefficient domains and monomial/module orders;
- syzygy and exactness certificates;
- broader theorem-producing graph encodings;
- stable Macaulay2 and Reservoir distribution after the protocol matures.
