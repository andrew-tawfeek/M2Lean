# M2Lean trust model

A defect anywhere in the untrusted zone must cause rejection or
failure — never a false theorem.

## Trusted

1. The Lean 4 kernel and its standard trusted runtime assumptions
   (including `native_decide` is **not** used by any checker).
2. `lean/M2Lean/Protocol/Sparse.lean` and
   `lean/M2Lean/Semantics/Interp.lean`: the definitions giving
   protocol objects mathematical meaning. A wrong *definition* here
   changes what accepted claims mean.
3. The soundness theorems in `lean/M2Lean/Certificates/` (checked by
   the kernel, so "trusted" only in the sense that their *statements*
   must be read and endorsed by a human).
4. mathlib, to the same extent any mathlib-based development trusts it.

## Untrusted

- Macaulay2: engine, interpreter, packages, and our bridge package;
- serialization, transport, files, caches;
- every field of every protocol document, including provenance;
- generated Lean syntax before elaboration and kernel checking;
- the JSON schema (a convenience pre-filter, not a gatekeeper).

## Required behavior (tested)

| behavior | test |
|---|---|
| malformed JSON rejected | `fixtures/invalid/*parse*` |
| structurally invalid documents rejected | `fixtures/invalid/*structure*` |
| non-canonical polynomials rejected | `fixtures/invalid/noncanonical-*` |
| corrupted membership cofactors rejected | `fixtures/invalid/corrupt-membership.json` |
| corrupted GB evidence (wrong quotient, missing pair, violated lm bound) rejected | `fixtures/invalid/corrupt-gb-*.json` |
| accepted claims add no axioms, contain no `sorry` | `#print axioms` check in `lean/M2Lean/Examples/` |
| assurance levels reported per claim, never conflated | report format, §5–6 of SPEC |

## Non-promises

- Acceptance of a `ChainComplex` claim does **not** assert exactness.
- Acceptance of a `GroebnerBasis` claim is at level `checked`: the
  executable criterion was verified, but the implication
  "criterion ⇒ Gröbner basis" is cited (Buchberger), not yet
  formalized. Downstream Lean proofs in this repository only consume
  `proved`-level claims.
- Provenance is displayed for reproducibility; it is never evidence.
