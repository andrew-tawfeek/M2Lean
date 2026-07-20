# M2Lean architecture

M2Lean has four layers (README §4). This document records how the
current implementation realizes them.

```text
Macaulay2  --export-->  protocol document (JSON)  --parse/validate-->  Lean
   |                                                                    |
   |  computes objects, extracts evidence                               |  interprets objects into
   |  (change matrices, cofactors,                                      |  mathlib types, runs
   |   S-pair reductions)                                               |  certificate checkers,
   |                                                                    |  applies soundness theorems
   +------------------<--  verification report (JSON)  <----------------+
```

## Layer 1 — interchange representation (`protocol/`)

`protocol/SPEC.md` is normative. Version 0.1.0 covers: ℚ and prime
fields; multivariate polynomial rings with Lex/GRevLex; sparse
canonical polynomials; ideals; matrices; graded free modules; and six
claim kinds (identity, membership, span inclusion, Gröbner basis,
chain complex, graded complex). `protocol/schema/` holds a JSON
Schema for structural validation; `protocol/fixtures/` holds valid and
adversarial documents shared by both implementations' test suites.

## Layer 2 — semantics (`lean/M2Lean/Protocol`, `lean/M2Lean/Semantics`)

- `Protocol/Ast.lean` — Lean datatypes mirroring the spec, plus JSON
  decoding with path-carrying error messages.
- `Protocol/Sparse.lean` — the executable computational model:
  sparse polynomials as sorted term lists over ℚ, with normalization,
  ring operations, monomial orders, and canonicality checking.
- `Semantics/Interp.lean` — the bridge to mathematics: an
  interpretation `toMv : SPoly n → MvPolynomial (Fin n) ℚ` together
  with proved lemmas that normalization, addition, multiplication, and
  scalar operations on the sparse model commute with `toMv`. These
  lemmas are what turn a byte-level check into a statement about
  actual mathlib polynomials.

Parsing a document is not a proof. Structural validation (arities,
canonical scalars, dependency order, dimensions) happens before any
interpretation, and rejects rather than repairs.

## Layer 3 — claims and certificates (`lean/M2Lean/Certificates`)

One checker per claim kind. Each checker is an executable Boolean (or
error-reporting) function on the sparse model. The `proved`-level
checkers additionally have soundness theorems of the shape

```text
theorem membership_sound (cl : MembershipClaim) :
    checkMembership cl = true →
    toMv cl.element ∈ Ideal.span (toMv '' cl.generators)
```

so that acceptance yields a genuine mathlib proposition. The
`GroebnerBasis` checker verifies Buchberger's criterion in
standard-representation form computationally; its soundness theorem
(the criterion itself) is future formalization work, and the claim is
therefore reported at assurance level `checked`, not `proved`.

## Layer 4 — user-facing integrations (`m2/`, `scripts/`)

- `m2/M2Lean.m2` is a Macaulay2 package exposing `exportRing`,
  `membershipCertificate`, `gbCertificate`, `complexCertificate`,
  `unitIdealCertificate`, and `writeM2LeanDocument`. Evidence comes
  from public M2 interfaces: `quotientRemainder` against a Gröbner
  basis for cofactors, `getChangeMatrix`/`forceGB` for change of
  basis, and ordinary matrix arithmetic for S-polynomials.
- `lean/Main.lean` builds a CLI `m2lean-check` that reads a document,
  runs all checkers, and writes a verification report.
- `scripts/` glues the two: an example is an M2 script that emits a
  document, then a Lean invocation that checks it, then (for the
  flagship) a Lean theorem file that consumes the accepted claim.

## Trusted boundary

See `docs/trust-model.md`. In one line: everything left of the JSON
document is untrusted; the Lean kernel, the semantics files, and the
soundness theorems are the trusted core.
