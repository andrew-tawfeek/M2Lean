# M2Lean architecture

M2Lean 0.2.0 has two related verification paths. They share the same protocol
and executable checkers but end at different assurance levels.

```text
                         untrusted production
Macaulay2  ───────▶  protocol 0.2.0 JSON  ───────▶  parse and validate
   │                                                     │
   │ computes witnesses                                  ▼
   │                                            executable checker
   │                                                     │
   │                              ┌──────────────────────┴──────────────────┐
   │                              ▼                                         ▼
   └──────────────────── runtime JSON report                 soundness theorem instance
                              (`checked`/`proved`)                         │
                                                                          ▼
                                                               Lean kernel theorem
```

A runtime `proved` label means that the accepted checker has a formal
soundness theorem in the library. The report is not a serialized proof term.
The right-hand path is complete only when a Lean theorem instantiates the
soundness result and is checked by the kernel.

## Layer 1: interchange representation

[`protocol/SPEC.md`](../protocol/SPEC.md) is normative. Protocol 0.2.0 covers:

- rational and prime coefficient fields;
- multivariate polynomial rings with Lex or GRevLex order;
- canonical sparse polynomials, ideals, matrices, and graded free modules;
- polynomial identity, ideal membership, span inclusion, Gröbner basis,
  non-membership, chain-complex, and graded-complex claims.

Every Gröbner certificate contains evidence for every pair of distinct basis
elements. A `NonMembership` claim explicitly depends on a Gröbner claim in the
same document. The JSON schema is a convenience filter; the Lean consumer
performs the normative structural and mathematical checks.

## Layer 2: executable semantics

- `lean/M2Lean/Protocol/Ast.lean` decodes protocol documents and produces
  path-aware errors.
- `lean/M2Lean/Protocol/Sparse.lean` implements canonical sparse polynomials,
  arithmetic, and the Lex/GRevLex comparators.
- `lean/M2Lean/Semantics/Interp.lean` interprets sparse polynomials as mathlib
  `MvPolynomial` values and proves compatibility of the basic operations.

Structural validation checks version, identifier dependencies, arities,
dimensions, coefficient canonicality, monomial order, and polynomial
canonicality before claims are evaluated. Invalid input is rejected rather
than silently repaired, except where the normative specification explicitly
says otherwise.

Provenance has a validated shape and is echoed in reports, but remains
informational: it is not an input to any mathematical checker and reported
nondeterminism does not reduce independently established assurance.

## Layer 3: certificate checkers and soundness

`lean/M2Lean/Certificates/Checkers.lean` contains the executable checks.
`lean/M2Lean/Certificates/Soundness.lean` connects identity, membership, span
inclusion, and chain-complex acceptance to mathlib propositions.

The Gröbner path is split by monomial order:

- For **GRevLex**, `lean/M2Lean/Groebner/DegRevLex.lean` defines the abstract
  order, `Bridge.lean` proves agreement with the executable comparator, and
  `Sound.lean` proves soundness of the Gröbner and non-membership checkers via
  the formalized Buchberger criterion. These claims are `proved`.
- For **Lex**, the executable check is available, but comparator-to-abstract-
  order agreement and the final soundness bridge are not yet formalized.
  These claims are `checked`.

`GradedComplex` checks matrix sizes, twists, homogeneity, and consecutive
composition at runtime. Its graded semantic bridge is not yet formalized, so
it remains `checked`. `ChainComplex` is `proved`, but asserts only that
consecutive differentials compose to zero—not exactness, minimality, or a
resolution statement.

## Layer 4: integrations

- `m2/M2Lean.m2` exports supported Macaulay2 objects and witnesses as protocol
  documents. Its public claim constructors are `polynomialIdentityClaim`,
  `membershipClaim`, `unitIdealClaim`, `spanInclusionClaim`, `gbClaim`,
  `nonMembershipClaim`, `chainComplexClaim`, and `gradedComplexClaim`.
- `lean/Main.lean` builds `m2lean-check`, which validates a document, evaluates
  claims, and emits a JSON verification report.
- `verifyWithLean` lets a Macaulay2 session invoke the executable and display
  per-claim assurance levels.
- `by macaulay2` is an optional Lean elaborator tactic for a restricted class
  of ground ideal-membership goals. The live Macaulay2 process is a witness
  generator, not a trusted proof oracle.

## Boundaries and reproducibility

The logical trust boundary is described in [`trust-model.md`](trust-model.md).
Operational reproducibility is separate: the release gate verifies the
shipped artifacts, regenerates JSON and generated Lean data, checks their
raw-byte SHA-256 digests, builds theorem files, and audits axioms. The recorded
environment and authoritative artifact inventory live in
[`../reproducibility/manifest.json`](../reproducibility/manifest.json); the
same hashes are exposed in the standard-tool
[`generated.sha256`](../reproducibility/generated.sha256) ledger.
