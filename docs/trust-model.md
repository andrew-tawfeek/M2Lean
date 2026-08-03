# M2Lean trust and assurance model

M2Lean is designed so that a defect in Macaulay2, certificate generation,
transport, or generated source cannot by itself produce a false Lean theorem.
Runtime acceptance and theorem production nevertheless have different trust
and operational boundaries.

## Three outcomes

1. **Runtime acceptance.** `m2lean-check` parses a document and runs executable
   validators and certificate checkers. Its JSON report is useful for testing
   and interoperability, but is not a kernel theorem.
2. **Soundness formalized.** A `proved` report label means the accepted checker
   has a Lean theorem showing that acceptance implies a stated mathematical
   proposition. `checked` means that only the executable path is currently
   available.
3. **Kernel-instantiated theorem.** A case-study theorem imports concrete data,
   proves that the checker accepts it, applies the soundness theorem, and is
   elaborated by Lean. This is the strongest outcome in this repository.

## Logical trusted computing base

- the Lean 4 kernel and its ordinary runtime assumptions;
- the definitions that assign mathematical meaning to protocol data,
  principally `Protocol/Sparse.lean` and `Semantics/Interp.lean`;
- the statements and proofs in the relevant soundness layer;
- mathlib and Lean's standard axioms to the same extent as the surrounding
  formal development.

The proofs are kernel-checked, so their implementation is not trusted as an
oracle. Their *statements* and the semantic definitions they mention still
require human review: a perfectly proved theorem about the wrong
interpretation would not establish the intended mathematics.

The theorem files audited for this release depend only on `propext`,
`Classical.choice`, and `Quot.sound`. The certificate checkers do not use
`native_decide`.

## Untrusted inputs and components

- the Macaulay2 engine, interpreter, packages, and M2Lean producer;
- algorithms used to discover Gröbner bases, cofactors, matrices, or points;
- JSON serialization, files, transport, caches, and provenance;
- every object, claim, coefficient, identifier, and witness in a document;
- generated Lean syntax before elaboration and kernel checking;
- the JSON schema, CI service, benchmark harness, and documentation.

The parser and executable checker are part of the operational runtime path.
For a kernel-instantiated theorem, a bug in those implementations cannot
establish a false proposition unless it is also reflected in a false semantic
definition or an unsound theorem accepted by the kernel.

## Current assurance matrix

| Claim | Assurance | Exact proposition established |
|---|---|---|
| `PolynomialIdentity` | proved | interpreted polynomials are equal |
| `IdealMembership` | proved | the element belongs to the span of the supplied generators |
| `SpanInclusion` | proved | every source generator belongs to the target span |
| `GroebnerBasis`, GRevLex | proved | basis generates the ideal and is Gröbner for the formal GRevLex order |
| `GroebnerBasis`, Lex | checked | certificate equations and Buchberger conditions pass executable checks |
| `NonMembership`, GRevLex | proved | element is not in the generated ideal |
| `NonMembership`, Lex | checked | division and referenced Gröbner evidence pass executable checks |
| `ChainComplex` | proved | consecutive matrices compose to zero |
| `GradedComplex` | checked | dimensions, twists, homogeneity, and compositions pass runtime checks |

## Tested failure behavior

The release suite contains 15 accepted documents and 20 targeted invalid
documents. It covers malformed JSON, structural errors, noncanonical
encodings (including membership elements), duplicate and colliding
identifiers, unsupported versions and fields, coefficient errors, monomial-
order mismatches, provenance shape, corrupt membership and Gröbner evidence,
and corrupt graded or ungraded complex data. The test harness checks the
diagnostic class rather than treating every nonzero exit as equivalent.

The suite is evidence for the named cases, not a proof that the executable
accepts only valid documents. The formal soundness theorems provide that
logical guarantee for their exact inputs and conclusions.

Provenance requires `producer` and `producerVersion`, validates the types of
optional fields, and is echoed as `inputProvenance` in a report. It remains
informational even when a producer records `deterministic: false`; it never
influences mathematical acceptance.

## Explicit non-promises

- A chain or graded-complex claim does not assert exactness, minimality,
  cokernel identification, or Betti numbers.
- The graph theorem is currently instantiated for the six-vertex wheel;
  other graph documents do not by themselves produce kernel theorems.
- The Jacobian case study formalizes rational-point injectivity and a
  polynomial-map inverse formulation over `ℚ` in dimension three. Its nine
  membership certificates are all promoted through soundness, but the final
  noninjectivity proof independently evaluates the displayed collision.
- Lex Gröbner soundness and graded-complex soundness remain future work.
