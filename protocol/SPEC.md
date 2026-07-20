# M2Lean Protocol, version 0.1.0

This document is the normative specification of the M2Lean interchange
protocol, version 0. The protocol describes mathematical objects and
*claims with evidence* so that a computation performed in Macaulay2 can
be interpreted, and its result certified, in Lean 4. The specification
is intentionally independent of both implementations: it defines
mathematical meaning first and JSON encoding second (§9 of the project
README).

Version 0 deliberately restricts attention to exact, deterministic
commutative algebra over the rational numbers and prime fields
(project principle 2.5).

Conformance keywords **MUST**, **MUST NOT**, **SHOULD** are used in the
RFC 2119 sense.

## 1. Documents

A *document* is the unit of exchange. It is encoded as a single JSON
object with fields:

| field           | type   | required | meaning                                    |
|-----------------|--------|----------|--------------------------------------------|
| `m2leanVersion` | string | yes      | protocol version; this spec defines `"0.1.0"` |
| `documentId`    | string | yes      | producer-chosen identifier                  |
| `objects`       | array  | yes      | mathematical objects, in dependency order   |
| `claims`        | array  | yes      | claims with evidence (may be empty)         |
| `provenance`    | object | yes      | see §7                                      |

A consumer MUST reject a document whose `m2leanVersion` it does not
support. Objects MUST be listed in dependency order: an object may only
reference identifiers introduced earlier in the `objects` array.
Identifiers are strings, MUST be unique within a document, and have no
mathematical meaning.

Rejection is always a *protocol-level* outcome, never a mathematical
one: a rejected document says nothing about the truth of its claims.

## 2. Scalars

JSON numbers are never used to encode mathematical data (their
precision is implementation-defined). Instead:

- **Integer**: a string matching `-?(0|[1-9][0-9]*)`, interpreted in
  base 10. Leading zeros and `-0` are forbidden.
- **Rational**: an object `{"num": Integer, "den": Integer}` with
  `den` positive and `gcd(|num|, den) = 1`. The rational `0` is
  `{"num": "0", "den": "1"}`.
- **Prime-field element** (in characteristic `p`): an Integer `c` with
  `0 <= c < p`, denoting the residue class of `c`.
- **Natural number** (arities, exponents, indices): a JSON-native
  non-negative integer; producers MUST keep these below 2^53 and in
  practice exponents are small.

A *coefficient* is a Rational or a prime-field element according to the
coefficient domain of the enclosing ring. Consumers MUST reject
non-canonical scalars (e.g. non-reduced fractions) rather than
normalizing them silently.

## 3. Objects

Every entry of `objects` is a JSON object with fields `id` (string),
`kind` (string), and kind-specific fields. Version 0 defines:

### 3.1 `RationalField`

```json
{ "id": "QQ", "kind": "RationalField" }
```

Denotes the field of rational numbers.

### 3.2 `PrimeField`

```json
{ "id": "F101", "kind": "PrimeField", "characteristic": "101" }
```

`characteristic` is an Integer that MUST be prime; consumers MUST
verify primality or reject. Denotes the field with `p` elements.

### 3.3 `PolynomialRing`

```json
{
  "id": "R",
  "kind": "PolynomialRing",
  "coefficients": "QQ",
  "variables": ["x", "y", "z", "w"],
  "monomialOrder": { "kind": "GRevLex" }
}
```

Denotes the polynomial ring over the referenced coefficient field in
`n` variables, where `n` is the length of `variables`. Variable
*identity* is positional: the i-th variable (0-based) is the
mathematical object; the strings in `variables` are display names only
and MUST be pairwise distinct. Supported monomial orders (see §3.5) are
part of the ring object because Gröbner-type claims are meaningless
without them; rings differing only in order are distinct protocol
objects with equal underlying rings.

### 3.4 Polynomials

Polynomials are *inline values* (not identified objects). A polynomial
in a ring with `n` variables is:

```json
{ "terms": [ { "coefficient": c, "exponents": [e_0, ..., e_{n-1}] }, ... ] }
```

Each term denotes `c · x_0^{e_0} ⋯ x_{n-1}^{e_{n-1}}`; the polynomial
denotes the sum of its terms. **Canonical form** requires:

1. every `coefficient` is nonzero and canonical (§2);
2. every `exponents` array has length exactly `n`;
3. exponent vectors are pairwise distinct;
4. terms are sorted strictly decreasing in the ring's monomial order.

The zero polynomial is `{"terms": []}`. A *raw* polynomial satisfies
only conditions 1'–2: scalars are canonical (§2) but coefficients may
be zero, exponent vectors may repeat, and terms may appear in any
order. A *canonical* polynomial satisfies all four conditions.
Canonical form is required everywhere a polynomial appears in this
specification **except** where a field is explicitly documented as
raw (`PolynomialIdentity.lhs/rhs`, §4.1). Producers MUST emit
canonical form where it is required; consumers MUST reject
non-canonical polynomials there rather than normalizing them.
Canonicality makes equality of encoded polynomials decidable by
structural equality, which is the base of every checker.

### 3.5 Monomial orders

Version 0 supports exactly two orders on exponent vectors
`a, b ∈ ℕ^n`:

- **`Lex`**: `a > b` iff at the smallest index `i` with `a_i ≠ b_i`
  we have `a_i > b_i`.
- **`GRevLex`** (graded reverse lexicographic, the Macaulay2 default):
  `a > b` iff `|a| > |b|`, or `|a| = |b|` and at the *largest* index
  `i` with `a_i ≠ b_i` we have `a_i < b_i`. Here `|a| = Σ a_i`.

These definitions are normative; implementations MUST agree with them
exactly (this is a known source of cross-system mismatch).

### 3.6 `Ideal`

```json
{ "id": "I", "kind": "Ideal", "ring": "R", "generators": [poly, ...] }
```

Denotes the ideal of the referenced ring generated by the listed
polynomials (possibly none: the zero ideal).

### 3.7 `Matrix`

```json
{ "id": "d1", "kind": "Matrix", "ring": "R",
  "rows": 1, "cols": 3, "entries": [[p, q, r]] }
```

`entries` is row-major and MUST have exactly `rows` rows each of
`cols` polynomial entries. A matrix with `r` rows and `c` columns
denotes the homomorphism `R^c → R^r` acting on column vectors.

### 3.8 `GradedFreeModule`

```json
{ "id": "F1", "kind": "GradedFreeModule", "ring": "R",
  "degrees": [2, 2, 2] }
```

Denotes `⊕_j R(−d_j)` with the standard grading of `R` (every variable
in degree 1), i.e. basis element `j` sits in degree `degrees[j]`.
Degrees are (possibly negative) JSON integers.

## 4. Claims

A *claim* is a proposition about previously introduced objects,
together with *evidence* addressed to a specific checker. Each entry
of `claims` has fields `id`, `kind`, kind-specific proposition fields,
and `evidence` (an object, possibly empty).

The semantics of acceptance is: **if the checker for the claim's kind
accepts the claim, the proposition of §4.x holds** — under the
soundness theorem or documented assurance level of that checker
(see §6). Evidence is never trusted; it is only raw material the
checker verifies.

### 4.1 `PolynomialIdentity`

Proposition: `lhs = rhs` in the referenced ring.

```json
{ "id": "c1", "kind": "PolynomialIdentity", "ring": "R",
  "lhs": poly, "rhs": poly, "evidence": {} }
```

`lhs` and `rhs` are *raw* polynomials (§3.4): this is the one place
the protocol admits unnormalized input, so that the claim expresses a
genuine identity between differently presented sums of terms rather
than structural equality of strings. No further evidence is needed:
the checker normalizes both sides. This claim kind is the base case
of the certificate family (every other checker reduces to it) and the
primary cross-implementation test surface.

### 4.2 `IdealMembership`

Proposition: `element ∈ I` where `I` is the referenced ideal with
generators `g_1, …, g_k`.

```json
{ "id": "c2", "kind": "IdealMembership", "ideal": "I",
  "element": poly,
  "evidence": { "cofactors": [poly_1, ..., poly_k] } }
```

Evidence: cofactors `c_1, …, c_k` (one per generator, in order). The
checker verifies the polynomial identity
`element = c_1 g_1 + ⋯ + c_k g_k`. In Macaulay2 the cofactors are
obtained from `element // gens I` once a Gröbner basis is known,
composed with the change-of-basis matrix `getChangeMatrix`.

A membership claim with `element = 1` certifies that `I` is the unit
ideal; this is the algebraic core of the flagship example
(certified emptiness of an intersection of varieties).

### 4.3 `SpanInclusion`

Proposition: `I ⊆ J` for referenced ideals `I` (generators
`f_1, …, f_m`) and `J` (generators `g_1, …, g_k`) in the same ring.

```json
{ "id": "c3", "kind": "SpanInclusion", "source": "I", "target": "J",
  "evidence": { "cofactorRows": [[poly, ...], ...] } }
```

Evidence: an `m × k` array of cofactors; row `i` witnesses
`f_i = Σ_j cofactorRows[i][j] · g_j`. Two `SpanInclusion` claims in
opposite directions certify `I = J`.

### 4.4 `GroebnerBasis`

Proposition: `basis` is a Gröbner basis, with respect to the ring's
monomial order, of the referenced ideal.

```json
{ "id": "c4", "kind": "GroebnerBasis", "ideal": "I",
  "basis": [b_1, ..., b_r],
  "evidence": {
    "basisCofactors":     [[poly, ...], ...],
    "generatorCofactors": [[poly, ...], ...],
    "sPairs": [ { "i": 0, "j": 1, "quotients": [poly, ...] }, ... ]
  }
}
```

Evidence has three parts:

1. `basisCofactors[i]` expresses `b_i` in the ideal's generators
   (so span(basis) ⊆ I);
2. `generatorCofactors[i]` expresses generator `g_i` in the basis
   (so I ⊆ span(basis));
3. for every unordered pair `i < j` of basis elements whose leading
   monomials are not coprime, a *standard representation* of the
   S-polynomial: quotients `q_1, …, q_r` such that
   `S(b_i, b_j) = Σ_k q_k b_k` and, for every `k` with `q_k ≠ 0`,
   `lm(q_k b_k) ≤ lm(S(b_i, b_j))` in the ring's order.

The checker verifies 1–3 literally (including the leading-monomial
side conditions and that every required pair is present). By
Buchberger's criterion in standard-representation form
[Becker–Weispfenning, Thm. 5.64; Cox–Little–O'Shea, Ch. 2 §9 Thm. 3],
acceptance implies the proposition. Pairs with coprime leading
monomials MAY be omitted (Buchberger's first criterion). In Macaulay2
the quotients are produced by dividing the S-polynomial by the basis
(`quotientRemainder`), and the change matrices by `forceGB` /
`getChangeMatrix`.

### 4.5 `ChainComplex`

Proposition: the referenced matrices form a complex, i.e. consecutive
composites vanish.

```json
{ "id": "c5", "kind": "ChainComplex", "ring": "R",
  "differentials": ["d1", "d2"], "evidence": {} }
```

`differentials[i]` is `d_{i+1} : F_{i+1} → F_i`; the checker verifies
`cols(d_i) = rows(d_{i+1})` and that every entry of the product
`d_i · d_{i+1}` normalizes to zero. Note the deliberately modest
proposition: this certifies *a complex*, not exactness (README §5.5).

### 4.6 `GradedComplex`

Proposition: the referenced complex is a complex of *graded* free
modules with the stated twists, i.e. each differential is homogeneous
of degree 0 with respect to the stated degrees. Acceptance certifies
the Betti-table data displayed for the complex.

```json
{ "id": "c6", "kind": "GradedComplex", "ring": "R",
  "modules": ["F0", "F1", "F2"],
  "differentials": ["d1", "d2"], "evidence": {} }
```

For `d : F → G` with source degrees `s_j` and target degrees `t_i`,
the checker verifies that entry `(i, j)` is zero or homogeneous of
total degree `s_j − t_i`, and that the `ChainComplex` conditions hold.

## 5. Verification reports

The verifier (Lean) answers with a report document:

```json
{
  "m2leanVersion": "0.1.0",
  "documentId": "...",
  "reportFor": "<documentId of the input>",
  "results": [
    { "claim": "c2", "status": "accepted",
      "assurance": "proved",
      "proposition": "element ∈ I",
      "message": "" },
    { "claim": "c4", "status": "rejected",
      "assurance": "none",
      "message": "sPair (0,2): quotient 1 violates lm bound at term 3" }
  ],
  "provenance": { ... }
}
```

`status` is `accepted` or `rejected`. Failure messages MUST
distinguish parsing, structural (semantic), and verification failures.

## 6. Assurance levels

Each accepted claim carries an assurance level; these MUST NOT be
conflated (project principle 2.3):

| level        | meaning                                                              |
|--------------|----------------------------------------------------------------------|
| `transported`| the object parsed and validated; no claim checked                    |
| `reproduced` | the computation was re-run and matched; no certificate               |
| `checked`    | the certificate was verified by an executable checker                |
| `proved`     | as `checked`, and the checker has a machine-checked soundness theorem connecting acceptance to the mathematical proposition |

In the current implementation, `PolynomialIdentity`, `IdealMembership`,
`SpanInclusion`, and `ChainComplex` report `proved`;
`GroebnerBasis` and `GradedComplex` report `checked` (their checkers
are executable and complete, but the Buchberger-criterion and
graded-semantics soundness theorems are not yet formalized).

## 7. Provenance

```json
{
  "producer": "Macaulay2",
  "producerVersion": "1.24.11",
  "packageVersion": "0.1.0",
  "algorithm": "gb (engine default)",
  "options": {},
  "coefficientNotes": "QQ exact",
  "deterministic": true
}
```

All fields are informative, not trusted; provenance never influences
acceptance. Producers SHOULD record enough context to re-run the
computation (README §2.4). Probabilistic or heuristic steps MUST set
`deterministic: false`, and consumers MUST NOT report `proved` or
`checked` assurance for claims whose evidence depends on them (v0
defines no such claim kinds).

## 8. Versioning

The triple `major.minor.patch` follows: incompatible changes to the
meaning of existing kinds bump `major` (currently the leading `0`
marks the experimental series); new object or claim kinds bump
`minor`; clarifications bump `patch`. A consumer MAY accept any
document whose kinds it fully supports, and MUST reject unknown kinds
rather than skipping them. Semantic changes require an ADR in
`docs/decisions/`.

## 9. Fixtures

`protocol/fixtures/valid/` contains documents every conforming
consumer must accept; `protocol/fixtures/invalid/` contains documents
that MUST be rejected, each with a comment field `"_expectRejection"`
explaining why. Corrupted-certificate fixtures (well-formed documents
whose evidence is wrong) live in `invalid/` too: rejecting them is the
project's central acceptance test.
