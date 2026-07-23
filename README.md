# M2Lean

[![CI](https://github.com/andrew-tawfeek/M2Lean/actions/workflows/ci.yml/badge.svg)](https://github.com/andrew-tawfeek/M2Lean/actions/workflows/ci.yml)

> **Status (July 2026).** The Bridge Core described below is
> implemented and tested: see `protocol/` (interchange format 0.1.0),
> `m2/` (Macaulay2 exporter and certificate generator), `lean/`
> (Lean 4 semantics, checkers, soundness theorems, `m2lean-check`
> CLI), `examples/` (end-to-end workflows including the flagship
> twisted-cubic theorem), and `paper/` (the preprint *M2Lean: A
> Certificate-Based Bridge Between Macaulay2 and Lean 4*).
> Reproduce everything with `scripts/lean-build.sh`,
> `scripts/run-checks.sh`, and `scripts/audit.sh` (WSL/Linux with
> Macaulay2 and elan).  Design documents live in `docs/`.

## Quickstart

**Coming from Macaulay2?**  You never need to touch Lean.  Load the
package, do your mathematics as usual, attach claims, and verify:

```m2
loadPackage("M2Lean", FileName => "m2/M2Lean.m2")
R = QQ[x,y];
I = ideal(x+y, x-y);
D = newM2LeanDocument "mysession";
membershipClaim(D, "mem1", x^3 + y^3, I);
verifyWithLean D
--   mem1: accepted [proved]  element lies in the ideal
```

The document written by `writeM2LeanDocument` is a permanent,
machine-checkable record of your computation — coefficient field,
monomial order, versions, and evidence included.  Requires the
`m2lean-check` binary (built once via `scripts/lean-build.sh
m2lean-check`, or set `M2LEAN_CHECK`).

**Coming from Lean?**  Certified M2 computations arrive as ordinary
mathlib propositions (see `lean/M2Lean/Examples/` — no `sorry`, no
extra axioms), and with `M2` on your `PATH` you can delegate a
computation from inside a proof:

```lean
import M2Lean.Tactic.Macaulay2

example : toMv 2 f ∈ spanOf 2 gs := by macaulay2
```

The mathematical content lives in `lean/M2Lean/Groebner/`:
Buchberger's criterion in standard-representation form and the
degree-reverse-lexicographic `MonomialOrder`, both stated against
mathlib's own theory.

## Highlighted example: the Jacobian-conjecture counterexample

The [Jacobian conjecture](https://en.wikipedia.org/wiki/Jacobian_conjecture)
(Keller, 1939) — open for every `n ≥ 2` for 87 years — asserts that a
polynomial map `F : ℂⁿ → ℂⁿ` whose Jacobian determinant is a nonzero
constant has a polynomial inverse. On **19 July 2026**, Levent Alpöge
announced an explicit dimension-three counterexample, found with the
assistance of Anthropic's *Claude Fable 5* model after Akhil Mathew
proposed the search; because the witness is a handful of polynomial
evaluations, it was independently checked by many mathematicians within
a day ([New Scientist](https://www.newscientist.com/article/2580374-ais-solution-to-87-year-old-riddle-takes-mathematicians-by-surprise/),
[Secret Blogging Seminar](https://sbseminar.wordpress.com/2026/07/20/the-new-counterexample-to-the-jacobian-conjecture/)),
and Terence Tao related it to the Bass–Connell–Wright and Yagzhev
reductions.

M2Lean neither trusts nor relies on that provenance — the object is a
self-contained algebraic fact, re-verified end to end with **no `sorry`
and only Lean's three standard axioms**:

```
F(x,y,z) = ( (1+xy)³·z + y²(1+xy)(4+3xy),
             y + 3x(1+xy)²·z + 3xy²(4+3xy),
             2x − 3x²y − x³·z )
```

- **Macaulay2** ([`examples/jacobian/jacobian.m2`](examples/jacobian/jacobian.m2))
  forms the Jacobian and sees its determinant collapse to the constant
  `−2` (the conjecture's *hypothesis*), then certifies that the three
  distinct points `(0,0,−¼)`, `(1,−³⁄₂,¹³⁄₂)`, `(−1,³⁄₂,¹³⁄₂)` all map to
  `(−¼,0,0)` (the *conclusion*, non-injectivity). It exports this as a
  10-claim protocol document, every claim `proved`.
- **Lean** ([`lean/M2Lean/Examples/Jacobian.lean`](lean/M2Lean/Examples/Jacobian.lean))
  re-checks the nine collision certificates in its kernel, proves
  `det (Jacobian F) = −2` directly over mathlib's `MvPolynomial`, and
  concludes:

  ```lean
  theorem jacobian_conjecture_false : ¬ JacobianConjecture 3
  ```

Non-injectivity is the strongest possible refutation (an injective map
would be the weakest conclusion), so the Jacobian conjecture *as stated*
is false in dimension three — and, by adjoining identity coordinates, in
every dimension `≥ 3`. The plane case `n = 2` remains open.

## Also certified: graph non-3-colorability (nonexistence via Nullstellensatz)

A certificate can prove something is *impossible*, too. Encode a
3-coloring of a graph `G` algebraically (one variable per vertex, colors
= cube roots of unity via `x_v³ − 1`, adjacent vertices differ via
`x_u² + x_u x_v + x_v²`); then `G` is 3-colorable **iff**
`1 ∉ coloringIdeal(G)`, so a Nullstellensatz certificate `1 = Σ cᵢ gᵢ`
is a *proof of non-colorability*. This is the infeasibility counterpart
to mathlib's existing Combinatorial Nullstellensatz (Alon) — the standard
non-vanishing criterion for proving combinatorial objects like colorings
*exist* — landing on the same `SimpleGraph.Colorable` predicate.

- **Macaulay2** ([`examples/coloring/`](examples/coloring/)) finds the
  certificate; **Lean** ([`Coloring.lean`](lean/M2Lean/Examples/Coloring.lean))
  kernel-checks it and, via an encoding-correctness lemma (a proper
  coloring would give a common zero `x_v = ζ^{c(v)}` over ℂ), proves
  `theorem wheel5_not_three_colorable : ¬ W.Colorable 3` — no `sorry`,
  only the three standard axioms.
- The certificate **grows with the graph** while checking stays trivial:
  `K₄` (4.5 kB) → odd wheel `W₅` (8 kB) → the **Grötzsch graph** (112 kB
  — the smallest triangle-free non-3-colorable graph, where no clique
  forces the fourth color), each verified by `m2lean-check` in under a
  second.

The remainder of this file is the founding vision document.

# Founding exchange

## Request

I am less actually interested in this quotient ring nonsense but more-so the bigger picture: some kind of grand cross collaboration between Lean and M2 — tying them together.

## Response

Yes—that larger vision is much more interesting. I would frame it as a partnership between two different mathematical roles:

- **M2 is the computational laboratory:** it discovers examples, performs large algebraic computations, finds presentations, resolutions, decompositions, invariants, and counterexamples.
- **Lean is the logical authority:** it states the mathematical meaning of those computations, combines them with abstract theory, and certifies conclusions.

The goal should not be to translate M2 source code into Lean source code. It should be to create a shared mathematical language and a bidirectional protocol.

```text
                 shared mathematical representation
              rings · modules · maps · complexes · schemes
                        ↙                 ↘
             Macaulay2                     Lean
       discover and compute         specify and formally reason
                        ↘                 ↙
                results + proof evidence
```

From Lean, one might eventually write:

```lean
by
  macaulay2
```

Lean would send a computational subproblem to M2, receive evidence, check it, and incorporate the result into a larger proof.

From M2, one might write something like:

```m2
certify betti res I
certify isPrime I
certify dim I
```

M2 would invoke Lean and return not merely `true`, but something like:

```text
Result: dimension(R/I) = 3
Lean verification: accepted
Theorem artifact: ...
Assumptions: coefficient field is QQ; graded reverse lexicographic order
```

More ambitiously, an interactive M2 session could accumulate a formal Lean document. Ring declarations, maps, ideals, computations, and assertions would acquire precise meanings on the Lean side. A researcher could experiment in M2 first, then ask which parts of the session are formally certified.

## What “compatible” should mean

There are several progressively stronger levels.

1. **Shared representation**

   Both systems agree on how to describe polynomial rings, coefficient domains, monomial orders, ideals, modules, matrices, complexes, maps, gradings, and presentations.

   This sounds mundane, but it is foundational. M2’s objects are dynamic runtime objects; Lean’s mathematical objects are typed. Bridging those worlds cleanly is a serious design problem.

2. **Bidirectional translation**

   Lean can construct an M2 problem, and M2 can emit Lean-readable objects. This gives interoperability but not yet mathematical trust.

3. **Certified computation**

   M2 attaches evidence to results, and Lean checks its mathematical meaning. Gröbner change matrices, reductions, syzygies, transformation matrices, and explicit maps are examples of useful evidence.

4. **Formalized algorithms**

   Important M2 algorithms receive abstract correctness proofs in Lean. The highly optimized M2 implementation remains separate, but its output is checked against the formally proved specification.

5. **Verified implementation components**

   Selected engine routines are connected directly to their Lean specifications. This is valuable eventually, but should not be required before the collaboration becomes useful.

## The central opportunity

The deepest gain would not merely be “M2 answers questions for Lean.” M2 could expose the computational structure that Lean’s algebra library currently lacks, while Lean could force that structure to be described with unprecedented precision.

That could lead to formal libraries covering:

- Gröbner bases and normal forms
- syzygies and module presentations
- kernels, images, cokernels, and exact sequences
- free resolutions and Betti tables
- elimination and implicitization
- Hilbert functions and polynomials
- dimension and codimension arguments
- normalization and integral dependence
- primary decomposition
- computations supporting concrete algebraic geometry

Conversely, Lean’s abstract results could provide the final logical step after M2 establishes computational hypotheses. A proof might look conceptually like:

1. M2 certifies the exactness of a concrete complex.
2. Lean invokes an abstract theorem about resolutions.
3. Lean concludes a homological or geometric result that M2 itself was never programmed to formulate.

That is where the collaboration becomes more than “computer algebra with verification.”

## The right first project

For the grand vision, I would start by building neither a quotient-ring demo nor a proof of M2’s entire correctness. I would build the shared spine:

- a formally specified interchange format;
- a Lean interpretation of that format;
- an M2 exporter/importer;
- one extensible notion of a checked computational claim;
- provenance recording assumptions, algorithms, coefficient domains, and orderings.

Then demonstrate it on three connected workflows:

1. **Polynomial and module computations:** Gröbner bases, reductions, membership, kernels.
2. **Homological computations:** complexes, syzygies, resolutions, Betti data.
3. **A mathematical application:** a concrete theorem about a projective variety or module proved using those certified calculations.

That would show the bridge is architectural rather than a one-operation novelty.

The real research program is therefore something like:

> Create a formal interface between abstract mathematics and computational commutative algebra, with Lean providing semantics and proof composition and Macaulay2 providing discovery and scalable computation.

I think that could make substantial advances in Lean formalization, but it could also change M2 itself: computations would gradually acquire explicit specifications, portable evidence, machine-checkable documentation, and a clearer distinction between heuristic answers and certified conclusions. That two-way influence is the genuinely compelling part.

---

# M2Lean: project base core

## 1. Project thesis

M2Lean will connect Macaulay2 and Lean as complementary mathematical systems.

Macaulay2 will remain a flexible, high-performance environment for computational commutative algebra and algebraic geometry. Lean will provide formal semantics, proof checking, and the ability to compose concrete computations with abstract theorems. Neither system should be forced to imitate the other.

The project will succeed when a mathematical object or claim can cross the boundary between the systems without losing its meaning, assumptions, provenance, or checkability.

The long-term objective is not merely an API. It is a shared foundation on which computational experiments can become formal theorems, formal questions can invoke serious algebraic computation, and important algorithms can gradually acquire precise specifications.

## 2. Guiding principles

### 2.1 Share mathematical meaning, not implementation traces

The primary interface will describe mathematical objects, claims, answers, and evidence. It will not depend on replaying M2’s internal control flow or translating its C++ and M2 source code into Lean.

An engine trace explains what an implementation did. A certificate establishes why a mathematical conclusion follows. M2Lean should request and preserve the latter.

### 2.2 Keep the initial trusted boundary small

Macaulay2 should initially be treated as an untrusted computational worker. Lean should accept an M2 result only after a sound checker establishes the corresponding proposition.

The initial trusted core should consist of:

- the Lean kernel;
- the formal semantics of the interchange representation;
- small certificate checkers with soundness theorems;
- the ordinary trusted components already required by Lean and mathlib.

A defect in M2, its bridge package, its serializer, or a certificate-generation routine must cause rejection or failure—not a false theorem.

### 2.3 Make formal verification progressive

M2Lean should support several assurance levels:

1. an object was transported successfully;
2. a computation was reproduced;
3. a result was checked from explicit evidence;
4. an algorithm has an abstract correctness proof;
5. an implementation is connected to a verified algorithm or refinement proof.

These levels must be visible to users. “Computed,” “checked,” and “formally proved” must not be presented as interchangeable statuses.

### 2.4 Preserve provenance

Every claim must record the mathematical and computational context needed to interpret it:

- coefficient domain and its exact parameters;
- variables, grading, weights, and degrees;
- monomial or module order;
- generators and presentations;
- relevant M2 and M2Lean versions;
- algorithm and meaningful options;
- assumptions and resource limits;
- whether probabilistic or heuristic steps occurred;
- the certificate type and checker version.

### 2.5 Prefer exact mathematics first

The first protocol and checkers should target exact coefficient domains and deterministic claims. Numerical approximations, floating-point computations, interval methods, probabilistic algorithms, and external black-box libraries can be added later with explicit semantics appropriate to them.

### 2.6 Design an extensible protocol, not a collection of ad hoc printers

The interchange format must be versioned, documented, testable, and independent of the pretty-printing conventions of either system. Extensions should add new object kinds and claim kinds without invalidating the core.

### 2.7 Serve users from both directions

Lean users should be able to delegate computation to M2 without leaving a proof. M2 users should be able to request certification without becoming Lean metaprogrammers. The bridge is bidirectional even if its internal trust relationship is asymmetric.

## 3. Scope and non-goals

### Initial scope

The first implementation should focus on:

- exact prime fields and rational coefficients;
- finitely generated multivariate polynomial rings;
- a small, precisely defined set of monomial orders;
- sparse polynomials;
- ideals, free modules, matrices, and graded maps;
- Gröbner data, reductions, membership witnesses, and syzygies;
- finite chain complexes and the evidence needed to reason about them.

### Explicit non-goals for the first project

The first project will not attempt to:

- prove the correctness of the complete Macaulay2 codebase;
- formalize the operational semantics of the M2 language or all of C++;
- support every M2 ring, package, coefficient type, or algorithm;
- certify claims merely because equivalent M2 code returned `true`;
- treat generated Lean text as trustworthy without kernel checking;
- hide semantic mismatches through lossy string conversion;
- promise practical certification for every large computation;
- replace M2’s existing user interface or Lean’s mathematical library.

## 4. Conceptual architecture

M2Lean should have four layers.

### 4.1 Mathematical interchange representation

The lowest layer describes mathematical data independently of either system’s in-memory representation.

Core object families should include:

- scalars and coefficient domains;
- variables and finite index sets;
- monomials and monomial orders;
- polynomials;
- rings and ring presentations;
- ideals and submodules;
- free and presented modules;
- matrices and homomorphisms;
- graded objects;
- chain complexes;
- named claims and evidence.

Every object should have a stable identifier within a document so that later objects can refer to it without duplicating context.

### 4.2 Semantics

Lean will define an interpretation from well-formed interchange objects into mathematical objects. Parsing a document is not itself a proof: the semantics layer must first validate structural conditions such as:

- variable indices are in range;
- exponent vectors have the declared arity;
- coefficients belong to the declared domain;
- matrices have compatible dimensions;
- graded maps have consistent degrees;
- monomial orders match an explicitly supported definition;
- referenced objects exist and have the expected kind.

A successful interpretation should return either a typed semantic object or a precise error. It should never silently repair ambiguous input.

### 4.3 Claims and certificates

A claim is a proposition plus evidence intended for a particular checker.

Conceptually:

```text
Claim {
  context
  proposition
  result
  evidence
  provenance
}
```

Examples include:

- a polynomial belongs to an ideal;
- two generating sets span the same ideal or module;
- a returned family is a Gröbner basis;
- a matrix represents a kernel or image;
- a sequence is a chain complex;
- a complex is exact in specified degrees;
- a displayed complex is a free resolution;
- a Hilbert-series computation agrees with certified graded data.

Each checker must have a Lean soundness theorem connecting acceptance of the certificate to the mathematical proposition.

### 4.4 User-facing integrations

Possible Lean-facing commands include:

```lean
example : targetProposition := by
  macaulay2
```

```lean
#m2 compute groebnerBasis I
#m2 inspect lastCertificate
```

Possible M2-facing commands include:

```m2
C = leanCertificate(gb I)
verifyWithLean C
```

```m2
certify res I
certificationStatus oo
```

These are design sketches, not committed syntax.

## 5. The first right project: the shared spine

The first project is a complete vertical slice called the **M2Lean Bridge Core**. Its purpose is to demonstrate that the architecture works across representation, computation, certification, and mathematical use.

### 5.1 Deliverable A: a versioned protocol

Define M2Lean Protocol version 0 with:

- a human-readable specification;
- a JSON encoding for development and debugging;
- canonical encodings for integers, rationals, finite-field elements, exponent vectors, and sparse maps;
- explicit object and claim tags;
- schema-version negotiation;
- error objects;
- provenance fields;
- small valid and invalid examples.

Canonicalization should be precise enough that fixtures can be compared across implementations. Large certificates may later use a compact binary encoding, but it should represent the same abstract protocol.

### 5.2 Deliverable B: Lean semantics

Create a Lean library that:

- parses protocol documents;
- validates their structure;
- interprets supported domains, polynomials, matrices, modules, and maps;
- exposes typed objects to later proofs;
- reports errors with paths into the source document;
- round-trips canonical fixtures.

The representation layer should be computational. Its interpretation should connect cleanly to mathlib’s existing algebraic objects rather than creating an isolated parallel universe.

### 5.3 Deliverable C: an M2 bridge package

Create an M2 package that:

- exports supported M2 objects into the protocol;
- imports supported protocol requests;
- invokes selected computations;
- extracts mathematical evidence already available from M2 computations;
- records provenance;
- communicates through files or a subprocess protocol;
- can ask Lean to verify a certificate and display the result.

The bridge package should use public or deliberately stabilized M2 interfaces wherever possible. Where new engine support is required, that dependency should be narrow and documented.

### 5.4 Deliverable D: the first sound certificate checkers

Implement checkers in an order that builds reusable infrastructure.

#### Polynomial identity

Check exact equality of sparse polynomials after normalization. This is the base operation beneath most later certificates.

#### Ideal and module membership

M2 supplies coefficients expressing an element as a linear combination of generators. Lean checks the identity and derives membership.

#### Equality of generated ideals or submodules

M2 supplies witnesses in both directions. Lean checks that each generator of either presentation belongs to the other span.

#### Gröbner basis

M2 supplies:

- the proposed basis;
- witnesses relating it to the original generators;
- reduction data for the required S-polynomials;
- the exact monomial order and coefficient context.

Lean checks the relevant criterion and proves that the basis has the claimed semantics. The checker should reuse mathlib’s formal polynomial-division infrastructure where practical.

#### Kernel and syzygy claims

M2 supplies candidate generators, verifies that their images vanish, and supplies Gröbner or reduction evidence establishing completeness. Lean checks both containment directions.

These claims form the computational foundation for the homological phase.

### 5.5 Deliverable E: homological vertical slice

Represent a finite graded complex of free modules and certify:

- matrix dimensions and grading;
- consecutive differentials compose to zero;
- claimed kernel/image relationships at selected positions;
- exactness at those positions;
- that a displayed finite complex resolves its cokernel, within explicitly stated bounds and hypotheses;
- Betti data read from the certified graded free modules.

Simply checking \(d_{i-1}d_i=0\) establishes a complex, not exactness. M2Lean must make that distinction explicit.

### 5.6 Deliverable F: one flagship theorem

Choose one concrete example that exercises the full path:

1. declare an algebraic object;
2. send a substantial computation to M2;
3. receive a resolution or related structure with certificates;
4. verify the computation in Lean;
5. apply an abstract Lean theorem;
6. state a final mathematical conclusion not obtained by merely reprinting M2 output.

Candidate subjects include a classical determinantal ideal, a rational normal curve, a small projective scheme, or a concrete finitely generated graded module. The example should be mathematically recognizable, computationally nontrivial, small enough for continuous integration, and rich enough to require both M2 and Lean.

## 6. Suggested repository shape

```text
M2Lean/
├── README.md
├── LICENSE
├── CONTRIBUTING.md
├── protocol/
│   ├── SPEC.md
│   ├── schema/
│   └── fixtures/
├── lean/
│   ├── lakefile.toml
│   └── M2Lean/
│       ├── Protocol/
│       ├── Semantics/
│       ├── Certificates/
│       ├── Tactic/
│       └── Examples/
├── m2/
│   ├── M2Lean.m2
│   └── tests/
├── examples/
│   ├── polynomial/
│   ├── modules/
│   ├── resolutions/
│   └── flagship/
└── docs/
    ├── architecture.md
    ├── trust-model.md
    ├── roadmap.md
    └── decisions/
```

The protocol specification should remain conceptually independent of the two implementations. Protocol changes that alter mathematical meaning should receive short architecture decision records.

## 7. Initial protocol sketch

A development-format request might have the following shape:

```json
{
  "m2leanVersion": "0",
  "requestId": "example-001",
  "objects": [
    {
      "id": "k",
      "kind": "RationalField"
    },
    {
      "id": "R",
      "kind": "PolynomialRing",
      "coefficientDomain": "k",
      "variables": ["x", "y", "z"],
      "monomialOrder": {
        "kind": "GRevLex"
      }
    }
  ],
  "claim": {
    "kind": "GroebnerBasis",
    "ring": "R",
    "generators": [],
    "basis": [],
    "evidence": {}
  },
  "provenance": {
    "producer": "Macaulay2",
    "producerVersion": "...",
    "algorithm": "...",
    "options": {}
  }
}
```

This is illustrative only. Version 0 should be designed from actual Lean and M2 representations, and it must specify semantics independently of JSON field names.

## 8. Trust and security model

### Trusted

- Lean’s kernel and normal trusted runtime assumptions;
- the definitions giving protocol objects mathematical meaning;
- soundness proofs for certificate checkers.

### Untrusted

- M2 computation results;
- M2 and C++ bridge code;
- serializers and transport;
- generated certificate files;
- generated Lean syntax before elaboration and kernel checking;
- caches;
- network or subprocess boundaries.

### Required behavior

- malformed data is rejected;
- unsupported semantics are rejected explicitly;
- certificates are bounded by configurable resource policies;
- the verifier does not execute arbitrary code embedded in a certificate;
- claims do not acquire proof status merely because an external process succeeded;
- probabilistic evidence is labeled and is not silently promoted to deductive proof;
- all accepted theorems can be rebuilt from retained source data and certificates.

## 9. Milestones

### Milestone 0: vocabulary and design

- Inventory overlapping Lean/mathlib and M2 concepts.
- Record semantic mismatches.
- Select exact coefficient domains and monomial orders for version 0.
- Write the trust model.
- Specify the first claim kinds.

Exit condition: representative objects and claims can be described unambiguously on paper.

### Milestone 1: transport and round-trip

- Implement the protocol parser in Lean.
- Implement export/import in M2.
- Round-trip rings, polynomials, matrices, and modules.
- Add cross-language fixture tests.

Exit condition: supported objects survive M2 → protocol → Lean and Lean → protocol → M2 with preserved semantics.

### Milestone 2: certified polynomial and module core

- Polynomial identity checker.
- Membership and span-equality checkers.
- Gröbner-basis checker.
- Kernel and syzygy checker.
- Initial Lean tactic and M2 certification command.

Exit condition: a corrupted result is rejected, while real M2 computations generate Lean theorems without `sorry` or newly introduced axioms.

### Milestone 3: complexes and resolutions

- Graded free modules and maps.
- Chain-complex representation.
- Exactness certificates.
- Certified finite resolution example.
- Betti-data connection.

Exit condition: Lean proves a nontrivial exactness or resolution statement using evidence produced by M2.

### Milestone 4: flagship mathematics

- Select and document the mathematical example.
- Perform the computation in M2.
- Verify its computational claims in Lean.
- derive an abstract mathematical consequence in Lean;
- publish the complete reproducible example.

Exit condition: the example clearly needs both systems and communicates the project’s value to mathematicians who use either one.

### Milestone 5: ergonomic integration

- Stable subprocess interaction.
- Useful diagnostics on both sides.
- Certificate caching and replay.
- Editor-facing status where practical.
- Documentation for extending object and certificate types.

Exit condition: a new user can run an example from each system and understand exactly what was computed and what was proved.

## 10. Acceptance criteria for the bridge core

The first project is complete only if:

- the protocol has a written, versioned mathematical specification;
- Lean and M2 independently implement the supported subset;
- exact round-trip fixtures run in continuous integration;
- at least one M2-produced Gröbner or module certificate is accepted by Lean;
- intentional mutations of the answer, order, coefficients, or witnesses are rejected;
- accepted claims contain no `sorry` and introduce no project-specific axioms;
- the retained certificate can be checked without trusting a live M2 process;
- provenance is displayed and inspectable;
- failure messages distinguish parsing, semantic, computational, and proof failures;
- a certified homological computation is completed;
- one flagship theorem combines an M2 computation with abstract Lean reasoning;
- the limitations of the supported fragment are documented.

## 11. Important design questions

The initial design phase must answer:

1. How should dynamically described M2 rings be interpreted as Lean types without making ordinary use unbearably cumbersome?
2. Which coefficient domains have sufficiently aligned exact semantics in both systems?
3. How will variable identity be separated from user-facing variable names?
4. How will each supported monomial and module order be specified mathematically?
5. Which M2 data already provides adequate certificates, and which algorithms need new evidence-export paths?
6. Should checkers construct explicit proof terms, use verified reflection, or combine both approaches?
7. How will very large certificates be streamed, cached, and checked without excessive proof-term growth?
8. How will partial computations, limits, and interrupted algorithms be represented?
9. Which statements require positive witnesses, and which negative results require substantially different certificates?
10. How will protocol evolution preserve replay of old certified computations?

## 12. Principal risks and mitigations

### Semantic mismatch

The two systems may use superficially similar objects with different conventions.

Mitigation: specify semantics before encodings; reject unsupported variants; maintain adversarial cross-language fixtures.

### Certificate explosion

Evidence for large Gröbner or homological computations may dwarf the result.

Mitigation: begin with small canonical examples; support sharing and hashing; investigate verified reflective checkers and compact certificate formats.

### Checker performance

A logically small checker can still elaborate enormous proof terms.

Mitigation: benchmark from the beginning; separate parsing, computation, and proof construction; use formally justified computation where appropriate.

### Oversized initial scope

Attempting all of computational algebra would prevent a working vertical slice.

Mitigation: enforce protocol version 0 boundaries and require a complete end-to-end path before adding domains.

### Accidental trust expansion

Convenient generated code, native execution, or bridge assertions could blur the trusted boundary.

Mitigation: maintain a dedicated trust-model document and test that fabricated certificates fail.

### Divergence from upstream communities

A private representation could duplicate mathlib or bypass stable M2 abstractions.

Mitigation: engage both communities early, design around existing public concepts, and upstream generally useful formal mathematics and M2 interfaces.

## 13. Broader research program

Once the bridge core is established, the project can grow in several directions.

### Richer certificate families

- elimination and implicitization;
- Hilbert functions, series, and polynomials;
- dimension and codimension;
- Fitting ideals and determinantal conditions;
- regular sequences and depth calculations;
- normalization and integral dependence;
- radical membership;
- primality and primary decomposition;
- spectral or numerical computations with appropriately different assurance models.

### Formal algorithm library

The certificate checkers will expose missing abstractions and theorems in Lean. These can develop into reusable formalizations of:

- monomial and module orders;
- Gröbner-basis criteria and algorithms;
- Schreyer orders and syzygies;
- graded free resolutions;
- Hilbert-series arguments;
- effective commutative algebra.

### M2 as a formalization guide

M2’s algorithms, test corpus, packages, documentation examples, and real user workloads can guide Lean formalization toward computationally relevant mathematics rather than only isolated textbook statements.

### Lean as a specification guide

Formalizing the meaning of M2 operations can sharpen:

- documentation of preconditions and guarantees;
- distinctions between mathematical objects and cached computational representations;
- provenance and reproducibility;
- algorithm-independent package interfaces;
- testing based on mathematical invariants.

### Selective verification of M2 internals

After stable specifications exist, high-value algorithms can be related more directly to Lean proofs. Possibilities include:

- proving an abstract algorithm correct in Lean and comparing M2 output against it;
- extracting a reference implementation for differential testing;
- refining selected engine routines against a formal specification;
- verifying small foundational components while retaining optimized untrusted computation elsewhere.

This is the appropriate stage for asking whether parts of M2 are “internally formally correct.” The bridge supplies the specifications and evidence vocabulary that make the question concrete.

## 14. Collaboration model

M2Lean should be developed as a collaboration between:

- Macaulay2 engine and package developers;
- Lean and mathlib algebra contributors;
- computational algebraists who can identify meaningful workflows;
- formalizers who can design tractable semantics and checkers;
- researchers interested in proof-producing computation.

Important decisions should be evaluated from all four perspectives:

1. Is the mathematical statement correct?
2. Can M2 produce the required evidence at realistic cost?
3. Can Lean check it with a manageable trusted base and acceptable performance?
4. Does the interface make sense to a working mathematician?

## 15. Immediate next actions

1. Establish the repository and license.
2. Open architecture decision records for the trust model, coefficient domains, monomial orders, and protocol encoding.
3. Inventory relevant mathlib definitions and current M2 evidence interfaces.
4. Write ten representative cross-language examples before freezing a schema.
5. Implement rational sparse-polynomial round-tripping.
6. Implement the polynomial identity and membership checkers.
7. Export an actual M2 change matrix or reduction witness.
8. Mutate the certificate deliberately and confirm Lean rejects it.
9. Add the first module/syzygy computation.
10. Select the flagship mathematical example only after the core path works.

## 16. Definition of success

In the near term, success means that Lean can formally use a nontrivial M2 computation and that an M2 user can request and inspect that certification.

In the medium term, success means that certified Gröbner, module, and homological computations are reusable components of larger Lean proofs.

In the long term, success means that computational commutative algebra and formal abstract mathematics no longer occupy separate ecosystems: conjectures, computations, certificates, and theorems can move between them while retaining precise meaning and explicit trust.

M2Lean should allow each system to remain excellent at what it already does while creating a mathematical capability that neither possesses alone.
