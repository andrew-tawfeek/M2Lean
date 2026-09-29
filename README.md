# M2Lean (core)

This branch contains only the infrastructure M2Lean needs to function: the
Macaulay2 package, the Lean library and verifier, and the Lake build files.
Examples, demos, case studies, the protocol specification, scripts, the paper,
and reproducibility records live on `master`.

## Contents

| Path | Role |
|---|---|
| `m2/M2Lean.m2` | The Macaulay2 package: builds certificate documents, serializes them to JSON, and calls the checker (`verifyWithLean`) |
| `lean/M2Lean/Protocol/` | Certificate parsing and the sparse polynomial representation |
| `lean/M2Lean/Certificates/Checkers.lean` | The executable checkers |
| `lean/M2Lean/Certificates/Soundness.lean`, `lean/M2Lean/Groebner/` | Soundness theorems for the checkers |
| `lean/M2Lean/Semantics/` | Interpretation of certificate data as mathlib polynomials |
| `lean/M2Lean/Verify.lean` | The verification driver: maps claims to checkers and produces the report |
| `lean/M2Lean/Tactic/Macaulay2.lean` | The `by macaulay2` tactic |
| `lean/Main.lean` | The `m2lean-check` executable |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Lake build files; they set `srcDir = "lean"` and pin mathlib and Lean 4.32.0 |

The `by macaulay2` tactic needs `m2/M2Lean.m2` at run time. It finds the file
through `M2LEAN_HOME` or the package's own Lake checkout, so the Lean half
alone is not enough for the tactic.

## Building

```sh
lake build                 # the M2Lean library
lake build m2lean-check    # the verifier executable
```

## How the checker works

`verifyWithLean` runs a program written in Lean, but it does not run Lean the
proof checker. No proof is built or checked by Lean's kernel at that moment.

### What happens when you call `verifyWithLean D`

1. **Macaulay2 writes the document.** It writes `D` to a temporary JSON file
   and runs `m2lean-check file.json -o report.json`, finding the executable
   through `PATH` or `M2LEAN_CHECK`.
2. **`m2lean-check` is compiled Lean, ordinary machine code.** `lake build`
   compiles the Lean functions to C and then to a native executable.
   `lean/Main.lean` imports only the executable slice (`M2Lean.Verify`) on
   purpose: the soundness proofs are irrelevant at runtime and would drag all
   of mathlib into native compilation.
3. **The program runs plain checking functions.** It parses the JSON
   (`parseDocument`), checks its structure (`validateDocument`), and for each
   claim calls a function that returns true or false. Membership, for
   example, uses `checkMembership`: it checks that there is one cofactor per
   generator and that `f = Σ cᵢ·gᵢ` holds as polynomials, by expanding and
   comparing.
4. **Macaulay2 reads the report back** and prints `accepted [proved]` and so
   on.

At run time this is a fast arithmetic check. The Macaulay2 side is
untrusted, and the checker repeats the key calculation independently.

### Where proof comes in: "proved" is a guarantee made in advance

The proof happens once, when the library is built, not per certificate.
`Certificates/Soundness.lean` proves theorems about the same checking
functions the executable runs:

```lean
theorem checkMembership_sound
    (h : checkMembership f gs cs = true) :
    toMv n f ∈ spanOf n gs
```

In words: whenever this function returns `true`, the polynomial really is in
the ideal, stated using mathlib's own polynomials and ideals. Lean's kernel
checks that theorem during `lake build`. `Verify.lean` labels a claim
`proved` only when its checker has such a theorem, and `checked` otherwise
(Lex Gröbner bases, graded complexes).

So `accepted [proved]` means that a function proven correct returned `true`
on this input. It does not mean that Lean produced a proof of this claim.

### What you still trust on the `verifyWithLean` path

- **Lean's compiler and runtime:** that the compiled machine code faithfully
  runs the function the theorem is about, including the big-integer
  arithmetic.
- **The JSON-to-Lean translation:** the parser and `Conv`, the step that reads
  coefficients as ℚ or ℤ/p. It has no correctness proof tying the JSON back to
  the ring you meant in Macaulay2.
- **The binary itself:** that the `m2lean-check` you run was built from these
  sources.

The JSON report is not itself a Lean proof object.

### The path where the kernel checks each claim

The `by macaulay2` tactic closes this gap:

1. It asks Macaulay2 for cofactors.
2. It builds the statement `checkMembership f gs cs = true`, and the kernel
   checks it with `decide`, evaluating it itself rather than running compiled
   code.
3. It feeds that into `checkMembership_sound` to get a real theorem.

On this path the compiler, the JSON parser, and the binary drop out of what
you trust. What is left is Lean's kernel and the soundness proof. Theorem
files that instantiate the soundness theorems work the same way.

In short, `verifyWithLean` is a quick independent check whose correctness has
been proven in advance. The tactic, or a theorem file, is where Lean's kernel
checks each individual certificate.

## M2Lean vs Macaulean: ideal membership

[Macaulean](https://github.com/Macaulean/Macaulean) also proves ideal
membership with help from Macaulay2, through its `m2idealmem` tactic. Both
tactics ask Macaulay2 for cofactors `cᵢ` with `f = Σ cᵢ·gᵢ` and both
produce proofs checked by Lean's kernel, but they differ in how the
identity is proved and in what the theorem says.

| | M2Lean `by macaulay2` | Macaulean `m2idealmem` |
|---|---|---|
| How the identity is proved | Proof by reflection: `decide` has the kernel evaluate `checkMembership f gs cs = true`, and `checkMembership_sound` turns that into the theorem | The tactic rebuilds `Σ cᵢ·gᵢ` as a Lean term and closes the goal with `simp` and `grind` |
| What is proved | `toMv n f ∈ spanOf n gs`: membership in mathlib's `MvPolynomial (Fin n) ℚ` | For `xᵢ : ℚ`, if every `gⱼ = 0` then `f = 0` (a consequence of membership) |
| How the goal is written | Sparse data (`SPoly ℚ` literals) | Ordinary Lean terms |
| Fixed cost | Imports Mathlib: about 4.7 s and 6.7 GB | About 1 s and 1.6 GB |

### Benchmark

Both tactics were run on the same generated problems (Macaulay2 1.26.06,
Xeon E5-1620 v2, 30-minute limit). Each problem was also run with the proof
replaced by `sorry`, to separate the cost of *stating* the goal from the
cost of *proving* it. Seconds, median of up to 3 runs; statement times
include each tool's import cost.

| Problem | Terms in f | M2Lean statement | **M2Lean proof** | Macaulean statement | **Macaulean proof** |
|---|---|---|---|---|---|
| 8 generators | 72 | 5.2 | **2.2** | 13.7 | **3.1** |
| 16 generators | 144 | 6.0 | **5.5** | 55.6 | **7.4** |
| 32 generators | 288 | 9.4 | **21.0** | 235.5 | **32.6** |
| 64 generators | 576 | 58.6 | **93.1** | 1136 | fails¹ |
| cofactor degree 3 | 119 | 5.2 | **6.1** | 52.2 | **6.0** |
| cofactor degree 4 | 209 | 5.5 | **14.6** | 245.0 | **14.7** |
| cofactor degree 6 | 476 | 6.4 | **72.4** | over 30 min | — |
| Macaulean's `foo3` | 40 | 5.0 | **2.9** | 12.7 | **2.7** |

¹ Macaulean's tactic hard-codes `simp (maxSteps := 100000)`, which is
exceeded at this size.

What the numbers show:

- **The proof methods cost about the same.** Reflection is not what makes
  M2Lean faster: proof times are equal at cofactor degrees 3–4 and within
  about 1.5× at 32 generators.
- **The input format is the main difference.** Elaborating a long
  polynomial goal written as Lean terms over ℚ is expensive (typeclass
  inference for every `+`, `*`, `^` and numeral) and grows roughly
  quadratically with the number of terms. M2Lean's goals are data and stay
  cheap. The flip side is usability: Macaulean accepts the goals users
  naturally write.
- **Limits differ.** Macaulean fails at 64 generators (its `simp` step
  budget) and cannot state the degree-6 goal within 30 minutes. M2Lean
  completes these, but its memory grows steeply: 15–16 GB at the largest
  completed problems, and about 35 GB (killed) at cofactor degree 12.
- **On small problems Macaulean is faster end to end**, because M2Lean
  pays Mathlib's import cost.
- The compiled `m2lean-check` checks every one of these certificates in
  under 0.2 s, but that path is not formally verified (see "How the
  checker works").
