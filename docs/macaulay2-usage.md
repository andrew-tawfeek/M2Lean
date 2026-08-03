# Macaulay2 package usage

M2Lean 0.2.0 is tested with Macaulay2 1.24.11 and 1.26.06 on Debian 13.
Version 1.24.11 is the end-to-end reproducibility and benchmark environment;
1.26.06 passed direct and installed loading, package checks, documentation,
and the Macaulay2-only smoke suite in an isolated official-package container.
See [`../reproducibility/macaulay2-compatibility.md`](../reproducibility/macaulay2-compatibility.md)
for exact package versions and hashes. Other versions may work, but are not
part of the release matrix until the same checks pass.

## Load from a checkout

From the repository root:

```macaulay2
loadPackage("M2Lean", FileName => "m2/M2Lean.m2")
```

This is the preferred mode for development because the exact source under
test is explicit.

## Install for the current user

Run once from the repository root:

```macaulay2
installPackage("M2Lean", FileName => "m2/M2Lean.m2")
```

`installPackage` copies the package into Macaulay2's user-local package tree,
generates its documentation, and checks documentation references. In a fresh
session:

```macaulay2
loadPackage "M2Lean"
```

The public package-review and Macaulay2 distribution process has not yet been
completed. Until it is, installation requires a checkout of the tagged source.

## Construct and verify a document

```macaulay2
R = QQ[x,y,z];
I = ideal(x+y, y+z);
D = newM2LeanDocument "membership-demo";
membershipClaim(D, "mem1", x-z, I);
writeM2LeanDocument(D, "membership-demo.json")
```

The producer is untrusted: a written file is a certificate document, not a
proof. To invoke the Lean runtime verifier from the same session:

```macaulay2
verifyWithLean D
```

`verifyWithLean` locates the executable in this order:

1. the path named by `M2LEAN_CHECK`;
2. `m2lean-check` on `PATH`;
3. `$HOME/m2lean-lean/.lake/build/bin/m2lean-check`, the default used by the
   repository build script.

It returns the parsed report for programmatic inspection and prints each
claim's acceptance and assurance level.

## Public interface

| Symbol | Purpose |
|---|---|
| `newM2LeanDocument` | create a protocol document builder |
| `exportRing`, `exportIdeal`, `exportMatrix` | add supported objects and return their protocol IDs |
| `exportGradedFreeModule` | add a graded free module from an explicit degree list |
| `polynomialIdentityClaim` | emit an equality claim |
| `membershipClaim`, `unitIdealClaim` | emit ideal-membership evidence |
| `spanInclusionClaim` | express every source generator in the target ideal |
| `gbClaim` | emit a Gröbner basis, change-of-generators data, and every S-pair reduction |
| `nonMembershipClaim` | emit a nonzero reduced remainder relative to a referenced Gröbner claim |
| `chainComplexClaim` | emit matrices whose consecutive products are zero |
| `gradedComplexClaim` | additionally emit module degrees for graded runtime checking |
| `writeM2LeanDocument` | serialize a protocol 0.2.0 document |
| `divisionAlgorithm` | compute quotients and a reduced remainder used by certificates |
| `jsonOfPolynomial` | expose the canonical polynomial encoding for inspection |
| `verifyWithLean` | invoke the Lean runtime verifier |

`gbClaim` supports the protocol's Lex and GRevLex orders, but only GRevLex has
kernel-checked Gröbner soundness in the current Lean library. `ChainComplex`
means composition zero only. `GradedComplex` is runtime-checked and does not
assert exactness or minimality.

## Package checks

From the repository root:

```sh
M2 --script m2/tests/smoke.m2
M2 --script m2/tests/verify-loop.m2
```

The second command requires a built `m2lean-check`. The complete cross-system
gate is `bash scripts/test-all.sh`.

Before submission to the Macaulay2 package collection, run `installPackage`
with documentation checking enabled and `check "M2Lean"` on every advertised
Macaulay2 version.
