Basic usage:

1. Launch M2
2. `loadPackage("M2Lean", FileName => "THIS_REPO/m2/M2Lean.m2")` e.g. 

`loadPackage("M2Lean", FileName => "/mnt/c/Users/Andrew/Macaulay2/M2-Lean/M2Lean/m2/M2Lean.m2")`

Then exampels can be readily computed.

e.g.

```
-- EXAMPLE 1: certify ideal membership.
-- Is x^3 + y^3 in the ideal (x+y, x-y)?
R = QQ[x,y];
I = ideal(x+y, x-y)
f = x^3 + y^3
-- Display the cofactors Macaulay2 discovers.
f // gens I
-- Build a certificate document and ask Lean to check it.
D = newM2LeanDocument "demo-membership";
membershipClaim(D, "membership", f, I);
verifyWithLean D
-- Save the certificate to the Windows desktop.
writeM2LeanDocument(D, "/mnt/c/Users/Andrew/Desktop/" | D#"docId" | ".json")
-- Expected: membership accepted [proved].
```
====
```
-- EXAMPLE 2: certify equality of ideals using both inclusions.
R = QQ[x,y];
I = ideal(x+y, x-y)
J = ideal(x,y)
D = newM2LeanDocument "demo-equal-ideals";
spanInclusionClaim(D, "I-in-J", I, J);
spanInclusionClaim(D, "J-in-I", J, I);
verifyWithLean D
-- Save the certificate to the Windows desktop.
writeM2LeanDocument(D, "/mnt/c/Users/Andrew/Desktop/" | D#"docId" | ".json")
-- Expected: both inclusions accepted [proved].
-- Together these show that I and J generate the same ideal.
```
====
```
-- EXAMPLE 3: certify a Groebner basis and non-membership.
R = QQ[x,y,z,w, MonomialOrder => GRevLex];
I = minors(2, matrix{{x,y,z},{y,z,w}})
gens gb I
x % I
D = newM2LeanDocument "demo-groebner";
gbClaim(D, "basis", I);
nonMembershipClaim(D, "x-not-in-I", x, I, "groebnerClaim" => "basis");
verifyWithLean D
-- Save the certificate to the Windows desktop.
writeM2LeanDocument(D, "/mnt/c/Users/Andrew/Desktop/" | D#"docId" | ".json")
-- Expected: basis and x-not-in-I accepted [proved].
-- The negative claim uses a nonzero remainder and the certified basis.
```
====
```
-- EXAMPLE 4: certify that two affine zero sets have no common point.
-- I defines the affine cone over the twisted cubic.
-- J defines the line (t,1,0,0).
R = QQ[x,y,z,w];
I = minors(2, matrix{{x,y,z},{y,z,w}})
J = ideal(y-1,z,w)
U = I + J;
gens gb U
D = newM2LeanDocument "demo-empty-intersection";
unitIdealClaim(D, "one-in-sum", U);
verifyWithLean D
-- Save the certificate to the Windows desktop.
writeM2LeanDocument(D, "/mnt/c/Users/Andrew/Desktop/" | D#"docId" | ".json")
-- Expected: one-in-sum accepted [proved].
-- The certificate expresses 1 as a combination of generators of I+J.
-- A common zero would therefore imply 1=0.
```
====
```
-- EXAMPLE 5: certify that consecutive resolution maps compose to zero.
R = QQ[x,y,z,w];
I = minors(2, matrix{{x,y,z},{y,z,w}});
C = res comodule I;
betti C
C.dd_1
C.dd_2
C.dd_1 * C.dd_2
D = newM2LeanDocument "demo-chain-complex";
chainComplexClaim(D, "composition-zero", {C.dd_1, C.dd_2});
verifyWithLean D
-- Save the certificate to the Windows desktop.
writeM2LeanDocument(D, "/mnt/c/Users/Andrew/Desktop/" | D#"docId" | ".json")
-- Expected: composition-zero accepted [proved].
-- This certifies composition zero, not exactness or minimality.
```
