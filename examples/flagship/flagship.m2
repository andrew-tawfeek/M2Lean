-- The flagship example (README 5.6, milestone M4).
--
-- The twisted cubic curve C in P^3 is cut out by the 2x2 minors of
--   [ x y z ]
--   [ y z w ],
-- i.e. I = (xz - y^2, xw - yz, yw - z^2).  Let L be the affine line
-- {(t, 1, 0, 0)} = V(J), J = (y - 1, z, w).
--
-- Macaulay2 discovers that I + J is the unit ideal and produces an
-- explicit certificate 1 = sum c_i g_i; it also produces the minimal
-- graded free resolution of R/I (the Eagon-Northcott complex,
-- Betti numbers 1, 3, 2) with its differentials, and a Groebner
-- certificate for I.  Lean re-verifies all of this and derives, from
-- the unit-ideal certificate alone, the geometric conclusion that the
-- cone over C and the line L have no common point over ANY nontrivial
-- commutative Q-algebra (M2Lean.Examples.Flagship.lean).
loadPackage("M2Lean", FileName => "m2/M2Lean.m2", Reload => true)

R = QQ[x,y,z,w];
I = minors(2, matrix{{x,y,z},{y,z,w}});
J = ideal(y - 1, z, w);
U = I + J;
assert(U == 1);  -- discovery step: M2 sees the intersection is empty

D = newM2LeanDocument "flagship";
unitIdealClaim(D, "unit1", U);
gbClaim(D, "gb1", I);
C = res comodule I;
gradedComplexClaim(D, "res1", {C.dd_1, C.dd_2});
chainComplexClaim(D, "cx1", {C.dd_1, C.dd_2});
writeM2LeanDocument(D, "examples/flagship/flagship.json");
<< "wrote examples/flagship/flagship.json" << endl;
<< "betti of resolution: " << toString betti C << endl;
