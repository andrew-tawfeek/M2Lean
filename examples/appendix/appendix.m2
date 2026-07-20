-- Five condensed M2 -> Lean crossings from different areas of
-- mathematics (paper, Appendix B).  Each produces one protocol
-- document; scripts/run-checks.sh verifies that m2lean-check accepts
-- all of them.
loadPackage("M2Lean", FileName => "m2/M2Lean.m2", Reload => true)

----------------------------------------------------------------------
-- B.1  Symmetric functions (invariant theory): Newton's identity
--      p3 = e1^3 - 3 e1 e2 + 3 e3  in QQ[x,y,z].
----------------------------------------------------------------------
R = QQ[x,y,z];
e1 = x+y+z; e2 = x*y+x*z+y*z; e3 = x*y*z;
p3 = x^3+y^3+z^3;
D = newM2LeanDocument "appendix-symmetric";
polynomialIdentityClaim(D, "newton3", p3, e1^3 - 3*e1*e2 + 3*e3);
writeM2LeanDocument(D, "examples/appendix/symmetric.json");
<< "wrote symmetric.json" << endl;

----------------------------------------------------------------------
-- B.2  Toric ideals / algebraic statistics: for 2x3 contingency
--      tables, the "long" Markov move times p22 lies in the ideal of
--      the two adjacent moves:
--      p22 (p11 p23 - p13 p21) = p23 m1 + p21 m2,
--      m1 = p11 p22 - p12 p21,  m2 = p12 p23 - p13 p22.
----------------------------------------------------------------------
S = QQ[p11,p12,p13,p21,p22,p23];
m1 = p11*p22 - p12*p21;
m2 = p12*p23 - p13*p22;
longMove = p11*p23 - p13*p21;
D = newM2LeanDocument "appendix-toric";
membershipClaim(D, "markov", p22*longMove, ideal(m1, m2));
writeM2LeanDocument(D, "examples/appendix/toric.json");
<< "wrote toric.json" << endl;

----------------------------------------------------------------------
-- B.3  Galois theory: the cyclotomic polynomial Phi_8 = x^4 + 1 is
--      separable: 1 in (f, f').  Hence no repeated root in any
--      extension of QQ; QQ(zeta_8)/QQ is etale.
----------------------------------------------------------------------
T = QQ[t];
f = t^4 + 1;
D = newM2LeanDocument "appendix-galois";
unitIdealClaim(D, "separable", ideal(f, diff(t, f)));
writeM2LeanDocument(D, "examples/appendix/galois.json");
<< "wrote galois.json" << endl;

----------------------------------------------------------------------
-- B.4  Combinatorics: K4 is not 3-colorable, by a graph-coloring
--      Nullstellensatz certificate (colors = cube roots of unity):
--      1 in ( x_i^3 - 1,  x_i^2 + x_i x_j + x_j^2 : ij edge of K4 ).
----------------------------------------------------------------------
G = QQ[x1,x2,x3,x4];
verts = {x1,x2,x3,x4};
vertexIdeal = for v in verts list v^3 - 1;
edgeIdeal = flatten for i from 0 to 3 list for j from i+1 to 3 list (
    (verts#i)^2 + (verts#i)*(verts#j) + (verts#j)^2);
U = ideal(vertexIdeal | edgeIdeal);
assert(U == 1);   -- discovery: K4 has no 3-coloring
D = newM2LeanDocument "appendix-coloring";
unitIdealClaim(D, "k4not3col", U);
writeM2LeanDocument(D, "examples/appendix/coloring.json");
<< "wrote coloring.json" << endl;

----------------------------------------------------------------------
-- B.5  Combinatorial algebraic geometry: the Stanley-Reisner ideal
--      of the 4-cycle, I = (ac, bd), is a complete intersection; its
--      Koszul resolution has Betti numbers 1,2,1.
----------------------------------------------------------------------
Q = QQ[a,b,c,d];
Isr = ideal(a*c, b*d);
C = res comodule Isr;
D = newM2LeanDocument "appendix-stanley-reisner";
gradedComplexClaim(D, "koszul", {C.dd_1, C.dd_2});
chainComplexClaim(D, "koszulcx", {C.dd_1, C.dd_2});
writeM2LeanDocument(D, "examples/appendix/stanley-reisner.json");
<< "wrote stanley-reisner.json" << endl;
<< "betti: " << toString betti C << endl;
<< "ALL APPENDIX EXAMPLES WRITTEN" << endl;
