-- smoke test for M2Lean.m2; run from repo root:
--   M2 --script m2/tests/smoke.m2
loadPackage("M2Lean", FileName => "m2/M2Lean.m2", Reload => true)

-- 1. order conventions vs SPEC 3.5
R = QQ[x,y,z];
f = x + y^2*z;
exps = for t in terms f list first exponents t;
assert(exps === {{0,2,1},{1,0,0}});  -- GRevLex: y^2 z  >  x
RL = QQ[x,y,z, MonomialOrder => Lex];
fL = substitute(f, RL);
expsL = for t in terms fL list first exponents t;
assert(expsL === {{1,0,0},{0,2,1}}); -- Lex: x > y^2 z
-- GRevLex tie-break: x^2 > x y > y^2 and x > y
S = QQ[x,y];
g = (x+y)^2;
assert((for t in terms g list first exponents t) === {{2,0},{1,1},{0,2}});
<< "order conventions OK" << endl;

-- 2. polynomial json
<< jsonOfPolynomial (x_S^2 - (1/2)*y_S) << endl;

-- 3. membership document
D = newM2LeanDocument "smoke-membership";
I = ideal(x_S + y_S, x_S - y_S);
membershipClaim(D, "c1", 2*x_S, I);
writeM2LeanDocument(D, "build/smoke-membership.json");
<< "membership doc written" << endl;

-- 4. GB certificate for the twisted cubic
T = QQ[a,b,c,d];
Itc = minors(2, matrix{{a,b,c},{b,c,d}});
D2 = newM2LeanDocument "smoke-gb";
gbClaim(D2, "gb1", Itc);
writeM2LeanDocument(D2, "build/smoke-gb.json");
<< "gb doc written; basis size = " << numcols gens gb Itc << endl;

-- 5. graded complex from the resolution of the twisted cubic
C = res comodule Itc;
D3 = newM2LeanDocument "smoke-complex";
gradedComplexClaim(D3, "cx1", {C.dd_1, C.dd_2});
writeM2LeanDocument(D3, "build/smoke-complex.json");
<< "complex doc written; betti = " << toString betti C << endl;

-- 6. division algorithm invariant
gbB = first entries gens gb Itc;
felt = a*(gbB#0) + b*(gbB#1) + (c+d)*(gbB#2);
(q, r) = divisionAlgorithm(felt, gbB);
assert(r == 0);
assert(felt == sum(#q, i -> q#i * gbB#i));
-- a non-member must leave a nonzero remainder
(q2, r2) = divisionAlgorithm(a^2*d - b^2*c, gbB);
assert(r2 != 0);
assert(a^2*d - b^2*c == sum(#q2, i -> q2#i * gbB#i) + r2);
<< "division algorithm OK" << endl;
<< "ALL SMOKE TESTS PASSED" << endl;
