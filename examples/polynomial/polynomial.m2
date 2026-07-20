-- Workflow 1 (README 5.6 / SPEC): polynomial and ideal-theoretic claims.
-- Produces examples/polynomial/polynomial.json with:
--   id1   PolynomialIdentity   (x+y)^2 = x^2+2xy+y^2 (expanded by M2)
--   mem1  IdealMembership      x^3+y^3 in (x+y, x-y)
--   inc1/inc2  SpanInclusion   (x+y, x-y) = (x, y)  (both directions)
loadPackage("M2Lean", FileName => "m2/M2Lean.m2", Reload => true)

R = QQ[x,y];
D = newM2LeanDocument "example-polynomial";

f = (x+y)^2;
polynomialIdentityClaim(D, "id1", f, x^2 + 2*x*y + y^2);

I = ideal(x+y, x-y);
membershipClaim(D, "mem1", x^3 + y^3, I);

J = ideal(x, y);
spanInclusionClaim(D, "inc1", I, J);
spanInclusionClaim(D, "inc2", J, I);

writeM2LeanDocument(D, "examples/polynomial/polynomial.json");
<< "wrote examples/polynomial/polynomial.json" << endl;
