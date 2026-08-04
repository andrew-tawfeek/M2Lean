-- The Alpoge--Fable Jacobian-conjecture counterexample (case study; README §5).
--
-- Background (as reported July 2026).  The Jacobian Conjecture (Keller's
-- problem, 1939) asserts that a polynomial map F : C^n -> C^n whose
-- Jacobian determinant is a nonzero constant has a polynomial inverse.
-- On 2026-07-19 Levent Alpoge announced an explicit counterexample in
-- dimension three, found with the assistance of Anthropic's "Claude
-- Fable 5" model (the problem having been floated by Akhil Mathew); the
-- short announcement was checked by many mathematicians within a day,
-- and Terence Tao related it to the Bass-Connell-Wright and Yagzhev
-- reductions.  Sources are cited in examples/jacobian and paper/m2lean.tex.
-- M2Lean neither trusts nor relies on that provenance: the object below
-- is a self-contained algebraic fact, and everything is re-verified by
-- the Lean checkers.  (See docs/trust-model.md: provenance never
-- influences acceptance.)
--
-- The map is
--   F(x,y,z) = ( (1+xy)^3 z + y^2 (1+xy)(4+3xy),
--                y + 3x(1+xy)^2 z + 3x y^2 (4+3xy),
--                2x - 3x^2 y - x^3 z ).
-- Its Jacobian determinant is the constant -2 (the conjecture's
-- hypothesis holds), yet it is not injective: the three distinct points
--   P0 = (0, 0, -1/4),  P1 = (1, -3/2, 13/2),  P2 = (-1, 3/2, 13/2)
-- all map to (-1/4, 0, 0) (so the conclusion fails).
--
-- This script exports, as an M2Lean protocol document:
--   detJac        PolynomialIdentity  det Jac(F) = -2   (M2's computation)
--   P{k}_F{i}     IdealMembership     F_i - v_i in m_{P_k}   (9 claims),
-- where m_P = (x-a, y-b, z-c) is the maximal ideal of P = (a,b,c).  The
-- membership  F_i - v_i in m_P  is the protocol-native encoding of the
-- evaluation F_i(P) = v_i: the cofactor identity
--   F_i - v_i = A(x-a) + B(y-b) + C(z-c),
-- evaluated at P, kills the ideal part and forces F_i(P) = v_i.  These
-- memberships are M2's transported evidence for the collision; Lean
-- kernel-checks them and confirms their soundness, and -- checking the
-- collision itself by evaluation -- derives non-injectivity, hence a
-- machine-checked refutation of the conjecture as stated
-- (M2Lean.Examples.Jacobian).
loadPackage("M2Lean", FileName => "m2/M2Lean.m2", Reload => true)

R = QQ[x,y,z];
F1 = (1+x*y)^3*z + y^2*(1+x*y)*(4+3*x*y);
F2 = y + 3*x*(1+x*y)^2*z + 3*x*y^2*(4+3*x*y);
F3 = 2*x - 3*x^2*y - x^3*z;
Fcoords = {F1, F2, F3};
vars3 = {x, y, z};

-- Jacobian J with J_(i,j) = d F_i / d x_j  (rows = components, cols = vars)
Jac = matrix table(3, 3, (i,j) -> diff(vars3#j, Fcoords#i));
assert(det Jac == -2_R);  -- discovery/verification step: the hypothesis holds

D = newM2LeanDocument "jacobian-counterexample";

-- (1) the conjecture's hypothesis: the Jacobian determinant is constant -2
polynomialIdentityClaim(D, "detJac", det Jac, -2_R);

-- (2) the conjecture's conclusion fails: three distinct points collide.
-- Every component value is certified as a membership in the point's
-- maximal ideal.  All three points map to the common image (-1/4,0,0).
img = {(-1)/4, 0, 0};
points = {
    {"P0", { 0,      0,    (-1)/4 }},
    {"P1", { 1,   (-3)/2,  13/2   }},
    {"P2", {-1,     3/2,   13/2   }}
    };
for pt in points do (
    name := pt#0;
    coords := pt#1;
    m := ideal(x - coords#0, y - coords#1, z - coords#2);
    for i from 0 to 2 do
        membershipClaim(D, name | "_F" | toString(i+1),
            Fcoords#i - img#i, m);
    );

writeM2LeanDocument(D, "examples/jacobian/jacobian.json");
<< "wrote examples/jacobian/jacobian.json" << endl;
<< "det Jacobian = " << det Jac << "   (hypothesis: nonzero constant)" << endl;
<< "F(P0) = F(P1) = F(P2) = (-1/4, 0, 0)   (conclusion fails: not injective)" << endl;
