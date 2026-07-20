/-
M2Lean: executable certificate checkers.

Each checker is a Boolean function on sparse data.  Checkers here are
*independent of the protocol AST*: they take plain mathematical data,
so the soundness theorems in `Certificates.Soundness` apply to them
directly, and the AST layer merely marshals validated documents into
these calls.

Assurance levels (SPEC §6):
- `checkMembership`, `checkSpanInclusion`, `checkComposeZero` have
  soundness theorems (`proved`).
- `checkGroebner` and `checkGradedComplex` are complete executable
  checks whose mathematical soundness rests on cited, not yet
  formalized, theorems (`checked`).  Nothing in
  `M2Lean/Examples` derives a Lean theorem from them.
-/
import Mathlib.Algebra.Field.Defs
import M2Lean.Protocol.Sparse

namespace M2Lean

variable {α : Type*} [Field α] [DecidableEq α]

/-- The assurance level carried by Gröbner-backed claims
(`GroebnerBasis`, `NonMembership`).  For GRevLex — Macaulay2's
default and the order of every certificate this project produces —
the checker has a kernel-checked soundness theorem
(`M2Lean.Groebner.Sound`, via `buchberger_criterion`); the Lex
soundness proof is future work, so Lex claims stay at `checked`. -/
def GroebnerSound.level : MonOrder → String
  | .grevlex => "proved"
  | .lex => "checked"

def GroebnerSound.acceptMessage : MonOrder → String
  | .grevlex => "Buchberger criterion verified; soundness kernel-checked"
  | .lex => "Buchberger criterion verified from certificate (Lex soundness theorem pending)"

/-! ## Identity, membership, span inclusion -/

/-- `lhs = rhs` as polynomials. -/
def checkIdentity (lhs rhs : SPoly α) : Bool := polyEq lhs rhs

/-- `f = Σᵢ csᵢ · gsᵢ` with one cofactor per generator. -/
def checkMembership (f : SPoly α) (gs cs : List (SPoly α)) : Bool :=
  cs.length == gs.length && polyEq f (combo cs gs)

/-- Row-by-row membership of `src` generators in the span of `tgt`. -/
def checkSpanInclusion : List (SPoly α) → List (SPoly α) → List (List (SPoly α)) → Bool
  | [], _, [] => true
  | f :: fs, tgt, cs :: rows =>
    checkMembership f tgt cs && checkSpanInclusion fs tgt rows
  | _, _, _ => false

/-! ## Chain complexes -/

/-- Both dimension chains match and every entry of `A * B` is zero.
(`A : r × m`, `B : m × c`.) -/
def checkComplexPair (r m c : Nat) (A B : SMatrix α) : Bool :=
  A.length == r && A.all (fun row => row.length == m) &&
  B.length == m && B.all (fun row => row.length == c) &&
  checkComposeZero r c A B

/-! ## Gröbner bases (assurance level: `checked`)

The checker verifies Buchberger's criterion in standard-representation
form: both span inclusions between generators and proposed basis, and
for every pair of basis elements with non-coprime leading monomials a
representation `S(bᵢ,bⱼ) = Σ qₖ bₖ` with
`lm(qₖ bₖ) ≤ lm(S(bᵢ,bⱼ))`. -/

/-- Pointwise maximum of exponent vectors (the lcm of monomials). -/
def zipMax : List Nat → List Nat → List Nat
  | [], l => l
  | l, [] => l
  | a :: as, b :: bs => (max a b) :: zipMax as bs

/-- Pointwise truncated difference (valid when the first argument
dominates, which the checker guarantees by construction). -/
def zipSub : List Nat → List Nat → List Nat
  | l, [] => l
  | [], _ => []
  | a :: as, b :: bs => (a - b) :: zipSub as bs

/-- Monomials are coprime: no variable occurs in both. -/
def coprimeExps (a b : List Nat) : Bool :=
  (List.zipWith min a b).all (· == 0)

/-- The leading term of `p` with respect to `ord`: the head of the
`ord`-sorted normalization; `none` iff `p` is (semantically) zero. -/
def leadTerm? (ord : MonOrder) (p : SPoly α) : Option (STerm α) :=
  (normalizeBy ord p).head?

/-- Certifies that the head of the `ord`-normalization strictly
dominates every other term — exactly the hypothesis the soundness
proof needs to identify the head with the abstract leading term.
(Always true when the sort comparator matches `ord`, but *checked*,
never assumed.) -/
def leadOK (ord : MonOrder) (p : SPoly α) : Bool :=
  match normalizeBy ord p with
  | [] => false
  | t :: rest => rest.all fun s => ord.cmp s.exps t.exps = .lt

/-- Every exponent vector of `p` has length at most `n`. -/
def arityLe (n : Nat) (p : SPoly α) : Bool :=
  p.all fun t => t.exps.length ≤ n

def negP (p : SPoly α) : SPoly α := p.map fun t => { t with coeff := -t.coeff }

/-- One S-pair certificate: indices and division quotients. -/
structure SPairCert (α : Type*) where
  i : Nat
  j : Nat
  quotients : List (SPoly α)
  deriving Repr

/-- The sparse S-polynomial of two polynomials with the given leading
terms. -/
def sparseSPoly (ti tj : STerm α) (bi bj : SPoly α) : SPoly α :=
  let l := zipMax ti.exps tj.exps
  mulRaw [⟨1 / ti.coeff, zipSub l ti.exps⟩] bi ++
  mulRaw [⟨-(1 / tj.coeff), zipSub l tj.exps⟩] bj

/-- Verify one S-pair standard representation. -/
def checkSPair (ord : MonOrder) (basis : List (SPoly α)) (sp : SPairCert α) : Bool :=
  match basis[sp.i]?, basis[sp.j]? with
  | some bi, some bj =>
    match leadTerm? ord bi, leadTerm? ord bj with
    | some ti, some tj =>
      leadOK ord bi && leadOK ord bj &&
      sp.quotients.length == basis.length &&
      polyEq (sparseSPoly ti tj bi bj) (combo sp.quotients basis) &&
      -- leading-monomial bound for every nonzero quotient product
      (List.zip sp.quotients basis).all fun (q, b) =>
        match leadTerm? ord (mulRaw q b), leadTerm? ord (sparseSPoly ti tj bi bj) with
        | none, _ => true                 -- product is zero: fine
        | some tp, some ts =>
          leadOK ord (mulRaw q b) && leadOK ord (sparseSPoly ti tj bi bj) &&
          ord.cmp tp.exps ts.exps ≠ .gt
        | some _, none => false           -- S-poly zero but product nonzero
    | _, _ => false                       -- zero basis elements are rejected
  | _, _ => false

/-- Every pair `i < j` is covered by some S-pair certificate. -/
def sPairsCover (ord : MonOrder) (basis : List (SPoly α)) (sps : List (SPairCert α)) : Bool :=
  (List.range basis.length).all fun i =>
    (List.range basis.length).all fun j =>
      if i < j then sps.any fun sp => sp.i == i && sp.j == j
      else true

/-- The full Gröbner-basis certificate check.  `n` is the declared
ring arity; bounding every exponent vector by it lets the soundness
theorem interpret all monomials in `Fin n`. -/
def checkGroebner (n : Nat) (ord : MonOrder) (gens basis : List (SPoly α))
    (basisCof genCof : List (List (SPoly α))) (sps : List (SPairCert α)) : Bool :=
  (gens ++ basis ++ basisCof.flatten ++ genCof.flatten ++
    sps.flatMap (·.quotients)).all (arityLe n) &&
  basis.all (leadOK ord) &&
  checkSpanInclusion basis gens basisCof &&
  checkSpanInclusion gens basis genCof &&
  sps.all (checkSPair ord basis) &&
  sPairsCover ord basis sps

/-- `a` divides `b` as monomials: every exponent of `a` is at most the
corresponding exponent of `b` (missing entries are 0). -/
def expsLe (a b : List Nat) : Bool :=
  (List.range (max a.length b.length)).all fun i => a.getD i 0 ≤ b.getD i 0

/-- Negative certificate: `f ∉ span basis`, witnessed by division data
`f = Σ qᵢ bᵢ + r` with `r ≠ 0` and no term of `r` divisible by any
leading monomial of the basis.  Sound only in combination with an
accepted Gröbner certificate for `basis` (see `Verify`): the reduced
nonzero remainder contradicts the Gröbner property if `f` were a
member. -/
def checkNonMembership (n : Nat) (ord : MonOrder) (basis : List (SPoly α))
    (f : SPoly α) (quots : List (SPoly α)) (r : SPoly α) : Bool :=
  ([f, r] ++ quots ++ basis).all (arityLe n) &&
  quots.length == basis.length &&
  polyEq f (addRaw (combo quots basis) r) &&
  leadOK ord r &&
  (normalizeBy ord r).all fun t => basis.all fun b =>
    leadOK ord b &&
    match leadTerm? ord b with
    | some tb => !(expsLe tb.exps t.exps)
    | none => false

/-! ## Graded complexes (assurance level: `checked`) -/

/-- Entry `(i, j)` of `M` must be zero or homogeneous of degree
`src j - tgt i` (standard grading, all variables in degree 1). -/
def checkGradedMatrix (tgt src : List Int) (M : SMatrix α) : Bool :=
  M.length == tgt.length &&
  M.all (fun row => row.length == src.length) &&
  (List.range tgt.length).all fun i =>
    (List.range src.length).all fun j =>
      let e := normalize ((M.getD i []).getD j [])
      e.isEmpty || isHomogeneousOfDeg e (src.getD j 0 - tgt.getD i 0)

/-- Graded complex: `modDegs` are the twists of `F₀, …, F_m`;
`mats[k]` is `d_{k+1} : F_{k+1} → F_k`.  Checks gradings and that
consecutive differentials compose to zero. -/
def checkGradedComplex (modDegs : List (List Int)) (mats : List (SMatrix α)) : Bool :=
  mats.length + 1 == modDegs.length &&
  (List.range mats.length).all (fun k =>
    checkGradedMatrix (modDegs.getD k []) (modDegs.getD (k+1) []) (mats.getD k [])) &&
  (List.range (mats.length - 1)).all (fun k =>
    checkComposeZero (modDegs.getD k []).length (modDegs.getD (k+2) []).length
      (mats.getD k []) (mats.getD (k+1) []))

end M2Lean
