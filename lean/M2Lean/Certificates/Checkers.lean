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
import M2Lean.Protocol.Sparse

namespace M2Lean

/-! ## Identity, membership, span inclusion -/

/-- `lhs = rhs` as polynomials. -/
def checkIdentity (lhs rhs : SPoly) : Bool := polyEq lhs rhs

/-- `f = Σᵢ csᵢ · gsᵢ` with one cofactor per generator. -/
def checkMembership (f : SPoly) (gs cs : List SPoly) : Bool :=
  cs.length == gs.length && polyEq f (combo cs gs)

/-- Row-by-row membership of `src` generators in the span of `tgt`. -/
def checkSpanInclusion : List SPoly → List SPoly → List (List SPoly) → Bool
  | [], _, [] => true
  | f :: fs, tgt, cs :: rows =>
    checkMembership f tgt cs && checkSpanInclusion fs tgt rows
  | _, _, _ => false

/-! ## Chain complexes -/

/-- Both dimension chains match and every entry of `A * B` is zero.
(`A : r × m`, `B : m × c`.) -/
def checkComplexPair (r m c : Nat) (A B : SMatrix) : Bool :=
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

/-- The leading term of `p` with respect to `ord`, after
normalization; `none` iff `p` is (semantically) zero. -/
def leadTerm? (ord : MonOrder) (p : SPoly) : Option STerm :=
  (normalize p).foldl (init := none) fun acc t =>
    match acc with
    | none => some t
    | some s => if ord.cmp t.exps s.exps = .gt then some t else some s

def negP (p : SPoly) : SPoly := p.map fun t => { t with coeff := -t.coeff }

/-- One S-pair certificate: indices and division quotients. -/
structure SPairCert where
  i : Nat
  j : Nat
  quotients : List SPoly
  deriving Repr, Inhabited

/-- Verify one S-pair standard representation. -/
def checkSPair (ord : MonOrder) (basis : List SPoly) (sp : SPairCert) : Bool :=
  match basis[sp.i]?, basis[sp.j]? with
  | some bi, some bj =>
    match leadTerm? ord bi, leadTerm? ord bj with
    | some ti, some tj =>
      let l := zipMax ti.exps tj.exps
      let s : SPoly :=
        mulRaw [⟨1 / ti.coeff, zipSub l ti.exps⟩] bi ++
        mulRaw [⟨-(1 / tj.coeff), zipSub l tj.exps⟩] bj
      sp.quotients.length == basis.length &&
      polyEq s (combo sp.quotients basis) &&
      -- leading-monomial bound for every nonzero quotient
      (List.zip sp.quotients basis).all fun (q, b) =>
        let prod := normalize (mulRaw q b)
        prod.isEmpty ||
        (match leadTerm? ord prod, leadTerm? ord s with
         | some tp, some ts => ord.cmp tp.exps ts.exps ≠ .gt
         | _, some _ => true      -- product is zero: fine
         | _, none => false)      -- S-poly zero but product nonzero
    | _, _ => false               -- zero basis elements are rejected
  | _, _ => false

/-- Every non-coprime pair `i < j` is covered by some S-pair
certificate. -/
def sPairsCover (ord : MonOrder) (basis : List SPoly) (sps : List SPairCert) : Bool :=
  (List.range basis.length).all fun i =>
    (List.range basis.length).all fun j =>
      if h : i < j then
        match leadTerm? ord basis[i]!, leadTerm? ord basis[j]! with
        | some ti, some tj =>
          coprimeExps ti.exps tj.exps ||
          sps.any fun sp => sp.i == i && sp.j == j
        | _, _ => false
      else true

/-- The full Gröbner-basis certificate check. -/
def checkGroebner (ord : MonOrder) (gens basis : List SPoly)
    (basisCof genCof : List (List SPoly)) (sps : List SPairCert) : Bool :=
  basis.all (fun b => !(normalize b).isEmpty) &&
  checkSpanInclusion basis gens basisCof &&
  checkSpanInclusion gens basis genCof &&
  sps.all (checkSPair ord basis) &&
  sPairsCover ord basis sps

/-! ## Graded complexes (assurance level: `checked`) -/

/-- Entry `(i, j)` of `M` must be zero or homogeneous of degree
`src j - tgt i` (standard grading, all variables in degree 1). -/
def checkGradedMatrix (tgt src : List Int) (M : SMatrix) : Bool :=
  M.length == tgt.length &&
  M.all (fun row => row.length == src.length) &&
  (List.range tgt.length).all fun i =>
    (List.range src.length).all fun j =>
      let e := normalize ((M.getD i []).getD j [])
      e.isEmpty || isHomogeneousOfDeg e (src.getD j 0 - tgt.getD i 0)

/-- Graded complex: `modDegs` are the twists of `F₀, …, F_m`;
`mats[k]` is `d_{k+1} : F_{k+1} → F_k`.  Checks gradings and that
consecutive differentials compose to zero. -/
def checkGradedComplex (modDegs : List (List Int)) (mats : List SMatrix) : Bool :=
  mats.length + 1 == modDegs.length &&
  (List.range mats.length).all (fun k =>
    checkGradedMatrix (modDegs.getD k []) (modDegs.getD (k+1) []) (mats.getD k [])) &&
  (List.range (mats.length - 1)).all (fun k =>
    checkComposeZero (modDegs.getD k []).length (modDegs.getD (k+2) []).length
      (mats.getD k []) (mats.getD (k+1) []))

end M2Lean
