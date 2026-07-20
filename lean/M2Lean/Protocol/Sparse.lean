/-
M2Lean: the executable sparse-polynomial model.

This file is part of the *trusted semantics layer* (docs/trust-model.md):
the definitions here give protocol polynomials their computational
meaning.  It keeps mathlib dependencies minimal (only `List.insertionSort`)
so that the computational model is small and auditable; the connection
to mathematics lives in `M2Lean.Semantics.Interp`.

Exponent vectors are positional lists of naturals; entries beyond the
end of the list denote exponent 0.  Protocol validation enforces that
all exponent vectors in a document have the declared ring arity, but
none of the *soundness* results depend on that (see `Interp`).
-/
import Mathlib.Data.List.Sort

namespace M2Lean

/-- A sparse term `c · x^e`. -/
structure STerm where
  coeff : Rat
  exps  : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- A sparse polynomial: a list of terms, interpreted as their sum. -/
abbrev SPoly := List STerm

/-- Pointwise sum of exponent vectors, padding the shorter with zeros. -/
def zipAdd : List Nat → List Nat → List Nat
  | [], l => l
  | l, [] => l
  | a :: as, b :: bs => (a + b) :: zipAdd as bs

/-- Total degree of an exponent vector. -/
def totalDeg (e : List Nat) : Nat := e.foldr (· + ·) 0

/-! ## Monomial orders (SPEC §3.5, normative definitions) -/

/-- Lexicographic order: at the smallest index where the vectors
differ, the larger entry wins.  Missing entries count as 0. -/
def cmpLex : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], bs => if bs.all (· = 0) then .eq else .lt
  | as, [] => if as.all (· = 0) then .eq else .gt
  | a :: as, b :: bs =>
    if a < b then .lt else if b < a then .gt else cmpLex as bs

/-- Compare reversed equal-length exponent vectors for GRevLex: at the
first index where the *reversed* vectors differ (i.e. the largest
original index), the **smaller** entry wins. -/
def cmpRevAux : List Nat → List Nat → Ordering
  | x :: xs, y :: ys =>
    if x < y then .gt else if y < x then .lt else cmpRevAux xs ys
  | _, _ => .eq

/-- Graded reverse lexicographic order (Macaulay2's default):
compare total degrees first; ties are broken by `cmpRevAux` on the
zero-padded, reversed vectors. -/
def cmpGRevLex (a b : List Nat) : Ordering :=
  match compare (totalDeg a) (totalDeg b) with
  | .eq =>
    let m := max a.length b.length
    cmpRevAux ((a ++ List.replicate (m - a.length) 0).reverse)
              ((b ++ List.replicate (m - b.length) 0).reverse)
  | o => o

inductive MonOrder where
  | lex | grevlex
  deriving DecidableEq, Repr

def MonOrder.cmp : MonOrder → List Nat → List Nat → Ordering
  | .lex => cmpLex
  | .grevlex => cmpGRevLex

/-! ## Normalization

`normalize` sorts terms (descending in a fixed total comparator) and
merges runs of equal exponent vectors, dropping zero coefficients.
Soundness of the checkers only needs that `normalize` preserves the
interpretation (`Interp.toMv_normalize`); *which* comparator is used
here is irrelevant for soundness, so we fix GRevLex. -/

/-- The sorting relation: `s` precedes `t` when its exponent vector is
not smaller in GRevLex. -/
def termGE (s t : STerm) : Prop := cmpGRevLex s.exps t.exps ≠ .lt

instance : DecidableRel termGE := fun s t => by
  unfold termGE; infer_instance

def sortTerms (p : SPoly) : SPoly := List.insertionSort termGE p

/-- Merge adjacent terms with equal exponent vectors and drop zero
coefficients.  Assumes (for effectiveness, not soundness) that equal
exponent vectors are adjacent, which sorting guarantees. -/
def merge1 : SPoly → SPoly
  | [] => []
  | [t] => if t.coeff = 0 then [] else [t]
  | t₁ :: t₂ :: rest =>
    if t₁.exps = t₂.exps then
      merge1 ({ coeff := t₁.coeff + t₂.coeff, exps := t₁.exps } :: rest)
    else if t₁.coeff = 0 then
      merge1 (t₂ :: rest)
    else
      t₁ :: merge1 (t₂ :: rest)
  termination_by l => l.length

/-- Canonicalize a raw term list. -/
def normalize (p : SPoly) : SPoly := merge1 (sortTerms p)

/-! ## Ring operations on raw term lists -/

/-- Product of two terms. -/
def mulTerm (s t : STerm) : STerm :=
  { coeff := s.coeff * t.coeff, exps := zipAdd s.exps t.exps }

/-- Raw sum: concatenation. -/
def addRaw (p q : SPoly) : SPoly := p ++ q

/-- Raw product: all pairwise term products. -/
def mulRaw (p q : SPoly) : SPoly := p.flatMap fun s => q.map (mulTerm s)

/-- `combo cs gs` is the raw linear combination `Σᵢ csᵢ · gsᵢ`
(truncating at the shorter list). -/
def combo (cs gs : List SPoly) : SPoly :=
  (List.zipWith mulRaw cs gs).foldr addRaw []

/-- Decidable semantic equality of raw term lists (via normalization).
Sound by `Interp.polyEq_sound`; used by every checker. -/
def polyEq (p q : SPoly) : Bool := decide (normalize p = normalize q)

/-- Is `p` semantically zero? -/
def polyIsZero (p : SPoly) : Bool := decide (normalize p = [])

/-! ## Canonical-form validation (SPEC §3.4)

These checks enforce protocol strictness.  They are *not* needed for
soundness (a non-canonical but honest certificate would still verify);
they exist so that both implementations agree byte-for-byte on
canonical documents and so malformed input is rejected loudly. -/

def isCanonical (ord : MonOrder) (arity : Nat) (p : SPoly) : Bool :=
  p.all (fun t => t.coeff ≠ 0 && t.exps.length = arity) &&
  (p.zip (p.drop 1)).all (fun (s, t) => ord.cmp s.exps t.exps = .gt)

/-- A raw polynomial (allowed only in `PolynomialIdentity`): arity must
still be respected. -/
def isRaw (arity : Nat) (p : SPoly) : Bool :=
  p.all (fun t => t.exps.length = arity)

/-! ## Sparse matrices -/

/-- A sparse matrix: rows of raw polynomials. -/
abbrev SMatrix := List (List SPoly)

def SMatrix.row (M : SMatrix) (i : Nat) : List SPoly := M.getD i []

def SMatrix.col (M : SMatrix) (j : Nat) : List SPoly :=
  M.map fun r => r.getD j []

/-- Entry `(i, j)` of the matrix product `A * B` as a raw polynomial:
`Σₖ A i k · B k j`. -/
def mulEntry (A B : SMatrix) (i j : Nat) : SPoly :=
  combo (A.row i) (B.col j)

/-- All entries of `A * B` normalize to zero.  `r`, `m`, `c` are the
declared dimensions (`A : r × m`, `B : m × c`). -/
def checkComposeZero (r c : Nat) (A B : SMatrix) : Bool :=
  (List.range r).all fun i => (List.range c).all fun j =>
    polyIsZero (mulEntry A B i j)

/-! ## Homogeneity (for `GradedComplex`) -/

/-- Every term of `p` has total degree `d`. -/
def isHomogeneousOfDeg (p : SPoly) (d : Int) : Bool :=
  p.all fun t => (totalDeg t.exps : Int) = d

end M2Lean
