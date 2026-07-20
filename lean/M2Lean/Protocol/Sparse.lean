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

/-- A sparse term `c · x^e`, over a coefficient type `α` (`ℚ` for
`RationalField` documents, `ZMod p` for `PrimeField` documents). -/
structure STerm (α : Type*) where
  coeff : α
  exps  : List Nat
  deriving DecidableEq, Repr

/-- A sparse polynomial: a list of terms, interpreted as their sum. -/
abbrev SPoly (α : Type*) := List (STerm α)

variable {α : Type*}

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
def termGE (s t : STerm α) : Prop := cmpGRevLex s.exps t.exps ≠ .lt

instance : DecidableRel (termGE (α := α)) := fun s t => by
  unfold termGE; infer_instance

def sortTerms (p : SPoly α) : SPoly α := List.insertionSort termGE p

/-- Sorting relation for an arbitrary supported order. -/
def termGEBy (ord : MonOrder) (s t : STerm α) : Prop := ord.cmp s.exps t.exps ≠ .lt

instance {ord : MonOrder} : DecidableRel (termGEBy (α := α) ord) := fun s t => by
  unfold termGEBy; infer_instance

def sortTermsBy (ord : MonOrder) (p : SPoly α) : SPoly α :=
  List.insertionSort (termGEBy ord) p

/-- Fold step of `merge1`: prepend `t` to an already-merged tail,
combining with the head when the exponent vectors agree and dropping
zero coefficients.  Structural recursion only, so that certificate
checks reduce inside the Lean kernel (`by decide`). -/
def insertMerged [DecidableEq α] [Zero α] [Add α] (t : STerm α) : SPoly α → SPoly α
  | [] => if t.coeff = 0 then [] else [t]
  | u :: rest =>
    if t.exps = u.exps then
      let c := t.coeff + u.coeff
      if c = 0 then rest else ⟨c, t.exps⟩ :: rest
    else if t.coeff = 0 then u :: rest
    else t :: u :: rest

/-- Merge adjacent terms with equal exponent vectors and drop zero
coefficients.  Assumes (for effectiveness, not soundness) that equal
exponent vectors are adjacent, which sorting guarantees. -/
def merge1 [DecidableEq α] [Zero α] [Add α] (p : SPoly α) : SPoly α := p.foldr insertMerged []

/-- Drop trailing zero exponents, so that the same monomial written
with different paddings (e.g. `[1]` vs `[1,0,0]`) has one canonical
representation inside `normalize`. -/
def trimExps : List Nat → List Nat
  | [] => []
  | a :: as =>
    match trimExps as with
    | [] => if a = 0 then [] else [a]
    | l => a :: l

def canonTerm (t : STerm α) : STerm α := ⟨t.coeff, trimExps t.exps⟩

/-- Canonicalize a raw term list. -/
def normalize [DecidableEq α] [Zero α] [Add α] (p : SPoly α) : SPoly α := merge1 (sortTerms (p.map canonTerm))

/-- Canonicalize with the given order's comparator, so the head of the
result is the leading term with respect to that order (used by the
Gröbner checkers; `normalize` itself uses a fixed comparator). -/
def normalizeBy [DecidableEq α] [Zero α] [Add α] (ord : MonOrder) (p : SPoly α) : SPoly α :=
  merge1 (sortTermsBy ord (p.map canonTerm))

/-! ## Ring operations on raw term lists -/

/-- Product of two terms. -/
def mulTerm [Mul α] (s t : STerm α) : STerm α :=
  { coeff := s.coeff * t.coeff, exps := zipAdd s.exps t.exps }

/-- Raw sum: concatenation. -/
def addRaw (p q : SPoly α) : SPoly α := p ++ q

/-- Raw product: all pairwise term products. -/
def mulRaw [Mul α] (p q : SPoly α) : SPoly α := p.flatMap fun s => q.map (mulTerm s)

/-- `combo cs gs` is the raw linear combination `Σᵢ csᵢ · gsᵢ`
(truncating at the shorter list). -/
def combo [Mul α] (cs gs : List (SPoly α)) : SPoly α :=
  (List.zipWith mulRaw cs gs).foldr addRaw []

/-- Decidable semantic equality of raw term lists (via normalization).
Sound by `Interp.polyEq_sound`; used by every checker. -/
def polyEq [DecidableEq α] [Zero α] [Add α] (p q : SPoly α) : Bool := decide (normalize p = normalize q)

/-- Is `p` semantically zero? -/
def polyIsZero [DecidableEq α] [Zero α] [Add α] (p : SPoly α) : Bool := decide (normalize p = [])

/-! ## Canonical-form validation (SPEC §3.4)

These checks enforce protocol strictness.  They are *not* needed for
soundness (a non-canonical but honest certificate would still verify);
they exist so that both implementations agree byte-for-byte on
canonical documents and so malformed input is rejected loudly. -/

def isCanonical [DecidableEq α] [Zero α] (ord : MonOrder) (arity : Nat) (p : SPoly α) : Bool :=
  p.all (fun t => t.coeff ≠ 0 && t.exps.length = arity) &&
  (p.zip (p.drop 1)).all (fun (s, t) => ord.cmp s.exps t.exps = .gt)

/-- A raw polynomial (allowed only in `PolynomialIdentity`): arity must
still be respected. -/
def isRaw (arity : Nat) (p : SPoly α) : Bool :=
  p.all (fun t => t.exps.length = arity)

/-! ## Sparse matrices -/

/-- A sparse matrix: rows of raw polynomials. -/
abbrev SMatrix (α : Type*) := List (List (SPoly α))

def SMatrix.row (M : SMatrix α) (i : Nat) : List (SPoly α) := M.getD i []

def SMatrix.col (M : SMatrix α) (j : Nat) : List (SPoly α) :=
  M.map fun r => r.getD j []

/-- Entry `(i, j)` of the matrix product `A * B` as a raw polynomial:
`Σₖ A i k · B k j`. -/
def mulEntry [Mul α] (A B : SMatrix α) (i j : Nat) : SPoly α :=
  combo (A.row i) (B.col j)

/-- All entries of `A * B` normalize to zero.  `r`, `m`, `c` are the
declared dimensions (`A : r × m`, `B : m × c`). -/
def checkComposeZero [DecidableEq α] [Zero α] [Add α] [Mul α]
    (r c : Nat) (A B : SMatrix α) : Bool :=
  (List.range r).all fun i => (List.range c).all fun j =>
    polyIsZero (mulEntry A B i j)

/-! ## Homogeneity (for `GradedComplex`) -/

/-- Every term of `p` has total degree `d`. -/
def isHomogeneousOfDeg (p : SPoly α) (d : Int) : Bool :=
  p.all fun t => (totalDeg t.exps : Int) = d

end M2Lean
