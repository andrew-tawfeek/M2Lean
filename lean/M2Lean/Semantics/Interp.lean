/-
M2Lean: interpretation of the sparse model into mathlib.

`toMv n` maps a sparse term list to an element of
`MvPolynomial (Fin n) ℚ`.  The theorems here show that the executable
operations of `Protocol.Sparse` commute with this interpretation; they
are the bridge that turns byte-level certificate checks into
statements about actual polynomials.  This file is part of the
trusted semantics layer.
-/
import Mathlib
import M2Lean.Protocol.Sparse

namespace M2Lean

open MvPolynomial

noncomputable section

variable (n : Nat)

/-- Exponent list as a finitely supported function on `Fin n`.
Entries beyond the list (or beyond `n`) are zero. -/
def toMon (e : List Nat) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => e.getD i 0

@[simp] theorem toMon_apply (e : List Nat) (i : Fin n) :
    toMon n e i = e.getD i 0 := rfl

/-- Interpretation of a term. -/
def toTerm (t : STerm) : MvPolynomial (Fin n) ℚ :=
  monomial (toMon n t.exps) t.coeff

/-- Interpretation of a sparse polynomial. -/
def toMv (p : SPoly) : MvPolynomial (Fin n) ℚ :=
  (p.map (toTerm n)).sum

@[simp] theorem toMv_nil : toMv n [] = 0 := rfl

@[simp] theorem toMv_cons (t : STerm) (p : SPoly) :
    toMv n (t :: p) = toTerm n t + toMv n p := by
  simp [toMv]

theorem toMv_append (p q : SPoly) :
    toMv n (p ++ q) = toMv n p + toMv n q := by
  simp [toMv]

theorem toMv_perm {p q : SPoly} (h : p.Perm q) :
    toMv n p = toMv n q :=
  (h.map (toTerm n)).sum_eq

/-! ### Multiplication -/

theorem getD_zipAdd : ∀ (as bs : List Nat) (i : Nat),
    (zipAdd as bs).getD i 0 = as.getD i 0 + bs.getD i 0
  | [], bs, i => by simp [zipAdd]
  | a :: as, [], i => by cases i <;> simp [zipAdd]
  | a :: as, b :: bs, 0 => by simp [zipAdd]
  | a :: as, b :: bs, i + 1 => by
    simpa [zipAdd] using getD_zipAdd as bs i

theorem toMon_zipAdd (as bs : List Nat) :
    toMon n (zipAdd as bs) = toMon n as + toMon n bs := by
  ext i
  rw [Finsupp.add_apply, toMon_apply, toMon_apply, toMon_apply]
  exact getD_zipAdd as bs i

theorem toTerm_mulTerm (s t : STerm) :
    toTerm n (mulTerm s t) = toTerm n s * toTerm n t := by
  simp [toTerm, mulTerm, toMon_zipAdd, monomial_mul]

theorem toMv_map_mulTerm (s : STerm) (q : SPoly) :
    toMv n (q.map (mulTerm s)) = toTerm n s * toMv n q := by
  induction q with
  | nil => simp
  | cons t q ih => simp [ih, toTerm_mulTerm, mul_add]

theorem toMv_mulRaw (p q : SPoly) :
    toMv n (mulRaw p q) = toMv n p * toMv n q := by
  induction p with
  | nil => simp [mulRaw]
  | cons s p ih =>
    simp only [mulRaw, List.flatMap_cons] at *
    rw [toMv_append, ih, toMv_map_mulTerm, toMv_cons, add_mul]

/-! ### Normalization preserves the interpretation -/

theorem toMv_merge1 (p : SPoly) : toMv n (merge1 p) = toMv n p := by
  induction p using merge1.induct with
  | case1 => simp [merge1]
  | case2 t h =>
    simp [merge1, h, toTerm, toMv]
  | case3 t h =>
    simp [merge1, h]
  | case4 t₁ t₂ rest h ih =>
    rw [merge1, if_pos h, ih]
    simp only [toMv_cons]
    rw [← add_assoc]
    congr 1
    simp [toTerm, h, map_add]
  | case5 t₁ t₂ rest hne h0 ih =>
    rw [merge1]
    simp only [hne, if_neg, if_pos, h0, ite_false, ite_true]
    rw [ih]
    simp [toTerm, h0]
  | case6 t₁ t₂ rest hne h0 ih =>
    rw [merge1]
    simp only [hne, h0, ite_false]
    simp [ih]

theorem toMv_sortTerms (p : SPoly) : toMv n (sortTerms p) = toMv n p :=
  toMv_perm n (List.perm_insertionSort termGE p)

theorem toMv_normalize (p : SPoly) : toMv n (normalize p) = toMv n p := by
  rw [normalize, toMv_merge1, toMv_sortTerms]

/-- Soundness of the executable equality test. -/
theorem polyEq_sound {p q : SPoly} (h : polyEq p q = true) :
    toMv n p = toMv n q := by
  have := of_decide_eq_true h
  rw [← toMv_normalize n p, ← toMv_normalize n q, this]

/-- Soundness of the executable zero test. -/
theorem polyIsZero_sound {p : SPoly} (h : polyIsZero p = true) :
    toMv n p = 0 := by
  have := of_decide_eq_true h
  rw [← toMv_normalize n p, this, toMv_nil]

/-! ### Linear combinations -/

theorem toMv_combo (cs gs : List SPoly) :
    toMv n (combo cs gs) =
      ((List.zipWith (fun c g => toMv n c * toMv n g) cs gs)).sum := by
  induction cs generalizing gs with
  | nil => simp [combo]
  | cons c cs ih =>
    cases gs with
    | nil => simp [combo]
    | cons g gs =>
      simp only [combo, List.zipWith_cons_cons, List.foldr_cons] at *
      rw [addRaw, toMv_append, toMv_mulRaw, ih, List.sum_cons]

/-- The interpretation of a certified linear combination lies in the
span of the interpreted generators. -/
theorem combo_mem_span (cs gs : List SPoly) :
    toMv n (combo cs gs) ∈ Ideal.span {p | p ∈ gs.map (toMv n)} := by
  induction cs generalizing gs with
  | nil => simp [combo]
  | cons c cs ih =>
    cases gs with
    | nil => simp [combo]
    | cons g gs =>
      simp only [combo, List.zipWith_cons_cons, List.foldr_cons]
      rw [addRaw, toMv_append, toMv_mulRaw]
      refine Ideal.add_mem _ ?_ ?_
      · exact Ideal.mul_mem_left _ _
          (Ideal.subset_span (by simp))
      · refine Ideal.span_mono ?_ (ih gs)
        intro x hx
        simp only [Set.mem_setOf_eq, List.mem_map] at hx ⊢
        obtain ⟨a, ha, rfl⟩ := hx
        exact ⟨a, List.mem_cons_of_mem _ ha, rfl⟩

end

end M2Lean
