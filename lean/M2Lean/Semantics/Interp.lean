/-
M2Lean: interpretation of the sparse model into mathlib.

`toMv n` maps a sparse term list to an element of
`MvPolynomial (Fin n) α`.  The theorems here show that the executable
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

set_option linter.unusedSectionVars false

variable {α : Type*} [CommRing α] [DecidableEq α]
variable (n : Nat)

/-- Exponent list as a finitely supported function on `Fin n`.
Entries beyond the list (or beyond `n`) are zero. -/
def toMon (e : List Nat) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => e.getD i 0

@[simp] theorem toMon_apply (e : List Nat) (i : Fin n) :
    toMon n e i = e.getD i 0 := rfl

/-- Interpretation of a term. -/
def toTerm (t : STerm α) : MvPolynomial (Fin n) α :=
  monomial (toMon n t.exps) t.coeff

/-- Interpretation of a sparse polynomial. -/
def toMv (p : SPoly α) : MvPolynomial (Fin n) α :=
  (p.map (toTerm n)).sum

@[simp] theorem toMv_nil : toMv n ([] : SPoly α) = 0 := rfl

@[simp] theorem toMv_cons (t : STerm α) (p : SPoly α) :
    toMv n (t :: p) = toTerm n t + toMv n p := by
  simp [toMv]

theorem toMv_append (p q : SPoly α) :
    toMv n (p ++ q) = toMv n p + toMv n q := by
  simp [toMv]

theorem toMv_perm {p q : SPoly α} (h : p.Perm q) :
    toMv n p = toMv n q :=
  (h.map (toTerm n)).sum_eq

/-- Human-readable form of a term: `C c · Π xᵢ^eᵢ`.  Used to restate
certified conclusions in terms of `MvPolynomial.X`. -/
theorem toTerm_eq_prod (c : α) (es : List Nat) :
    toTerm n ⟨c, es⟩ = C c * ∏ i : Fin n, X i ^ es.getD i 0 := by
  rw [toTerm, monomial_eq]
  congr 1
  exact Finsupp.prod_fintype _ _ fun i => pow_zero _

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

theorem toTerm_mulTerm (s t : STerm α) :
    toTerm n (mulTerm s t) = toTerm n s * toTerm n t := by
  simp [toTerm, mulTerm, toMon_zipAdd, monomial_mul]

theorem toMv_map_mulTerm (s : STerm α) (q : SPoly α) :
    toMv n (q.map (mulTerm s)) = toTerm n s * toMv n q := by
  induction q with
  | nil => simp
  | cons t q ih => simp [ih, toTerm_mulTerm, mul_add]

theorem toMv_mulRaw (p q : SPoly α) :
    toMv n (mulRaw p q) = toMv n p * toMv n q := by
  induction p with
  | nil => simp [mulRaw]
  | cons s p ih =>
    simp only [mulRaw, List.flatMap_cons] at *
    rw [toMv_append, ih, toMv_map_mulTerm, toMv_cons, add_mul]

/-! ### Normalization preserves the interpretation -/

theorem toMv_insertMerged (t : STerm α) (l : SPoly α) :
    toMv n (insertMerged t l) = toTerm n t + toMv n l := by
  cases l with
  | nil =>
    by_cases h : t.coeff = 0 <;> simp [insertMerged, h, toTerm]
  | cons u rest =>
    by_cases he : t.exps = u.exps
    · by_cases hc : t.coeff + u.coeff = 0
      · simp only [insertMerged, he, if_pos, hc, ite_true]
        have : toTerm n t + toTerm n u = 0 := by
          simp [toTerm, he, ← map_add, hc]
        simp [← add_assoc, this]
      · simp only [insertMerged, he, if_pos, hc, ite_false]
        simp only [toMv_cons, ← add_assoc]
        congr 1
        simp [toTerm, he, map_add]
    · by_cases h0 : t.coeff = 0 <;>
        simp [insertMerged, he, h0, toTerm]

theorem toMv_merge1 (p : SPoly α) : toMv n (merge1 p) = toMv n p := by
  induction p with
  | nil => simp [merge1]
  | cons t rest ih =>
    simp only [merge1, List.foldr_cons] at *
    rw [toMv_insertMerged, ih, toMv_cons]

theorem toMv_sortTerms (p : SPoly α) : toMv n (sortTerms p) = toMv n p :=
  toMv_perm n (List.perm_insertionSort termGE p)

theorem getD_trimExps : ∀ (e : List Nat) (i : Nat),
    (trimExps e).getD i 0 = e.getD i 0
  | [], _ => rfl
  | a :: as, i => by
    have ih := getD_trimExps as
    cases htr : trimExps as with
    | nil =>
      cases i with
      | zero =>
        by_cases h : a = 0 <;> simp [trimExps, htr, h]
      | succ i =>
        have h0 : as.getD i 0 = 0 := by simpa using (htr ▸ ih i).symm
        by_cases h : a = 0 <;> simp [trimExps, htr, h] <;> simpa using h0.symm
    | cons b l =>
      cases i with
      | zero => simp [trimExps, htr]
      | succ i => simpa [trimExps, htr] using htr ▸ ih i

theorem toMon_trimExps (es : List Nat) :
    toMon n (trimExps es) = toMon n es := by
  ext i
  rw [toMon_apply, toMon_apply]
  exact getD_trimExps es i

theorem toTerm_canonTerm (t : STerm α) :
    toTerm n (canonTerm t) = toTerm n t := by
  simp [canonTerm, toTerm, toMon_trimExps]

theorem toMv_map_canonTerm (p : SPoly α) :
    toMv n (p.map canonTerm) = toMv n p := by
  induction p with
  | nil => simp
  | cons t p ih => simp [ih, toTerm_canonTerm]

theorem toMv_normalize (p : SPoly α) : toMv n (normalize p) = toMv n p := by
  rw [normalize, toMv_merge1, toMv_sortTerms, toMv_map_canonTerm]

/-- Soundness of the executable equality test. -/
theorem polyEq_sound {p q : SPoly α} (h : polyEq p q = true) :
    toMv n p = toMv n q := by
  have := of_decide_eq_true h
  rw [← toMv_normalize n p, ← toMv_normalize n q, this]

/-- Soundness of the executable zero test. -/
theorem polyIsZero_sound {p : SPoly α} (h : polyIsZero p = true) :
    toMv n p = 0 := by
  have := of_decide_eq_true h
  rw [← toMv_normalize n p, this, toMv_nil]

/-! ### Linear combinations -/

theorem toMv_combo (cs gs : List (SPoly α)) :
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
theorem combo_mem_span (cs gs : List (SPoly α)) :
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
