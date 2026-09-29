/-
M2Lean: soundness theorems for the certificate checkers.

These theorems realize the project's central contract (SPEC §4, §6):
if a `proved`-level checker accepts, the corresponding *mathlib*
proposition holds.  Acceptance of a corrupted certificate would
require a false theorem here — and these are checked by the Lean
kernel with no additional axioms.
-/
import Mathlib
import M2Lean.Protocol.Sparse
import M2Lean.Semantics.Interp
import M2Lean.Certificates.Checkers

namespace M2Lean

open MvPolynomial

noncomputable section

variable {α : Type*} [Field α] [DecidableEq α]
variable (n : Nat)

/-! ### Polynomial identity -/

theorem checkIdentity_sound {lhs rhs : SPoly α}
    (h : checkIdentity lhs rhs = true) :
    toMv n lhs = toMv n rhs :=
  polyEq_sound n h

/-! ### Ideal membership -/

/-- The span of the interpreted generators. -/
def spanOf (gs : List (SPoly α)) : Ideal (MvPolynomial (Fin n) α) :=
  Ideal.span {p | p ∈ gs.map (toMv n)}

theorem checkMembership_sound {f : SPoly α} {gs cs : List (SPoly α)}
    (h : checkMembership f gs cs = true) :
    toMv n f ∈ spanOf n gs := by
  have h2 : polyEq f (combo cs gs) = true :=
    (Bool.and_eq_true .. ▸ h).2
  rw [spanOf, polyEq_sound n h2]
  exact combo_mem_span n cs gs

/-! ### Span inclusion -/

theorem checkSpanInclusion_sound :
    ∀ {src tgt : List (SPoly α)} {rows : List (List (SPoly α))},
    checkSpanInclusion src tgt rows = true →
    spanOf n src ≤ spanOf n tgt := by
  intro src
  induction src with
  | nil =>
    intro tgt rows _
    rw [spanOf]
    simp only [List.map_nil]
    refine Ideal.span_le.mpr ?_
    rintro x ⟨⟩
  | cons f fs ih =>
    intro tgt rows h
    cases rows with
    | nil => simp [checkSpanInclusion] at h
    | cons cs rows =>
      simp only [checkSpanInclusion, Bool.and_eq_true] at h
      refine Ideal.span_le.mpr ?_
      rintro x hx
      simp only [Set.mem_setOf_eq, List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact checkMembership_sound n h.1
      · exact Ideal.span_le.mp (ih h.2) hx

/-- Two accepted inclusions certify equality of spans. -/
theorem span_eq_of_inclusions {src tgt : List (SPoly α)}
    {rows₁ rows₂ : List (List (SPoly α))}
    (h₁ : checkSpanInclusion src tgt rows₁ = true)
    (h₂ : checkSpanInclusion tgt src rows₂ = true) :
    spanOf n src = spanOf n tgt :=
  le_antisymm (checkSpanInclusion_sound n h₁) (checkSpanInclusion_sound n h₂)

/-! ### Unit ideal and the geometric corollary -/

/-- The constant polynomial 1 in the sparse model. -/
def onePoly : SPoly α := [⟨1, []⟩]

@[simp] theorem toMon_nil : toMon n [] = 0 := by
  ext i; simp

omit [DecidableEq α] in
@[simp] theorem toMv_onePoly : toMv n (onePoly : SPoly α) = 1 := by
  simp [onePoly, toMv, toTerm, toMon_nil]

/-- A membership certificate for 1 makes the span the unit ideal. -/
theorem checkMembership_one_span_top {gs cs : List (SPoly α)}
    (h : checkMembership onePoly gs cs = true) :
    spanOf n gs = ⊤ := by
  have := checkMembership_sound n h
  rw [toMv_onePoly] at this
  exact Ideal.eq_top_iff_one _ |>.mpr this

/-- **Certified emptiness.**  If M2 exhibits `1 = Σ cᵢ gᵢ` and the
certificate checks, then the `gs` have no common zero in any
nontrivial commutative ℚ-algebra — every point of every variety
`V(gs)` over every field extension of ℚ is ruled out at once. -/
theorem no_common_zero {gs cs : List (SPoly α)}
    (h : checkMembership onePoly gs cs = true)
    {K : Type*} [CommRing K] [Nontrivial K] [Algebra α K]
    (pt : Fin n → K)
    (hv : ∀ g ∈ gs, aeval pt (toMv n g) = 0) : False := by
  have h1 : (1 : MvPolynomial (Fin n) α) ∈ spanOf n gs := by
    rw [checkMembership_one_span_top n h]; trivial
  have hker : spanOf n gs ≤ RingHom.ker (aeval pt : MvPolynomial (Fin n) α →ₐ[α] K) := by
    rw [spanOf]
    refine Ideal.span_le.mpr ?_
    rintro x hx
    simp only [Set.mem_setOf_eq, List.mem_map] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    exact hv g hg
  have : aeval pt (1 : MvPolynomial (Fin n) α) = 0 := hker h1
  rw [map_one] at this
  exact one_ne_zero this

/-! ### Matrices and complexes -/

/-- Interpretation of a sparse matrix with declared dimensions. -/
def toMatrix (r c : Nat) (M : SMatrix α) :
    Matrix (Fin r) (Fin c) (MvPolynomial (Fin n) α) :=
  Matrix.of fun i j => toMv n ((M.getD i []).getD j [])

omit [Field α] [DecidableEq α] in
theorem col_getD (B : SMatrix α) (j k : Nat) :
    (SMatrix.col B j).getD k [] = (B.getD k []).getD j [] := by
  induction B generalizing k with
  | nil => simp [SMatrix.col]
  | cons row B ih =>
    cases k with
    | zero => simp [SMatrix.col]
    | succ k => simpa [SMatrix.col] using ih k

omit [Field α] [DecidableEq α] in
/-- Bridge between list sums and `Fin`-indexed sums. -/
theorem sum_zipWith_eq_finsum {β : Type*} [AddCommMonoid β]
    (f : SPoly α → SPoly α → β) :
    ∀ (m : Nat) (xs ys : List (SPoly α)), xs.length = m → ys.length = m →
    (List.zipWith f xs ys).sum = ∑ k : Fin m, f (xs.getD k []) (ys.getD k [])
  | 0, [], [], _, _ => by simp
  | m + 1, x :: xs, y :: ys, hx, hy => by
    simp only [List.zipWith_cons_cons, List.sum_cons, Fin.sum_univ_succ]
    congr 1
    exact sum_zipWith_eq_finsum f m xs ys
      (by simpa using hx) (by simpa using hy)

theorem checkComplexPair_sound {r m c : Nat} {A B : SMatrix α}
    (h : checkComplexPair r m c A B = true) :
    toMatrix n r m A * toMatrix n m c B = 0 := by
  simp only [checkComplexPair, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hAr, hAm⟩, hBm⟩, hBc⟩, hz⟩ := h
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply]
  simp only [Matrix.zero_apply]
  -- the certified entry
  have hzij : polyIsZero (mulEntry A B i j) = true := by
    simp only [checkComposeZero, List.all_eq_true, List.mem_range] at hz
    exact hz i i.isLt j j.isLt
  have hrowlen : (A.row i).length = m := by
    have hi : (i : Nat) < A.length := by omega
    have hmem : A.getD i [] ∈ A := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    simpa [SMatrix.row] using hAm _ hmem
  have hcollen : (SMatrix.col B j).length = m := by
    simp [SMatrix.col, hBm]
  have hmv := polyIsZero_sound n hzij
  rw [mulEntry, toMv_combo,
    sum_zipWith_eq_finsum (fun c g => toMv n c * toMv n g) m _ _ hrowlen hcollen] at hmv
  calc ∑ k, toMatrix n r m A i k * toMatrix n m c B k j
      = ∑ k : Fin m,
          toMv n ((A.row i).getD k []) * toMv n ((SMatrix.col B j).getD k []) :=
        Finset.sum_congr rfl fun k _ => by
          simp only [toMatrix, Matrix.of_apply, SMatrix.row, col_getD]
    _ = 0 := hmv

end

end M2Lean
