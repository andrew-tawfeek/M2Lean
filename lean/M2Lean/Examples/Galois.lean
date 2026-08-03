/-
M2Lean promoted example: separability of the eighth cyclotomic
polynomial, kernel-checked from a Macaulay2 certificate.

Macaulay2 produced the Bézout witness
  1 = 1·(t⁴+1) + (−t/4)·(4t³)
(examples/appendix/galois.json → GaloisData.lean).  Lean re-verifies
it in the kernel and derives a genuine mathlib statement:
`(X⁴ + 1 : ℚ[X]).Separable` — mathlib's `Polynomial.Separable` is by
definition coprimality with the derivative, which is exactly what the
certificate witnesses.  Hence Φ₈ has no repeated root in any
extension of ℚ, i.e. ℚ(ζ₈)/ℚ is étale.
-/
import Mathlib
import M2Lean.Certificates.Soundness
import M2Lean.Examples.GaloisData

namespace M2Lean.Galois

open M2Lean MvPolynomial

/-! ### Step 1: kernel-check the untrusted certificate -/

theorem certificate_checks :
    checkMembership onePoly separable_gens separable_cofactors = true := by
  decide +kernel

/-! ### Step 2: extract the Bézout identity -/

private noncomputable def c₁ : MvPolynomial (Fin 1) ℚ :=
  toMv 1 (separable_cofactors.getD 0 [])
private noncomputable def c₂ : MvPolynomial (Fin 1) ℚ :=
  toMv 1 (separable_cofactors.getD 1 [])

theorem gens_interp :
    separable_gens.map (toMv 1) = [X 0 ^ 4 + 1, 4 * X 0 ^ 3] := by
  simp only [separable_gens, List.map_cons, List.map_nil, toMv_cons, toMv_nil,
    toTerm_eq_prod, Fin.prod_univ_one, List.getD]
  norm_num
  constructor

theorem bezout :
    c₁ * (X 0 ^ 4 + 1) + c₂ * (4 * X 0 ^ 3) = (1 : MvPolynomial (Fin 1) ℚ) := by
  have hcheck : polyEq onePoly (combo separable_cofactors separable_gens) = true :=
    (Bool.and_eq_true _ _ |>.mp certificate_checks).2
  have h := polyEq_sound 1 hcheck
  rw [toMv_onePoly, toMv_combo] at h
  simp only [separable_cofactors, separable_gens, List.zipWith_cons_cons,
    List.zipWith_nil_right, List.sum_cons, List.sum_nil, add_zero] at h
  have hg1 : toMv 1 ([⟨(1 : Rat), [4]⟩, ⟨(1 : Rat), [0]⟩] : SPoly Rat) =
      X 0 ^ 4 + 1 := by
    simp [toMv, toTerm_eq_prod]
  have hg2 : toMv 1 ([⟨(4 : Rat), [3]⟩] : SPoly Rat) = 4 * X 0 ^ 3 := by
    have hC : (C (4 : ℚ) : MvPolynomial (Fin 1) ℚ) = 4 := map_ofNat C 4
    simp [toMv, toTerm_eq_prod, hC]
  rw [hg1, hg2] at h
  rw [c₁, c₂]
  simp only [separable_cofactors, List.getD_cons_zero, List.getD_cons_succ]
  linear_combination -h

/-! ### Step 3: the mathlib theorem -/

/-- The transfer to univariate polynomials. -/
noncomputable def toUni : MvPolynomial (Fin 1) ℚ ≃ₐ[ℚ] Polynomial ℚ :=
  MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)

@[simp] theorem toUni_X : toUni (X 0) = Polynomial.X := by
  simp [toUni, MvPolynomial.uniqueAlgEquiv]

theorem phi8_coprime :
    IsCoprime (Polynomial.X ^ 4 + 1 : Polynomial ℚ)
      (4 * Polynomial.X ^ 3) := by
  refine ⟨toUni c₁, toUni c₂, ?_⟩
  have := congrArg toUni bezout
  simpa [map_add, map_mul, map_pow, map_one, map_ofNat] using this

/-- **Certified separability.**  The eighth cyclotomic polynomial is
separable over ℚ: it has no repeated root in any extension.  The
computational content — the Bézout identity between Φ₈ and its
derivative — comes entirely from the Macaulay2 certificate. -/
theorem phi8_separable : (Polynomial.X ^ 4 + 1 : Polynomial ℚ).Separable := by
  rw [Polynomial.separable_def]
  have hder : Polynomial.derivative (Polynomial.X ^ 4 + 1 : Polynomial ℚ) =
      4 * Polynomial.X ^ 3 := by
    have hC : (Polynomial.C (4 : ℚ)) = 4 := map_ofNat Polynomial.C 4
    rw [Polynomial.derivative_add, Polynomial.derivative_one, add_zero,
      Polynomial.derivative_X_pow]
    norm_num [hC]
  rw [hder]
  exact phi8_coprime

end M2Lean.Galois
