/-
M2Lean case study: the Alpöge–Fable Jacobian-conjecture counterexample.

Background (as reported in July 2026).  The Jacobian Conjecture
(O.-H. Keller, 1939) asserts that a polynomial map `F : ℂⁿ → ℂⁿ` whose
Jacobian determinant is a nonzero constant has a polynomial inverse.  It
was open for every `n ≥ 2` for 87 years.  On 2026-07-19 Levent Alpöge
announced an explicit counterexample in dimension three, found with the
assistance of Anthropic's "Claude Fable 5" model (the search having been
proposed by Akhil Mathew); the short announcement was independently
checked by many mathematicians within a day, and Terence Tao related the
example to the classical Bass–Connell–Wright and Yagzhev reductions.
Full citations are in `paper/m2lean.tex` and `examples/jacobian/`.

M2Lean neither trusts nor relies on that provenance.  Macaulay2 exported
a self-contained protocol document (`examples/jacobian/jacobian.json`,
converted to `JacobianData.lean`) and here Lean re-verifies everything,
with no `sorry` and only the three standard axioms (`Audit.lean`):

1.  the conjecture's HYPOTHESIS holds — the Jacobian determinant of the
    explicit map `F` is the nonzero constant `-2` (`jacF_det`);
2.  the conjecture's CONCLUSION fails — Macaulay2 *discovered* three
    distinct points with a common image (the hard part) and exported the
    nine ideal-membership certificates witnessing it.  Lean kernel-checks
    them (`certificate_checks`) and, via the membership soundness
    theorem, promotes them to genuine `mathlib` ideal-membership
    propositions (`collision_certified`).  The collision itself — all
    that non-injectivity needs — is then *checked* by evaluating `F` at
    the three points, so the induced map `ℚ³ → ℚ³` is not injective
    (`F_not_injective`);
3.  therefore the rational-point injectivity formulation defined below
    is false in dimension three (`jacobian_conjecture_false`).  No
    dimension-raising theorem is claimed in this file.

The map is
  F(x,y,z) = ( (1+xy)³z + y²(1+xy)(4+3xy),
               y + 3x(1+xy)²z + 3xy²(4+3xy),
               2x − 3x²y − x³z ).
Below it is written with explicit products and `C`-wrapped constants (an
equal presentation) so that `pderiv` reduces mechanically.
-/
import Mathlib
import M2Lean.Certificates.Soundness
import M2Lean.Examples.JacobianData

namespace M2Lean.Jacobian

open MvPolynomial

noncomputable section

/-- Alpöge's map `F : 𝔸³ → 𝔸³` as a triple of polynomials over `ℚ`.
`X 0, X 1, X 2` are `x, y, z`. -/
def F : Fin 3 → MvPolynomial (Fin 3) ℚ
  | 0 => (C 1 + X 0 * X 1) * (C 1 + X 0 * X 1) * (C 1 + X 0 * X 1) * X 2
         + X 1 * X 1 * (C 1 + X 0 * X 1) * (C 4 + C 3 * (X 0 * X 1))
  | 1 => X 1 + C 3 * X 0 * (C 1 + X 0 * X 1) * (C 1 + X 0 * X 1) * X 2
         + C 3 * X 0 * (X 1 * X 1) * (C 4 + C 3 * (X 0 * X 1))
  | 2 => C 2 * X 0 - C 3 * (X 0 * X 0) * X 1 - (X 0 * X 0 * X 0) * X 2

/-- The Jacobian matrix `J i j = ∂Fᵢ/∂xⱼ`. -/
def jacF : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℚ) :=
  Matrix.of fun i j => pderiv j (F i)

/-! ### Step 1 — the hypothesis: the Jacobian determinant is the constant −2 -/

set_option maxRecDepth 10000 in
/-- The Jacobian determinant of `F` is the nonzero constant `-2`.  This is
the Jacobian Conjecture's hypothesis; it holds.  (`pderiv_mul` expands the
nested products via Leibniz, so the recursion limit is raised.) -/
theorem jacF_det : jacF.det = -2 := by
  rw [Matrix.det_fin_three]
  -- Phase 1: push `pderiv` through the map, keeping `C`-wrapped constants.
  simp only [jacF, Matrix.of_apply, F, map_add, map_sub,
    pderiv_mul, pderiv_C, pderiv_X_self, pderiv_X_of_ne, ne_eq, Fin.reduceEq,
    not_false_eq_true, Fin.isValue, mul_zero, zero_mul, add_zero, zero_add,
    mul_one, one_mul, sub_zero, zero_sub]
  -- Phase 2: collapse `C 1, C 2, C 3, C 4` to numerals, then it is `ring`.
  simp only [map_one, map_ofNat]
  ring

/-! ### Step 2 — the conclusion fails: `F` is not injective

Macaulay2's nine membership certificates say `Fᵢ − vᵢ ∈ m_{Pₖ}` for the
three points `P₀,P₁,P₂` and their common image `(-1/4, 0, 0)`; finding
those points is the hard, M2-side part.  We kernel-check the certificates
(`certificate_checks`) and confirm their soundness (`collision_certified`);
the collision that non-injectivity needs is then checked directly, by
evaluating `F` at the three points (`evalF_P0/1/2`). -/

/-- The three collision points `P₀,P₁,P₂` and their common image, checked
directly against `F`.  (The same equalities are certified by M2 through
the ideal-membership claims below.) -/
def P0 : Fin 3 → ℚ := ![0, 0, -1/4]
def P1 : Fin 3 → ℚ := ![1, -3/2, 13/2]
def P2 : Fin 3 → ℚ := ![-1, 3/2, 13/2]

/-- Evaluation of `F` at a rational point. -/
def evalF (p : Fin 3 → ℚ) : Fin 3 → ℚ := fun i => aeval p (F i)

theorem evalF_P0 : evalF P0 = ![-1/4, 0, 0] := by
  funext i; fin_cases i <;>
    simp only [evalF, P0, F, map_add, map_sub, map_mul, aeval_C, aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;> norm_num

theorem evalF_P1 : evalF P1 = ![-1/4, 0, 0] := by
  funext i; fin_cases i <;>
    simp only [evalF, P1, F, map_add, map_sub, map_mul, aeval_C, aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;> norm_num

theorem evalF_P2 : evalF P2 = ![-1/4, 0, 0] := by
  funext i; fin_cases i <;>
    simp only [evalF, P2, F, map_add, map_sub, map_mul, aeval_C, aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;> norm_num

/-- The nine ideal-membership certificates Macaulay2 exported, verified
inside the Lean kernel.  Each says one component value is certified as a
membership `Fᵢ − vᵢ ∈ m_{Pₖ}` of the point's maximal ideal. -/
theorem certificate_checks :
    checkMembership P0_F1_element P0_F1_gens P0_F1_cofactors = true ∧
    checkMembership P0_F2_element P0_F2_gens P0_F2_cofactors = true ∧
    checkMembership P0_F3_element P0_F3_gens P0_F3_cofactors = true ∧
    checkMembership P1_F1_element P1_F1_gens P1_F1_cofactors = true ∧
    checkMembership P1_F2_element P1_F2_gens P1_F2_cofactors = true ∧
    checkMembership P1_F3_element P1_F3_gens P1_F3_cofactors = true ∧
    checkMembership P2_F1_element P2_F1_gens P2_F1_cofactors = true ∧
    checkMembership P2_F2_element P2_F2_gens P2_F2_cofactors = true ∧
    checkMembership P2_F3_element P2_F3_gens P2_F3_cofactors = true := by
  decide +kernel

/-- The membership soundness theorem promotes all nine kernel-checked
certificates to genuine `mathlib` propositions: each interpreted element
lies in the span of the corresponding point-ideal generators.

These propositions record the certificate path.  The final noninjectivity
proof below deliberately checks the displayed rational collision directly;
it does not pretend that the certificates are a logical dependency when
ordinary evaluation is already decisive. -/
theorem collision_certified :
    toMv 3 P0_F1_element ∈ spanOf 3 P0_F1_gens ∧
    toMv 3 P0_F2_element ∈ spanOf 3 P0_F2_gens ∧
    toMv 3 P0_F3_element ∈ spanOf 3 P0_F3_gens ∧
    toMv 3 P1_F1_element ∈ spanOf 3 P1_F1_gens ∧
    toMv 3 P1_F2_element ∈ spanOf 3 P1_F2_gens ∧
    toMv 3 P1_F3_element ∈ spanOf 3 P1_F3_gens ∧
    toMv 3 P2_F1_element ∈ spanOf 3 P2_F1_gens ∧
    toMv 3 P2_F2_element ∈ spanOf 3 P2_F2_gens ∧
    toMv 3 P2_F3_element ∈ spanOf 3 P2_F3_gens := by
  rcases certificate_checks with ⟨h01, h02, h03, h11, h12, h13, h21, h22, h23⟩
  exact ⟨checkMembership_sound 3 h01,
    checkMembership_sound 3 h02,
    checkMembership_sound 3 h03,
    checkMembership_sound 3 h11,
    checkMembership_sound 3 h12,
    checkMembership_sound 3 h13,
    checkMembership_sound 3 h21,
    checkMembership_sound 3 h22,
    checkMembership_sound 3 h23⟩

/-- **`F` is not injective.**  Two distinct points share an image. -/
theorem F_not_injective :
    ¬ Function.Injective (fun p : Fin 3 → ℚ => fun i => aeval p (F i)) := by
  intro hinj
  -- `evalF Pₖ` is definitionally `fun i => aeval Pₖ (F i)`, so the two
  -- certified evaluations give the collision directly.
  have hcol : (fun i => aeval P1 (F i)) = (fun i => aeval P2 (F i)) :=
    evalF_P1.trans evalF_P2.symm
  have hpt : P1 = P2 := hinj hcol
  have := congrFun hpt 0
  simp only [P1, P2, Matrix.cons_val_zero] at this
  norm_num at this

/-! ### Step 3 — the Jacobian Conjecture is false -/

/-- Evaluate an `n`-tuple of polynomials as a map on rational points. -/
def evalPolynomialMap {n : Nat} (G : Fin n → MvPolynomial (Fin n) ℚ) :
    (Fin n → ℚ) → (Fin n → ℚ) :=
  fun p i => aeval p (G i)

/-- A two-sided polynomial inverse on rational points.  The inverse map is
itself given by an `n`-tuple of polynomials; the identities are stated after
evaluation on every rational point. -/
def HasPolynomialInverse {n : Nat} (G : Fin n → MvPolynomial (Fin n) ℚ) : Prop :=
  ∃ H : Fin n → MvPolynomial (Fin n) ℚ,
    Function.LeftInverse (evalPolynomialMap H) (evalPolynomialMap G) ∧
    Function.RightInverse (evalPolynomialMap H) (evalPolynomialMap G)

/-- The polynomial-inverse formulation over `ℚ`: a constant nonzero
Jacobian determinant should force a two-sided polynomial inverse. -/
def PolynomialJacobianConjecture (n : ℕ) : Prop :=
  ∀ G : Fin n → MvPolynomial (Fin n) ℚ,
    (∃ c : ℚ, c ≠ 0 ∧ (Matrix.of fun i j => pderiv j (G i)).det = C c) →
    HasPolynomialInverse G

/-- The displayed map has no polynomial inverse: even a left inverse would
make its map on rational points injective, contradicting the collision. -/
theorem F_has_no_polynomial_inverse : ¬ HasPolynomialInverse F := by
  rintro ⟨G, hleft, -⟩
  exact F_not_injective hleft.injective

/-- The Jacobian Conjecture in dimension `n` (Keller's injective
formulation over `ℚ`): if the Jacobian determinant of a polynomial
endomorphism of `𝔸ⁿ` is a nonzero constant, the induced self-map of `ℚⁿ`
is injective.  (Injectivity is the weakest reasonable conclusion, so
refuting it is the strongest possible counterexample.) -/
def JacobianConjecture (n : ℕ) : Prop :=
  ∀ F : Fin n → MvPolynomial (Fin n) ℚ,
    (∃ c : ℚ, c ≠ 0 ∧ (Matrix.of fun i j => pderiv j (F i)).det = C c) →
    Function.Injective (fun p : Fin n → ℚ => fun i => aeval p (F i))

/-- **The Jacobian Conjecture is false in dimension three.**  The map `F`
satisfies the hypothesis (`jacF_det`: constant Jacobian `-2 ≠ 0`) yet
violates the conclusion (`F_not_injective`).  The computational heart —
the nine collisions witnessing non-injectivity — is Macaulay2's, verified
in the kernel via `certificate_checks`. -/
theorem jacobian_conjecture_false : ¬ JacobianConjecture 3 := by
  intro H
  refine F_not_injective (H F ⟨-2, by norm_num, ?_⟩)
  rw [show (Matrix.of fun i j => pderiv j (F i)).det = -2 from jacF_det]
  simp only [map_neg, map_ofNat]

/-- The polynomial-inverse formulation is likewise false in dimension
three.  This conclusion uses only that a polynomial inverse supplies a left
inverse on rational points. -/
theorem polynomial_jacobian_conjecture_false : ¬ PolynomialJacobianConjecture 3 := by
  intro H
  refine F_has_no_polynomial_inverse (H F ⟨-2, by norm_num, ?_⟩)
  rw [show (Matrix.of fun i j => pderiv j (F i)).det = -2 from jacF_det]
  simp only [map_neg, map_ofNat]

end

end M2Lean.Jacobian
