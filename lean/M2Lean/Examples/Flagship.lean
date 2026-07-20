/-
M2Lean flagship example (README §5.6, milestone M4).

Macaulay2 discovered that the cone over the twisted cubic curve and
the line {(t,1,0,0)} ⊆ 𝔸⁴ have no common point, and exported the
Nullstellensatz-style certificate 1 = Σ cᵢ gᵢ
(examples/flagship/flagship.json → FlagshipData.lean).  Here Lean:

1. re-verifies the certificate *inside the kernel* (`by decide`);
2. applies the soundness theorem `no_common_zero` to obtain a
   mathematical conclusion M2 was never programmed to state: the two
   varieties are disjoint over EVERY nontrivial commutative
   ℚ-algebra — every field extension of ℚ at once;
3. re-verifies that the two differentials of the Eagon–Northcott
   resolution of the twisted cubic compose to zero, as an honest
   `Matrix` identity over `MvPolynomial (Fin 4) ℚ`.

No axioms are added and no `sorry` appears; see `Audit.lean`.
-/
import Mathlib
import M2Lean.Certificates.Soundness
import M2Lean.Examples.FlagshipData

namespace M2Lean.Flagship

open M2Lean MvPolynomial

/-! ### Step 1: kernel-check the untrusted certificate -/

theorem certificate_checks :
    checkMembership onePoly unit1_gens unit1_cofactors = true := by decide +kernel

theorem complex_checks :
    checkComplexPair 1 3 2 cx1_d1 cx1_d2 = true := by decide +kernel

/-! ### Step 2: the certified conclusions -/

/-- The six interpreted generators, in readable form: the three 2×2
minors of `[x y z; y z w]` cutting out the twisted cubic cone,
followed by the ideal of the line `V(y-1, z, w)`.
(`X 0, X 1, X 2, X 3` are `x, y, z, w`.) -/
theorem gens_interp :
    unit1_gens.map (toMv 4) =
      [X 0 * X 2 - X 1 ^ 2,
       X 0 * X 3 - X 1 * X 2,
       X 1 * X 3 - X 2 ^ 2,
       X 1 - 1,
       X 2,
       X 3] := by
  simp only [unit1_gens, List.map_cons, List.map_nil, toMv_cons, toMv_nil,
    toTerm_eq_prod, Fin.prod_univ_four, List.getD]
  norm_num
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- **The flagship theorem.**  The cone over the twisted cubic and the
line `{(t,1,0,0)}` have no common point with coordinates in any
nontrivial commutative ℚ-algebra (in particular, in any field
extension of ℚ).  The computational content — that 1 lies in the sum
of the two ideals — comes entirely from the Macaulay2 certificate. -/
theorem twisted_cubic_cone_misses_line
    {K : Type*} [CommRing K] [Nontrivial K] [Algebra ℚ K]
    (p : Fin 4 → K)
    (h1 : aeval p (X 0 * X 2 - X 1 ^ 2 : MvPolynomial (Fin 4) ℚ) = 0)
    (h2 : aeval p (X 0 * X 3 - X 1 * X 2 : MvPolynomial (Fin 4) ℚ) = 0)
    (h3 : aeval p (X 1 * X 3 - X 2 ^ 2 : MvPolynomial (Fin 4) ℚ) = 0)
    (h4 : aeval p (X 1 - 1 : MvPolynomial (Fin 4) ℚ) = 0)
    (h5 : aeval p (X 2 : MvPolynomial (Fin 4) ℚ) = 0)
    (h6 : aeval p (X 3 : MvPolynomial (Fin 4) ℚ) = 0) : False := by
  refine no_common_zero 4 certificate_checks p ?_
  intro g hg
  have hm : toMv 4 g ∈ unit1_gens.map (toMv 4) := List.mem_map_of_mem hg
  rw [gens_interp] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h <;> rw [h] <;> assumption

/-- Concrete corollary over ℚ itself, phrased with plain equations. -/
theorem no_rational_point (x y z w : ℚ)
    (e1 : x * z = y ^ 2) (e2 : x * w = y * z) (e3 : y * w = z ^ 2)
    (e4 : y = 1) (e5 : z = 0) (e6 : w = 0) : False := by
  subst e4 e5 e6
  simp at e1

/-! ### Step 3: the certified resolution fragment -/

/-- The two differentials of the minimal graded free resolution of the
twisted cubic (computed by M2, certified entry-by-entry in the kernel)
compose to zero — an honest `Matrix` identity in mathlib. -/
theorem resolution_composes_to_zero :
    toMatrix 4 1 3 cx1_d1 * toMatrix 4 3 2 cx1_d2 = 0 :=
  checkComplexPair_sound 4 complex_checks

end M2Lean.Flagship
