/-
M2Lean example: graph non-3-colourability as Nullstellensatz infeasibility.

A proper 3-colouring of a graph `G` is the same as a common zero of its
*colouring ideal*: one variable `x_v` per vertex, the constraint
`x_v^3 - 1` ("the colour is a cube root of unity") for each vertex, and
`x_u^2 + x_u x_v + x_v^2 = (x_u^3 - x_v^3)/(x_u - x_v)` ("adjacent colours
differ") for each edge.  Hence

    G is 3-colourable  ↔  the colouring ideal has a common zero
                       ↔  1 ∉ the colouring ideal,

so a Nullstellensatz certificate `1 = Σ cᵢ gᵢ` is a *proof of
non-colourability* (De Loera-Lee-Malkin-Margulies; Bayer).  This is the
infeasibility counterpart to Alon's Combinatorial Nullstellensatz --
which is already in `mathlib` (`Mathlib.Combinatorics.Nullstellensatz`)
and certifies that colourings *exist*: here the certificate proves that
none does, landing on the same `SimpleGraph.Colorable` predicate.

Macaulay2 finds the certificate (a real Gröbner computation whose size
grows with the graph); Lean re-checks it in the kernel
(`certificate_checks`), and the *encoding-correctness* argument below --
a proper colouring would give a common zero over ℂ, contradicting the
certificate via the membership soundness theorem (`no_common_zero`) --
turns it into `¬ W.Colorable 3` for the honest mathlib predicate.  No
`sorry`, only Lean's three standard axioms (see `Audit.lean`).

The graph here is the odd wheel `W₅` (a 5-cycle plus a hub), which needs
four colours.  The larger Grötzsch graph -- the smallest *triangle-free*
graph that is not 3-colourable -- has its (much larger) certificate
verified by `m2lean-check` in `examples/coloring/grotzsch.json`.
-/
import Mathlib
import M2Lean.Certificates.Soundness
import M2Lean.Examples.ColoringData

namespace M2Lean.Coloring

open MvPolynomial

noncomputable section

/-- Edges of the odd wheel `W₅` (5-cycle `0-1-2-3-4` plus hub `5`), in the
order Macaulay2 emitted the edge generators. -/
def E : List (Fin 6 × Fin 6) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(5,0),(5,1),(5,2),(5,3),(5,4)]

/-- Vertices `0,…,5`, in Macaulay2's variable order. -/
def V : List (Fin 6) := [0,1,2,3,4,5]

/-- The wheel `W₅` as a mathlib `SimpleGraph`. -/
def W : SimpleGraph (Fin 6) := SimpleGraph.fromRel (fun a b => (a, b) ∈ E)

/-- Every listed edge is an adjacency of `W`. -/
theorem edge_adj : ∀ e ∈ E, W.Adj e.1 e.2 := by
  intro e he
  fin_cases he <;>
    · unfold W; rw [SimpleGraph.fromRel_adj]; exact ⟨by decide, Or.inl (by decide)⟩

/-! ### A primitive cube root of unity -/

/-- `ζ = e^{2πi/3}`, a primitive cube root of unity. -/
def ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

theorem hζ : IsPrimitiveRoot ζ 3 := Complex.isPrimitiveRoot_exp 3 (by norm_num)

theorem hζ3 : ζ ^ 3 = 1 := hζ.pow_eq_one

/-! ### The colouring generators, read back from Macaulay2 -/

/-- Readable colouring-ideal generators over ℚ. -/
def vertPolys : List (MvPolynomial (Fin 6) ℚ) := V.map (fun v => X v ^ 3 - 1)
def edgePolys : List (MvPolynomial (Fin 6) ℚ) :=
  E.map (fun e => X e.1 ^ 2 + X e.1 * X e.2 + X e.2 ^ 2)

/-- Macaulay2's exported generators, interpreted into `mathlib`, are
exactly the vertex and edge polynomials above. -/
theorem gens_interp : not3col_gens.map (toMv 6) = vertPolys ++ edgePolys := by
  simp only [not3col_gens, vertPolys, edgePolys, V, E, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, toMv_cons, toMv_nil, toTerm_eq_prod,
    Fin.prod_univ_six, List.getD, map_one, map_neg]
  norm_num [List.cons.injEq]
  repeat' apply And.intro
  all_goals ring

/-! ### The encoding-correctness lemmas -/

variable (c : Fin 6 → Fin 3)

/-- A vertex generator vanishes at the point `x_v = ζ^(colour of v)`. -/
theorem vertex_vanish (v : Fin 6) :
    aeval (fun w => ζ ^ (c w : ℕ)) (X v ^ 3 - 1 : MvPolynomial (Fin 6) ℚ) = 0 := by
  simp only [map_sub, map_pow, aeval_X, map_one]
  rw [← pow_mul, mul_comm, pow_mul, hζ3, one_pow, sub_self]

/-- An edge generator vanishes at that point when its endpoints get
different colours (which a proper colouring guarantees). -/
theorem edge_vanish (u v : Fin 6) (hne : c u ≠ c v) :
    aeval (fun w => ζ ^ (c w : ℕ))
      (X u ^ 2 + X u * X v + X v ^ 2 : MvPolynomial (Fin 6) ℚ) = 0 := by
  simp only [map_add, map_mul, map_pow, aeval_X]
  have hzne : ζ ^ (c u : ℕ) ≠ ζ ^ (c v : ℕ) :=
    fun h => hne (Fin.ext (hζ.pow_inj (c u).isLt (c v).isLt h))
  have key : (ζ ^ (c u : ℕ) - ζ ^ (c v : ℕ)) *
      ((ζ ^ (c u : ℕ)) ^ 2 + ζ ^ (c u : ℕ) * ζ ^ (c v : ℕ) + (ζ ^ (c v : ℕ)) ^ 2)
      = (ζ ^ (c u : ℕ)) ^ 3 - (ζ ^ (c v : ℕ)) ^ 3 := by ring
  have h3 : (ζ ^ (c u : ℕ)) ^ 3 - (ζ ^ (c v : ℕ)) ^ 3 = 0 := by
    rw [← pow_mul, ← pow_mul, mul_comm (c u : ℕ) 3, mul_comm (c v : ℕ) 3, pow_mul, pow_mul,
      hζ3, one_pow, one_pow, sub_self]
  rw [h3] at key
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (sub_ne_zero.mpr hzne)
  · exact h

/-! ### The certificate and the theorem -/

/-- Macaulay2's Nullstellensatz certificate `1 ∈ colouringIdeal(W₅,3)`,
re-verified inside the Lean kernel. -/
theorem certificate_checks :
    checkMembership onePoly not3col_gens not3col_cofactors = true := by decide +kernel

/-- **The odd wheel `W₅` is not 3-colourable.**  A proper 3-colouring `c`
would give the common zero `x_v = ζ^(c v)` of every colouring generator
(`vertex_vanish`, `edge_vanish`); but Macaulay2's kernel-checked
certificate puts `1` in the ideal, so no common zero exists
(`no_common_zero`).  The statement is the honest mathlib predicate. -/
theorem wheel5_not_three_colorable : ¬ W.Colorable 3 := by
  rintro ⟨c⟩
  refine no_common_zero 6 certificate_checks (fun w => ζ ^ (c w : ℕ)) ?_
  intro g hg
  have hmem : toMv 6 g ∈ vertPolys ++ edgePolys := gens_interp ▸ List.mem_map_of_mem hg
  rw [List.mem_append] at hmem
  rcases hmem with hv | he
  · rw [vertPolys, List.mem_map] at hv
    obtain ⟨v, -, hgv⟩ := hv
    rw [← hgv]; exact vertex_vanish c v
  · rw [edgePolys, List.mem_map] at he
    obtain ⟨e, heE, hge⟩ := he
    rw [← hge]; exact edge_vanish c e.1 e.2 (c.valid (edge_adj e heE))

end

end M2Lean.Coloring
