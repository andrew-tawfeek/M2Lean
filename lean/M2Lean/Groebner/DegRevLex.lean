/-
M2Lean: the degree-reverse-lexicographic monomial order.

Macaulay2's default order, absent from mathlib (which provides `lex`
and `degLex`).  Following the `DegLex` template
(`Mathlib/Data/Finsupp/MonomialOrder/DegLex.lean`): the synonym
`DegRevLex (σ →₀ ℕ)` carries the order "compare degrees, then compare
*reversed* colexicographically" — `a < b` iff `degree a < degree b`,
or degrees agree and at the *largest* index where they differ, `a`
has the *larger* exponent.  The second component is the order dual of
mathlib's `Colex`, which compares at the largest differing index.

Unlike `degLex`, the underlying reverse-lexicographic order is *not*
well-founded on its own (`x₀ > x₀² > x₀³ > …` after forgetting
degrees would read upward), so well-foundedness comes from a
finiteness argument: `σ` is finite, degrees are non-increasing along
a descending chain, and there are only finitely many exponent vectors
of bounded degree.  This is why `degRevLex` requires `[Finite σ]`.

A candidate for upstreaming to mathlib next to `degLex`.
-/
import Mathlib

namespace M2Lean

open Finsupp

/-- A type synonym for `σ →₀ ℕ` equipped with the
degree-reverse-lexicographic order. -/
def DegRevLex (α : Type*) := α

variable {α : Type*}

/-- The identity map into the synonym. -/
@[match_pattern] def toDegRevLex : α ≃ DegRevLex α := Equiv.refl _

/-- The identity map out of the synonym. -/
@[match_pattern] def ofDegRevLex : DegRevLex α ≃ α := Equiv.refl _

@[simp] theorem ofDegRevLex_toDegRevLex (a : α) :
    ofDegRevLex (toDegRevLex a) = a := rfl

@[simp] theorem toDegRevLex_ofDegRevLex (a : DegRevLex α) :
    toDegRevLex (ofDegRevLex a) = a := rfl

theorem toDegRevLex_inj {a b : α} :
    toDegRevLex a = toDegRevLex b ↔ a = b := Iff.rfl

theorem ofDegRevLex_inj {a b : DegRevLex α} :
    ofDegRevLex a = ofDegRevLex b ↔ a = b := Iff.rfl

noncomputable instance [AddCommMonoid α] : AddCommMonoid (DegRevLex α) :=
  ofDegRevLex.addCommMonoid

theorem toDegRevLex_add [AddCommMonoid α] (a b : α) :
    toDegRevLex (a + b) = toDegRevLex a + toDegRevLex b := rfl

theorem ofDegRevLex_add [AddCommMonoid α] (a b : DegRevLex α) :
    ofDegRevLex (a + b) = ofDegRevLex a + ofDegRevLex b := rfl

namespace DegRevLex

variable {σ : Type*} [LinearOrder σ]

open OrderDual

/-- The comparison key: total degree first, then the *dual* of the
colexicographic order (so that, at the largest differing index, the
larger exponent loses). -/
noncomputable def key (f : DegRevLex (σ →₀ ℕ)) :
    ℕ ×ₗ (Colex (σ →₀ ℕ))ᵒᵈ :=
  toLex ((ofDegRevLex f).degree, toDual (toColex (ofDegRevLex f)))

omit [LinearOrder σ] in
theorem key_injective : Function.Injective (key (σ := σ)) := by
  intro f g h
  have := congrArg (fun p => ofColex (ofDual (ofLex p).2)) h
  exact ofDegRevLex.injective this

noncomputable instance : LinearOrder (DegRevLex (σ →₀ ℕ)) :=
  LinearOrder.lift' key key_injective

theorem lt_iff {a b : DegRevLex (σ →₀ ℕ)} :
    a < b ↔ (ofDegRevLex a).degree < (ofDegRevLex b).degree ∨
      ((ofDegRevLex a).degree = (ofDegRevLex b).degree ∧
        toColex (ofDegRevLex b) < toColex (ofDegRevLex a)) := by
  show key a < key b ↔ _
  rw [key, key, Prod.Lex.toLex_lt_toLex]
  simp [toDual_lt_toDual]

theorem le_iff {a b : DegRevLex (σ →₀ ℕ)} :
    a ≤ b ↔ (ofDegRevLex a).degree < (ofDegRevLex b).degree ∨
      ((ofDegRevLex a).degree = (ofDegRevLex b).degree ∧
        toColex (ofDegRevLex b) ≤ toColex (ofDegRevLex a)) := by
  show key a ≤ key b ↔ _
  rw [key, key, Prod.Lex.toLex_le_toLex]
  simp [toDual_le_toDual]

instance : IsOrderedCancelAddMonoid (DegRevLex (σ →₀ ℕ)) where
  le_of_add_le_add_left a b c h := by
    rw [le_iff] at h ⊢
    simpa only [ofDegRevLex_add, map_add, add_lt_add_iff_left, add_lt_add_iff_right,
      add_right_inj, add_left_inj, toColex_add, add_le_add_iff_left,
      add_le_add_iff_right] using h
  add_le_add_left a b h c := by
    rw [le_iff] at h ⊢
    simpa only [ofDegRevLex_add, map_add, add_lt_add_iff_left, add_lt_add_iff_right,
      add_right_inj, add_left_inj, toColex_add, add_le_add_iff_left,
      add_le_add_iff_right] using h

theorem degree_monotone :
    Monotone fun x : DegRevLex (σ →₀ ℕ) => (ofDegRevLex x).degree := by
  intro x y h
  rcases le_iff.mp h with h | h
  · exact le_of_lt h
  · exact le_of_eq h.1

omit [LinearOrder σ] in
/-- Over a finite index type there are only finitely many exponent
vectors of bounded degree. -/
theorem finite_degree_le [Finite σ] (D : ℕ) :
    {x : σ →₀ ℕ | Finsupp.degree x ≤ D}.Finite := by
  cases nonempty_fintype σ
  have hsub : {x : σ →₀ ℕ | Finsupp.degree x ≤ D} ⊆
      Finsupp.equivFunOnFinite.symm '' (Set.univ.pi fun _ : σ => Set.Iic D) := by
    intro x hx
    refine ⟨⇑x, fun i _ => ?_, by simp⟩
    calc x i ≤ Finsupp.degree x := Finsupp.le_degree i x
      _ ≤ D := hx
  exact Set.Finite.subset
    ((Set.Finite.pi fun _ => Set.finite_Iic D).image _) hsub

instance wellFoundedLT [Finite σ] :
    WellFoundedLT (DegRevLex (σ →₀ ℕ)) := by
  constructor
  rw [RelEmbedding.wellFounded_iff_isEmpty]
  constructor
  intro f
  set D := (ofDegRevLex (f 0)).degree with hD
  have hmem : ∀ n, (ofDegRevLex (f n)).degree ≤ D := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h]
    · exact degree_monotone (le_of_lt (f.map_rel_iff.mpr h))
  have hfin : {x : DegRevLex (σ →₀ ℕ) |
      (ofDegRevLex x).degree ≤ D}.Finite := by
    have := finite_degree_le (σ := σ) D
    exact Set.Finite.image toDegRevLex this |>.subset fun x hx =>
      ⟨ofDegRevLex x, hx, rfl⟩
  haveI := hfin.to_subtype
  obtain ⟨mn, nn, hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun n : ℕ => (⟨f n, hmem n⟩ : {x : DegRevLex (σ →₀ ℕ) |
        (ofDegRevLex x).degree ≤ D}))
  exact hne (f.injective (by simpa using congrArg Subtype.val heq))

end DegRevLex

/-- Pointwise-comparable exponent vectors over a finite type with
equal degrees are equal. -/
theorem Finsupp.eq_of_le_of_degree_le {σ : Type*} [Finite σ] {a b : σ →₀ ℕ}
    (hab : a ≤ b) (hd : Finsupp.degree b ≤ Finsupp.degree a) : a = b := by
  cases nonempty_fintype σ
  have hpt : ∀ i, a i ≤ b i := fun i => hab i
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum] at hd
  have heq := (Finset.sum_eq_sum_iff_of_le fun i _ => hpt i).mp
    (le_antisymm (Finset.sum_le_sum fun i _ => hpt i) hd)
  ext i
  exact heq i (Finset.mem_univ i)

open scoped MonomialOrder in
/-- The degree-reverse-lexicographic monomial order (Macaulay2's
default) on a finite, linearly ordered set of variables. -/
noncomputable def _root_.MonomialOrder.degRevLex (σ : Type*) [LinearOrder σ] [Finite σ] :
    MonomialOrder σ where
  syn := DegRevLex (σ →₀ ℕ)
  toSyn := { toDegRevLex with map_add' := toDegRevLex_add }
  toSyn_monotone a b h := by
    change toDegRevLex a ≤ toDegRevLex b
    rw [DegRevLex.le_iff]
    rcases lt_or_eq_of_le (Finsupp.degree_mono h) with hlt | heq
    · exact Or.inl hlt
    · have : a = b := Finsupp.eq_of_le_of_degree_le h (le_of_eq heq.symm)
      subst this
      exact Or.inr ⟨rfl, le_rfl⟩

end M2Lean
