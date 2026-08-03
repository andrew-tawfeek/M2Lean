/-
M2Lean: the bridge between the executable sparse checkers and the
abstract Gröbner theory.

Relates the executable GRevLex comparator on exponent *lists* to the
formal `MonomialOrder.degRevLex` on `Fin n →₀ ℕ`, and the head of an
`ord`-sorted normalization (certified by `leadOK`) to the abstract
`MonomialOrder.degree`/`leadingCoeff` of the interpreted polynomial.
These are the load-bearing lemmas that turn `checkGroebner`'s
byte-level acceptance into the hypotheses of `buchberger_criterion`.
-/
import Mathlib
import M2Lean.Semantics.Interp
import M2Lean.Certificates.Checkers
import M2Lean.Groebner.Criterion
import M2Lean.Groebner.DegRevLex

namespace M2Lean

open MvPolynomial Finsupp

set_option maxHeartbeats 1000000

/-! ### `totalDeg` computes `Finsupp.degree` -/

theorem sum_getD_eq_sum : ∀ (e : List ℕ) (n : ℕ), e.length ≤ n →
    (∑ i : Fin n, e.getD i 0) = e.sum
  | [], n, _ => by simp
  | a :: as, 0, h => by simp at h
  | a :: as, n + 1, h => by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_succ, List.getD_cons_succ,
      List.sum_cons]
    congr 1
    exact sum_getD_eq_sum as n (by simpa using h)

theorem totalDeg_eq_sum (e : List ℕ) : totalDeg e = e.sum := rfl

theorem degree_toMon (n : ℕ) (e : List ℕ) (he : e.length ≤ n) :
    Finsupp.degree (toMon n e) = totalDeg e := by
  rw [Finsupp.degree_eq_sum, totalDeg_eq_sum, ← sum_getD_eq_sum e n he]
  rfl

/-! ### Characterizing the executable reverse comparison -/

theorem cmpRevAux_eq_iff : ∀ {u v : List ℕ}, u.length = v.length →
    (cmpRevAux u v = .eq ↔ u = v)
  | [], [], _ => by simp [cmpRevAux]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: u, y :: v, h => by
    rcases Nat.lt_trichotomy x y with hxy | hxy | hxy
    · simp [cmpRevAux, hxy, Nat.ne_of_lt hxy]
    · subst hxy
      rw [cmpRevAux]
      simp only [lt_irrefl, if_false, List.cons.injEq, true_and]
      exact cmpRevAux_eq_iff (by simpa using h)
    · rw [cmpRevAux]
      simp [Nat.not_lt_of_lt hxy, hxy, (Nat.ne_of_lt hxy).symm]

theorem cmpRevAux_lt_iff : ∀ {u v : List ℕ}, u.length = v.length →
    (cmpRevAux u v = .lt ↔ ∃ k, k < v.length ∧ v.getD k 0 < u.getD k 0 ∧
      ∀ j, j < k → u.getD j 0 = v.getD j 0)
  | [], [], _ => by simp [cmpRevAux]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: u, y :: v, h => by
    rcases Nat.lt_trichotomy x y with hxy | hxy | hxy
    · rw [cmpRevAux]
      simp only [hxy, if_true]
      constructor
      · intro habs
        exact absurd habs (by simp)
      · rintro ⟨k, hk, hlt, hbefore⟩
        exfalso
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · simp only [List.getD_cons_zero] at hlt
          omega
        · have := hbefore 0 hkpos
          simp only [List.getD_cons_zero] at this
          omega
    · subst hxy
      rw [cmpRevAux]
      simp only [lt_irrefl, if_false]
      rw [cmpRevAux_lt_iff (by simpa using h)]
      constructor
      · rintro ⟨k, hk, hlt, hbefore⟩
        refine ⟨k + 1, by simpa using hk, by simpa using hlt, ?_⟩
        intro j hj
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · simp
        · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hjpos)
          simpa using hbefore j' (by omega)
      · rintro ⟨k, hk, hlt, hbefore⟩
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · simp only [List.getD_cons_zero] at hlt
          omega
        · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hkpos)
          refine ⟨k', by simpa using hk, by simpa using hlt, ?_⟩
          intro j hj
          simpa using hbefore (j + 1) (by omega)
    · rw [cmpRevAux]
      simp only [Nat.not_lt_of_lt hxy, if_false, hxy, if_true]
      constructor
      · intro _
        exact ⟨0, by simp, by simpa using hxy,
          fun j hj => absurd hj (Nat.not_lt_zero j)⟩
      · intro _
        trivial

/-! ### Padding -/

/-- Zero-pad an exponent list to length `m`. -/
def padE (m : ℕ) (e : List ℕ) : List ℕ := e ++ List.replicate (m - e.length) 0

theorem padE_length {m : ℕ} {e : List ℕ} (he : e.length ≤ m) :
    (padE m e).length = m := by
  simp [padE]
  omega

theorem getD_padE (m : ℕ) (e : List ℕ) (i : ℕ) :
    (padE m e).getD i 0 = e.getD i 0 := by
  unfold padE
  rcases Nat.lt_or_ge i e.length with hi | hi
  · rw [List.getD_append _ _ _ _ hi]
  · rw [List.getD_eq_default _ _ hi]
    rcases Nat.lt_or_ge i (e ++ List.replicate (m - e.length) 0).length with hip | hip
    · rw [List.getD_eq_getElem _ _ hip, List.getElem_append_right hi]
      simp
    · rw [List.getD_eq_default _ _ hip]

theorem totalDeg_padE (m : ℕ) (e : List ℕ) : totalDeg (padE m e) = totalDeg e := by
  simp [padE, totalDeg_eq_sum]

theorem toMon_padE (n m : ℕ) (e : List ℕ) : toMon n (padE m e) = toMon n e := by
  ext i
  rw [toMon_apply, toMon_apply, getD_padE]

/-! ### The GRevLex agreement -/

/-- The formal counterpart of the ring's GRevLex order. -/
noncomputable abbrev grevlexOrder (n : ℕ) : MonomialOrder (Fin n) :=
  MonomialOrder.degRevLex (Fin n)

theorem cmpGRevLex_eq_iff (n : ℕ) {e₁ e₂ : List ℕ}
    (h₁ : e₁.length ≤ n) (h₂ : e₂.length ≤ n) :
    cmpGRevLex e₁ e₂ = .eq ↔ toMon n e₁ = toMon n e₂ := by
  set m := max e₁.length e₂.length with hm
  have hm₁ : e₁.length ≤ m := le_max_left _ _
  have hm₂ : e₂.length ≤ m := le_max_right _ _
  have hmn : m ≤ n := max_le h₁ h₂
  have hlen : ((padE m e₁).reverse).length = ((padE m e₂).reverse).length := by
    simp [padE_length hm₁, padE_length hm₂]
  rw [cmpGRevLex]
  rcases hcmp : compare (totalDeg e₁) (totalDeg e₂) with hlt | heq | hgt
  · -- degrees differ: never equal
    simp only []
    constructor
    · intro habs
      exact absurd habs (by simp)
    · intro habs
      exfalso
      have : totalDeg e₁ = totalDeg e₂ := by
        rw [← degree_toMon n e₁ h₁, ← degree_toMon n e₂ h₂, habs]
      rw [this, Nat.compare_eq_eq.mpr rfl] at hcmp
      cases hcmp
  · -- equal degrees: compare the reversed pads
    rw [← hm]
    show cmpRevAux (padE m e₁).reverse (padE m e₂).reverse = Ordering.eq ↔ _
    rw [cmpRevAux_eq_iff hlen]
    constructor
    · intro hrev
      have hpad : padE m e₁ = padE m e₂ := List.reverse_injective hrev
      rw [← toMon_padE n m e₁, ← toMon_padE n m e₂, hpad]
    · intro hmon
      have hpads : padE m e₁ = padE m e₂ := by
        apply List.ext_getElem (by rw [padE_length hm₁, padE_length hm₂])
        intro k hk hk'
        have hkm : k < m := by rwa [padE_length hm₁] at hk
        have hmon' := congrArg (fun f => f ⟨k, lt_of_lt_of_le hkm hmn⟩) hmon
        simp only [toMon_apply] at hmon'
        rw [← List.getD_eq_getElem (padE m e₁) 0 hk,
          ← List.getD_eq_getElem (padE m e₂) 0 hk', getD_padE, getD_padE]
        exact hmon'
      rw [hpads]
  · simp only []
    constructor
    · intro habs
      exact absurd habs (by simp)
    · intro habs
      exfalso
      have : totalDeg e₁ = totalDeg e₂ := by
        rw [← degree_toMon n e₁ h₁, ← degree_toMon n e₂ h₂, habs]
      rw [this, Nat.compare_eq_eq.mpr rfl] at hcmp
      cases hcmp

theorem revPadE_getD {m : ℕ} {e : List ℕ} (he : e.length ≤ m) {k : ℕ} (hk : k < m) :
    ((padE m e).reverse).getD k 0 = e.getD (m - 1 - k) 0 := by
  rw [List.getD_reverse k (by rwa [padE_length he]), padE_length he, getD_padE]

theorem cmpGRevLex_lt_iff (n : ℕ) {e₁ e₂ : List ℕ}
    (h₁ : e₁.length ≤ n) (h₂ : e₂.length ≤ n) :
    cmpGRevLex e₁ e₂ = .lt ↔
      toDegRevLex (toMon n e₁) < toDegRevLex (toMon n e₂) := by
  set m := max e₁.length e₂.length with hm
  have hm₁ : e₁.length ≤ m := le_max_left _ _
  have hm₂ : e₂.length ≤ m := le_max_right _ _
  have hmn : m ≤ n := max_le h₁ h₂
  have hlen : ((padE m e₁).reverse).length = ((padE m e₂).reverse).length := by
    simp [padE_length hm₁, padE_length hm₂]
  -- entries beyond the original lists vanish
  have hz₁ : ∀ j : Fin n, m ≤ (j : ℕ) → toMon n e₁ j = 0 := fun j hj => by
    rw [toMon_apply]
    exact List.getD_eq_default _ _ (le_trans hm₁ hj)
  have hz₂ : ∀ j : Fin n, m ≤ (j : ℕ) → toMon n e₂ j = 0 := fun j hj => by
    rw [toMon_apply]
    exact List.getD_eq_default _ _ (le_trans hm₂ hj)
  rw [cmpGRevLex]
  rcases hcmp : compare (totalDeg e₁) (totalDeg e₂) with _ | _ | _
  · -- strictly smaller degree
    simp only []
    have hdlt : Finsupp.degree (toMon n e₁) < Finsupp.degree (toMon n e₂) := by
      rw [degree_toMon n e₁ h₁, degree_toMon n e₂ h₂]
      exact Nat.compare_eq_lt.mp hcmp
    constructor
    · intro _
      rw [DegRevLex.lt_iff]
      exact Or.inl (by simpa using hdlt)
    · intro _
      trivial
  · -- equal degrees: the colex tie-break
    have hdeq : Finsupp.degree (toMon n e₁) = Finsupp.degree (toMon n e₂) := by
      rw [degree_toMon n e₁ h₁, degree_toMon n e₂ h₂]
      exact Nat.compare_eq_eq.mp hcmp
    rw [← hm]
    show cmpRevAux (padE m e₁).reverse (padE m e₂).reverse = Ordering.lt ↔ _
    rw [cmpRevAux_lt_iff hlen, DegRevLex.lt_iff]
    simp only [ofDegRevLex_toDegRevLex]
    constructor
    · rintro ⟨k, hk, hklt, hbefore⟩
      have hkm : k < m := by rwa [List.length_reverse, padE_length hm₂] at hk
      have hmpos : 0 < m := by omega
      refine Or.inr ⟨hdeq, ?_⟩
      rw [Finsupp.Colex.lt_iff]
      simp only [ofColex_toColex]
      refine ⟨⟨m - 1 - k, by omega⟩, ?_, ?_⟩
      · intro j hj
        have hjval : m - 1 - k < (j : ℕ) := hj
        rcases Nat.lt_or_ge (j : ℕ) m with hjm | hjm
        · -- inside the padded range: translate back to a reversed index
          have hk' : m - 1 - (j : ℕ) < k := by omega
          have := hbefore (m - 1 - (j : ℕ)) hk'
          rw [revPadE_getD hm₁ (by omega), revPadE_getD hm₂ (by omega)] at this
          have hjj : m - 1 - (m - 1 - (j : ℕ)) = (j : ℕ) := by omega
          rw [hjj] at this
          rw [toMon_apply, toMon_apply]
          exact this.symm
        · rw [hz₁ j hjm, hz₂ j hjm]
      · have h1 := revPadE_getD hm₁ hkm
        have h2 := revPadE_getD hm₂ hkm
        rw [h1, h2] at hklt
        rw [toMon_apply, toMon_apply]
        exact hklt
    · rintro (hdlt | ⟨_, hcolex⟩)
      · exact absurd (hdeq ▸ hdlt) (lt_irrefl _)
      · rw [Finsupp.Colex.lt_iff] at hcolex
        simp only [ofColex_toColex] at hcolex
        obtain ⟨i, hafter, hilt⟩ := hcolex
        have him : (i : ℕ) < m := by
          by_contra hge
          push Not at hge
          rw [hz₁ i hge, hz₂ i hge] at hilt
          exact lt_irrefl _ hilt
        refine ⟨m - 1 - (i : ℕ), ?_, ?_, ?_⟩
        · rw [List.length_reverse, padE_length hm₂]
          omega
        · rw [revPadE_getD hm₁ (by omega), revPadE_getD hm₂ (by omega)]
          have hii : m - 1 - (m - 1 - (i : ℕ)) = (i : ℕ) := by omega
          rw [hii]
          rw [toMon_apply, toMon_apply] at hilt
          exact hilt
        · intro j hj
          have hjm : j < m := by omega
          rw [revPadE_getD hm₁ hjm, revPadE_getD hm₂ hjm]
          have : (i : ℕ) < m - 1 - j := by omega
          have := hafter ⟨m - 1 - j, by omega⟩ this
          rw [toMon_apply, toMon_apply] at this
          exact this.symm
  · -- strictly larger degree: both sides false
    simp only []
    have hdgt : Finsupp.degree (toMon n e₂) < Finsupp.degree (toMon n e₁) := by
      rw [degree_toMon n e₁ h₁, degree_toMon n e₂ h₂]
      exact Nat.compare_eq_gt.mp hcmp
    constructor
    · intro habs
      exact absurd habs (by simp)
    · intro habs
      exfalso
      rw [DegRevLex.lt_iff] at habs
      rcases habs with h | h
      · simp only [ofDegRevLex_toDegRevLex] at h
        omega
      · simp only [ofDegRevLex_toDegRevLex] at h
        omega

/-- Trichotomy corollary: `.gt` means strictly greater. -/
theorem cmpGRevLex_gt_iff (n : ℕ) {e₁ e₂ : List ℕ}
    (h₁ : e₁.length ≤ n) (h₂ : e₂.length ≤ n) :
    cmpGRevLex e₁ e₂ = .gt ↔
      toDegRevLex (toMon n e₂) < toDegRevLex (toMon n e₁) := by
  constructor
  · intro hgt
    rcases lt_trichotomy (toDegRevLex (toMon n e₁)) (toDegRevLex (toMon n e₂)) with
      h | h | h
    · rw [← cmpGRevLex_lt_iff n h₁ h₂] at h
      rw [h] at hgt
      cases hgt
    · have := toDegRevLex_inj.mp h
      rw [← cmpGRevLex_eq_iff n h₁ h₂] at this
      rw [this] at hgt
      cases hgt
    · exact h
  · intro h
    rcases hc : cmpGRevLex e₁ e₂ with _ | _ | _
    · rw [cmpGRevLex_lt_iff n h₁ h₂] at hc
      exact absurd (lt_trans hc h) (lt_irrefl _)
    · rw [cmpGRevLex_eq_iff n h₁ h₂] at hc
      rw [hc] at h
      exact absurd h (lt_irrefl _)
    · rfl

/-! ### Structural facts about normalization outputs -/

section Coeffs

variable {α : Type*} [Field α] [DecidableEq α]

theorem insertMerged_coeff_ne_zero {t : STerm α} {l : SPoly α}
    (hl : ∀ s ∈ l, s.coeff ≠ 0) :
    ∀ s ∈ insertMerged t l, s.coeff ≠ 0 := by
  cases l with
  | nil =>
    intro s hs
    by_cases h : t.coeff = 0 <;> simp [insertMerged, h] at hs
    · rcases hs with rfl
      simpa using h
  | cons u rest =>
    intro s hs
    by_cases he : t.exps = u.exps
    · by_cases hc : t.coeff + u.coeff = 0
      · simp only [insertMerged, he, if_pos, hc] at hs
        exact hl s (List.mem_cons_of_mem u hs)
      · simp only [insertMerged, he, if_pos, hc, if_false] at hs
        rcases List.mem_cons.mp hs with rfl | hs
        · simpa using hc
        · exact hl s (List.mem_cons_of_mem u hs)
    · by_cases h0 : t.coeff = 0
      · simp only [insertMerged, he, h0, if_true, ite_false] at hs
        exact hl s hs
      · simp only [insertMerged, he, h0, ite_false] at hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact h0
        · exact hl s hs

theorem merge1_coeff_ne_zero (l : SPoly α) :
    ∀ s ∈ merge1 l, s.coeff ≠ 0 := by
  induction l with
  | nil => intro s hs; simp [merge1] at hs
  | cons t l ih =>
    simp only [merge1, List.foldr_cons] at *
    exact insertMerged_coeff_ne_zero ih

theorem normalizeBy_coeff_ne_zero (ord : MonOrder) (p : SPoly α) :
    ∀ s ∈ normalizeBy ord p, s.coeff ≠ 0 :=
  merge1_coeff_ne_zero _

theorem insertMerged_exps_mem {t : STerm α} {l : SPoly α} :
    ∀ s ∈ insertMerged t l, s.exps = t.exps ∨ ∃ u ∈ l, s.exps = u.exps := by
  cases l with
  | nil =>
    intro s hs
    by_cases h : t.coeff = 0 <;> simp [insertMerged, h] at hs
    · exact Or.inl (by rw [hs])
  | cons u rest =>
    intro s hs
    by_cases he : t.exps = u.exps
    · by_cases hc : t.coeff + u.coeff = 0
      · simp only [insertMerged, he, if_pos, hc] at hs
        exact Or.inr ⟨s, List.mem_cons_of_mem u hs, rfl⟩
      · simp only [insertMerged, he, if_pos, hc, if_false] at hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact Or.inl (by simpa using he.symm)
        · exact Or.inr ⟨s, List.mem_cons_of_mem u hs, rfl⟩
    · by_cases h0 : t.coeff = 0
      · simp only [insertMerged, he, h0, if_true, ite_false] at hs
        exact Or.inr ⟨s, hs, rfl⟩
      · simp only [insertMerged, he, h0, ite_false] at hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact Or.inl rfl
        · exact Or.inr ⟨s, hs, rfl⟩

theorem merge1_exps_mem (l : SPoly α) :
    ∀ s ∈ merge1 l, ∃ u ∈ l, s.exps = u.exps := by
  induction l with
  | nil => intro s hs; simp [merge1] at hs
  | cons t l ih =>
    simp only [merge1, List.foldr_cons] at *
    intro s hs
    rcases insertMerged_exps_mem s hs with h | ⟨u, hu, h⟩
    · exact ⟨t, List.mem_cons_self .., h⟩
    · obtain ⟨w, hw, hw'⟩ := ih u hu
      exact ⟨w, List.mem_cons_of_mem t hw, h.trans hw'⟩

theorem trimExps_length_le (e : List ℕ) : (trimExps e).length ≤ e.length := by
  induction e with
  | nil => simp [trimExps]
  | cons a as ih =>
    rw [trimExps]
    cases h : trimExps as with
    | nil =>
      by_cases ha : a = 0 <;> simp [ha]
    | cons b l =>
      simp only [List.length_cons]
      rw [h] at ih
      simpa using ih

/-- Normalization outputs respect the arity bound of their input. -/
theorem normalizeBy_arity {n : ℕ} (ord : MonOrder) {p : SPoly α}
    (hp : arityLe n p = true) :
    ∀ s ∈ normalizeBy ord p, s.exps.length ≤ n := by
  intro s hs
  obtain ⟨u, hu, hexps⟩ := merge1_exps_mem _ s hs
  have hu' : u ∈ p.map canonTerm :=
    (List.perm_insertionSort (termGEBy ord) _).mem_iff.mp hu
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu'
  rw [hexps]
  simp only [canonTerm]
  refine le_trans (trimExps_length_le _) ?_
  have := List.all_eq_true.mp hp w hw
  simpa using this

/-! ### Coefficients of interpreted term lists -/

theorem coeff_toMv_of_forall_ne {n : ℕ} {p : SPoly α} {μ : Fin n →₀ ℕ}
    (h : ∀ t ∈ p, toMon n t.exps ≠ μ) :
    (toMv n p).coeff μ = 0 := by
  induction p with
  | nil => simp
  | cons t p ih =>
    rw [toMv_cons, coeff_add, toTerm, coeff_monomial,
      if_neg (h t (List.mem_cons_self ..)),
      ih fun s hs => h s (List.mem_cons_of_mem t hs), add_zero]

theorem grevlex_toSyn (n : ℕ) (a : Fin n →₀ ℕ) :
    (grevlexOrder n).toSyn a = toDegRevLex a := rfl

theorem degree_toMv_le {n : ℕ} {p : SPoly α} {μ : Fin n →₀ ℕ}
    (h : ∀ t ∈ p, toDegRevLex (toMon n t.exps) ≤ toDegRevLex μ) :
    (grevlexOrder n).toSyn ((grevlexOrder n).degree (toMv n p)) ≤
      (grevlexOrder n).toSyn μ := by
  induction p with
  | nil => simp
  | cons t p ih =>
    rw [toMv_cons]
    refine le_trans (grevlexOrder n).degree_add_le (max_le ?_ ?_)
    · refine le_trans ((grevlexOrder n).degree_monomial_le _) ?_
      exact h t (List.mem_cons_self ..)
    · exact ih fun s hs => h s (List.mem_cons_of_mem t hs)

/-- **The lead bridge.**  When `leadOK` certifies the head of the
GRevLex normalization, that head *is* the abstract leading term of the
interpreted polynomial. -/
theorem lead_bridge {n : ℕ} {p : SPoly α} {t : STerm α} {rest : SPoly α}
    (hnorm : normalizeBy .grevlex p = t :: rest)
    (hok : leadOK .grevlex p = true)
    (harity : arityLe n p = true) :
    (grevlexOrder n).degree (toMv n p) = toMon n t.exps ∧
      (grevlexOrder n).leadingCoeff (toMv n p) = t.coeff ∧
      toMv n p ≠ 0 := by
  have hcoeffs := normalizeBy_coeff_ne_zero (α := α) .grevlex p
  have harities := normalizeBy_arity (n := n) .grevlex harity
  rw [hnorm] at hcoeffs harities
  have htc : t.coeff ≠ 0 := hcoeffs t (List.mem_cons_self ..)
  have htar : t.exps.length ≤ n := harities t (List.mem_cons_self ..)
  have hrest : ∀ s ∈ rest, toDegRevLex (toMon n s.exps) < toDegRevLex (toMon n t.exps) := by
    intro s hs
    have hok' := hok
    rw [leadOK, hnorm] at hok'
    have := List.all_eq_true.mp hok' s hs
    have hslt : cmpGRevLex s.exps t.exps = .lt := by
      simpa [MonOrder.cmp] using this
    exact (cmpGRevLex_lt_iff n (harities s (List.mem_cons_of_mem t hs)) htar).mp hslt
  set μ := toMon n t.exps with hμ
  have hp' : toMv n p = toTerm n t + toMv n rest := by
    rw [← toMv_normalizeBy n .grevlex p, hnorm, toMv_cons]
  have hcμ : (toMv n p).coeff μ = t.coeff := by
    rw [hp', coeff_add, toTerm, coeff_monomial, if_pos rfl,
      coeff_toMv_of_forall_ne fun s hs => ?_, add_zero]
    intro habs
    have := hrest s hs
    rw [habs] at this
    exact lt_irrefl _ this
  have hne : toMv n p ≠ 0 := fun h => htc (by rw [h] at hcμ; simpa using hcμ.symm)
  have hdegle : (grevlexOrder n).toSyn ((grevlexOrder n).degree (toMv n p)) ≤
      (grevlexOrder n).toSyn μ := by
    rw [hp', ← toMv_cons]
    refine degree_toMv_le fun s hs => ?_
    rcases List.mem_cons.mp hs with rfl | hs
    · exact le_rfl
    · exact le_of_lt (hrest s hs)
  have hdegge : (grevlexOrder n).toSyn μ ≤
      (grevlexOrder n).toSyn ((grevlexOrder n).degree (toMv n p)) :=
    (grevlexOrder n).le_degree (by rwa [MvPolynomial.mem_support_iff, hcμ])
  have hdeg : (grevlexOrder n).degree (toMv n p) = μ :=
    (grevlexOrder n).toSyn.injective (le_antisymm hdegle hdegge)
  refine ⟨hdeg, ?_, hne⟩
  rw [MonomialOrder.leadingCoeff, hdeg, hcμ]

end Coeffs

end M2Lean
