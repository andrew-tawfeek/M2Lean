/-
M2Lean: Buchberger's criterion, standard-representation form.

This file is pure mathematics over an arbitrary `MonomialOrder` and
field — no sparse model, no protocol.  The main result is

  `buchberger_criterion` :
    if every S-polynomial of a family `b : Fin nb → MvPolynomial σ k`
    of nonzero polynomials admits a *standard representation*
    (a cofactor family whose products are degree-bounded by the
    S-polynomial), then the leading monomial of every nonzero member
    of `Ideal.span (Set.range b)` is divisible by the leading
    monomial of some `b i`.

This is Theorem 5.64 of Becker–Weispfenning (see also Cox–Little–
O'Shea, Ch. 2 §9), the correctness core of Gröbner-basis theory.  It
is exactly the statement needed to promote the M2Lean `checkGroebner`
certificate checker from `checked` to `proved`
(`M2Lean.Groebner.Sound`), and a natural candidate for upstreaming to
mathlib alongside `MonomialOrder.div`.

The proof is the classical one: pick a representation of `f`
minimizing (by well-foundedness of the monomial order) the largest
product degree `δ`; if `δ` exceeds `m.degree f`, the top-degree layer
cancels, is rewritten through S-polynomial standard representations
(the `cancellation` lemma, by strong induction on the size of the
top layer), and yields a representation with smaller `δ`.
-/
import Mathlib

namespace M2Lean.Groebner

open MvPolynomial MonomialOrder Finset

open scoped MonomialOrder

set_option maxHeartbeats 1000000

variable {σ : Type*} {k : Type*} [Field k] (m : MonomialOrder σ)
variable {nb : ℕ} (b : Fin nb → MvPolynomial σ k)

/-! ### Representations of ideal elements -/

/-- The combination `Σ cᵢ bᵢ`. -/
noncomputable def comboF (c : Fin nb → MvPolynomial σ k) : MvPolynomial σ k :=
  ∑ i, c i * b i

/-- The largest product degree of a representation, in the order's
synonym type (`⊥ = 0` for the empty family). -/
noncomputable def repDeg (c : Fin nb → MvPolynomial σ k) : m.syn :=
  univ.sup fun i => m.toSyn (m.degree (c i * b i))

theorem degree_comboF_le (c : Fin nb → MvPolynomial σ k) :
    m.toSyn (m.degree (comboF b c)) ≤ repDeg m b c := by
  unfold comboF repDeg
  exact m.degree_sum_le

theorem comboF_add (c d : Fin nb → MvPolynomial σ k) :
    comboF b (c + d) = comboF b c + comboF b d := by
  simp [comboF, add_mul, Finset.sum_add_distrib]

theorem comboF_zero : comboF b (0 : Fin nb → MvPolynomial σ k) = 0 := by
  simp [comboF]

theorem repDeg_add_le (c d : Fin nb → MvPolynomial σ k) :
    repDeg m b (c + d) ≤ max (repDeg m b c) (repDeg m b d) := by
  refine Finset.sup_le fun i _ => ?_
  have : (c + d) i * b i = c i * b i + d i * b i := by
    simp [add_mul]
  rw [this]
  refine le_trans (m.degree_add_le) ?_
  rcases max_cases (m.toSyn (m.degree (c i * b i))) (m.toSyn (m.degree (d i * b i))) with
    ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
    exact le_max_of_le_left
      (Finset.le_sup (f := fun i => m.toSyn (m.degree (c i * b i))) (mem_univ i))
  · rw [h]
    exact le_max_of_le_right
      (Finset.le_sup (f := fun i => m.toSyn (m.degree (d i * b i))) (mem_univ i))

theorem exists_rep {f : MvPolynomial σ k}
    (hf : f ∈ Ideal.span (Set.range b)) :
    ∃ c, comboF b c = f := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hf
  exact ⟨c, by simpa [comboF, smul_eq_mul] using hc⟩

/-! ### S-polynomials -/

/-- The S-polynomial of `f` and `g` (for `f, g ≠ 0`): the top terms of
the two scaled shifts cancel at `m.degree f ⊔ m.degree g`. -/
noncomputable def sPoly (f g : MvPolynomial σ k) : MvPolynomial σ k :=
  monomial (m.degree f ⊔ m.degree g - m.degree f) (m.leadingCoeff f)⁻¹ * f -
  monomial (m.degree f ⊔ m.degree g - m.degree g) (m.leadingCoeff g)⁻¹ * g

theorem sPoly_self (f : MvPolynomial σ k) : sPoly m f f = 0 := by
  simp [sPoly]

theorem sPoly_antisymm (f g : MvPolynomial σ k) :
    sPoly m g f = - sPoly m f g := by
  rw [sPoly, sPoly, sup_comm (m.degree g) (m.degree f)]
  ring

/-- The degree of an S-polynomial is strictly below the sup of the
degrees, unless the S-polynomial vanishes. -/
theorem degree_sPoly_lt {f g : MvPolynomial σ k} (hf : f ≠ 0) (hg : g ≠ 0)
    (hs : sPoly m f g ≠ 0) :
    m.toSyn (m.degree (sPoly m f g)) < m.toSyn (m.degree f ⊔ m.degree g) := by
  set δ := m.degree f ⊔ m.degree g with hδ
  classical
  have hdf : m.degree f ≤ δ := le_sup_left
  have hdg : m.degree g ≤ δ := le_sup_right
  have hlf : m.leadingCoeff f ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hf
  have hlg : m.leadingCoeff g ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hg
  have hmonf : m.degree (monomial (δ - m.degree f) (m.leadingCoeff f)⁻¹) =
      δ - m.degree f := by
    rw [m.degree_monomial]
    simp [inv_eq_zero, hlf]
  have hmong : m.degree (monomial (δ - m.degree g) (m.leadingCoeff g)⁻¹) =
      δ - m.degree g := by
    rw [m.degree_monomial]
    simp [inv_eq_zero, hlg]
  have hd1 : m.toSyn (m.degree (monomial (δ - m.degree f) (m.leadingCoeff f)⁻¹ * f)) ≤
      m.toSyn δ := by
    refine le_trans m.degree_mul_le (m.toSyn_monotone ?_)
    rw [hmonf, tsub_add_cancel_of_le hdf]
  have hd2 : m.toSyn (m.degree (monomial (δ - m.degree g) (m.leadingCoeff g)⁻¹ * g)) ≤
      m.toSyn δ := by
    refine le_trans m.degree_mul_le (m.toSyn_monotone ?_)
    rw [hmong, tsub_add_cancel_of_le hdg]
  have hcoeff : (sPoly m f g).coeff δ = 0 := by
    have c1 : (monomial (δ - m.degree f) (m.leadingCoeff f)⁻¹ * f).coeff δ =
        (m.leadingCoeff f)⁻¹ * m.leadingCoeff f := by
      have h := coeff_mul_of_degree_add (m := m)
        (f := monomial (δ - m.degree f) (m.leadingCoeff f)⁻¹) (g := f)
      rw [hmonf, tsub_add_cancel_of_le hdf, m.leadingCoeff_monomial] at h
      exact h
    have c2 : (monomial (δ - m.degree g) (m.leadingCoeff g)⁻¹ * g).coeff δ =
        (m.leadingCoeff g)⁻¹ * m.leadingCoeff g := by
      have h := coeff_mul_of_degree_add (m := m)
        (f := monomial (δ - m.degree g) (m.leadingCoeff g)⁻¹) (g := g)
      rw [hmong, tsub_add_cancel_of_le hdg, m.leadingCoeff_monomial] at h
      exact h
    simp [sPoly, coeff_sub, ← hδ, c1, c2, inv_mul_cancel₀ hlf, inv_mul_cancel₀ hlg]
  have hle : m.toSyn (m.degree (sPoly m f g)) ≤ m.toSyn δ := by
    refine le_trans m.degree_sub_le ?_
    simp only [sup_le_iff]
    exact ⟨hδ ▸ hd1, hδ ▸ hd2⟩
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    have hdeq : m.degree (sPoly m f g) = δ := m.toSyn.injective h
    have hlc : m.leadingCoeff (sPoly m f g) = 0 := by
      rw [MonomialOrder.leadingCoeff, hdeq]
      exact hcoeff
    exact hs (m.leadingCoeff_eq_zero_iff.mp hlc)

/-- A standard representation: cofactors whose products are
degree-bounded by the represented polynomial. -/
def HasStdRep (p : MvPolynomial σ k) : Prop :=
  ∃ c : Fin nb → MvPolynomial σ k, comboF b c = p ∧
    ∀ i, m.toSyn (m.degree (c i * b i)) ≤ m.toSyn (m.degree p)

theorem HasStdRep.zero : HasStdRep m b 0 :=
  ⟨0, comboF_zero b, fun i => by simp⟩

theorem HasStdRep.neg {p : MvPolynomial σ k} (h : HasStdRep m b p) :
    HasStdRep m b (-p) := by
  obtain ⟨c, hc, hdeg⟩ := h
  refine ⟨-c, ?_, fun i => ?_⟩
  · rw [← hc]; simp [comboF]
  · simpa [m.degree_neg] using hdeg i

/-! ### The cancellation lemma

A top-degree layer `Σ_{t ∈ T} monomial (δ - deg bₜ) (γₜ) · bₜ` whose
leading coefficients cancel is rewritten, through S-polynomial
standard representations, as a combination whose products all sit
strictly below `δ`. -/

theorem comboF_smul (e : k) (c : Fin nb → MvPolynomial σ k) :
    comboF b (e • c) = e • comboF b c := by
  simp [comboF, Finset.smul_sum]

theorem comboF_mulLeft (q : MvPolynomial σ k) (c : Fin nb → MvPolynomial σ k) :
    comboF b (fun t => q * c t) = q * comboF b c := by
  simp [comboF, Finset.mul_sum, mul_assoc]

/-- The scaled shift of `bᵢ` to degree `δ`: monic of degree `δ` when
`deg bᵢ ≤ δ` and `bᵢ ≠ 0`. -/
noncomputable def shift (δ : σ →₀ ℕ) (i : Fin nb) : MvPolynomial σ k :=
  monomial (δ - m.degree (b i)) (m.leadingCoeff (b i))⁻¹ * b i

theorem shift_sub_shift {δ : σ →₀ ℕ} {i j : Fin nb}
    (hi : m.degree (b i) ≤ δ) (hj : m.degree (b j) ≤ δ) :
    shift m b δ i - shift m b δ j =
      monomial (δ - (m.degree (b i) ⊔ m.degree (b j))) 1 *
        sPoly m (b i) (b j) := by
  have hsup : m.degree (b i) ⊔ m.degree (b j) ≤ δ := sup_le hi hj
  rw [sPoly, mul_sub, shift, shift]
  congr 1
  · rw [← mul_assoc, monomial_mul, one_mul,
      tsub_add_tsub_cancel hsup le_sup_left]
  · rw [← mul_assoc, monomial_mul, one_mul,
      tsub_add_tsub_cancel hsup le_sup_right]

/-- All products of a cofactor family sit strictly below `δ` (or
vanish). -/
def SmallAt (δ : σ →₀ ℕ) (c : Fin nb → MvPolynomial σ k) : Prop :=
  ∀ i, m.toSyn (m.degree (c i * b i)) < m.toSyn δ ∨ c i * b i = 0

theorem SmallAt.add {δ : σ →₀ ℕ} {c d : Fin nb → MvPolynomial σ k}
    (hc : SmallAt m b δ c) (hd : SmallAt m b δ d) :
    SmallAt m b δ (c + d) := by
  intro i
  have hcd : (c + d) i * b i = c i * b i + d i * b i := by simp [add_mul]
  rcases hc i with h1 | h1 <;> rcases hd i with h2 | h2
  · left
    rw [hcd]
    exact lt_of_le_of_lt m.degree_add_le (max_lt h1 h2)
  · left; rw [hcd, h2, add_zero]; exact h1
  · left; rw [hcd, h1, zero_add]; exact h2
  · right; rw [hcd, h1, h2, add_zero]

theorem cancellation
    (hS : ∀ i j, HasStdRep m b (sPoly m (b i) (b j)))
    (δ : σ →₀ ℕ) :
    ∀ (T : Finset (Fin nb)) (γ : Fin nb → k),
    (∀ i ∈ T, γ i ≠ 0 ∧ m.degree (b i) ≠ 0 ∧ m.degree (b i) ≤ δ) →
    (∑ i ∈ T, γ i * m.leadingCoeff (b i)) = 0 →
    ∃ c, comboF b c = (∑ i ∈ T, monomial (δ - m.degree (b i)) (γ i) * b i) ∧
      SmallAt m b δ c := by
  intro T
  induction T using Finset.strongInduction with
  | _ T IH =>
  intro γ hdeg hzero
  rcases Nat.lt_or_ge T.card 2 with hcard | hcard
  · -- 0 or 1 elements
    rcases Nat.lt_or_ge T.card 1 with h0 | h1
    · -- empty
      have : T = ∅ := Finset.card_eq_zero.mp (by omega)
      subst this
      exact ⟨0, by simp [comboF_zero], fun i => Or.inr (by simp)⟩
    · -- singleton: the cancellation condition forces γ i = 0, absurd
      have h1' : T.card = 1 := by omega
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1'
      exfalso
      rw [Finset.sum_singleton] at hzero
      have hbi : b i ≠ 0 :=
        m.ne_zero_of_degree_ne_zero (hdeg i (Finset.mem_singleton_self i)).2.1
      have hlci : m.leadingCoeff (b i) ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hbi
      exact (hdeg i (Finset.mem_singleton_self i)).1
        ((mul_eq_zero.mp hzero).resolve_right hlci)
  · -- at least two elements: extract i ≠ j and telescope
    obtain ⟨i, hiT, j, hjT, hij⟩ := Finset.one_lt_card.mp hcard
    obtain ⟨hγi, hdbi, hdi⟩ := hdeg i hiT
    obtain ⟨hγj, hdbj, hdj⟩ := hdeg j hjT
    have hbi : b i ≠ 0 := m.ne_zero_of_degree_ne_zero hdbi
    have hbj : b j ≠ 0 := m.ne_zero_of_degree_ne_zero hdbj
    have hlci : m.leadingCoeff (b i) ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hbi
    have hlcj : m.leadingCoeff (b j) ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hbj
    set e := γ i * m.leadingCoeff (b i) with he
    set γij := m.degree (b i) ⊔ m.degree (b j) with hγij
    have hγijδ : γij ≤ δ := sup_le hdi hdj
    have hγij0 : γij ≠ 0 := fun h => hdbi (le_antisymm (h ▸ le_sup_left) _root_.zero_le)
    set γ' := Function.update γ j (γ j + e * (m.leadingCoeff (b j))⁻¹) with hγ'
    set M := fun t => monomial (δ - m.degree (b t)) (γ t) * b t with hM
    set M' := fun t => monomial (δ - m.degree (b t)) (γ' t) * b t with hM'
    have hjTi : j ∈ T.erase i := Finset.mem_erase.mpr ⟨(Ne.symm hij), hjT⟩
    -- M i as a scalar multiple of the shift
    have hMi : M i = e • shift m b δ i := by
      simp only [hM]
      rw [shift, ← smul_mul_assoc, smul_monomial, smul_eq_mul, he,
        mul_assoc, mul_inv_cancel₀ hlci, mul_one]
    have hshiftj : e • shift m b δ j =
        monomial (δ - m.degree (b j)) (e * (m.leadingCoeff (b j))⁻¹) * b j := by
      rw [shift, ← smul_mul_assoc, smul_monomial, smul_eq_mul]
    -- the splitting identity
    have hsplit : (∑ t ∈ T, M t) =
        e • (shift m b δ i - shift m b δ j) + ∑ t ∈ T.erase i, M' t := by
      have h1 : (∑ t ∈ T, M t) = M i + ∑ t ∈ T.erase i, M t :=
        (Finset.add_sum_erase T M hiT).symm
      have h2 : (∑ t ∈ T.erase i, M' t) = M' j + ∑ t ∈ (T.erase i).erase j, M' t :=
        (Finset.add_sum_erase _ M' hjTi).symm
      have h3 : (∑ t ∈ T.erase i, M t) = M j + ∑ t ∈ (T.erase i).erase j, M t :=
        (Finset.add_sum_erase _ M hjTi).symm
      have h4 : ∀ t ∈ (T.erase i).erase j, M' t = M t := by
        intro t ht
        have : t ≠ j := (Finset.mem_erase.mp ht).1
        simp only [hM', hM, hγ']
        rw [Function.update_of_ne this]
      have h5 : M' j = M j + e • shift m b δ j := by
        simp only [hM', hM, hγ']
        rw [Function.update_self, map_add, add_mul, hshiftj]
      rw [h1, h2, h3, h5, Finset.sum_congr rfl h4, hMi, smul_sub]
      abel
    -- new cancellation condition on the erased set
    have hzero' : (∑ t ∈ T.erase i, γ' t * m.leadingCoeff (b t)) = 0 := by
      have e1 : (∑ t ∈ T, γ t * m.leadingCoeff (b t)) =
          γ i * m.leadingCoeff (b i) + ∑ t ∈ T.erase i, γ t * m.leadingCoeff (b t) :=
        (Finset.add_sum_erase _ _ hiT).symm
      have e2 : (∑ t ∈ T.erase i, γ' t * m.leadingCoeff (b t)) =
          γ' j * m.leadingCoeff (b j) +
            ∑ t ∈ (T.erase i).erase j, γ' t * m.leadingCoeff (b t) :=
        (Finset.add_sum_erase _ _ hjTi).symm
      have e3 : (∑ t ∈ T.erase i, γ t * m.leadingCoeff (b t)) =
          γ j * m.leadingCoeff (b j) +
            ∑ t ∈ (T.erase i).erase j, γ t * m.leadingCoeff (b t) :=
        (Finset.add_sum_erase _ _ hjTi).symm
      have e4 : ∀ t ∈ (T.erase i).erase j,
          γ' t * m.leadingCoeff (b t) = γ t * m.leadingCoeff (b t) := by
        intro t ht
        rw [hγ', Function.update_of_ne (Finset.mem_erase.mp ht).1]
      have h6 : γ j * m.leadingCoeff (b j) +
          ∑ t ∈ (T.erase i).erase j, γ t * m.leadingCoeff (b t) = -e := by
        have h0 := hzero
        rw [e1, e3] at h0
        rw [he]
        linear_combination h0
      rw [e2, Finset.sum_congr rfl e4, hγ', Function.update_self, add_mul,
        mul_assoc, inv_mul_cancel₀ hlcj, mul_one]
      linear_combination h6
    -- the S-polynomial chunk
    obtain ⟨cS, hcS, hcSdeg⟩ := hS i j
    set c₂ : Fin nb → MvPolynomial σ k :=
      fun t => e • (monomial (δ - γij) 1 * cS t) with hc₂
    have hc₂combo : comboF b c₂ = e • (shift m b δ i - shift m b δ j) := by
      have : comboF b c₂ = e • (monomial (δ - γij) 1 * comboF b cS) := by
        rw [hc₂]
        have := comboF_mulLeft b (monomial (δ - γij) 1) cS
        calc comboF b (fun t => e • (monomial (δ - γij) 1 * cS t))
            = e • comboF b (fun t => monomial (δ - γij) 1 * cS t) := by
              rw [← comboF_smul]; rfl
          _ = e • (monomial (δ - γij) 1 * comboF b cS) := by rw [this]
      rw [this, hcS, ← shift_sub_shift m b hdi hdj]
    have hc₂small : SmallAt m b δ c₂ := by
      intro t
      by_cases hz : cS t * b t = 0
      · right
        rw [hc₂, smul_mul_assoc, mul_assoc, hz, mul_zero, smul_zero]
      · left
        have habove : m.toSyn (m.degree (c₂ t * b t)) ≤
            m.toSyn (δ - γij) + m.toSyn (m.degree (cS t * b t)) := by
          rw [hc₂, smul_mul_assoc, mul_assoc]
          refine le_trans (m.degree_smul_le) ?_
          refine le_trans m.degree_mul_le ?_
          rw [map_add]
          gcongr
          exact m.degree_monomial_le _
        have hbelow : m.toSyn (m.degree (cS t * b t)) < m.toSyn γij := by
          by_cases hsp : sPoly m (b i) (b j) = 0
          · have h0 := hcSdeg t
            rw [hsp, m.degree_zero, map_zero] at h0
            have : m.toSyn (m.degree (cS t * b t)) = 0 := le_antisymm h0 (m.zero_le _)
            rw [this]
            exact lt_of_le_of_ne (m.zero_le _)
              (fun h => hγij0 ((m.toSyn_eq_zero_iff γij).mp h.symm))
          · exact lt_of_le_of_lt (hcSdeg t) (degree_sPoly_lt m hbi hbj hsp)
        calc m.toSyn (m.degree (c₂ t * b t))
            ≤ m.toSyn (δ - γij) + m.toSyn (m.degree (cS t * b t)) := habove
          _ < m.toSyn (δ - γij) + m.toSyn γij := add_lt_add_of_le_of_lt le_rfl hbelow
          _ = m.toSyn δ := by rw [← map_add, tsub_add_cancel_of_le hγijδ]
    -- the remaining layer, by induction
    have hssub : T.erase i ⊂ T := Finset.erase_ssubset hiT
    by_cases hγ'j : γ' j = 0
    · -- the merged coefficient vanished: drop j as well
      have hjz : M' j = 0 := by
        simp only [hM']
        rw [hγ'j]
        simp
      have hsum : (∑ t ∈ T.erase i, M' t) = ∑ t ∈ (T.erase i).erase j, M t := by
        rw [← Finset.add_sum_erase _ M' hjTi, hjz, zero_add]
        refine Finset.sum_congr rfl fun t ht => ?_
        simp only [hM', hM, hγ']
        rw [Function.update_of_ne (Finset.mem_erase.mp ht).1]
      have hz'' : (∑ t ∈ (T.erase i).erase j, γ t * m.leadingCoeff (b t)) = 0 := by
        have h0 := hzero'
        rw [← Finset.add_sum_erase _ (fun t => γ' t * m.leadingCoeff (b t)) hjTi,
          hγ'j, zero_mul, zero_add] at h0
        rw [← h0]
        exact (Finset.sum_congr rfl fun t ht => by
          rw [hγ', Function.update_of_ne (Finset.mem_erase.mp ht).1]).symm
      have hssub2 : (T.erase i).erase j ⊂ T :=
        Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset _ _) hssub
      have hdeg'' : ∀ t ∈ (T.erase i).erase j,
          γ t ≠ 0 ∧ m.degree (b t) ≠ 0 ∧ m.degree (b t) ≤ δ :=
        fun t ht => hdeg t (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht))
      obtain ⟨c₁, hc₁, hs₁⟩ := IH _ hssub2 γ hdeg'' hz''
      refine ⟨c₂ + c₁, ?_, SmallAt.add m b hc₂small hs₁⟩
      rw [comboF_add, hc₂combo, hc₁, hsplit, hsum]
    · -- the merged coefficient survives
      have hdeg' : ∀ t ∈ T.erase i,
          γ' t ≠ 0 ∧ m.degree (b t) ≠ 0 ∧ m.degree (b t) ≤ δ := by
        intro t ht
        by_cases htj : t = j
        · subst htj
          exact ⟨hγ'j, hdbj, hdj⟩
        · rw [hγ', Function.update_of_ne htj]
          exact hdeg t (Finset.mem_of_mem_erase ht)
      obtain ⟨c₁, hc₁, hs₁⟩ := IH _ hssub γ' hdeg' hzero'
      refine ⟨c₂ + c₁, ?_, SmallAt.add m b hc₂small hs₁⟩
      rw [comboF_add, hc₂combo, hc₁, hsplit]

/-! ### Buchberger's criterion -/

/-- Constants have vanishing `subLTerm`. -/
theorem sub_leadingTerm_eq_zero_of_degree_eq_zero
    {f : MvPolynomial σ k} (hf : m.degree f = 0) :
    f - m.leadingTerm f = 0 := by
  rw [sub_eq_zero, MonomialOrder.leadingTerm, hf, monomial_zero']
  exact m.eq_C_of_degree_eq_zero hf

/-- **Buchberger's criterion, standard-representation form**
(Becker–Weispfenning Thm. 5.64; Buchberger 1970).  If every
S-polynomial of the nonzero family `b` has a standard representation,
then the leading monomial of every nonzero element of
`Ideal.span (Set.range b)` is divisible by some `m.degree (b i)`. -/
theorem buchberger_criterion
    (hb : ∀ i, b i ≠ 0)
    (hS : ∀ i j, HasStdRep m b (sPoly m (b i) (b j)))
    {f : MvPolynomial σ k} (hf : f ∈ Ideal.span (Set.range b)) (hf0 : f ≠ 0) :
    ∃ i, m.degree (b i) ≤ m.degree f := by
  classical
  -- trivial if some bᵢ has degree 0
  by_cases hconst : ∃ i, m.degree (b i) = 0
  · obtain ⟨i, hi⟩ := hconst
    refine ⟨i, ?_⟩
    rw [hi]
    exact _root_.zero_le
  push Not at hconst
  -- choose a representation with minimal top product degree
  obtain ⟨c0, hc0⟩ := exists_rep b hf
  set RD : Set m.syn := {d | ∃ c, comboF b c = f ∧ repDeg m b c = d} with hRD
  have hne : RD.Nonempty := ⟨_, c0, hc0, rfl⟩
  obtain ⟨δs, hδmem, hδmin⟩ := (wellFounded_lt (α := m.syn)).has_min RD hne
  obtain ⟨c, hcf, hcd⟩ := hδmem
  have hlow : m.toSyn (m.degree f) ≤ δs := by
    rw [← hcd, ← hcf]
    exact degree_comboF_le m b c
  rcases eq_or_lt_of_le hlow with heq | hlt
  · -- the minimum is the degree of f: extract a divisor
    set d := m.degree f with hd
    have h1 : f.coeff d ≠ 0 := m.coeff_degree_ne_zero_iff.mpr hf0
    have h3 : ∃ i, (c i * b i).coeff d ≠ 0 := by
      by_contra hall
      push Not at hall
      apply h1
      have hh : f.coeff d = ∑ i, (c i * b i).coeff d := by
        conv_lhs => rw [← hcf]
        rw [comboF, coeff_sum]
      rw [hh]
      exact Finset.sum_eq_zero fun i _ => hall i
    obtain ⟨i, hi⟩ := h3
    have hne0 : c i * b i ≠ 0 := by
      intro h
      rw [h] at hi
      simp at hi
    have hle : m.toSyn d ≤ m.toSyn (m.degree (c i * b i)) :=
      m.le_degree (mem_support_iff.mpr hi)
    have hup : m.toSyn (m.degree (c i * b i)) ≤ δs := by
      rw [← hcd]
      exact Finset.le_sup (f := fun i => m.toSyn (m.degree (c i * b i))) (mem_univ i)
    have heq2 : m.degree (c i * b i) = d :=
      m.toSyn.injective (le_antisymm (le_trans hup heq.symm.le) hle)
    have hci : c i ≠ 0 := fun h => hne0 (by rw [h, zero_mul])
    have hmul : m.degree (c i * b i) = m.degree (c i) + m.degree (b i) :=
      m.degree_mul hci (hb i)
    refine ⟨i, ?_⟩
    rw [← heq2, hmul]
    exact le_add_self
  · -- the minimum sits strictly above the degree of f: contradiction
    exfalso
    set δ' := m.toSyn.symm δs with hδ'
    have hδ's : m.toSyn δ' = δs := m.toSyn.apply_symm_apply δs
    set T : Finset (Fin nb) := univ.filter
      (fun i => c i * b i ≠ 0 ∧ m.toSyn (m.degree (c i * b i)) = δs) with hT
    have hmemT : ∀ i, i ∈ T ↔
        c i * b i ≠ 0 ∧ m.toSyn (m.degree (c i * b i)) = δs := by
      intro i; simp [hT]
    -- on T, both factors are nonzero and degrees add to δ'
    have hTfacts : ∀ i ∈ T, c i ≠ 0 ∧ b i ≠ 0 ∧
        m.degree (c i) + m.degree (b i) = δ' := by
      intro i hiT
      obtain ⟨hne0, hds⟩ := (hmemT i).mp hiT
      have hci : c i ≠ 0 := fun h => hne0 (by rw [h, zero_mul])
      refine ⟨hci, hb i, ?_⟩
      have := m.degree_mul hci (hb i)
      rw [this] at hds
      exact m.toSyn.injective (by rw [hδ's, hds])
    -- the top-layer coefficients cancel
    have hzero : (∑ i ∈ T, m.leadingCoeff (c i) * m.leadingCoeff (b i)) = 0 := by
      have hcf' : f.coeff δ' = 0 := by
        apply m.coeff_eq_zero_of_lt
        rw [hδ's]
        exact hlt
      have hsum : f.coeff δ' = ∑ i, (c i * b i).coeff δ' := by
        rw [← hcf, comboF, coeff_sum]
      have hsplit : (∑ i, (c i * b i).coeff δ') =
          ∑ i ∈ T, (c i * b i).coeff δ' := by
        rw [hT]
        refine (Finset.sum_filter_of_ne fun i _ hne => ?_).symm
        by_contra hnot
        push Not at hnot
        rcases Decidable.em (c i * b i = 0) with hz | hz
        · exact hne (by rw [hz]; simp)
        · refine hne ?_
          have hlt' : m.toSyn (m.degree (c i * b i)) < m.toSyn δ' := by
            rw [hδ's]
            exact lt_of_le_of_ne
              (by rw [← hcd]
                  exact Finset.le_sup
                    (f := fun i => m.toSyn (m.degree (c i * b i))) (mem_univ i))
              (hnot hz)
          exact m.coeff_eq_zero_of_lt hlt'
      have hterm : ∀ i ∈ T, (c i * b i).coeff δ' =
          m.leadingCoeff (c i) * m.leadingCoeff (b i) := by
        intro i hiT
        obtain ⟨_, _, hadd⟩ := hTfacts i hiT
        rw [← hadd]
        exact coeff_mul_of_degree_add (m := m)
      rw [hcf', hsplit] at hsum
      rw [← Finset.sum_congr rfl hterm]
      exact hsum.symm
    -- apply the cancellation lemma to the top layer
    have hdegT : ∀ i ∈ T, m.leadingCoeff (c i) ≠ 0 ∧
        m.degree (b i) ≠ 0 ∧ m.degree (b i) ≤ δ' := by
      intro i hiT
      obtain ⟨hci, _, hadd⟩ := hTfacts i hiT
      exact ⟨m.leadingCoeff_ne_zero_iff.mpr hci, hconst i,
        hadd ▸ le_add_self⟩
    obtain ⟨cT, hcT, hsmallT⟩ :=
      cancellation m b hS δ' T (fun i => m.leadingCoeff (c i)) hdegT hzero
    -- the low-order remainder
    set c'' : Fin nb → MvPolynomial σ k :=
      fun i => if i ∈ T then c i - m.leadingTerm (c i) else c i with hc''
    have hsmall'' : SmallAt m b δ' c'' := by
      intro i
      by_cases hiT : i ∈ T
      · obtain ⟨hci, hbi, hadd⟩ := hTfacts i hiT
        by_cases hz : c i - m.leadingTerm (c i) = 0
        · right
          rw [hc'']
          simp [hiT, hz]
        · left
          have hdegc : m.degree (c i) ≠ 0 := by
            intro h0
            exact hz (sub_leadingTerm_eq_zero_of_degree_eq_zero m h0)
          have hstrict : m.toSyn (m.degree (c i - m.leadingTerm (c i))) <
              m.toSyn (m.degree (c i)) := m.degree_sub_LTerm_lt hdegc
          rw [hc'']
          simp only [hiT, if_pos]
          calc m.toSyn (m.degree ((c i - m.leadingTerm (c i)) * b i))
              ≤ m.toSyn (m.degree (c i - m.leadingTerm (c i))) +
                m.toSyn (m.degree (b i)) := by
                refine le_trans m.degree_mul_le ?_
                rw [map_add]
            _ < m.toSyn (m.degree (c i)) + m.toSyn (m.degree (b i)) :=
                add_lt_add_of_lt_of_le hstrict le_rfl
            _ = m.toSyn δ' := by rw [← map_add, hadd]
      · rw [hc'']
        simp only [hiT, ite_false]
        by_cases hz : c i * b i = 0
        · exact Or.inr hz
        · left
          rw [hδ's]
          refine lt_of_le_of_ne ?_ ?_
          · rw [← hcd]
            exact Finset.le_sup
              (f := fun i => m.toSyn (m.degree (c i * b i))) (mem_univ i)
          · intro h
            exact hiT ((hmemT i).mpr ⟨hz, h⟩)
    -- assemble the smaller representation
    set c' := cT + c'' with hc'
    have hrepf : comboF b c' = f := by
      have htop : (∑ i ∈ T, monomial (δ' - m.degree (b i))
          (m.leadingCoeff (c i)) * b i) = ∑ i ∈ T, m.leadingTerm (c i) * b i := by
        refine Finset.sum_congr rfl fun i hiT => ?_
        obtain ⟨_, _, hadd⟩ := hTfacts i hiT
        rw [MonomialOrder.leadingTerm]
        congr 2
        exact (eq_tsub_of_add_eq hadd).symm ▸ rfl
      have hcombo'' : comboF b c'' = f - ∑ i ∈ T, m.leadingTerm (c i) * b i := by
        rw [comboF]
        have : ∀ i, c'' i * b i = c i * b i -
            (if i ∈ T then m.leadingTerm (c i) else 0) * b i := by
          intro i
          rw [hc'']
          by_cases hiT : i ∈ T <;> simp [hiT, sub_mul]
        rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_sub_distrib]
        have h1 : (∑ i, c i * b i) = f := hcf
        have h2 : (∑ i, (if i ∈ T then m.leadingTerm (c i) else 0) * b i) =
            ∑ i ∈ T, m.leadingTerm (c i) * b i := by
          have he : ∀ i, (if i ∈ T then m.leadingTerm (c i) else 0) * b i =
              if i ∈ T then m.leadingTerm (c i) * b i else 0 := by
            intro i
            by_cases hiT : i ∈ T <;> simp [hiT]
          rw [Finset.sum_congr rfl fun i _ => he i, Finset.sum_ite_mem,
            Finset.univ_inter]
        rw [h1, h2]
      rw [hc', comboF_add, hcT, htop, hcombo'']
      abel
    have hsmall' : SmallAt m b δ' c' := SmallAt.add m b hsmallT hsmall''
    -- its measure is strictly below δs
    have hmeas : repDeg m b c' < δs := by
      rw [repDeg, ← hδ's]
      refine Finset.sup_lt_iff ?_ |>.mpr fun i _ => ?_
      · rw [hδ's]
        exact lt_of_le_of_lt (bot_le) hlt
      · rcases hsmall' i with h | h
        · exact h
        · rw [h, m.degree_zero, map_zero, hδ's]
          exact lt_of_le_of_lt (m.zero_le _) hlt
    exact hδmin (repDeg m b c') ⟨c', hrepf, rfl⟩ hmeas

end M2Lean.Groebner
