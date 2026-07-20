/-
M2Lean: soundness of the Gröbner and non-membership checkers.

The capstone of the Gröbner tier: `checkGroebner_sound` connects
acceptance of a `GroebnerBasis` certificate (over GRevLex, the ring
order of every Macaulay2 default computation) to the mathematical
Gröbner property via `buchberger_criterion`, and
`checkNonMembership_sound` derives genuine non-membership — the
negative certificate that is unsound without a proved Gröbner basis.
With these theorems the `GroebnerBasis` and `NonMembership` claims are
promoted from `checked` to `proved` (`GroebnerSound.level`).
-/
import Mathlib
import M2Lean.Groebner.Bridge
import M2Lean.Certificates.Soundness

namespace M2Lean

open MvPolynomial Finsupp

set_option maxHeartbeats 1000000

variable {α : Type} [Field α] [DecidableEq α] (n : ℕ)

/-! ### Exponent-arithmetic transfer -/

theorem getD_zipMax : ∀ (as bs : List ℕ) (i : ℕ),
    (zipMax as bs).getD i 0 = max (as.getD i 0) (bs.getD i 0)
  | [], bs, i => by simp [zipMax]
  | a :: as, [], i => by cases i <;> simp [zipMax]
  | a :: as, b :: bs, 0 => by simp [zipMax]
  | a :: as, b :: bs, i + 1 => by simpa [zipMax] using getD_zipMax as bs i

theorem getD_zipSub : ∀ (as bs : List ℕ) (i : ℕ),
    (zipSub as bs).getD i 0 = as.getD i 0 - bs.getD i 0
  | [], [], i => by simp [zipSub]
  | [], b :: bs, i => by simp [zipSub]
  | a :: as, [], i => by cases i <;> simp [zipSub]
  | a :: as, b :: bs, 0 => by simp [zipSub]
  | a :: as, b :: bs, i + 1 => by simpa [zipSub] using getD_zipSub as bs i

theorem toMon_zipMax (as bs : List ℕ) :
    toMon n (zipMax as bs) = toMon n as ⊔ toMon n bs := by
  ext i
  rw [toMon_apply, Finsupp.sup_apply, toMon_apply, toMon_apply, getD_zipMax]

theorem toMon_zipSub (as bs : List ℕ) :
    toMon n (zipSub as bs) = toMon n as - toMon n bs := by
  ext i
  rw [toMon_apply, Finsupp.tsub_apply, toMon_apply, toMon_apply, getD_zipSub]

theorem zipMax_length (as bs : List ℕ) :
    (zipMax as bs).length = max as.length bs.length := by
  induction as generalizing bs with
  | nil => simp [zipMax]
  | cons a as ih =>
    cases bs with
    | nil => simp [zipMax]
    | cons b bs =>
      simp [zipMax, ih]
      try omega

theorem zipSub_length_le (as bs : List ℕ) :
    (zipSub as bs).length ≤ as.length := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [zipSub]
  | cons a as ih =>
    cases bs with
    | nil => simp [zipSub]
    | cons b bs => simpa [zipSub] using ih bs

theorem zipAdd_length (as bs : List ℕ) :
    (zipAdd as bs).length = max as.length bs.length := by
  induction as generalizing bs with
  | nil => simp [zipAdd]
  | cons a as ih =>
    cases bs with
    | nil => simp [zipAdd]
    | cons b bs =>
      simp [zipAdd, ih]
      try omega

theorem arityLe_mulRaw {p q : SPoly α} (hp : arityLe n p = true)
    (hq : arityLe n q = true) : arityLe n (mulRaw p q) = true := by
  rw [arityLe, List.all_eq_true]
  intro t ht
  simp only [mulRaw, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨s, hs, u, hu, rfl⟩ := ht
  have h1 := List.all_eq_true.mp hp s hs
  have h2 := List.all_eq_true.mp hq u hu
  simp only [decide_eq_true_eq] at h1 h2 ⊢
  rw [mulTerm, zipAdd_length]
  omega

theorem expsLe_iff {a b : List ℕ} (ha : a.length ≤ n) (hb : b.length ≤ n) :
    expsLe a b = true ↔ toMon n a ≤ toMon n b := by
  rw [expsLe, List.all_eq_true]
  constructor
  · intro h i
    rw [toMon_apply, toMon_apply]
    rcases Nat.lt_or_ge (i : ℕ) (max a.length b.length) with hi | hi
    · simpa using h (i : ℕ) (List.mem_range.mpr hi)
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  · intro h k hk
    have hkn : k < n := lt_of_lt_of_le (List.mem_range.mp hk) (max_le ha hb)
    have := h ⟨k, hkn⟩
    rw [toMon_apply, toMon_apply] at this
    simpa using this

/-! ### From lists to `Fin`-indexed families -/

/-- The interpreted basis as a `Fin`-indexed family. -/
noncomputable def basisFun (basis : List (SPoly α)) :
    Fin basis.length → MvPolynomial (Fin n) α :=
  fun i => toMv n basis[(i : ℕ)]

theorem spanOf_eq_range (basis : List (SPoly α)) :
    spanOf n basis = Ideal.span (Set.range (basisFun n basis)) := by
  unfold spanOf basisFun
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, List.mem_map, Set.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨basis[i], List.getElem_mem _, rfl⟩

/-- Transfer a certified sparse combination into a `Fin`-indexed one. -/
theorem comboF_toMv (quots basis : List (SPoly α))
    (hlen : quots.length = basis.length) :
    Groebner.comboF (basisFun n basis)
        (fun i => toMv n (quots.getD i [])) =
      toMv n (combo quots basis) := by
  rw [Groebner.comboF, toMv_combo,
    sum_zipWith_eq_finsum (fun c g => toMv n c * toMv n g) basis.length _ _
      hlen rfl]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [basisFun]
  rw [List.getD_eq_getElem basis [] i.isLt]

/-! ### The Gröbner soundness theorem -/

theorem checkGroebner_sound {gens basis : List (SPoly α)}
    {bc gc : List (List (SPoly α))} {sps : List (SPairCert α)}
    (h : checkGroebner n .grevlex gens basis bc gc sps = true) :
    spanOf n gens = spanOf n basis ∧
      ∀ f ∈ spanOf n basis, f ≠ 0 →
        ∃ b ∈ basis, (grevlexOrder n).degree (toMv n b) ≤
          (grevlexOrder n).degree f := by
  rw [checkGroebner] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨harity, hlead⟩, hbc⟩, hgc⟩, hsp⟩, hcover⟩ := h
  have harityAll := List.all_eq_true.mp harity
  have hbasisAr : ∀ b ∈ basis, arityLe n b = true := fun b hb =>
    harityAll b (by simp [hb])
  -- span equality from the existing proved-level machinery
  have hspan : spanOf n gens = spanOf n basis :=
    le_antisymm (checkSpanInclusion_sound n hgc) (checkSpanInclusion_sound n hbc)
  refine ⟨hspan, ?_⟩
  -- basis elements are nonzero with identified leading data
  have hleadAll := List.all_eq_true.mp hlead
  have hbases : ∀ i : Fin basis.length,
      ∃ t rest, normalizeBy .grevlex basis[(i : ℕ)] = t :: rest ∧
        (grevlexOrder n).degree (toMv n basis[(i : ℕ)]) = toMon n t.exps ∧
        (grevlexOrder n).leadingCoeff (toMv n basis[(i : ℕ)]) = t.coeff ∧
        toMv n basis[(i : ℕ)] ≠ 0 := by
    intro i
    have hOK := hleadAll basis[(i : ℕ)] (List.getElem_mem _)
    have har := hbasisAr basis[(i : ℕ)] (List.getElem_mem _)
    rcases hnorm : normalizeBy (α := α) .grevlex basis[(i : ℕ)] with _ | ⟨t, rest⟩
    · rw [leadOK, hnorm] at hOK
      cases hOK
    · obtain ⟨h1, h2, h3⟩ := lead_bridge hnorm hOK har
      exact ⟨t, rest, rfl, h1, h2, h3⟩
  have hb : ∀ i : Fin basis.length, basisFun n basis i ≠ 0 := fun i =>
    (hbases i).choose_spec.choose_spec.2.2.2
  -- standard representations for every ordered pair
  have hS : ∀ i j : Fin basis.length,
      Groebner.HasStdRep (grevlexOrder n) (basisFun n basis)
        (Groebner.sPoly (grevlexOrder n) (basisFun n basis i)
          (basisFun n basis j)) := by
    -- first: the certificate delivers it for i < j
    have key : ∀ i j : Fin basis.length, i < j →
        Groebner.HasStdRep (grevlexOrder n) (basisFun n basis)
          (Groebner.sPoly (grevlexOrder n) (basisFun n basis i)
            (basisFun n basis j)) := by
      intro i j hij
      -- find the covering certificate
      have hcov := List.all_eq_true.mp hcover (i : ℕ)
        (List.mem_range.mpr (lt_of_lt_of_le i.isLt le_rfl))
      have hcov := List.all_eq_true.mp hcov (j : ℕ)
        (List.mem_range.mpr j.isLt)
      rw [if_pos (show (i : ℕ) < (j : ℕ) from hij)] at hcov
      obtain ⟨sp, hspmem, hsp'⟩ := List.any_eq_true.mp hcov
      simp only [Bool.and_eq_true, beq_iff_eq] at hsp'
      obtain ⟨hspi, hspj⟩ := hsp'
      have hcheck := List.all_eq_true.mp hsp sp hspmem
      rw [checkSPair] at hcheck
      rw [hspi] at hcheck
      rw [hspj] at hcheck
      rw [List.getElem?_eq_getElem i.isLt, List.getElem?_eq_getElem j.isLt] at hcheck
      obtain ⟨ti, resti, hnormi, hdegi, hlci, hnei⟩ := hbases i
      obtain ⟨tj, restj, hnormj, hdegj, hlcj, hnej⟩ := hbases j
      simp only [leadTerm?] at hcheck
      rw [hnormi, hnormj] at hcheck
      simp only [List.head?_cons, Bool.and_eq_true, beq_iff_eq] at hcheck
      obtain ⟨⟨⟨⟨hoki, hokj⟩, hlen⟩, hpe⟩, hbounds⟩ := hcheck
      -- the sparse S-polynomial interprets to the abstract one
      set S : SPoly α := sparseSPoly ti tj basis[(i : ℕ)] basis[(j : ℕ)] with hSdef
      have harl : (zipMax ti.exps tj.exps).length ≤ n := by
        rw [zipMax_length]
        have h1 : ti.exps.length ≤ n := by
          have := normalizeBy_arity (n := n) .grevlex
            (hbasisAr basis[(i : ℕ)] (List.getElem_mem _)) ti
          rw [hnormi] at this
          exact this (List.mem_cons_self ..)
        have h2 : tj.exps.length ≤ n := by
          have := normalizeBy_arity (n := n) .grevlex
            (hbasisAr basis[(j : ℕ)] (List.getElem_mem _)) tj
          rw [hnormj] at this
          exact this (List.mem_cons_self ..)
        omega
      have hSmv : toMv n S = Groebner.sPoly (grevlexOrder n)
          (basisFun n basis i) (basisFun n basis j) := by
        rw [hSdef, sparseSPoly, Groebner.sPoly, toMv_append, toMv_mulRaw,
          toMv_mulRaw, toMv_cons, toMv_nil, add_zero, toMv_cons, toMv_nil,
          add_zero, toTerm, toTerm, toMon_zipSub, toMon_zipSub, toMon_zipMax]
        simp only [basisFun]
        rw [hdegi, hdegj, hlci, hlcj]
        rw [one_div, one_div, map_neg, neg_mul, ← sub_eq_add_neg]
      -- arity facts for the certificate data
      have harq : ∀ t : Fin basis.length,
          arityLe n (sp.quotients.getD t []) = true := by
        intro t
        rcases Nat.lt_or_ge (t : ℕ) sp.quotients.length with ht | ht
        · rw [List.getD_eq_getElem _ _ ht]
          refine harityAll _ ?_
          have : sp.quotients[(t : ℕ)] ∈ sp.quotients := List.getElem_mem _
          simp only [List.mem_append, List.mem_flatMap]
          exact Or.inr ⟨sp, hspmem, this⟩
        · rw [List.getD_eq_default _ _ ht]
          rfl
      have harS : arityLe n S = true := by
        rw [hSdef, sparseSPoly]
        have hb1 : arityLe n
            ([⟨1 / ti.coeff, zipSub (zipMax ti.exps tj.exps) ti.exps⟩] : SPoly α) = true := by
          simp only [arityLe, List.all_cons, List.all_nil, Bool.and_true,
            decide_eq_true_eq]
          exact le_trans (zipSub_length_le _ _) harl
        have hb2 : arityLe n
            ([⟨-(1 / tj.coeff), zipSub (zipMax ti.exps tj.exps) tj.exps⟩] : SPoly α) = true := by
          simp only [arityLe, List.all_cons, List.all_nil, Bool.and_true,
            decide_eq_true_eq]
          exact le_trans (zipSub_length_le _ _) harl
        have hAr1 := arityLe_mulRaw n hb1
          (hbasisAr basis[(i : ℕ)] (List.getElem_mem _))
        have hAr2 := arityLe_mulRaw n hb2
          (hbasisAr basis[(j : ℕ)] (List.getElem_mem _))
        rw [arityLe, List.all_append, Bool.and_eq_true]
        exact ⟨hAr1, hAr2⟩
      -- the cofactors and their bounds
      refine ⟨fun t => toMv n (sp.quotients.getD t []), ?_, ?_⟩
      · rw [comboF_toMv n sp.quotients basis (by exact_mod_cast hlen), ← hSmv]
        exact (polyEq_sound n hpe).symm
      · intro t
        have hqlen : sp.quotients.length = basis.length := by exact_mod_cast hlen
        have htq : (t : ℕ) < sp.quotients.length := by rw [hqlen]; exact t.isLt
        have htzip : (t : ℕ) < (List.zip sp.quotients basis).length := by
          rw [List.length_zip, hqlen]
          simpa using t.isLt
        have hmem : (sp.quotients[(t : ℕ)]'htq, basis[(t : ℕ)]) ∈
            List.zip sp.quotients basis := by
          rw [List.mem_iff_getElem]
          exact ⟨t, htzip, by rw [List.getElem_zip]⟩
        have hbound := List.all_eq_true.mp hbounds _ hmem
        have hgetD : sp.quotients.getD (t : ℕ) [] = sp.quotients[(t : ℕ)]'htq :=
          List.getD_eq_getElem _ _ htq
        set q := sp.quotients[(t : ℕ)]'htq with hq
        have hprod : toMv n (sp.quotients.getD (t : ℕ) []) * basisFun n basis t =
            toMv n (mulRaw q basis[(t : ℕ)]) := by
          simp only [basisFun]
          rw [toMv_mulRaw, hgetD]
        show (grevlexOrder n).toSyn ((grevlexOrder n).degree
            (toMv n (sp.quotients.getD (t : ℕ) []) * basisFun n basis t)) ≤ _
        rw [hprod]
        rcases hln : normalizeBy (α := α) .grevlex (mulRaw q basis[(t : ℕ)]) with
          _ | ⟨tp, restp⟩
        · -- product is semantically zero
          have hzero : toMv n (mulRaw q basis[(t : ℕ)]) = 0 := by
            rw [← toMv_normalizeBy n .grevlex, hln, toMv_nil]
          rw [hzero, (grevlexOrder n).degree_zero, map_zero]
          exact (grevlexOrder n).zero_le _
        · -- product nonzero: both leads exist, compare
          simp only [leadTerm?] at hbound
          rw [hln, List.head?_cons] at hbound
          rcases hlnS : normalizeBy (α := α) .grevlex S with _ | ⟨ts, restS⟩
          · rw [hlnS] at hbound
            simp at hbound
          · rw [hlnS, List.head?_cons] at hbound
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hbound
            obtain ⟨⟨hokp, hokS⟩, hcmp⟩ := hbound
            have harprod : arityLe n (mulRaw q basis[(t : ℕ)]) = true :=
              arityLe_mulRaw n (hgetD ▸ harq t) (hbasisAr _ (List.getElem_mem _))
            obtain ⟨hdp, _, _⟩ := lead_bridge hln hokp harprod
            obtain ⟨hdS, _, _⟩ := lead_bridge hlnS hokS harS
            have harp' : tp.exps.length ≤ n := by
              have := normalizeBy_arity (n := n) .grevlex harprod tp
              rw [hln] at this
              exact this (List.mem_cons_self ..)
            have harS' : ts.exps.length ≤ n := by
              have := normalizeBy_arity (n := n) .grevlex harS ts
              rw [hlnS] at this
              exact this (List.mem_cons_self ..)
            have hle : toDegRevLex (toMon n tp.exps) ≤ toDegRevLex (toMon n ts.exps) := by
              by_contra hgt
              push_neg at hgt
              exact hcmp ((cmpGRevLex_gt_iff n harp' harS').mpr hgt)
            rw [hdp, ← hSmv, hdS]
            exact hle
    intro i j
    rcases lt_trichotomy i j with hij | hij | hij
    · exact key i j hij
    · subst hij
      rw [Groebner.sPoly_self]
      exact Groebner.HasStdRep.zero _ _
    · rw [Groebner.sPoly_antisymm]
      exact (key j i hij).neg
  -- conclude via Buchberger
  intro f hf hf0
  rw [spanOf_eq_range] at hf
  obtain ⟨i, hi⟩ := Groebner.buchberger_criterion (grevlexOrder n)
    (basisFun n basis) hb hS hf hf0
  exact ⟨basis[i], List.getElem_mem _, hi⟩

/-! ### Negative certificates -/

/-- **Soundness of non-membership certificates.**  A division against
a certified Gröbner basis leaving a nonzero reduced remainder refutes
membership: if the element were in the span, so would be the
remainder, whose leading monomial the Gröbner property would then
force to be divisible by a basis leading monomial — exactly what the
reducedness check excludes. -/
theorem checkNonMembership_sound {gens basis : List (SPoly α)}
    {bc gc : List (List (SPoly α))} {sps : List (SPairCert α)}
    {f : SPoly α} {quots : List (SPoly α)} {r : SPoly α}
    (hgb : checkGroebner n .grevlex gens basis bc gc sps = true)
    (hnm : checkNonMembership n .grevlex basis f quots r = true) :
    toMv n f ∉ spanOf n basis := by
  intro hmem
  obtain ⟨_, hgro⟩ := checkGroebner_sound n hgb
  rw [checkNonMembership] at hnm
  simp only [Bool.and_eq_true] at hnm
  obtain ⟨⟨⟨⟨har, hlen⟩, hpe⟩, hokr⟩, hred⟩ := hnm
  have hid := polyEq_sound n hpe
  rw [addRaw, toMv_append] at hid
  have hrmem : toMv n r ∈ spanOf n basis := by
    have hr : toMv n r = toMv n f - toMv n (combo quots basis) := by
      rw [hid]; ring
    rw [hr]
    exact Ideal.sub_mem _ hmem (combo_mem_span n quots basis)
  have harr : arityLe n r = true :=
    List.all_eq_true.mp har r (by simp)
  rcases hnr : normalizeBy (α := α) .grevlex r with _ | ⟨tr, restr⟩
  · rw [leadOK, hnr] at hokr
    cases hokr
  · obtain ⟨hdr, _, hner⟩ := lead_bridge hnr hokr harr
    obtain ⟨b, hbmem, hble⟩ := hgro (toMv n r) hrmem hner
    have hbred := List.all_eq_true.mp hred tr
      (by rw [hnr]; exact List.mem_cons_self ..)
    have hbred := List.all_eq_true.mp hbred b hbmem
    simp only [Bool.and_eq_true] at hbred
    obtain ⟨hokb, hnd⟩ := hbred
    have harb : arityLe n b = true :=
      List.all_eq_true.mp har b (by simp [hbmem])
    rcases hnb : normalizeBy (α := α) .grevlex b with _ | ⟨tb, restb⟩
    · rw [leadOK, hnb] at hokb
      cases hokb
    · obtain ⟨hdb, _, _⟩ := lead_bridge hnb hokb harb
      simp only [leadTerm?] at hnd
      rw [hnb, List.head?_cons] at hnd
      rw [hdb, hdr] at hble
      have h1 : tb.exps.length ≤ n :=
        normalizeBy_arity .grevlex harb tb (by rw [hnb]; exact List.mem_cons_self ..)
      have h2 : tr.exps.length ≤ n :=
        normalizeBy_arity .grevlex harr tr (by rw [hnr]; exact List.mem_cons_self ..)
      have hdiv := (expsLe_iff n h1 h2).mpr hble
      simp [hdiv] at hnd

end M2Lean
