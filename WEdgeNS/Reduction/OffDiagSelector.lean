import WEdgeNS.Reduction.TruncClass
import WEdgeNS.Reduction.Marginal
import WEdgeNS.Reduction.ResolventShift
import WEdgeNS.Reduction.Cutoff
import WEdgeNS.Comparison.OffDiagSmallQ

/-!
# Off-diagonal resolvent entries at the selector positions
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-! ### Measurability of the selector events -/

/-- An entry of `symOfEntries c` is a measurable function of `c`. -/
private lemma offDiagSelector_measurable_entry {N : ℕ} (a b : Fin N) :
    Measurable fun c : Entries N => symOfEntries c a b := by
  unfold symOfEntries
  by_cases h : a = b
  · simp only [h, dite_true]
    exact (measurable_pi_apply b).comp measurable_fst
  · simp only [h, dite_false]
    by_cases h' : a < b
    · simp only [h', dite_true]
      exact (measurable_pi_apply _).comp measurable_snd
    · simp only [h', dite_false]
      exact (measurable_pi_apply _).comp measurable_snd

private lemma offDiagSelector_measurable_ne {N : ℕ} (a b : Fin N) :
    Measurable fun c : Entries N => symOfEntries c a b ≠ 0 :=
  measurableSet_setOfPred.1
    ((offDiagSelector_measurable_entry a b) (measurableSet_singleton 0).compl)

/-- `#{(i, j) : (H^C)_ij ≠ 0}` is a measurable function of the selector block. -/
private lemma offDiagSelector_measurable_nzCount {N : ℕ} :
    Measurable fun c : Entries N => (nzCount (symOfEntries c) : ℝ) := by
  classical
  have h : (fun c : Entries N => (nzCount (symOfEntries c) : ℝ)) = fun c =>
      ∑ p : Fin N × Fin N, if symOfEntries c p.1 p.2 ≠ 0 then (1 : ℝ) else 0 := by
    funext c
    rw [Finset.sum_boole]
    unfold nzCount
    congr 2
  rw [h]
  refine Finset.measurable_sum _ fun p _ => ?_
  exact Measurable.ite (measurableSet_setOfPred.2 (offDiagSelector_measurable_ne p.1 p.2))
    measurable_const measurable_const

/-- The admissible selector patterns (4.24)–(4.25) form a measurable set. -/
private lemma offDiagSelector_measurable_selGood (ε : ℝ) (N : ℕ) :
    Measurable fun c : Entries N => SelGood ε c := by
  change Measurable fun c : Entries N => (nzCount (symOfEntries c) : ℝ) ≤ (N : ℝ) ^ (5 * ε) ∧
    ∀ i j k l, symOfEntries c i j ≠ 0 → symOfEntries c k l ≠ 0 →
      ({i, j} : Finset (Fin N)) = {k, l} ∨ Disjoint ({i, j} : Finset (Fin N)) {k, l}
  refine Measurable.and ?_ ?_
  · exact measurableSet_setOfPred.1
      (measurableSet_le offDiagSelector_measurable_nzCount measurable_const)
  · refine Measurable.forall fun i => Measurable.forall fun j => Measurable.forall fun k =>
      Measurable.forall fun l => ?_
    exact (offDiagSelector_measurable_ne i j).imp
      ((offDiagSelector_measurable_ne k l).imp measurable_const)

private lemma offDiagSelector_measurable_touched {N : ℕ} (i : Fin N) :
    Measurable fun c : Entries N => ∃ k, symOfEntries c i k ≠ 0 :=
  Measurable.exists fun k => offDiagSelector_measurable_ne i k

/-! ### Counting the touched pairs -/

/-- On an admissible selector pattern, a set of ordered pairs of indices touched by `H^C` has at
most `(N^{5ε})²` elements; without an admissible pattern it is empty. -/
private lemma offDiagSelector_card_le {ε : ℝ} {N : ℕ} {c : Entries N}
    (F : Finset (Fin N × Fin N))
    (hF : ∀ p ∈ F, SelGood ε c ∧ (∃ k, symOfEntries c p.1 k ≠ 0) ∧
      (∃ k, symOfEntries c p.2 k ≠ 0)) :
    (F.card : ℝ) ≤ ((N : ℝ) ^ (5 * ε)) ^ 2 := by
  classical
  rcases F.eq_empty_or_nonempty with hE | ⟨p0, hp0⟩
  · rw [hE, Finset.card_empty, Nat.cast_zero]
    exact sq_nonneg _
  have hc : SelGood ε c := (hF p0 hp0).1
  set T := Finset.univ.filter fun i : Fin N => ∃ k, symOfEntries c i k ≠ 0 with hTdef
  have hT : T.card ≤ nzCount (symOfEntries c) := by
    have hsub : T ⊆ (Finset.univ.filter fun p : Fin N × Fin N =>
        symOfEntries c p.1 p.2 ≠ 0).image Prod.fst := by
      intro i hi
      obtain ⟨k, hk⟩ := (Finset.mem_filter.1 hi).2
      exact Finset.mem_image.2 ⟨(i, k), Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩, rfl⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  have hsub2 : F ⊆ T ×ˢ T := by
    intro p hp
    obtain ⟨-, h1, h2⟩ := hF p hp
    exact Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩⟩
  have h1 := Finset.card_le_card hsub2
  rw [Finset.card_product] at h1
  have h2 : (T.card : ℝ) ≤ (N : ℝ) ^ (5 * ε) := (Nat.cast_le.2 hT).trans hc.1
  calc (F.card : ℝ) ≤ ((T.card * T.card : ℕ) : ℝ) := Nat.cast_le.2 h1
    _ = (T.card : ℝ) ^ 2 := by push_cast; ring
    _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _) h2 2

/-! ### The union bound over rectangles -/

/-- If every off-diagonal event `b < |G_ij(z)|` of `H̃^S` has probability at most `M`, then the
event that it happens at two distinct positions touched by an admissible `H^C` has probability
at most `M (N^{5ε})²` on the auxiliary space. -/
private lemma offDiagSelector_union_bound {ν ν' : Measure ℝ} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] {ε : ℝ} {N : ℕ}
    (hS : ν {x | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)} ≠ 0)
    (hS' : ν' {x | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)} ≠ 0) (z : ℂ) (b M : ℝ)
    (hA : ∀ i j : Fin N, i ≠ j → (truncLawsNorm ν ν' ε N).law
      {ω | b < ‖resolventC (symOfEntries ω) z i j‖} ≤ ENNReal.ofReal M) :
    coupleLaw ν ν' ε N {u | SelGood ε u.2.2 ∧ ∃ i j, i ≠ j ∧
      (∃ k, selMat u i k ≠ 0) ∧ (∃ k, selMat u j k ≠ 0) ∧
      b < ‖resolventC (normSmall ν ε u) z i j‖} ≤
      ENNReal.ofReal M * ENNReal.ofReal (((N : ℝ) ^ (5 * ε)) ^ 2) := by
  classical
  have hT : IsProbabilityMeasure (truncCentered ν ((N : ℝ) ^ (1 / 2 - ε))) := by
    have := cond_isProbabilityMeasure (μ := ν) hS
    unfold truncCentered
    infer_instance
  have hT' : IsProbabilityMeasure (truncCentered ν' ((N : ℝ) ^ (1 / 2 - ε))) := by
    have := cond_isProbabilityMeasure (μ := ν') hS'
    unfold truncCentered
    infer_instance
  have hLg : ∀ μ : Measure ℝ, IsProbabilityMeasure μ →
      IsProbabilityMeasure (truncLargeCentered μ ((N : ℝ) ^ (1 / 2 - ε))) := by
    intro μ hμ
    unfold truncLargeCentered
    split_ifs with h
    · infer_instance
    · have := cond_isProbabilityMeasure (μ := μ) h
      infer_instance
  have hL := hLg ν inferInstance
  have hL' := hLg ν' inferInstance
  have hP := isProbabilityMeasure_coupleLaw (ε := ε) hS hS'
  set a : ℝ := truncNormFactor ν ε N * (Real.sqrt N)⁻¹ with ha
  set μC := entryLaw (ν.map (largeInd ((N : ℝ) ^ (1 / 2 - ε))))
    (ν'.map (largeInd ((N : ℝ) ^ (1 / 2 - ε)))) N with hμC
  set μL := entryLaw (truncLargeCentered ν ((N : ℝ) ^ (1 / 2 - ε)))
    (truncLargeCentered ν' ((N : ℝ) ^ (1 / 2 - ε))) N with hμL
  set μS := entryLaw (truncCentered ν ((N : ℝ) ^ (1 / 2 - ε)))
    (truncCentered ν' ((N : ℝ) ^ (1 / 2 - ε))) N with hμS
  have hcl : coupleLaw ν ν' ε N = μS.prod (μL.prod μC) := rfl
  set s := Finset.univ.filter fun p : Fin N × Fin N => p.1 ≠ p.2 with hs
  set A : Fin N × Fin N → Set (Entries N) := fun p =>
    {x | a • x ∈ {ω : Entries N | b < ‖resolventC (symOfEntries ω) z p.1 p.2‖}} with hAdef
  set R : Fin N × Fin N → Set (Entries N) := fun p =>
    {c | SelGood ε c ∧ (∃ k, symOfEntries c p.1 k ≠ 0) ∧ (∃ k, symOfEntries c p.2 k ≠ 0)}
    with hRdef
  have hR : ∀ p, MeasurableSet (R p) := fun p =>
    measurableSet_setOfPred.2 ((offDiagSelector_measurable_selGood ε N).and
      ((offDiagSelector_measurable_touched p.1).and (offDiagSelector_measurable_touched p.2)))
  have hsub : {u : CoupleSpace N | SelGood ε u.2.2 ∧ ∃ i j, i ≠ j ∧
      (∃ k, selMat u i k ≠ 0) ∧ (∃ k, selMat u j k ≠ 0) ∧
      b < ‖resolventC (normSmall ν ε u) z i j‖} ⊆
      ⋃ p ∈ s, A p ×ˢ (Set.univ ×ˢ R p) := by
    rintro u ⟨hG, i, j, hij, hi, hj, hb⟩
    refine Set.mem_iUnion₂.2 ⟨(i, j), Finset.mem_filter.2 ⟨Finset.mem_univ _, hij⟩, ?_⟩
    exact ⟨hb, Set.mem_univ _, hG, hi, hj⟩
  have hrect : ∀ p ∈ s, coupleLaw ν ν' ε N (A p ×ˢ (Set.univ ×ˢ R p)) ≤
      ENNReal.ofReal M * μC (R p) := by
    intro p hp
    have hij : p.1 ≠ p.2 := (Finset.mem_filter.1 hp).2
    have hA' : μS (A p) ≤ ENNReal.ofReal M := by
      have h1 := coupleLaw_normSmall_le hS hS'
        {ω : Entries N | b < ‖resolventC (symOfEntries ω) z p.1 p.2‖}
      have h2 : {u : CoupleSpace N | a • u.1 ∈
          {ω : Entries N | b < ‖resolventC (symOfEntries ω) z p.1 p.2‖}} =
          A p ×ˢ (Set.univ : Set (Entries N × Entries N)) := by
        ext u
        simp [hAdef, Set.mem_prod]
      rw [h2, hcl, Measure.prod_prod, measure_univ, mul_one] at h1
      exact h1.trans (hA _ _ hij)
    rw [hcl, Measure.prod_prod, Measure.prod_prod, measure_univ, one_mul]
    gcongr
  have hpt : ∀ c : Entries N, ∑ p ∈ s, (R p).indicator 1 c ≤
      ENNReal.ofReal (((N : ℝ) ^ (5 * ε)) ^ 2) := by
    intro c
    simp only [Set.indicator_apply, Pi.one_apply]
    rw [Finset.sum_boole, ← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal (offDiagSelector_card_le (c := c) _ fun p hp => ?_)
    exact (Finset.mem_filter.1 hp).2
  have hcount : ∑ p ∈ s, μC (R p) ≤ ENNReal.ofReal (((N : ℝ) ^ (5 * ε)) ^ 2) := by
    calc ∑ p ∈ s, μC (R p) = ∑ p ∈ s, ∫⁻ c, (R p).indicator 1 c ∂μC := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [lintegral_indicator_one (hR p)]
      _ = ∫⁻ c, ∑ p ∈ s, (R p).indicator 1 c ∂μC :=
          (lintegral_finsetSum s fun p _ => measurable_one.indicator (hR p)).symm
      _ ≤ ∫⁻ _, ENNReal.ofReal (((N : ℝ) ^ (5 * ε)) ^ 2) ∂μC := lintegral_mono hpt
      _ = ENNReal.ofReal (((N : ℝ) ^ (5 * ε)) ^ 2) := by
          rw [lintegral_const, measure_univ, mul_one]
  calc coupleLaw ν ν' ε N _ ≤ coupleLaw ν ν' ε N (⋃ p ∈ s, A p ×ˢ (Set.univ ×ˢ R p)) :=
        measure_mono hsub
    _ ≤ ∑ p ∈ s, coupleLaw ν ν' ε N (A p ×ˢ (Set.univ ×ˢ R p)) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ p ∈ s, ENNReal.ofReal M * μC (R p) := Finset.sum_le_sum hrect
    _ = ENNReal.ofReal M * ∑ p ∈ s, μC (R p) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by gcongr

/-! ### (4.39) -/

/-- (4.39): off-diagonal `|G_ij(z̃)| ≤ N^{-1/6}` on the positions touched by
`H̃^C`, which depend on the selector block only. -/
theorem tendsto_coupleLaw_offDiag {ν ν' : Measure ℝ} (hW : WignerLaws ν ν') (h14 : TailCond ν)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 30) :
    Tendsto (fun N : ℕ => (coupleLaw ν ν' ε N {u | SelGood ε u.2.2 ∧ ∃ i j, i ≠ j ∧
      (∃ k, selMat u i k ≠ 0) ∧ (∃ k, selMat u j k ≠ 0) ∧
      (N : ℝ) ^ (-(1 : ℝ) / 6) < ‖resolventC (normSmall ν ε u) (edgePt N) i j‖}).toReal)
      atTop (𝓝 0) := by
  have hprob := hW.prob
  have hprob' := hW.prob'
  obtain ⟨C1, N1, hC1⟩ := truncLawsNorm_smallQClass hW h14 hε0 (by linarith)
  obtain ⟨C, -, N2, hL38⟩ := offDiag_sq_le_smallQ (C1 := C1) (φs := 3 * ε / 4) (c := 1 / 3)
    (by positivity) (by norm_num) (by norm_num)
  obtain ⟨Cm, hCm1, hmsc⟩ := msc_bounds
  set a : ℝ := (1 / 3 - 10 * ε) / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have hev := (eventually_cutoff_mass_ne_zero (ν := ν) (ν' := ν') (ε := ε) (by linarith)).and
    ((eventually_ge_atTop (max (max N1 N2) 1)).and (phi_rpow_le_rpow C ha0))
  have hlim : Tendsto (fun N : ℕ => (Cm + 1) * (N : ℝ) ^ (-a)) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop ha0).comp tendsto_natCast_atTop_atTop).const_mul (Cm + 1)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun N => ENNReal.toReal_nonneg) ?_ hlim
  filter_upwards [hev] with N ⟨⟨hS, hS'⟩, hN, hφ⟩
  have hN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
  have hN0 : (0 : ℝ) < N := by linarith
  -- the scales `η = N^{-2/3}`, `u = N^{-1/3}`, `b = N^{-1/6}`
  set η : ℝ := (N : ℝ) ^ (-(2 : ℝ) / 3) with hηdef
  set u : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 3) with hudef
  set b : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 6) with hbdef
  set X : ℝ := (N : ℝ) ^ (5 * ε) with hXdef
  have hη0 : 0 < η := Real.rpow_pos_of_pos hN0 _
  have hu0 : 0 < u := Real.rpow_pos_of_pos hN0 _
  have hb0 : 0 < b := Real.rpow_pos_of_pos hN0 _
  have hpow2 : ∀ p : ℝ, ((N : ℝ) ^ p) ^ 2 = (N : ℝ) ^ (p * 2) := fun p => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hNηu : (N : ℝ) * η = u⁻¹ := by
    rw [hηdef, hudef, ← Real.rpow_neg hN0.le,
      show (N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3) = (N : ℝ) ^ ((1 : ℝ) + -(2 : ℝ) / 3) by
        rw [Real.rpow_add hN0, Real.rpow_one]]
    norm_num
  have huη : u ^ 2 = η := by rw [hudef, hpow2, hηdef]; norm_num
  have hbu : b ^ 2 = u := by rw [hbdef, hpow2, hudef]; norm_num
  have hfin : (N : ℝ) ^ a * u * X ^ 2 = (N : ℝ) ^ (-a) := by
    rw [hXdef, hpow2, hudef, ← Real.rpow_add hN0, ← Real.rpow_add hN0, ha]
    congr 1
    ring
  have hφ0 : 0 ≤ phi N ^ C := by
    unfold phi
    exact Real.rpow_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg N) _) _
  set M : ℝ := (Cm + 1) * phi N ^ C * u with hMdef
  have hM0 : 0 ≤ M := by positivity
  -- Lemma 3.8, (2.12) and Markov's inequality at `z̃`
  have hz_re : |(edgePt N).re| ≤ 5 := by
    change |(2 : ℝ)| ≤ 5
    norm_num
  have hz_im : (edgePt N).im = η := rfl
  have hLc := hC1 N hN1
  have hmsc' : (msc (edgePt N)).im ≤ Cm * u := by
    have hη10 : η ≤ 10 :=
      (Real.rpow_le_one_of_one_le_of_nonpos hN1' (by norm_num)).trans (by norm_num)
    have h := ((hmsc (edgePt N) hz_re (hz_im ▸ hη0) (hz_im ▸ hη10)).2.2.2
      (Or.inr (by change |(2 : ℝ)| ≤ 2; norm_num))).2
    have hk : kappa (edgePt N).re = 0 := by
      change kappa 2 = 0
      simp [kappa]
    rw [hk, zero_add, hz_im, ← huη, Real.sqrt_sq hu0.le] at h
    exact h
  have hA : ∀ i j : Fin N, i ≠ j → (truncLawsNorm ν ν' ε N).law
      {ω | b < ‖resolventC (symOfEntries ω) (edgePt N) i j‖} ≤ ENNReal.ofReal M := by
    intro i j hij
    have := isProbabilityMeasure_law hLc.1.isProb
    have hcont := continuous_resolventC_symOfEntries (N := N) (z := edgePt N)
      (hz_im ▸ hη0.ne') i j
    have hint : Integrable (fun ω => ‖resolventC (symOfEntries ω) (edgePt N) i j‖ ^ 2)
        (truncLawsNorm ν ν' ε N).law := by
      refine Integrable.of_bound (hcont.norm.pow 2).aestronglyMeasurable ((1 / η) ^ 2)
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (hz_im ▸ norm_resolventC_apply_le (symOfEntries_isHermitian ω) (hz_im ▸ hη0) i j) 2
    have hmk := mul_meas_ge_le_integral_of_nonneg
      (Eventually.of_forall fun ω => by positivity) hint (b ^ 2)
    have hE := hL38 N hN2 _ hLc (edgePt N) hz_re
      (by rw [hz_im, hηdef]; norm_num) i j hij
    have hbound : ∫ ω, ‖resolventC (symOfEntries ω) (edgePt N) i j‖ ^ 2
        ∂(truncLawsNorm ν ν' ε N).law ≤ phi N ^ C * ((Cm + 1) * u ^ 2) := by
      refine hE.trans (mul_le_mul_of_nonneg_left ?_ hφ0)
      rw [hz_im, hNηu, div_inv_eq_mul, one_div, inv_pow, inv_inv]
      nlinarith [mul_le_mul_of_nonneg_right hmsc' hu0.le]
    have hsub : {ω : Entries N | b < ‖resolventC (symOfEntries ω) (edgePt N) i j‖} ⊆
        {ω | b ^ 2 ≤ ‖resolventC (symOfEntries ω) (edgePt N) i j‖ ^ 2} :=
      fun ω hω => pow_le_pow_left₀ hb0.le (le_of_lt hω) 2
    have hmono := measureReal_mono (μ := (truncLawsNorm ν ν' ε N).law) hsub
    have hreal : ((truncLawsNorm ν ν' ε N).law
        {ω | b < ‖resolventC (symOfEntries ω) (edgePt N) i j‖}).toReal ≤ M := by
      rw [← measureReal_def]
      have h1 : u * (truncLawsNorm ν ν' ε N).law.real
          {ω | b < ‖resolventC (symOfEntries ω) (edgePt N) i j‖} ≤ u * M := by
        calc _ ≤ u * (truncLawsNorm ν ν' ε N).law.real
              {ω | b ^ 2 ≤ ‖resolventC (symOfEntries ω) (edgePt N) i j‖ ^ 2} :=
              mul_le_mul_of_nonneg_left hmono hu0.le
          _ = b ^ 2 * (truncLawsNorm ν ν' ε N).law.real
              {ω | b ^ 2 ≤ ‖resolventC (symOfEntries ω) (edgePt N) i j‖ ^ 2} := by rw [hbu]
          _ ≤ _ := hmk.trans hbound
          _ = u * M := by rw [hMdef]; ring
      exact le_of_mul_le_mul_left h1 hu0
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal hreal
  -- the union bound and the absorption of `φ^C`
  have hU := offDiagSelector_union_bound hS hS' (edgePt N) b M hA
  rw [← ENNReal.ofReal_mul hM0] at hU
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) hU).trans ?_
  calc M * X ^ 2 = (Cm + 1) * (phi N ^ C * u * X ^ 2) := by rw [hMdef]; ring
    _ ≤ (Cm + 1) * ((N : ℝ) ^ a * u * X ^ 2) := by
        gcongr
    _ = (Cm + 1) * (N : ℝ) ^ (-a) := by rw [hfin]

/-! ### Non-vacuity at Rademacher off-diagonal entries and `N(0, 2)` diagonal entries,
`ε = 1/100` -/

/-- (4.39) for Rademacher off-diagonal entries, `N(0, 2)` diagonal entries and `ε = 1/100`. -/
example : Tendsto (fun N : ℕ => (coupleLaw rademacher (gaussianReal 0 2) (1 / 100) N
    {u | SelGood (1 / 100) u.2.2 ∧ ∃ i j, i ≠ j ∧
      (∃ k, selMat u i k ≠ 0) ∧ (∃ k, selMat u j k ≠ 0) ∧
      (N : ℝ) ^ (-(1 : ℝ) / 6) <
        ‖resolventC (normSmall rademacher (1 / 100) u) (edgePt N) i j‖}).toReal)
    atTop (𝓝 0) :=
  tendsto_coupleLaw_offDiag rademacher_wignerLaws rademacher_tailCond (by norm_num) (by norm_num)

#print axioms tendsto_coupleLaw_offDiag

end WEdgeNS
