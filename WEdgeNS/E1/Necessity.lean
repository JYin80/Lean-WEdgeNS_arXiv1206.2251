import WEdgeNS.E1.Tail
import WEdgeNS.E1.Gamma

/-!
# Theorem 1.2: the necessary condition

If (1.4) fails, then `limsup_N P(λ_N ≥ 3) > 0`, which is (1.6). Consequently the rescaled largest
eigenvalue `N^{2/3}(λ_N - 2)` is not tight and converges in distribution to no probability law;
in particular it does not converge to the Tracy–Widom law.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace WEdgeNS

/-- Theorem 1.2, necessary condition, (1.6): if (1.4) fails, then `limsup_N P(λ_N ≥ 3) > 0`. -/
theorem E1 (ν ν' : Measure ℝ) (hW : WignerLaws ν ν') (h14 : ¬ TailCond ν) :
    ∃ c : ℝ, 0 < c ∧
      ∃ᶠ N in atTop, c ≤ (entryLaw ν ν' N {ω | 3 ≤ lambdaMax (wignerMatrix N ω)}).toReal := by
  have := hW.prob
  have := hW.prob'
  obtain ⟨c, hc, hfreq⟩ := frequently_tail_sqrt_ge h14
  refine ⟨(1 - Real.exp (-(c / 4))) / 4, ?_, ?_⟩
  · have : Real.exp (-(c / 4)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  · have hev : ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧ 2 * ∫ x, x ^ 2 ∂ν' ≤ N :=
      (eventually_ge_atTop 2).and (tendsto_natCast_atTop_atTop.eventually_ge_atTop _)
    refine (hfreq.and_eventually hev).mono ?_
    rintro N ⟨hp, hN2, hNm⟩
    have hp1 : (ν {x | 4 * Real.sqrt N ≤ |x|}).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    have hpow := one_sub_pow_choose_two_le hN2 hc.le hp hp1
    have hbig := entryLaw_bigEntryEvent (ν := ν) (ν' := ν') N
    have hdiag := diag_tail_le_half hW.sq_int' (by omega) hNm
    have hgam := entryLaw_gammaEvent_ge (ν := ν) hdiag
    have hmono : (entryLaw ν ν' N (gammaEvent N)).toReal ≤
        (entryLaw ν ν' N {ω | 3 ≤ lambdaMax (wignerMatrix N ω)}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (gammaEvent_subset N))
    linarith

/-- On `λ_N ≥ 3`, the rescaled largest eigenvalue is at least `N^{2/3}`. -/
private lemma rpow_le_edgeScaled {N : ℕ} {ω : Entries N}
    (h : 3 ≤ lambdaMax (wignerMatrix N ω)) : (N : ℝ) ^ ((2 : ℝ) / 3) ≤ edgeScaled N ω := by
  unfold edgeScaled
  have h0 : 0 ≤ (N : ℝ) ^ ((2 : ℝ) / 3) := by positivity
  nlinarith

/-- If (1.4) fails, then `P(N^{2/3}(λ_N - 2) > K) ≥ c` for infinitely many `N`, with `c > 0`
independent of `K`. -/
private lemma frequently_lt_edgeScaled (ν ν' : Measure ℝ) (hW : WignerLaws ν ν')
    (h14 : ¬ TailCond ν) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℝ,
      ∃ᶠ N in atTop, c ≤ (entryLaw ν ν' N {ω | K < edgeScaled N ω}).toReal := by
  have := hW.prob
  have := hW.prob'
  obtain ⟨c, hc, hfreq⟩ := E1 ν ν' hW h14
  refine ⟨c, hc, fun K => ?_⟩
  have hev : ∀ᶠ N : ℕ in atTop, K < (N : ℝ) ^ ((2 : ℝ) / 3) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
      tendsto_natCast_atTop_atTop).eventually_gt_atTop K
  refine (hfreq.and_eventually hev).mono ?_
  rintro N ⟨hN, hK⟩
  refine hN.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_))
  intro ω hω
  exact lt_of_lt_of_le hK (rpow_le_edgeScaled hω)

/-- Theorem 1.2, necessary condition: if (1.4) fails, `N^{2/3}(λ_N - 2)` is not tight. -/
theorem E1_not_tight (ν ν' : Measure ℝ) (hW : WignerLaws ν ν') (h14 : ¬ TailCond ν) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℝ,
      ∃ᶠ N in atTop, c ≤ (entryLaw ν ν' N {ω | K < |edgeScaled N ω|}).toReal := by
  have := hW.prob
  have := hW.prob'
  obtain ⟨c, hc, hfreq⟩ := frequently_lt_edgeScaled ν ν' hW h14
  refine ⟨c, hc, fun K => (hfreq K).mono fun N hN => ?_⟩
  refine hN.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_))
  intro ω (hω : K < edgeScaled N ω)
  exact lt_of_lt_of_le hω (le_abs_self _)

/-- Theorem 1.2, necessary condition: if (1.4) fails, `N^{2/3}(λ_N - 2)` converges in
distribution to no probability law on `ℝ`. -/
theorem E1_no_limit (ν ν' : Measure ℝ) (hW : WignerLaws ν ν') (h14 : ¬ TailCond ν) :
    ¬ ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      ∀ s : ℝ, ContinuousAt (cdf μ) s →
        Tendsto (fun N => edgeCdf ν ν' N s) atTop (𝓝 (cdf μ s)) := by
  rintro ⟨μ, -, hμ⟩
  have := hW.prob
  have := hW.prob'
  obtain ⟨c, hc, hfreq⟩ := frequently_lt_edgeScaled ν ν' hW h14
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, ∀ s ≥ K₀, 1 - c / 2 < cdf μ s :=
    eventually_atTop.mp ((tendsto_cdf_atTop μ).eventually (lt_mem_nhds (by linarith)))
  have hD : Dense {x | ¬ ContinuousAt (cdf μ) x}ᶜ :=
    (monotone_cdf μ).countable_not_continuousAt.dense_compl ℝ
  obtain ⟨K, hK, hK1, -⟩ := hD.exists_between (lt_add_one K₀)
  have hcont : ContinuousAt (cdf μ) K := by simpa using hK
  have hev : ∀ᶠ N in atTop, 1 - c / 2 < edgeCdf ν ν' N K :=
    (hμ K hcont).eventually (lt_mem_nhds (hK₀ K hK1.le))
  obtain ⟨N, hN1, hN2⟩ := ((hfreq K).and_eventually hev).exists
  have hcompl : edgeCdf ν ν' N K + (entryLaw ν ν' N {ω | K < edgeScaled N ω}).toReal = 1 := by
    unfold edgeCdf
    have hm : MeasurableSet {ω : Entries N | edgeScaled N ω ≤ K} :=
      measurableSet_le (measurable_edgeScaled N) measurable_const
    have hset : {ω : Entries N | K < edgeScaled N ω} = {ω | edgeScaled N ω ≤ K}ᶜ := by
      ext ω
      simp
    rw [hset, prob_compl_eq_one_sub hm, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
    simp
  linarith

/-- The hypotheses of `E1` hold at the law of `exists_wignerLaws_not_tailCond`, with `ν' = ν`. -/
example : ∃ ν : Measure ℝ, WignerLaws ν ν ∧ ¬ TailCond ν ∧
    ∃ c : ℝ, 0 < c ∧
      ∃ᶠ N in atTop, c ≤ (entryLaw ν ν N {ω | 3 ≤ lambdaMax (wignerMatrix N ω)}).toReal := by
  obtain ⟨ν, hW, h⟩ := exists_wignerLaws_not_tailCond
  exact ⟨ν, hW, h, E1 ν ν hW h⟩
#print axioms E1
#print axioms E1_not_tight
#print axioms E1_no_limit

end WEdgeNS
