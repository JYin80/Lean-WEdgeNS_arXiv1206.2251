import WEdgeNS.Reduction.Tail
import WEdgeNS.Comparison.Classes
import WEdgeNS.LocalLaw.Class

/-!
# The class of the truncated and normalised matrix
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-! ### Truncated moments from the tail condition (1.4) -/

/-- Condition (1.4) gives a uniform bound `s⁴ ν(|x| ≥ s) ≤ K` for `s ≥ 1`. -/
private lemma exists_tail_const {ν : Measure ℝ} [IsProbabilityMeasure ν] (h14 : TailCond ν) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, 1 ≤ s → s ^ 4 * (ν {x : ℝ | s ≤ |x|}).toReal ≤ K := by
  obtain ⟨s0, hs0⟩ := eventually_atTop.1 (h14.eventually (eventually_le_nhds zero_lt_one))
  refine ⟨max 1 (s0 ^ 4), le_trans zero_le_one (le_max_left _ _), fun s hs => ?_⟩
  have hm : (ν {x : ℝ | s ≤ |x|}).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := ν) (s := {x : ℝ | s ≤ |x|}))
    simpa using this
  by_cases h : s0 ≤ s
  · exact (hs0 s h).trans (le_max_left _ _)
  · push Not at h
    refine le_trans ?_ (le_max_right _ _)
    calc s ^ 4 * (ν {x : ℝ | s ≤ |x|}).toReal ≤ s ^ 4 * 1 :=
          mul_le_mul_of_nonneg_left hm (by positivity)
      _ ≤ s0 ^ 4 := by
          rw [mul_one]
          exact pow_le_pow_left₀ (by linarith) h.le 4

/-- Dyadic comparison: if `|x| ≤ 2^n` then
`|x|^p ≤ 1 + ∑_{k<n} ((2^{k+1})^p - (2^k)^p) 1_{2^k<|x|}`. -/
private lemma abs_pow_le_dyadic (p : ℕ) (n : ℕ) : ∀ x : ℝ, |x| ≤ 2 ^ n →
    |x| ^ p ≤ 1 + ∑ k ∈ Finset.range n,
      (((2 : ℝ) ^ (k + 1)) ^ p - ((2 : ℝ) ^ k) ^ p) * (if (2 : ℝ) ^ k < |x| then 1 else 0) := by
  induction n with
  | zero =>
    intro x hx
    simp only [pow_zero, Finset.range_zero, Finset.sum_empty, add_zero] at hx ⊢
    exact pow_le_one₀ (abs_nonneg x) hx
  | succ n ih =>
    intro x hx
    have hc : 0 ≤ ((2 : ℝ) ^ (n + 1)) ^ p - ((2 : ℝ) ^ n) ^ p := by
      have : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
      have := pow_le_pow_left₀ (by positivity) this p
      linarith
    rw [Finset.sum_range_succ]
    by_cases h : |x| ≤ 2 ^ n
    · have := ih x h
      have h0 : 0 ≤ (((2 : ℝ) ^ (n + 1)) ^ p - ((2 : ℝ) ^ n) ^ p) *
          (if (2 : ℝ) ^ n < |x| then 1 else 0) := by
        apply mul_nonneg hc; split_ifs <;> norm_num
      linarith
    · push Not at h
      have hall : ∀ k ∈ Finset.range n, (if (2 : ℝ) ^ k < |x| then (1 : ℝ) else 0) = 1 := by
        intro k hk
        have : (2 : ℝ) ^ k ≤ 2 ^ n :=
          pow_le_pow_right₀ (by norm_num) (Finset.mem_range.mp hk).le
        simp [lt_of_le_of_lt this h]
      have hn : (if (2 : ℝ) ^ n < |x| then (1 : ℝ) else 0) = 1 := by simp [h]
      rw [Finset.sum_congr rfl (fun k hk => by rw [hall k hk, mul_one]), hn, mul_one,
        Finset.sum_range_sub (fun k => ((2 : ℝ) ^ k) ^ p)]
      simp only [pow_zero, one_pow]
      have : |x| ^ p ≤ ((2 : ℝ) ^ (n + 1)) ^ p := pow_le_pow_left₀ (abs_nonneg x) hx p
      linarith

private lemma measurableSet_cut (T : ℝ) : MeasurableSet {x : ℝ | |x| ≤ T} :=
  measurableSet_le continuous_abs.measurable measurable_const

private lemma measurableSet_gt_abs (T : ℝ) : MeasurableSet {x : ℝ | T < |x|} :=
  measurableSet_lt measurable_const continuous_abs.measurable

private lemma cut_eq_Icc (T : ℝ) : {x : ℝ | |x| ≤ T} = Set.Icc (-T) T := by
  ext x; simp [abs_le]

/-- The truncated moment `∫_{|x| ≤ T} |x|^p dν` against a law with `s⁴ ν(|x| ≥ s) ≤ K`
for `s ≥ 1`, with `T ≤ 2^n`. -/
private lemma setIntegral_abs_pow_le {ν : Measure ℝ} [IsProbabilityMeasure ν] {K : ℝ}
    (hK : ∀ s : ℝ, 1 ≤ s → s ^ 4 * (ν {x : ℝ | s ≤ |x|}).toReal ≤ K)
    (p n : ℕ) {T : ℝ} (hT : T ≤ 2 ^ n) :
    ∫ x in {x : ℝ | |x| ≤ T}, |x| ^ p ∂ν ≤
      1 + ∑ k ∈ Finset.range n,
        (((2 : ℝ) ^ (k + 1)) ^ p - ((2 : ℝ) ^ k) ^ p) * (K / ((2 : ℝ) ^ k) ^ 4) := by
  set c : ℕ → ℝ := fun k => ((2 : ℝ) ^ (k + 1)) ^ p - ((2 : ℝ) ^ k) ^ p with hc
  have hc0 : ∀ k, 0 ≤ c k := fun k => by
    have : (2 : ℝ) ^ k ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ k)
    have := pow_le_pow_left₀ (by positivity) this p
    simp only [hc]; linarith
  have hmeas : ∀ k : ℕ, MeasurableSet {x : ℝ | (2 : ℝ) ^ k < |x|} := fun k => measurableSet_gt_abs _
  set g : ℝ → ℝ := fun x => 1 + ∑ k ∈ Finset.range n,
    ({x : ℝ | (2 : ℝ) ^ k < |x|}).indicator (fun _ => c k) x with hg
  have hgint : Integrable g ν :=
    (integrable_const 1).add (integrable_finsetSum _ fun k _ =>
      (integrable_const (c k)).indicator (hmeas k))
  have hg0 : ∀ x, 0 ≤ g x := fun x => by
    simp only [hg]
    refine add_nonneg zero_le_one (Finset.sum_nonneg fun k _ => ?_)
    exact Set.indicator_nonneg (fun _ _ => hc0 k) x
  have hpt : ∀ x ∈ {x : ℝ | |x| ≤ T}, |x| ^ p ≤ g x := by
    intro x hx
    have h1 := abs_pow_le_dyadic p n x (le_trans hx hT)
    refine h1.trans (le_of_eq ?_)
    simp only [hg]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : (2 : ℝ) ^ k < |x|
    · simp [Set.indicator, h, hc]
    · simp [Set.indicator, h]
  have hint : IntegrableOn (fun x : ℝ => |x| ^ p) {x : ℝ | |x| ≤ T} ν := by
    rw [cut_eq_Icc]
    exact (continuous_abs.pow p).integrableOn_Icc
  calc ∫ x in {x : ℝ | |x| ≤ T}, |x| ^ p ∂ν ≤ ∫ x in {x : ℝ | |x| ≤ T}, g x ∂ν :=
        setIntegral_mono_on hint hgint.integrableOn (measurableSet_cut T) hpt
    _ ≤ ∫ x, g x ∂ν := setIntegral_le_integral hgint (Eventually.of_forall hg0)
    _ = 1 + ∑ k ∈ Finset.range n, c k * (ν {x : ℝ | (2 : ℝ) ^ k < |x|}).toReal := by
        simp only [hg]
        rw [integral_add (integrable_const 1) (integrable_finsetSum _ fun k _ =>
          (integrable_const (c k)).indicator (hmeas k)), integral_const,
          integral_finsetSum _ fun k _ => (integrable_const (c k)).indicator (hmeas k)]
        simp only [integral_indicator_const _ (hmeas _), smul_eq_mul, measureReal_def]
        congr 1
        · simp
        · refine Finset.sum_congr rfl fun k _ => ?_
          ring
    _ ≤ 1 + ∑ k ∈ Finset.range n, c k * (K / ((2 : ℝ) ^ k) ^ 4) := by
        refine add_le_add_right (Finset.sum_le_sum fun k _ => ?_) 1
        refine mul_le_mul_of_nonneg_left ?_ (hc0 k)
        have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        have h2 := hK ((2 : ℝ) ^ k) h1
        have h3 : (ν {x : ℝ | (2 : ℝ) ^ k < |x|}).toReal ≤ (ν {x : ℝ | (2 : ℝ) ^ k ≤ |x|}).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _)
            (measure_mono fun x hx => show (2 : ℝ) ^ k ≤ |x| from le_of_lt hx)
        rw [le_div_iff₀ (by positivity)]
        calc (ν {x : ℝ | (2 : ℝ) ^ k < |x|}).toReal * ((2 : ℝ) ^ k) ^ 4
            ≤ (ν {x : ℝ | (2 : ℝ) ^ k ≤ |x|}).toReal * ((2 : ℝ) ^ k) ^ 4 :=
              mul_le_mul_of_nonneg_right h3 (by positivity)
          _ = ((2 : ℝ) ^ k) ^ 4 * (ν {x : ℝ | (2 : ℝ) ^ k ≤ |x|}).toReal := mul_comm _ _
          _ ≤ K := h2

/-- `E[|x|³; |x| ≤ T] ≤ 1 + 14 K`, uniformly in `T`. -/
private lemma setIntegral_abs_pow_three_le {ν : Measure ℝ} [IsProbabilityMeasure ν] {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ s : ℝ, 1 ≤ s → s ^ 4 * (ν {x : ℝ | s ≤ |x|}).toReal ≤ K) (T : ℝ) :
    ∫ x in {x : ℝ | |x| ≤ T}, |x| ^ 3 ∂ν ≤ 1 + 14 * K := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt T (show (1 : ℝ) < 2 by norm_num)
  refine (setIntegral_abs_pow_le hK 3 n hn.le).trans ?_
  have hterm : ∀ k : ℕ, (((2 : ℝ) ^ (k + 1)) ^ 3 - ((2 : ℝ) ^ k) ^ 3) * (K / ((2 : ℝ) ^ k) ^ 4) =
      7 * K * (1 / 2 : ℝ) ^ k := fun k => by
    have h2 : (0 : ℝ) < 2 ^ k := by positivity
    rw [one_div, inv_pow, pow_succ]
    field_simp
    ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.mul_sum]
  have := sum_geometric_two_le n
  nlinarith

/-- `E[x⁴; |x| ≤ T] ≤ 1 + 15 K n` for `T ≤ 2^n`. -/
private lemma setIntegral_pow_four_le {ν : Measure ℝ} [IsProbabilityMeasure ν] {K : ℝ}
    (hK : ∀ s : ℝ, 1 ≤ s → s ^ 4 * (ν {x : ℝ | s ≤ |x|}).toReal ≤ K) (n : ℕ) {T : ℝ}
    (hT : T ≤ 2 ^ n) :
    ∫ x in {x : ℝ | |x| ≤ T}, x ^ 4 ∂ν ≤ 1 + 15 * K * n := by
  have h := setIntegral_abs_pow_le hK 4 n hT
  have hterm : ∀ k : ℕ, (((2 : ℝ) ^ (k + 1)) ^ 4 - ((2 : ℝ) ^ k) ^ 4) * (K / ((2 : ℝ) ^ k) ^ 4) =
      15 * K := fun k => by
    field_simp
    ring
  rw [Finset.sum_congr rfl fun k _ => hterm k] at h
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  have e : ∀ x : ℝ, |x| ^ 4 = x ^ 4 := fun x => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
  simp only [e] at h
  linarith

/-! ### The cut-off conditional law -/

section Cond

variable {ν : Measure ℝ} {T : ℝ}

/-- Integrals against `ν( · | |x| ≤ T)`. -/
private lemma integral_cond_cut (f : ℝ → ℝ) :
    ∫ x, f x ∂(cond ν {x : ℝ | |x| ≤ T}) =
      ((ν {x : ℝ | |x| ≤ T}).toReal)⁻¹ * ∫ x in {x : ℝ | |x| ≤ T}, f x ∂ν := by
  unfold ProbabilityTheory.cond
  rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]

private lemma cond_cut_compl_null : cond ν {x : ℝ | |x| ≤ T} {x : ℝ | T < |x|} = 0 := by
  rw [cond_apply (measurableSet_cut T)]
  have : {x : ℝ | |x| ≤ T} ∩ {x : ℝ | T < |x|} = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2⟩
    exact absurd (show |x| ≤ T from h1) (not_le.mpr h2)
  simp [this]

private lemma ae_abs_le_cond : ∀ᵐ x ∂(cond ν {x : ℝ | |x| ≤ T}), |x| ≤ T := by
  rw [ae_iff]
  simpa using cond_cut_compl_null (ν := ν) (T := T)

private lemma integrable_cond_cut [IsFiniteMeasure ν] (hS : ν {x : ℝ | |x| ≤ T} ≠ 0)
    {g : ℝ → ℝ} (hg : Continuous g) : Integrable g (cond ν {x : ℝ | |x| ≤ T}) := by
  have h : IntegrableOn g {x : ℝ | |x| ≤ T} ν := by
    rw [cut_eq_Icc]
    exact hg.integrableOn_Icc
  unfold ProbabilityTheory.cond
  exact h.smul_measure (ENNReal.inv_ne_top.mpr hS)

private lemma isProb_cond_cut [IsFiniteMeasure ν] (hS : ν {x : ℝ | |x| ≤ T} ≠ 0) :
    IsProbabilityMeasure (cond ν {x : ℝ | |x| ≤ T}) :=
  cond_isProbabilityMeasure hS

/-- The centring `E[x | |x| ≤ T]` is at most `T` in absolute value. -/
private lemma abs_cutoffMean_le_cut [IsFiniteMeasure ν] (hS : ν {x : ℝ | |x| ≤ T} ≠ 0) :
    |cutoffMean ν T| ≤ T := by
  have := isProb_cond_cut hS
  have h := norm_integral_le_of_norm_le_const (μ := cond ν {x : ℝ | |x| ≤ T}) (f := fun x => x)
    (C := T) (by filter_upwards [ae_abs_le_cond (ν := ν) (T := T)] with x hx using hx)
  simpa [cutoffMean] using h

/-- For a probability law with finite second moment, `∫ (x - m)² = ∫ x² - m²`
for the mean `m`. -/
private lemma integral_sub_mean_sq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h1 : Integrable (fun x : ℝ => x) μ) (h2 : Integrable (fun x : ℝ => x ^ 2) μ) :
    ∫ x, (x - ∫ y, y ∂μ) ^ 2 ∂μ = ∫ x, x ^ 2 ∂μ - (∫ y, y ∂μ) ^ 2 := by
  set m := ∫ y, y ∂μ with hm
  have e : ∀ x : ℝ, (x - m) ^ 2 = (x ^ 2 - 2 * m * x) + m ^ 2 := fun x => by ring
  simp_rw [e]
  have i3 : Integrable (fun x : ℝ => x ^ 2 - 2 * m * x) μ := h2.sub (h1.const_mul (2 * m))
  rw [integral_add i3 (integrable_const _), integral_sub h2 (h1.const_mul (2 * m)),
    integral_const_mul, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul, ← hm]
  ring

/-- The law of the centred cut-off entry, scaled by `k`. -/
private def gk (ν : Measure ℝ) (T k : ℝ) : Measure ℝ :=
  (cond ν {x : ℝ | |x| ≤ T}).map (fun x => k * (x - cutoffMean ν T))

private lemma measurable_gk (ν : Measure ℝ) (T k : ℝ) :
    Measurable (fun x : ℝ => k * (x - cutoffMean ν T)) :=
  measurable_const.mul (measurable_id.sub_const _)

private lemma isProb_gk [IsFiniteMeasure ν] (hS : ν {x : ℝ | |x| ≤ T} ≠ 0) (k : ℝ) :
    IsProbabilityMeasure (gk ν T k) := by
  have := isProb_cond_cut hS
  exact (Measure.isProbabilityMeasure_map_iff (measurable_gk ν T k).aemeasurable).2 this

private lemma integral_gk {f : ℝ → ℝ} (hf : Continuous f) (k : ℝ) :
    ∫ x, f x ∂(gk ν T k) =
      ∫ x, f (k * (x - cutoffMean ν T)) ∂(cond ν {x : ℝ | |x| ≤ T}) :=
  integral_map (measurable_gk ν T k).aemeasurable hf.aestronglyMeasurable

end Cond

/-- The common scaling factor `(σ √N)⁻¹` of `truncLawsNorm`, `σ² = E|x^S_12 - m|²`. -/
private def normK (ν : Measure ℝ) (ε : ℝ) (N : ℕ) : ℝ :=
  (Real.sqrt (∫ x, x ^ 2 ∂(truncCentered ν ((N : ℝ) ^ (1 / 2 - ε)))))⁻¹ * (Real.sqrt N)⁻¹

private lemma map_map_scale (ν : Measure ℝ) (T c d : ℝ) :
    ((truncCentered ν T).map (fun x => c * x)).map (fun x => d * x) =
      gk ν T (d * c) := by
  have hm1 : Measurable (fun x : ℝ => x - ∫ y, y ∂(cond ν {x : ℝ | |x| ≤ T})) :=
    measurable_id.sub_const _
  have hm2 : Measurable (fun x : ℝ => c * x) := measurable_const.mul measurable_id
  have hm3 : Measurable (fun x : ℝ => d * x) := measurable_const.mul measurable_id
  unfold truncCentered gk cutoffMean
  rw [Measure.map_map hm2 hm1, Measure.map_map hm3 (hm2.comp hm1)]
  congr 1
  funext x
  simp only [Function.comp]
  ring

private lemma truncLawsNorm_off (ν ν' : Measure ℝ) (ε : ℝ) (N : ℕ) (p : OffDiag N) :
    (truncLawsNorm ν ν' ε N).off p = gk ν ((N : ℝ) ^ (1 / 2 - ε)) (normK ν ε N) := by
  have := map_map_scale ν ((N : ℝ) ^ (1 / 2 - ε)) (Real.sqrt N)⁻¹
    (Real.sqrt (∫ x, x ^ 2 ∂(truncCentered ν ((N : ℝ) ^ (1 / 2 - ε)))))⁻¹
  exact this

private lemma truncLawsNorm_diag (ν ν' : Measure ℝ) (ε : ℝ) (N : ℕ) (i : Fin N) :
    (truncLawsNorm ν ν' ε N).diag i = gk ν' ((N : ℝ) ^ (1 / 2 - ε)) (normK ν ε N) := by
  have := map_map_scale ν' ((N : ℝ) ^ (1 / 2 - ε)) (Real.sqrt N)⁻¹
    (Real.sqrt (∫ x, x ^ 2 ∂(truncCentered ν ((N : ℝ) ^ (1 / 2 - ε)))))⁻¹
  exact this

private lemma cut_eq_compl (T : ℝ) : {x : ℝ | |x| ≤ T} = {x : ℝ | T < |x|}ᶜ := by
  ext x; simp

/-- The mass of the cut-off event is `1 - α`. -/
private lemma toReal_cut {ν : Measure ℝ} [IsProbabilityMeasure ν] (T : ℝ) :
    (ν {x : ℝ | |x| ≤ T}).toReal = 1 - (ν {x : ℝ | T < |x|}).toReal := by
  rw [cut_eq_compl, prob_compl_eq_one_sub (measurableSet_gt_abs T),
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
  simp

private lemma cut_ne_zero_of_lt_one {ν : Measure ℝ} [IsProbabilityMeasure ν] {T : ℝ}
    (hα : (ν {x : ℝ | T < |x|}).toReal < 1) : ν {x : ℝ | |x| ≤ T} ≠ 0 := by
  intro h
  have := toReal_cut (ν := ν) T
  rw [h] at this
  simp only [ENNReal.toReal_zero] at this
  linarith

/-- The variance of the cut-off entry: `E|x^S - m|² = (1 - τ)/(1 - α) - m²`, where
`α = ν(|x| > T)`, `τ = E[x²; |x| > T]`, `m = E[x | |x| ≤ T]`. -/
private lemma sq_truncCentered_eq {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h2 : Integrable (fun x : ℝ => x ^ 2) ν) (hvar : ∫ x, x ^ 2 ∂ν = 1) {T : ℝ}
    (hα : (ν {x : ℝ | T < |x|}).toReal < 1) :
    ∫ x, x ^ 2 ∂(truncCentered ν T) =
      (1 - ∫ x in {x : ℝ | T < |x|}, x ^ 2 ∂ν) / (1 - (ν {x : ℝ | T < |x|}).toReal)
        - (cutoffMean ν T) ^ 2 := by
  have hS := cut_ne_zero_of_lt_one hα
  have := isProb_cond_cut hS
  have hmap : ∫ x, x ^ 2 ∂(truncCentered ν T) =
      ∫ x, (x - ∫ y, y ∂(cond ν {x : ℝ | |x| ≤ T})) ^ 2 ∂(cond ν {x : ℝ | |x| ≤ T}) := by
    unfold truncCentered
    exact integral_map (measurable_id.sub_const _).aemeasurable
      (continuous_pow 2).aestronglyMeasurable
  rw [hmap, integral_sub_mean_sq (integrable_cond_cut hS continuous_id)
    (integrable_cond_cut hS (continuous_pow 2)), integral_cond_cut, toReal_cut]
  have hsplit := integral_add_compl (measurableSet_gt_abs T) h2
  rw [← cut_eq_compl, hvar] at hsplit
  have : ∫ x in {x : ℝ | |x| ≤ T}, x ^ 2 ∂ν = 1 - ∫ x in {x : ℝ | T < |x|}, x ^ 2 ∂ν := by
    linarith
  rw [this, div_eq_inv_mul]
  rfl

private lemma rpow_pow_eq (N : ℕ) (a : ℝ) (k : ℕ) (b : ℝ) (h : b = a * k) :
    (N : ℝ) ^ b = ((N : ℝ) ^ a) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N), h]

private lemma one_le_cutoff {ε : ℝ} (hε : ε < 1 / 2) {N : ℕ} (hN : 1 ≤ N) :
    (1 : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε) :=
  Real.one_le_rpow (by exact_mod_cast hN) (by linarith)

/-- The real inequality behind (4.18). -/
private lemma sq_sub_one_le {t α τ m s : ℝ} (ht : 1 ≤ t) (hα0 : 0 ≤ α) (hα : α ≤ 1 / 2)
    (hτ : 0 ≤ τ) (hs : s = (1 - τ) / (1 - α) - m ^ 2) :
    t ^ 2 * |s - 1| ≤ 2 * (t ^ 4 * α + t ^ 2 * τ) + (t ^ 3 * |m|) ^ 2 := by
  have h1α : 0 < 1 - α := by linarith
  have hq0 : 0 ≤ (1 - α)⁻¹ := by positivity
  have hq2 : (1 - α)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ h1α (by norm_num)]; linarith
  have hsub : s - 1 = (α - τ) * (1 - α)⁻¹ - m ^ 2 := by
    rw [hs]; field_simp; ring
  have hab : |(α - τ) * (1 - α)⁻¹| ≤ 2 * (α + τ) := by
    rw [abs_le]
    have a1 := mul_le_mul_of_nonneg_left hq2 hα0
    have a2 := mul_le_mul_of_nonneg_left hq2 hτ
    have a3 := mul_nonneg hα0 hq0
    have a4 := mul_nonneg hτ hq0
    constructor <;> nlinarith
  have h2 : |s - 1| ≤ 2 * (α + τ) + m ^ 2 := by
    rw [hsub]
    calc |(α - τ) * (1 - α)⁻¹ - m ^ 2| ≤ |(α - τ) * (1 - α)⁻¹| + |m ^ 2| := abs_sub _ _
      _ ≤ 2 * (α + τ) + m ^ 2 := by rw [abs_of_nonneg (sq_nonneg m)]; linarith
  have ht2 : t ^ 2 ≤ t ^ 4 := pow_le_pow_right₀ ht (by norm_num)
  have ht6 : t ^ 2 ≤ t ^ 6 := pow_le_pow_right₀ ht (by norm_num)
  have e : (t ^ 3 * |m|) ^ 2 = t ^ 6 * m ^ 2 := by rw [mul_pow, sq_abs]; ring
  rw [e]
  have h3 : t ^ 2 * |s - 1| ≤ t ^ 2 * (2 * (α + τ) + m ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : t ^ 2 * α ≤ t ^ 4 * α := mul_le_mul_of_nonneg_right ht2 hα0
  have h5 : t ^ 2 * m ^ 2 ≤ t ^ 6 * m ^ 2 := mul_le_mul_of_nonneg_right ht6 (sq_nonneg m)
  nlinarith

/-- (4.18): `E|x^S_12|² = 1 - o(N^{-1+2ε})`. -/
theorem truncCentered_sq_sub_one {ν ν' : Measure ℝ} (hW : WignerLaws ν ν') (h14 : TailCond ν)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - 2 * ε) *
        |∫ x, x ^ 2 ∂(truncCentered ν ((N : ℝ) ^ (1 / 2 - ε))) - 1|) atTop (𝓝 0) := by
  have hprob := hW.prob
  obtain ⟨h1, -, -, -, h5⟩ := cutoff_tail_bounds hW h14 hε0 hε
  obtain ⟨hm, -⟩ := cutoffMean_bounds hW h14 hε0 hε
  have e2 : ∀ N : ℕ, (N : ℝ) ^ (1 - 2 * ε) = ((N : ℝ) ^ (1 / 2 - ε)) ^ 2 := fun N =>
    rpow_pow_eq N _ 2 _ (by push_cast; ring)
  have e3 : ∀ N : ℕ, (N : ℝ) ^ ((3 : ℝ) / 2 - 3 * ε) = ((N : ℝ) ^ (1 / 2 - ε)) ^ 3 := fun N =>
    rpow_pow_eq N _ 3 _ (by push_cast; ring)
  have e4 : ∀ N : ℕ, (N : ℝ) ^ (2 - 4 * ε) = ((N : ℝ) ^ (1 / 2 - ε)) ^ 4 := fun N =>
    rpow_pow_eq N _ 4 _ (by push_cast; ring)
  have hB : Tendsto (fun N : ℕ => 2 * ((N : ℝ) ^ (2 - 4 * ε) *
        (ν {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}).toReal +
      (N : ℝ) ^ (1 - 2 * ε) * ∫ x in {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}, x ^ 2 ∂ν) +
      ((N : ℝ) ^ ((3 : ℝ) / 2 - 3 * ε) * |cutoffMean ν ((N : ℝ) ^ (1 / 2 - ε))|) ^ 2)
      atTop (𝓝 0) := by
    have := ((h1.add h5).const_mul 2).add (hm.pow 2)
    simpa using this
  have hsmall := h1.eventually (eventually_le_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hB
  filter_upwards [hsmall, eventually_ge_atTop 1] with N hN hN1
  have ht := one_le_cutoff hε hN1
  have hα0 : 0 ≤ (ν {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}).toReal := ENNReal.toReal_nonneg
  have hα : (ν {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}).toReal ≤ 1 / 2 := by
    rw [e4] at hN
    have h4 : (1 : ℝ) ≤ ((N : ℝ) ^ (1 / 2 - ε)) ^ 4 := one_le_pow₀ ht
    nlinarith
  have hτ : 0 ≤ ∫ x in {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}, x ^ 2 ∂ν :=
    integral_nonneg fun x => sq_nonneg x
  have key := sq_sub_one_le ht hα0 hα hτ
    (sq_truncCentered_eq hW.sq_int hW.var (lt_of_le_of_lt hα (by norm_num)))
  rw [e2, e3, e4]
  exact key

/-! ### Moments of the scaled centred cut-off law -/

section Moments

variable {ν : Measure ℝ} {T : ℝ}

private lemma abs_sub_pow_three_le {x m : ℝ} (hm : |m| ≤ 1) :
    |x - m| ^ 3 ≤ 4 * |x| ^ 3 + 4 := by
  have h : |x - m| ≤ |x| + |m| := abs_sub x m
  have ha := abs_nonneg x
  have hb := abs_nonneg m
  calc |x - m| ^ 3 ≤ (|x| + |m|) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) h 3
    _ ≤ 4 * (|x| ^ 3 + |m| ^ 3) := by
        nlinarith [mul_nonneg (add_nonneg ha hb) (sq_nonneg (|x| - |m|))]
    _ ≤ 4 * |x| ^ 3 + 4 := by
        have : |m| ^ 3 ≤ 1 := pow_le_one₀ hb hm
        linarith

private lemma sub_pow_four_le {x m : ℝ} (hm : |m| ≤ 1) : (x - m) ^ 4 ≤ 8 * x ^ 4 + 8 := by
  have h : |x - m| ≤ |x| + |m| := abs_sub x m
  have ha := abs_nonneg x
  have hb := abs_nonneg m
  have e : ∀ y : ℝ, y ^ 4 = |y| ^ 4 := fun y => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  rw [e (x - m), e x]
  calc |x - m| ^ 4 ≤ (|x| + |m|) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) h 4
    _ ≤ 8 * (|x| ^ 4 + |m| ^ 4) := by
        nlinarith [mul_nonneg (sq_nonneg (|x| - |m|))
          (show 0 ≤ 7 * |x| ^ 2 + 10 * (|x| * |m|) + 7 * |m| ^ 2 by positivity)]
    _ ≤ 8 * |x| ^ 4 + 8 := by
        have : |m| ^ 4 ≤ 1 := pow_le_one₀ hb hm
        linarith

private lemma integral_gk_id [IsFiniteMeasure ν] (hS : ν {x : ℝ | |x| ≤ T} ≠ 0) (k : ℝ) :
    ∫ x, x ∂(gk ν T k) = 0 := by
  have := isProb_cond_cut hS
  have hi : Integrable (fun x : ℝ => x) (cond ν {x : ℝ | |x| ≤ T}) :=
    integrable_cond_cut hS continuous_id
  rw [integral_gk (f := fun x => x) continuous_id, integral_const_mul,
    integral_sub hi (integrable_const _), integral_const]
  simp [cutoffMean]

private lemma integral_gk_sq [IsFiniteMeasure ν] (k : ℝ) :
    ∫ x, x ^ 2 ∂(gk ν T k) =
      k ^ 2 * ∫ x, (x - cutoffMean ν T) ^ 2 ∂(cond ν {x : ℝ | |x| ≤ T}) := by
  rw [integral_gk (f := fun x => x ^ 2) (continuous_pow 2)]
  simp_rw [mul_pow]
  rw [integral_const_mul]

private lemma integral_gk_abs_three [IsFiniteMeasure ν] (k : ℝ) :
    ∫ x, |x| ^ 3 ∂(gk ν T k) =
      |k| ^ 3 * ∫ x, |x - cutoffMean ν T| ^ 3 ∂(cond ν {x : ℝ | |x| ≤ T}) := by
  rw [integral_gk (f := fun x => |x| ^ 3) (continuous_abs.pow 3)]
  simp_rw [abs_mul, mul_pow]
  rw [integral_const_mul]

private lemma integral_gk_four [IsFiniteMeasure ν] (k : ℝ) :
    ∫ x, x ^ 4 ∂(gk ν T k) =
      k ^ 4 * ∫ x, (x - cutoffMean ν T) ^ 4 ∂(cond ν {x : ℝ | |x| ≤ T}) := by
  rw [integral_gk (f := fun x => x ^ 4) (continuous_pow 4)]
  simp_rw [mul_pow]
  rw [integral_const_mul]

/-- The second moment of the centred cut-off law is the variance `∫ (x - m)² dμ` of
`μ = ν( · | |x| ≤ T)`. -/
private lemma integral_sub_cutoffMean_sq :
    ∫ x, (x - cutoffMean ν T) ^ 2 ∂(cond ν {x : ℝ | |x| ≤ T}) =
      ∫ x, x ^ 2 ∂(truncCentered ν T) := by
  unfold truncCentered
  exact (integral_map (measurable_id.sub_const _).aemeasurable
    (continuous_pow 2).aestronglyMeasurable).symm

private lemma integral_sub_cutoffMean_sq_le [IsFiniteMeasure ν] (hS : ν {x : ℝ | |x| ≤ T} ≠ 0) :
    ∫ x, (x - cutoffMean ν T) ^ 2 ∂(cond ν {x : ℝ | |x| ≤ T}) ≤
      ∫ x, x ^ 2 ∂(cond ν {x : ℝ | |x| ≤ T}) := by
  have := isProb_cond_cut hS
  have := integral_sub_mean_sq (integrable_cond_cut hS continuous_id)
    (integrable_cond_cut hS (continuous_pow 2))
  have h2 : (cutoffMean ν T) ^ 2 ≥ 0 := sq_nonneg _
  simp only [cutoffMean]
  nlinarith [sq_nonneg (∫ y, y ∂(cond ν {x : ℝ | |x| ≤ T}))]

private lemma integral_abs_sub_three_le [IsFiniteMeasure ν] (hS : ν {x : ℝ | |x| ≤ T} ≠ 0)
    (hm : |cutoffMean ν T| ≤ 1) :
    ∫ x, |x - cutoffMean ν T| ^ 3 ∂(cond ν {x : ℝ | |x| ≤ T}) ≤
      4 * ∫ x, |x| ^ 3 ∂(cond ν {x : ℝ | |x| ≤ T}) + 4 := by
  have := isProb_cond_cut hS
  have hi1 : Integrable (fun x : ℝ => |x - cutoffMean ν T| ^ 3) (cond ν {x : ℝ | |x| ≤ T}) :=
    integrable_cond_cut hS ((continuous_abs.comp (continuous_id.sub continuous_const)).pow 3)
  have hi2 : Integrable (fun x : ℝ => |x| ^ 3) (cond ν {x : ℝ | |x| ≤ T}) :=
    integrable_cond_cut hS (continuous_abs.pow 3)
  calc ∫ x, |x - cutoffMean ν T| ^ 3 ∂(cond ν {x : ℝ | |x| ≤ T})
      ≤ ∫ x, (4 * |x| ^ 3 + 4) ∂(cond ν {x : ℝ | |x| ≤ T}) :=
        integral_mono hi1 ((hi2.const_mul 4).add (integrable_const _))
          fun x => abs_sub_pow_three_le hm
    _ = 4 * ∫ x, |x| ^ 3 ∂(cond ν {x : ℝ | |x| ≤ T}) + 4 := by
        rw [integral_add (hi2.const_mul 4) (integrable_const _), integral_const_mul,
          integral_const]
        simp

private lemma integral_sub_four_le [IsFiniteMeasure ν] (hS : ν {x : ℝ | |x| ≤ T} ≠ 0)
    (hm : |cutoffMean ν T| ≤ 1) :
    ∫ x, (x - cutoffMean ν T) ^ 4 ∂(cond ν {x : ℝ | |x| ≤ T}) ≤
      8 * ∫ x, x ^ 4 ∂(cond ν {x : ℝ | |x| ≤ T}) + 8 := by
  have := isProb_cond_cut hS
  have hi1 : Integrable (fun x : ℝ => (x - cutoffMean ν T) ^ 4) (cond ν {x : ℝ | |x| ≤ T}) :=
    integrable_cond_cut hS ((continuous_id.sub continuous_const).pow 4)
  have hi2 : Integrable (fun x : ℝ => x ^ 4) (cond ν {x : ℝ | |x| ≤ T}) :=
    integrable_cond_cut hS (continuous_pow 4)
  calc ∫ x, (x - cutoffMean ν T) ^ 4 ∂(cond ν {x : ℝ | |x| ≤ T})
      ≤ ∫ x, (8 * x ^ 4 + 8) ∂(cond ν {x : ℝ | |x| ≤ T}) :=
        integral_mono hi1 ((hi2.const_mul 8).add (integrable_const _))
          fun x => sub_pow_four_le hm
    _ = 8 * ∫ x, x ^ 4 ∂(cond ν {x : ℝ | |x| ≤ T}) + 8 := by
        rw [integral_add (hi2.const_mul 8) (integrable_const _), integral_const_mul,
          integral_const]
        simp

private lemma inv_le_two {P : ℝ} (hP : 1 / 2 ≤ P) : P⁻¹ ≤ 2 := by
  have hP0 : 0 < P := by linarith
  rw [inv_le_comm₀ hP0 (by norm_num)]
  linarith

/-- The mass of `{|x| ≤ T}` is at least `1/2` when the tail mass is at most `1/2`. -/
private lemma half_le_cut [IsProbabilityMeasure ν]
    (hα : (ν {x : ℝ | T < |x|}).toReal ≤ 1 / 2) : 1 / 2 ≤ (ν {x : ℝ | |x| ≤ T}).toReal := by
  rw [toReal_cut]; linarith

private lemma integral_cond_abs_three_le [IsProbabilityMeasure ν] {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ s : ℝ, 1 ≤ s → s ^ 4 * (ν {x : ℝ | s ≤ |x|}).toReal ≤ K)
    (hα : (ν {x : ℝ | T < |x|}).toReal ≤ 1 / 2) :
    ∫ x, |x| ^ 3 ∂(cond ν {x : ℝ | |x| ≤ T}) ≤ 2 * (1 + 14 * K) := by
  rw [integral_cond_cut]
  have h1 := setIntegral_abs_pow_three_le hK0 hK T
  have h0 : 0 ≤ ∫ x in {x : ℝ | |x| ≤ T}, |x| ^ 3 ∂ν := integral_nonneg fun x => by positivity
  exact mul_le_mul (inv_le_two (half_le_cut hα)) h1 h0 (by norm_num)

private lemma integral_cond_four_le [IsProbabilityMeasure ν] {K : ℝ}
    (hK : ∀ s : ℝ, 1 ≤ s → s ^ 4 * (ν {x : ℝ | s ≤ |x|}).toReal ≤ K)
    (hα : (ν {x : ℝ | T < |x|}).toReal ≤ 1 / 2) {n : ℕ} (hT : T ≤ 2 ^ n) :
    ∫ x, x ^ 4 ∂(cond ν {x : ℝ | |x| ≤ T}) ≤ 2 * (1 + 15 * K * n) := by
  rw [integral_cond_cut]
  have h1 := setIntegral_pow_four_le hK n hT
  have h0 : 0 ≤ ∫ x in {x : ℝ | |x| ≤ T}, x ^ 4 ∂ν := integral_nonneg fun x => by positivity
  exact mul_le_mul (inv_le_two (half_le_cut hα)) h1 h0 (by norm_num)

private lemma integral_cond_sq_le [IsProbabilityMeasure ν] (h2 : Integrable (fun x : ℝ => x ^ 2) ν)
    (hα : (ν {x : ℝ | T < |x|}).toReal ≤ 1 / 2) :
    ∫ x, x ^ 2 ∂(cond ν {x : ℝ | |x| ≤ T}) ≤ 2 * ∫ x, x ^ 2 ∂ν := by
  rw [integral_cond_cut]
  have h1 : ∫ x in {x : ℝ | |x| ≤ T}, x ^ 2 ∂ν ≤ ∫ x, x ^ 2 ∂ν :=
    setIntegral_le_integral h2 (Eventually.of_forall fun x => sq_nonneg x)
  have h0 : 0 ≤ ∫ x in {x : ℝ | |x| ≤ T}, x ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg x
  exact mul_le_mul (inv_le_two (half_le_cut hα)) h1 h0 (by norm_num)

/-- The scaled centred cut-off law is carried by `{|x| ≤ r}` once `|k| · 2T ≤ r`. -/
private lemma gk_null_of_le [IsFiniteMeasure ν] {k r : ℝ} (hr : |k| * (2 * T) ≤ r)
    (hS : ν {x : ℝ | |x| ≤ T} ≠ 0) : gk ν T k {x : ℝ | r < |x|} = 0 := by
  have hm := abs_cutoffMean_le_cut hS
  have hmeas : MeasurableSet {x : ℝ | r < |x|} := measurableSet_gt_abs r
  unfold gk
  rw [Measure.map_apply (measurable_gk ν T k) hmeas]
  refine measure_mono_null (fun x hx => ?_) (cond_cut_compl_null (ν := ν) (T := T))
  by_contra hx'
  have hxT : |x| ≤ T := not_lt.mp hx'
  have : |k * (x - cutoffMean ν T)| ≤ r := by
    rw [abs_mul]
    calc |k| * |x - cutoffMean ν T| ≤ |k| * (T + T) :=
          mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hxT hm)) (abs_nonneg k)
      _ = |k| * (2 * T) := by ring
      _ ≤ r := hr
  exact absurd hx (not_lt.mpr this)

end Moments

/-! ### The class conditions for large `N` -/

private lemma invSqrt_pow_three (N : ℕ) :
    ((Real.sqrt N)⁻¹) ^ 3 = (N : ℝ) ^ (-(3 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg N), ← Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg N)]
  congr 1
  norm_num

private lemma invSqrt_sq (N : ℕ) : ((Real.sqrt N)⁻¹) ^ 2 = (N : ℝ)⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]

/-- Properties of the scaling factor `k = (σ √N)⁻¹` once `σ² ≥ 1/2`. -/
private lemma normK_props (ν : Measure ℝ) (ε : ℝ) (N : ℕ)
    (hσ : 1 / 2 ≤ ∫ x, x ^ 2 ∂(truncCentered ν ((N : ℝ) ^ (1 / 2 - ε)))) :
    0 ≤ normK ν ε N ∧
      (normK ν ε N) ^ 2 * (∫ x, x ^ 2 ∂(truncCentered ν ((N : ℝ) ^ (1 / 2 - ε)))) = (N : ℝ)⁻¹ ∧
      (normK ν ε N) ^ 2 ≤ 2 * (N : ℝ)⁻¹ ∧ normK ν ε N ≤ 3 / 2 * (Real.sqrt N)⁻¹ := by
  unfold normK
  set σ2 := ∫ x, x ^ 2 ∂(truncCentered ν ((N : ℝ) ^ (1 / 2 - ε))) with hσ2
  have hσ0 : 0 < σ2 := by linarith
  have hs : 0 < Real.sqrt σ2 := Real.sqrt_pos.mpr hσ0
  have hN : 0 ≤ (Real.sqrt N)⁻¹ := by positivity
  have hsq : ((Real.sqrt σ2)⁻¹ * (Real.sqrt N)⁻¹) ^ 2 = σ2⁻¹ * (N : ℝ)⁻¹ := by
    rw [mul_pow, inv_pow, Real.sq_sqrt hσ0.le, invSqrt_sq]
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · rw [hsq]; field_simp
  · rw [hsq]
    have : σ2⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hσ0 (by norm_num)]; linarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  · have h23 : (2 : ℝ) / 3 ≤ Real.sqrt σ2 := by
      rw [Real.le_sqrt' (by norm_num)]; linarith
    have : (Real.sqrt σ2)⁻¹ ≤ 3 / 2 := by
      rw [inv_le_comm₀ hs (by norm_num)]; linarith
    exact mul_le_mul_of_nonneg_right this hN

/-- The truncation level is at most `2^⌈log N⌉`, and `⌈log N⌉ ≤ 2 log N`. -/
private lemma cutoff_le_two_pow {ε : ℝ} (hε : 0 ≤ ε) {N : ℕ} (hN : 3 ≤ N) :
    (N : ℝ) ^ (1 / 2 - ε) ≤ 2 ^ ⌈Real.log N⌉₊ ∧ (⌈Real.log N⌉₊ : ℝ) ≤ 2 * Real.log N ∧
      1 ≤ Real.log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    have := Real.exp_one_lt_d9
    linarith
  have hceil := Nat.le_ceil (Real.log N)
  have hceil' : (⌈Real.log N⌉₊ : ℝ) < Real.log N + 1 := Nat.ceil_lt_add_one (by linarith)
  refine ⟨?_, by linarith, hlog1⟩
  have h1 : (N : ℝ) ^ (1 / 2 - ε) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : (N : ℝ) ^ ((1 : ℝ) / 2) = Real.exp (Real.log N * (1 / 2)) := by
    rw [Real.rpow_def_of_pos hN0]
  have h3 : (2 : ℝ) ^ (Real.log N) ≤ 2 ^ ⌈Real.log N⌉₊ := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hceil
  have h4 : (2 : ℝ) ^ (Real.log N) = Real.exp (Real.log 2 * Real.log N) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
  have h5 : Real.exp (Real.log N * (1 / 2)) ≤ Real.exp (Real.log 2 * Real.log N) := by
    apply Real.exp_le_exp.mpr
    have := Real.log_two_gt_d9
    nlinarith
  calc (N : ℝ) ^ (1 / 2 - ε) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := h1
    _ = Real.exp (Real.log N * (1 / 2)) := h2
    _ ≤ Real.exp (Real.log 2 * Real.log N) := h5
    _ = (2 : ℝ) ^ (Real.log N) := h4.symm
    _ ≤ _ := h3

/-- `T / √N = N^{-ε}` and `N^{-ε} N^{ε/4} = N^{-3ε/4}`. -/
private lemma cutoff_mul_invSqrt (ε : ℝ) {N : ℕ} (hN : 0 < N) :
    (N : ℝ) ^ (1 / 2 - ε) * (Real.sqrt N)⁻¹ = (N : ℝ) ^ (-ε) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hN0.le, ← Real.rpow_add hN0]
  congr 1
  ring

/-- The class of Theorem 3.6 for one `N`, under explicit quantitative preconditions. -/
private lemma smallQClass_of_good {ν ν' : Measure ℝ} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] {K V : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ s : ℝ, 1 ≤ s → s ^ 4 * (ν {x : ℝ | s ≤ |x|}).toReal ≤ K) (hV0 : 0 ≤ V)
    (h2' : Integrable (fun x : ℝ => x ^ 2) ν') (hV : ∫ x, x ^ 2 ∂ν' ≤ V)
    {ε : ℝ} (hε0 : 0 < ε) {N : ℕ} (hN : 3 ≤ N)
    (hα : (ν {x : ℝ | (N : ℝ) ^ (1 / 2 - ε) < |x|}).toReal ≤ 1 / 2)
    (hα' : (ν' {x : ℝ | (N : ℝ) ^ (1 / 2 - ε) < |x|}).toReal ≤ 1 / 2)
    (hm : |cutoffMean ν ((N : ℝ) ^ (1 / 2 - ε))| ≤ 1)
    (hσ : 1 / 2 ≤ ∫ x, x ^ 2 ∂(truncCentered ν ((N : ℝ) ^ (1 / 2 - ε))))
    (hq : 3 ≤ (N : ℝ) ^ (ε / 4)) :
    SmallQClass (3000 * (1 + K + V)) (3 * ε / 4) N (truncLawsNorm ν ν' ε N) := by
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hS : ν {x : ℝ | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)} ≠ 0 := by
    intro h
    have := half_le_cut (ν := ν) hα
    rw [h] at this
    simp at this
    linarith
  have hS' : ν' {x : ℝ | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)} ≠ 0 := by
    intro h
    have := half_le_cut (ν := ν') hα'
    rw [h] at this
    simp at this
    linarith
  obtain ⟨hk0, hkσ, hk2, hk1⟩ := normK_props ν ε N hσ
  obtain ⟨hTn, hn2, hlog1⟩ := cutoff_le_two_pow hε0.le hN
  have hb0 : 0 ≤ (Real.sqrt N)⁻¹ := by positivity
  have hT0 : 0 ≤ (N : ℝ) ^ (1 / 2 - ε) := (Real.rpow_pos_of_pos hNr _).le
  have hr : |normK ν ε N| * (2 * (N : ℝ) ^ (1 / 2 - ε)) ≤ ((N : ℝ) ^ (3 * ε / 4))⁻¹ := by
    rw [abs_of_nonneg hk0, ← Real.rpow_neg hNr.le]
    have e1 : (N : ℝ) ^ (-(3 * ε / 4)) = (N : ℝ) ^ (-ε) * (N : ℝ) ^ (ε / 4) := by
      rw [← Real.rpow_add hNr]; congr 1; ring
    have e2 := cutoff_mul_invSqrt ε hN0
    have hpos : 0 ≤ (N : ℝ) ^ (-ε) := (Real.rpow_pos_of_pos hNr _).le
    calc normK ν ε N * (2 * (N : ℝ) ^ (1 / 2 - ε))
        ≤ (3 / 2 * (Real.sqrt N)⁻¹) * (2 * (N : ℝ) ^ (1 / 2 - ε)) :=
          mul_le_mul_of_nonneg_right hk1 (by positivity)
      _ = 3 * ((N : ℝ) ^ (1 / 2 - ε) * (Real.sqrt N)⁻¹) := by ring
      _ = 3 * (N : ℝ) ^ (-ε) := by rw [e2]
      _ ≤ (N : ℝ) ^ (-ε) * (N : ℝ) ^ (ε / 4) := by nlinarith
      _ = (N : ℝ) ^ (-(3 * ε / 4)) := e1.symm
  have hsupp : (truncLawsNorm ν ν' ε N).BoundedSupportAS ((N : ℝ) ^ (3 * ε / 4)) :=
    ⟨fun i => by rw [truncLawsNorm_diag]; exact gk_null_of_le hr hS',
     fun p => by rw [truncLawsNorm_off]; exact gk_null_of_le hr hS⟩
  have hprob : (truncLawsNorm ν ν' ε N).IsProb :=
    ⟨fun i => by rw [truncLawsNorm_diag]; exact isProb_gk hS' _,
     fun p => by rw [truncLawsNorm_off]; exact isProb_gk hS _⟩
  refine ⟨⟨hprob, (hsupp.integrable_pow hprob 2).1, (hsupp.integrable_pow hprob 4).2,
    fun i => by rw [truncLawsNorm_diag]; exact integral_gk_id hS' _,
    fun p => by rw [truncLawsNorm_off]; exact integral_gk_id hS _, ?_, ?_, ?_, ?_⟩, hsupp⟩
  · -- diagonal variance
    intro i
    rw [truncLawsNorm_diag, integral_gk_sq]
    have h1 := integral_sub_cutoffMean_sq_le hS'
    have h2 := integral_cond_sq_le h2' hα'
    have hNi : 0 ≤ (N : ℝ)⁻¹ := by positivity
    calc normK ν ε N ^ 2 * ∫ x, (x - cutoffMean ν' ((N : ℝ) ^ (1 / 2 - ε))) ^ 2
          ∂(cond ν' {x : ℝ | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)})
        ≤ normK ν ε N ^ 2 * (2 * V) :=
          mul_le_mul_of_nonneg_left (h1.trans (h2.trans (by linarith))) (sq_nonneg _)
      _ ≤ (2 * (N : ℝ)⁻¹) * (2 * V) := mul_le_mul_of_nonneg_right hk2 (by positivity)
      _ ≤ 3000 * (1 + K + V) / N := by
          rw [div_eq_mul_inv]
          have := mul_nonneg (show 0 ≤ 3000 * (1 + K + V) - 4 * V by linarith) hNi
          nlinarith
  · -- off-diagonal variance
    intro p
    rw [truncLawsNorm_off, integral_gk_sq, integral_sub_cutoffMean_sq]
    exact hkσ
  · -- third moment
    intro p
    rw [truncLawsNorm_off, integral_gk_abs_three]
    have h1 := integral_abs_sub_three_le hS hm
    have h2 := integral_cond_abs_three_le hK0 hK hα
    have hk3 : |normK ν ε N| ^ 3 ≤ 27 / 8 * (N : ℝ) ^ (-(3 : ℝ) / 2) := by
      rw [abs_of_nonneg hk0, ← invSqrt_pow_three]
      calc normK ν ε N ^ 3 ≤ (3 / 2 * (Real.sqrt N)⁻¹) ^ 3 := pow_le_pow_left₀ hk0 hk1 3
        _ = 27 / 8 * ((Real.sqrt N)⁻¹) ^ 3 := by ring
    have hnn : 0 ≤ ∫ x, |x - cutoffMean ν ((N : ℝ) ^ (1 / 2 - ε))| ^ 3
        ∂(cond ν {x : ℝ | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)}) :=
      integral_nonneg fun x => by positivity
    have hp : 0 ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) := (Real.rpow_pos_of_pos hNr _).le
    calc |normK ν ε N| ^ 3 * ∫ x, |x - cutoffMean ν ((N : ℝ) ^ (1 / 2 - ε))| ^ 3
          ∂(cond ν {x : ℝ | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)})
        ≤ (27 / 8 * (N : ℝ) ^ (-(3 : ℝ) / 2)) * (12 + 112 * K) :=
          mul_le_mul hk3 (by linarith) hnn (by positivity)
      _ = (27 / 8 * (12 + 112 * K)) * (N : ℝ) ^ (-(3 : ℝ) / 2) := by ring
      _ ≤ 3000 * (1 + K + V) * (N : ℝ) ^ (-(3 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right (by linarith) hp
  · -- fourth moment
    intro p
    rw [truncLawsNorm_off, integral_gk_four]
    have h1 := integral_sub_four_le hS hm
    have h2 := integral_cond_four_le hK hα hTn
    have hnn : 0 ≤ ∫ x, (x - cutoffMean ν ((N : ℝ) ^ (1 / 2 - ε))) ^ 4
        ∂(cond ν {x : ℝ | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)}) :=
      integral_nonneg fun x => by positivity
    have hn' : K * (⌈Real.log N⌉₊ : ℝ) ≤ K * (2 * Real.log N) :=
      mul_le_mul_of_nonneg_left hn2 hK0
    have hJ : ∫ x, (x - cutoffMean ν ((N : ℝ) ^ (1 / 2 - ε))) ^ 4
        ∂(cond ν {x : ℝ | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)}) ≤ (24 + 480 * K) * Real.log N := by
      have : K * Real.log N ≥ 0 := mul_nonneg hK0 (by linarith)
      nlinarith
    have hNi : 0 ≤ ((N : ℝ) ^ 2)⁻¹ := by positivity
    have hk4 : normK ν ε N ^ 4 ≤ 4 * ((N : ℝ) ^ 2)⁻¹ := by
      have : normK ν ε N ^ 4 = (normK ν ε N ^ 2) ^ 2 := by ring
      rw [this]
      calc (normK ν ε N ^ 2) ^ 2 ≤ (2 * (N : ℝ)⁻¹) ^ 2 :=
            pow_le_pow_left₀ (sq_nonneg _) hk2 2
        _ = 4 * ((N : ℝ) ^ 2)⁻¹ := by rw [mul_pow, inv_pow]; norm_num
    have hL : 0 ≤ Real.log N := by linarith
    rw [div_eq_mul_inv]
    calc normK ν ε N ^ 4 * ∫ x, (x - cutoffMean ν ((N : ℝ) ^ (1 / 2 - ε))) ^ 4
          ∂(cond ν {x : ℝ | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)})
        ≤ (4 * ((N : ℝ) ^ 2)⁻¹) * ((24 + 480 * K) * Real.log N) :=
          mul_le_mul hk4 hJ hnn (by positivity)
      _ = ((96 + 1920 * K) * Real.log N) * ((N : ℝ) ^ 2)⁻¹ := by ring
      _ ≤ (3000 * (1 + K + V) * Real.log N) * ((N : ℝ) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hL) hNi

/-- If `N^e a_N → 0` with `e ≥ 0`, then eventually `a_N ≤ 1/2`. -/
private lemma eventually_le_half_of_rpow_mul {a : ℕ → ℝ} {e : ℝ} (he : 0 ≤ e)
    (h : Tendsto (fun N : ℕ => (N : ℝ) ^ e * a N) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, a N ≤ 1 / 2 := by
  filter_upwards [h.eventually (eventually_le_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
    eventually_ge_atTop 1] with N hN hN1
  have : (1 : ℝ) ≤ (N : ℝ) ^ e := Real.one_le_rpow (by exact_mod_cast hN1) he
  by_cases ha : 0 ≤ a N
  · nlinarith
  · linarith [not_le.mp ha]

/-- (4.18)–(4.19): `H̃^S` satisfies the hypotheses of Theorems 3.6–3.7 with support
`N^{-3ε/4}` and a constant `C1` depending only on `(ν, ν', ε)`. -/
theorem truncLawsNorm_smallQClass {ν ν' : Measure ℝ} (hW : WignerLaws ν ν') (h14 : TailCond ν)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    ∃ C1 : ℝ, ∃ N0 : ℕ, ∀ N ≥ N0, SmallQClass C1 (3 * ε / 4) N (truncLawsNorm ν ν' ε N) := by
  have hprob := hW.prob
  have hprob' := hW.prob'
  obtain ⟨K, hK0, hK⟩ := exists_tail_const h14
  have hV0 : 0 ≤ ∫ x, x ^ 2 ∂ν' := integral_nonneg fun x => sq_nonneg x
  refine ⟨3000 * (1 + K + ∫ x, x ^ 2 ∂ν'), ?_⟩
  obtain ⟨h1, h2, -, -, -⟩ := cutoff_tail_bounds hW h14 hε0 hε
  obtain ⟨hm, -⟩ := cutoffMean_bounds hW h14 hε0 hε
  have hσ := truncCentered_sq_sub_one hW h14 hε0 hε
  have eα : ∀ᶠ N : ℕ in atTop, (ν {x : ℝ | (N : ℝ) ^ (1 / 2 - ε) < |x|}).toReal ≤ 1 / 2 :=
    eventually_le_half_of_rpow_mul (by linarith) h1
  have eα' : ∀ᶠ N : ℕ in atTop, (ν' {x : ℝ | (N : ℝ) ^ (1 / 2 - ε) < |x|}).toReal ≤ 1 / 2 :=
    eventually_le_half_of_rpow_mul (by linarith) h2
  have em : ∀ᶠ N : ℕ in atTop, |cutoffMean ν ((N : ℝ) ^ (1 / 2 - ε))| ≤ 1 / 2 :=
    eventually_le_half_of_rpow_mul (by linarith) hm
  have eσ : ∀ᶠ N : ℕ in atTop,
      |∫ x, x ^ 2 ∂(truncCentered ν ((N : ℝ) ^ (1 / 2 - ε))) - 1| ≤ 1 / 2 :=
    eventually_le_half_of_rpow_mul (by linarith) hσ
  have eq : ∀ᶠ N : ℕ in atTop, 3 ≤ (N : ℝ) ^ (ε / 4) :=
    ((tendsto_rpow_atTop (show 0 < ε / 4 by linarith)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 3
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (((((eventually_ge_atTop 3).and eα).and eα').and
    (em.and eσ)).and eq)
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨⟨⟨⟨h3, hα⟩, hα'⟩, ⟨hm1, hσ1⟩⟩, hq⟩ := hN0 N hN
  refine smallQClass_of_good hK0 hK hV0 hW.sq_int' le_rfl hε0 h3 hα hα' (by linarith) ?_ hq
  have := (abs_le.mp hσ1).1
  linarith

/-- The class of Theorem 3.6 lies in the class of Lemma 3.1. -/
theorem SmallQClass.isGenWigner {C1 φs : ℝ} {N : ℕ} {L : EntryLaws N}
    (h : SmallQClass C1 φs N L) : L.IsGenWigner (max C1 1) :=
  h.1.isGenWigner

/-- The support parameter of Lemma 3.1 for the class of Theorem 3.6 (proved here). -/
theorem SmallQClass.supportParam {C1 φs : ℝ} {N : ℕ} {L : EntryLaws N}
    (h : SmallQClass C1 φs N L) {Q : ℝ} (hQ : Q ≤ (N : ℝ) ^ φs) (c : ℝ) :
    L.SupportParam Q c ((N : ℝ) ^ φs) :=
  ⟨hQ, h.2.boundedSupport c, h.2.tailVarOff c⟩

/-! ### Compiled instances

The hypotheses hold at `ν = N(0, 1)`, `ν' = N(0, 2)` (the cut removes mass of both laws) and at
`ν` Rademacher, `ν' = N(0, 2)` (no off-diagonal entry is cut), with `ε = 1/100`. -/

private lemma tendsto_setIntegral_fourth_tail {μ : Measure ℝ}
    (h : Integrable (fun x : ℝ => x ^ 4) μ) :
    Tendsto (fun T : ℝ => ∫ x in {x : ℝ | T < |x|}, x ^ 4 ∂μ) atTop (𝓝 0) := by
  have key : Tendsto (fun T : ℝ => ∫ x, ({x : ℝ | T < |x|}).indicator (fun x => x ^ 4) x ∂μ)
      atTop (𝓝 (∫ _x, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => x ^ 4) ?_ ?_ h ?_
    · exact Eventually.of_forall fun T => h.1.indicator (measurableSet_gt_abs T)
    · refine Eventually.of_forall fun T => Eventually.of_forall fun x => ?_
      by_cases hx : T < |x|
      · rw [Set.indicator_of_mem (show x ∈ {x : ℝ | T < |x|} from hx), Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
      · rw [Set.indicator_of_notMem (show x ∉ {x : ℝ | T < |x|} from hx), norm_zero]
        positivity
    · refine Eventually.of_forall fun x => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop |x|] with T hT
      simp [Set.indicator_of_notMem (show x ∉ {x : ℝ | T < |x|} from not_lt.mpr hT)]
  simp only [integral_zero] at key
  refine key.congr fun T => ?_
  exact integral_indicator (measurableSet_gt_abs T)

/-- A law with a finite fourth moment satisfies (1.4). -/
private lemma tailCond_of_integrable_fourth {ν : Measure ℝ} [IsFiniteMeasure ν]
    (h : Integrable (fun x : ℝ => x ^ 4) ν) : TailCond ν := by
  have hg := (tendsto_setIntegral_fourth_tail h).comp
    (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
  refine squeeze_zero' (Eventually.of_forall fun s => by positivity) ?_ hg
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
  have hm : MeasurableSet {x : ℝ | s ≤ |x|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  calc s ^ 4 * (ν {x : ℝ | s ≤ |x|}).toReal = ∫ _x in {x : ℝ | s ≤ |x|}, s ^ 4 ∂ν := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def]; ring
    _ ≤ ∫ x in {x : ℝ | s ≤ |x|}, x ^ 4 ∂ν := by
        refine setIntegral_mono_on (integrableOn_const (by simp [measure_ne_top])) h.integrableOn
          hm fun x hx => ?_
        have hx' : s ≤ |x| := hx
        have : s ^ 4 ≤ |x| ^ 4 := pow_le_pow_left₀ (by linarith) hx' 4
        have e : |x| ^ 4 = x ^ 4 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
        linarith
    _ ≤ ∫ x in {x : ℝ | s + -1 < |x|}, x ^ 4 ∂ν := by
        refine setIntegral_mono_set h.integrableOn (Eventually.of_forall fun x => ?_)
          (Eventually.of_forall fun x hx => ?_)
        · change 0 ≤ x ^ 4
          positivity
        · change s + -1 < |x|
          have : s ≤ |x| := hx
          linarith

private lemma integrable_fourth_gaussian_one :
    Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 1) := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) 4).integrable_norm_pow (by norm_num)
  refine h.congr (Eventually.of_forall fun x => ?_)
  change ‖x‖ ^ (4 : ℕ) = x ^ 4
  rw [Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]

private lemma tailCond_gaussian_one : TailCond (gaussianReal 0 1) :=
  tailCond_of_integrable_fourth integrable_fourth_gaussian_one

/-- A centred Gaussian charges `{|x| > T}`. -/
private lemma gaussianReal_tail_ne_zero {v : NNReal} (hv : v ≠ 0) (T : ℝ) :
    gaussianReal 0 v {x : ℝ | T < |x|} ≠ 0 := by
  intro h
  have h0 := gaussianReal_absolutelyContinuous' 0 hv h
  have hsub : Set.Ioi T ⊆ {x : ℝ | T < |x|} := fun x hx => lt_of_lt_of_le hx (le_abs_self x)
  have := measure_mono_null hsub h0
  simp at this

private lemma cutoffMean_eq_zero_of_null {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun x : ℝ => x) ν) (hmean : ∫ x, x ∂ν = 0) {T : ℝ}
    (h0 : ν {x : ℝ | T < |x|} = 0) : cutoffMean ν T = 0 := by
  have hsplit := integral_add_compl (measurableSet_gt_abs T) hint
  rw [← cut_eq_compl, hmean, setIntegral_measure_zero _ h0] at hsplit
  unfold cutoffMean
  rw [integral_cond_cut (fun y => y)]
  have : ∫ x in {x : ℝ | |x| ≤ T}, x ∂ν = 0 := by linarith
  rw [this, mul_zero]

/-- (4.18) for `ν = N(0, 1)` and `ε = 1/100`. -/
example := truncCentered_sq_sub_one goe_wignerLaws tailCond_gaussian_one
  (ε := 1 / 100) (by norm_num) (by norm_num)

/-- (4.18) for `ν` Rademacher and `ε = 1/100`. -/
example := truncCentered_sq_sub_one rademacher_wignerLaws rademacher_tailCond
  (ε := 1 / 100) (by norm_num) (by norm_num)

/-- At `N = 1000` no Rademacher entry is cut, so the variance in (4.18) is exactly `1`. -/
example : ∫ x, x ^ 2 ∂(truncCentered rademacher
    (((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ)))) = 1 := by
  have hW := rademacher_wignerLaws
  have := hW.prob
  have h0 : rademacher {x : ℝ | ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ)) < |x|} = 0 := by
    have hT' : (1 : ℝ) ≤ (1000 : ℝ) ^ ((2 : ℝ)⁻¹ - (100 : ℝ)⁻¹) :=
      Real.one_le_rpow (by norm_num) (by norm_num)
    simp only [rademacher, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply,
      smul_eq_mul]
    simp [hT']
  have hxint : Integrable (fun x : ℝ => x) rademacher :=
    ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hW.sq_int).integrable one_le_two
  rw [sq_truncCentered_eq hW.sq_int hW.var (by rw [h0]; norm_num),
    cutoffMean_eq_zero_of_null hxint hW.mean h0, setIntegral_measure_zero _ h0, h0]
  norm_num

/-- At `N = 1000` the cut removes mass from `N(0, 1)`: the instance is not the uncut case. -/
example : gaussianReal 0 1 {x : ℝ | ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ)) < |x|} ≠ 0 :=
  gaussianReal_tail_ne_zero one_ne_zero _

/-- At `N = 1000` the cut removes mass from `N(0, 2)`, the diagonal law. -/
example : gaussianReal 0 2 {x : ℝ | ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ)) < |x|} ≠ 0 :=
  gaussianReal_tail_ne_zero (by norm_num) _

/-- `H̃^S` for `ν = N(0, 1)`, `ν' = N(0, 2)`, `ε = 1/100` is in the class of Theorem 3.6, and
so in the class of Lemma 3.1 with an admissible support parameter, for some `N ≥ 1000`. -/
example : ∃ C1 : ℝ, ∃ N : ℕ, 1000 ≤ N ∧
    SmallQClass C1 (3 * (1 / 100) / 4) N (truncLawsNorm (gaussianReal 0 1) (gaussianReal 0 2)
      (1 / 100) N) ∧
    (truncLawsNorm (gaussianReal 0 1) (gaussianReal 0 2) (1 / 100) N).IsGenWigner (max C1 1) ∧
    (truncLawsNorm (gaussianReal 0 1) (gaussianReal 0 2) (1 / 100) N).SupportParam 1 (1 / 2)
      ((N : ℝ) ^ (3 * (1 / 100 : ℝ) / 4)) := by
  obtain ⟨C1, N0, h⟩ := truncLawsNorm_smallQClass goe_wignerLaws tailCond_gaussian_one
    (ε := 1 / 100) (by norm_num) (by norm_num)
  have hN : max N0 1000 ≥ N0 := le_max_left _ _
  refine ⟨C1, max N0 1000, le_max_right _ _, h _ hN, (h _ hN).isGenWigner,
    (h _ hN).supportParam ?_ _⟩
  exact Real.one_le_rpow
    (by exact_mod_cast (le_trans (by norm_num) (le_max_right N0 1000))) (by norm_num)

/-- `H̃^S` for `ν` Rademacher, `ν' = N(0, 2)`, `ε = 1/100` is in the class of Theorem 3.6 for
all large `N`. -/
example : ∃ C1 : ℝ, ∃ N0 : ℕ, ∀ N ≥ N0, SmallQClass C1 (3 * (1 / 100) / 4) N
    (truncLawsNorm rademacher (gaussianReal 0 2) (1 / 100) N) :=
  truncLawsNorm_smallQClass rademacher_wignerLaws rademacher_tailCond (by norm_num) (by norm_num)

/-- The same instance, in the class of Lemma 3.1 with an admissible support parameter, for some
`N ≥ 1000`. -/
example : ∃ C1 : ℝ, ∃ N : ℕ, 1000 ≤ N ∧
    SmallQClass C1 (3 * (1 / 100) / 4) N (truncLawsNorm rademacher (gaussianReal 0 2)
      (1 / 100) N) ∧
    (truncLawsNorm rademacher (gaussianReal 0 2) (1 / 100) N).IsGenWigner (max C1 1) ∧
    (truncLawsNorm rademacher (gaussianReal 0 2) (1 / 100) N).SupportParam 1 (1 / 2)
      ((N : ℝ) ^ (3 * (1 / 100 : ℝ) / 4)) := by
  obtain ⟨C1, N0, h⟩ := truncLawsNorm_smallQClass rademacher_wignerLaws rademacher_tailCond
    (ε := 1 / 100) (by norm_num) (by norm_num)
  have hN : max N0 1000 ≥ N0 := le_max_left _ _
  refine ⟨C1, max N0 1000, le_max_right _ _, h _ hN, (h _ hN).isGenWigner,
    (h _ hN).supportParam ?_ _⟩
  exact Real.one_le_rpow
    (by exact_mod_cast (le_trans (by norm_num) (le_max_right N0 1000))) (by norm_num)

#print axioms truncCentered_sq_sub_one
#print axioms truncLawsNorm_smallQClass
#print axioms SmallQClass.isGenWigner
#print axioms SmallQClass.supportParam

end WEdgeNS
