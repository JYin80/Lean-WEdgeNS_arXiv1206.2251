import WEdgeNS.Probability.ProductSpace

/-!
# Truncation to almost surely bounded entries
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-! ### The coordinatewise truncation map -/

/-- The tail `{|x| > q⁻¹}` of Definition 2.4. -/
private def tailSet (q : ℝ) : Set ℝ := {x | q⁻¹ < |x|}

/-- Truncation at level `q⁻¹`: `x` if `|x| ≤ q⁻¹`, and `0` otherwise. -/
private def trunc (q x : ℝ) : ℝ := (tailSet q)ᶜ.indicator id x

/-- Mean of the truncated entry. -/
private def truncMean (q : ℝ) (μ : Measure ℝ) : ℝ := ∫ x, trunc q x ∂μ

/-- Variance of the truncated entry. -/
private def truncVar (q : ℝ) (μ : Measure ℝ) : ℝ := ∫ x, (trunc q x - truncMean q μ) ^ 2 ∂μ

/-- Diagonal entries: truncate and recentre. -/
private def diagMap (q : ℝ) (μ : Measure ℝ) (x : ℝ) : ℝ := trunc q x - truncMean q μ

/-- Off-diagonal entries: truncate, recentre and rescale to variance `N⁻¹`. -/
private def offMap (N : ℕ) (q : ℝ) (μ : Measure ℝ) (x : ℝ) : ℝ :=
  (trunc q x - truncMean q μ) / Real.sqrt (N * truncVar q μ)

/-- The coordinatewise truncation map on the entries. -/
private def boundedMap {N : ℕ} (q : ℝ) (L : EntryLaws N) : Entries N → Entries N :=
  fun ω => (fun i => diagMap q (L.diag i) (ω.1 i), fun p => offMap N q (L.off p) (ω.2 p))

/-- The entry laws of the truncated entries. -/
private def boundedLaws {N : ℕ} (q : ℝ) (L : EntryLaws N) : EntryLaws N :=
  ⟨fun i => (L.diag i).map (diagMap q (L.diag i)),
   fun p => (L.off p).map (offMap N q (L.off p))⟩

/-! ### Elementary properties -/

private lemma measurableSet_tailSet (q : ℝ) : MeasurableSet (tailSet q) :=
  measurableSet_lt measurable_const continuous_abs.measurable

private lemma measurable_trunc (q : ℝ) : Measurable (trunc q) :=
  measurable_id.indicator (measurableSet_tailSet q).compl

private lemma measurable_diagMap (q : ℝ) (μ : Measure ℝ) : Measurable (diagMap q μ) :=
  (measurable_trunc q).sub_const _

private lemma measurable_offMap (N : ℕ) (q : ℝ) (μ : Measure ℝ) :
    Measurable (offMap N q μ) :=
  ((measurable_trunc q).sub_const _).div_const _

private lemma trunc_of_le {q x : ℝ} (hx : |x| ≤ q⁻¹) : trunc q x = x := by
  have : x ∈ (tailSet q)ᶜ := by simpa [tailSet] using hx
  simp [trunc, this]

private lemma abs_trunc_le {q : ℝ} (hq : 0 ≤ q) (x : ℝ) : |trunc q x| ≤ q⁻¹ := by
  by_cases h : x ∈ (tailSet q)ᶜ
  · have hx : |x| ≤ q⁻¹ := by simpa [tailSet] using h
    simpa [trunc, h] using hx
  · simp [trunc, h, inv_nonneg.mpr hq]

private lemma trunc_sq (q x : ℝ) :
    trunc q x ^ 2 = (tailSet q)ᶜ.indicator (fun y => y ^ 2) x := by
  by_cases h : x ∈ (tailSet q)ᶜ <;> simp [trunc, h]

private lemma integrable_of_sq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hx2 : Integrable (fun x : ℝ => x ^ 2) μ) : Integrable (fun x : ℝ => x) μ := by
  refine Integrable.mono' (hx2.add (integrable_const 1)) aestronglyMeasurable_id
    (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs]
  nlinarith [abs_nonneg x, sq_abs x]

private lemma integrable_trunc {μ : Measure ℝ} {q : ℝ} (hint : Integrable (fun x : ℝ => x) μ) :
    Integrable (trunc q) μ :=
  hint.indicator (measurableSet_tailSet q).compl

private lemma integrable_trunc_sq {μ : Measure ℝ} {q : ℝ}
    (hx2 : Integrable (fun x : ℝ => x ^ 2) μ) : Integrable (fun x => trunc q x ^ 2) μ := by
  simp_rw [trunc_sq]
  exact hx2.indicator (measurableSet_tailSet q).compl

private lemma truncMean_eq {μ : Measure ℝ} {q : ℝ} (hint : Integrable (fun x : ℝ => x) μ)
    (hmean : ∫ x, x ∂μ = 0) : truncMean q μ = -∫ x in tailSet q, x ∂μ := by
  have h1 : truncMean q μ = ∫ x in (tailSet q)ᶜ, x ∂μ := by
    unfold truncMean trunc
    rw [integral_indicator (measurableSet_tailSet q).compl]
    rfl
  have h2 := integral_add_compl (measurableSet_tailSet q) hint
  linarith

private lemma integral_trunc_sq {μ : Measure ℝ} {q : ℝ}
    (hx2 : Integrable (fun x : ℝ => x ^ 2) μ) :
    ∫ x, trunc q x ^ 2 ∂μ = ∫ x, x ^ 2 ∂μ - ∫ x in tailSet q, x ^ 2 ∂μ := by
  simp_rw [trunc_sq]
  rw [integral_indicator (measurableSet_tailSet q).compl]
  have h2 := integral_add_compl (measurableSet_tailSet q) hx2
  linarith

private lemma abs_truncMean_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {q : ℝ} (hq : 0 ≤ q)
    (hint : Integrable (fun x : ℝ => x) μ) : |truncMean q μ| ≤ q⁻¹ := by
  unfold truncMean
  calc |∫ x, trunc q x ∂μ| ≤ ∫ x, |trunc q x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _x, q⁻¹ ∂μ :=
        integral_mono (integrable_trunc hint).abs (integrable_const _) (abs_trunc_le hq)
    _ = q⁻¹ := by simp

/-- `|∫_s x| ≤ (K ∫_s x² + μ(s) / K) / 2` for every `K > 0`. -/
private lemma abs_setIntegral_le {μ : Measure ℝ} [IsFiniteMeasure μ] {s : Set ℝ}
    (hx2 : Integrable (fun x : ℝ => x ^ 2) μ) (hint : Integrable (fun x : ℝ => x) μ)
    {K : ℝ} (hK : 0 < K) :
    |∫ x in s, x ∂μ| ≤ (K * ∫ x in s, x ^ 2 ∂μ + μ.real s / K) / 2 := by
  have hpt : ∀ x : ℝ, |x| ≤ (K * x ^ 2 + 1 / K) / 2 := by
    intro x
    have e : (K * x ^ 2 + 1 / K) / 2 - |x| = (K * |x| - 1) ^ 2 / (2 * K) := by
      rw [← sq_abs x]; field_simp; ring
    have : 0 ≤ (K * |x| - 1) ^ 2 / (2 * K) := by positivity
    linarith
  have hg : Integrable (fun x : ℝ => (K * x ^ 2 + 1 / K) / 2) μ :=
    ((hx2.const_mul K).add (integrable_const _)).div_const 2
  calc |∫ x in s, x ∂μ| ≤ ∫ x in s, |x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x in s, (K * x ^ 2 + 1 / K) / 2 ∂μ :=
        setIntegral_mono hint.abs.integrableOn hg.integrableOn hpt
    _ = (K * ∫ x in s, x ^ 2 ∂μ + μ.real s / K) / 2 := by
        rw [integral_div, integral_add (hx2.const_mul K).integrableOn (integrable_const _),
          integral_const_mul, setIntegral_const, smul_eq_mul]
        ring

/-- `∫ (g - ∫ g)² = ∫ g² - (∫ g)²` for a probability measure. -/
private lemma integral_sub_mean_sq {μ : Measure ℝ} [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    (hg : Integrable g μ) (hg2 : Integrable (fun x => g x ^ 2) μ) :
    ∫ x, (g x - ∫ y, g y ∂μ) ^ 2 ∂μ = ∫ x, g x ^ 2 ∂μ - (∫ y, g y ∂μ) ^ 2 := by
  set m := ∫ y, g y ∂μ
  have e : ∀ x, (g x - m) ^ 2 = (g x ^ 2 - 2 * m * g x) + m ^ 2 := fun x => by ring
  simp_rw [e]
  have h1 : Integrable (fun x => g x ^ 2 - 2 * m * g x) μ := hg2.sub (hg.const_mul _)
  rw [integral_add h1 (integrable_const _),
    integral_sub hg2 (hg.const_mul _), integral_const_mul, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

private lemma integral_map_eq {μ : Measure ℝ} {g : ℝ → ℝ} (hg : Measurable g) {f : ℝ → ℝ}
    (hf : Continuous f) : ∫ x, f x ∂(μ.map g) = ∫ x, f (g x) ∂μ :=
  integral_map hg.aemeasurable hf.aestronglyMeasurable

private lemma integrable_sq_map {μ : Measure ℝ} [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    (hg : Measurable g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    Integrable (fun x : ℝ => x ^ 2) (μ.map g) := by
  rw [integrable_map_measure (continuous_pow 2).aestronglyMeasurable hg.aemeasurable]
  refine Integrable.of_bound ((hg.pow_const 2).aestronglyMeasurable) (B ^ 2)
    (ae_of_all _ fun x => ?_)
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2

private lemma map_tail_eq_zero {μ : Measure ℝ} {g : ℝ → ℝ} (hg : Measurable g) {q : ℝ}
    (hB : ∀ x, |g x| ≤ 2 * q⁻¹) : (μ.map g) {x | (q / 2)⁻¹ < |x|} = 0 := by
  rw [Measure.map_apply hg (measurableSet_lt measurable_const continuous_abs.measurable)]
  have : g ⁻¹' {x | (q / 2)⁻¹ < |x|} = ∅ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt,
      inv_div]
    have := hB x
    rw [div_eq_mul_inv]
    exact this
  rw [this, measure_empty]

/-! ### One off-diagonal entry -/

/-- An off-diagonal law with (2.1), tail mass and tail variance at most `τ`: the truncated,
recentred and rescaled entry has mean `0`, variance exactly `N⁻¹`, modulus at most `2 q⁻¹`,
and moves every `|x| ≤ q⁻¹` by at most `κ`. -/
private lemma off_facts {N : ℕ} {q τ κ : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hx2 : Integrable (fun x : ℝ => x ^ 2) μ) (hmean : ∫ x, x ∂μ = 0)
    (hvar : ∫ x, x ^ 2 ∂μ = (N : ℝ)⁻¹) (hA : μ (tailSet q) ≤ ENNReal.ofReal τ)
    (hAv : ∫ x in tailSet q, x ^ 2 ∂μ ≤ τ) (hq : 1 ≤ q) (hN : 1 ≤ (N : ℝ)) (hτ : 0 ≤ τ)
    (h6 : 6 * N * τ ≤ 1) (hκ : (4 * N + 2) * τ ≤ κ) :
    ∫ x, offMap N q μ x ∂μ = 0 ∧ ∫ x, offMap N q μ x ^ 2 ∂μ = (N : ℝ)⁻¹ ∧
      (∀ x, |offMap N q μ x| ≤ 2 * q⁻¹) ∧ ∀ x, |x| ≤ q⁻¹ → |x - offMap N q μ x| ≤ κ := by
  set n : ℝ := (N : ℝ) with hn_def
  have hn0 : 0 < n := by linarith
  have hnn : n * n⁻¹ = 1 := mul_inv_cancel₀ hn0.ne'
  have hint := integrable_of_sq hx2
  have hs := measurableSet_tailSet q
  have hq0 : 0 ≤ q := by linarith
  have hqi : q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
  have hqi0 : 0 ≤ q⁻¹ := inv_nonneg.mpr hq0
  have hnτ : 0 ≤ n * τ := mul_nonneg hn0.le hτ
  have hτ1 : τ ≤ 1 := by nlinarith
  set m := truncMean q μ with hm_def
  have hmabs : |m| ≤ τ := by
    rw [hm_def, truncMean_eq hint hmean, abs_neg]
    have h1 := abs_setIntegral_le (s := tailSet q) hx2 hint one_pos
    have h2 : μ.real (tailSet q) ≤ τ := ENNReal.toReal_le_of_le_ofReal hτ hA
    simp only [one_mul, div_one] at h1
    linarith
  have hAv0 : 0 ≤ ∫ x in tailSet q, x ^ 2 ∂μ := setIntegral_nonneg hs fun x _ => sq_nonneg x
  have hE2 : ∫ x, trunc q x ^ 2 ∂μ = n⁻¹ - ∫ x in tailSet q, x ^ 2 ∂μ := by
    rw [integral_trunc_sq hx2, hvar]
  have hV : truncVar q μ = ∫ x, trunc q x ^ 2 ∂μ - m ^ 2 :=
    integral_sub_mean_sq (integrable_trunc hint) (integrable_trunc_sq hx2)
  set V := truncVar q μ with hV_def
  have hm2 : m ^ 2 ≤ τ := by
    rw [← sq_abs]
    calc |m| ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hmabs 2
      _ ≤ τ := by nlinarith
  have hVle : V ≤ n⁻¹ := by rw [hV, hE2]; nlinarith [sq_nonneg m]
  have hVge : n⁻¹ - 2 * τ ≤ V := by rw [hV, hE2]; linarith
  have hnV1 : n * V ≤ 1 := hnn ▸ mul_le_mul_of_nonneg_left hVle hn0.le
  have hnV2 : 1 - 2 * (n * τ) ≤ n * V := by
    have := mul_le_mul_of_nonneg_left hVge hn0.le
    rw [mul_sub, hnn] at this
    linarith
  have hnV0 : 0 < n * V := by linarith
  set σ := Real.sqrt (n * V) with hσ_def
  have hσsq : σ ^ 2 = n * V := Real.sq_sqrt hnV0.le
  have hσ0 : 0 < σ := Real.sqrt_pos.mpr hnV0
  have hσ1 : σ ≤ 1 := Real.sqrt_le_one.mpr hnV1
  have hσge : n * V ≤ σ := by nlinarith
  have hσlow : 1 - 2 * (n * τ) ≤ σ := hnV2.trans hσge
  have hoff : ∀ x, offMap N q μ x = (trunc q x - m) / σ := fun x => rfl
  -- `q⁻¹ ≥ n⁻¹ - τ`
  have hE2q : ∫ x, trunc q x ^ 2 ∂μ ≤ q⁻¹ := by
    calc ∫ x, trunc q x ^ 2 ∂μ ≤ ∫ _x, q⁻¹ ^ 2 ∂μ := by
          refine integral_mono (integrable_trunc_sq hx2) (integrable_const _) fun x => ?_
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_trunc_le hq0 x) 2
      _ = q⁻¹ ^ 2 := by simp
      _ ≤ q⁻¹ := by nlinarith
  have hqlow : 1 - n * τ ≤ n * q⁻¹ := by
    have h : n⁻¹ - τ ≤ q⁻¹ := by linarith
    have := mul_le_mul_of_nonneg_left h hn0.le
    rw [mul_sub, hnn] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp_rw [hoff]
    rw [integral_div, integral_sub (integrable_trunc hint) (integrable_const _), integral_const]
    simp [hm_def, truncMean]
  · have e : ∀ x, offMap N q μ x ^ 2 = (trunc q x - m) ^ 2 / σ ^ 2 := fun x => by
      rw [hoff, div_pow]
    have hVint : ∫ x, (trunc q x - m) ^ 2 ∂μ = V := rfl
    simp_rw [e]
    have hVne : V ≠ 0 := fun h => by rw [h, mul_zero] at hnV0; exact lt_irrefl _ hnV0
    rw [integral_div, hVint, hσsq]
    field_simp [hVne]
  · intro x
    rw [hoff, abs_div, abs_of_pos hσ0, div_le_iff₀ hσ0]
    have h1 : |trunc q x - m| ≤ q⁻¹ + τ :=
      (abs_sub _ _).trans (add_le_add (abs_trunc_le hq0 x) hmabs)
    have h2a : τ ≤ q⁻¹ / 3 := by
      have h : n * τ ≤ n * (q⁻¹ / 3) := by linarith
      exact le_of_mul_le_mul_left h hn0
    have h2b : q⁻¹ / 3 ≤ q⁻¹ * (1 - 4 * (n * τ)) := by
      have := mul_nonneg hqi0 (by linarith : (0 : ℝ) ≤ 2 / 3 - 4 * (n * τ))
      linarith
    have h3 : 2 * q⁻¹ * (1 - 2 * (n * τ)) ≤ 2 * q⁻¹ * σ :=
      mul_le_mul_of_nonneg_left hσlow (by positivity)
    linarith
  · intro x hx
    rw [hoff, trunc_of_le hx]
    have e : x - (x - m) / σ = (x * (σ - 1) + m) / σ := by field_simp; ring
    rw [e, abs_div, abs_of_pos hσ0, div_le_iff₀ hσ0]
    have h1 : |x * (σ - 1) + m| ≤ |x| * (1 - σ) + τ := by
      calc |x * (σ - 1) + m| ≤ |x * (σ - 1)| + |m| := abs_add_le _ _
        _ = |x| * (1 - σ) + |m| := by rw [abs_mul, abs_of_nonpos (by linarith : σ - 1 ≤ 0)]; ring
        _ ≤ |x| * (1 - σ) + τ := by linarith
    have h2 : |x| * (1 - σ) ≤ 1 - σ := by
      have hx1 : |x| ≤ 1 := hx.trans hqi
      have := mul_le_mul_of_nonneg_right hx1 (by linarith : (0 : ℝ) ≤ 1 - σ)
      linarith
    have hκ0 : 0 ≤ κ := le_trans (by positivity) hκ
    have h3 : κ * (1 / 2) ≤ κ * σ := mul_le_mul_of_nonneg_left (by linarith) hκ0
    linarith

/-! ### One diagonal entry -/

/-- A diagonal law with (2.1) and tail mass at most `κ⁴`: the truncated and recentred entry has
mean `0`, variance within `max C0 1 · N⁻¹` of `N⁻¹`, modulus at most `2 q⁻¹`, and moves every
`|x| ≤ q⁻¹` by at most `κ`. -/
private lemma diag_facts {N : ℕ} {q C0 κ : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hx2 : Integrable (fun x : ℝ => x ^ 2) μ) (hmean : ∫ x, x ∂μ = 0)
    (hvar : |∫ x, x ^ 2 ∂μ - (N : ℝ)⁻¹| ≤ C0 * (N : ℝ)⁻¹)
    (hA : μ (tailSet q) ≤ ENNReal.ofReal (κ ^ 4)) (hq : 1 ≤ q) (hN : 1 ≤ (N : ℝ))
    (hC0 : 0 ≤ C0) (hκ0 : 0 < κ) (hκ : (2 + C0) * κ ≤ 2) :
    ∫ x, diagMap q μ x ∂μ = 0 ∧
      |∫ x, diagMap q μ x ^ 2 ∂μ - (N : ℝ)⁻¹| ≤ max C0 1 * (N : ℝ)⁻¹ ∧
      (∀ x, |diagMap q μ x| ≤ 2 * q⁻¹) ∧ ∀ x, |x| ≤ q⁻¹ → |x - diagMap q μ x| ≤ κ := by
  set n : ℝ := (N : ℝ) with hn_def
  have hn0 : 0 < n := by linarith
  have hni : n⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN
  have hni0 : 0 ≤ n⁻¹ := inv_nonneg.mpr hn0.le
  have hint := integrable_of_sq hx2
  have hs := measurableSet_tailSet q
  have hq0 : 0 ≤ q := by linarith
  set m := truncMean q μ with hm_def
  have hB : ∫ x, x ^ 2 ∂μ ≤ (1 + C0) * n⁻¹ := by
    have := (abs_le.mp hvar).2; linarith
  have hAv : ∫ x in tailSet q, x ^ 2 ∂μ ≤ ∫ x, x ^ 2 ∂μ :=
    setIntegral_le_integral hx2 (ae_of_all _ fun x => sq_nonneg x)
  have hAv0 : 0 ≤ ∫ x in tailSet q, x ^ 2 ∂μ := setIntegral_nonneg hs fun x _ => sq_nonneg x
  have hmabs : |m| ≤ κ := by
    rw [hm_def, truncMean_eq hint hmean, abs_neg]
    have hK : 0 < κ ^ 2 := by positivity
    have h1 := abs_setIntegral_le (s := tailSet q) hx2 hint hK
    have h2 : μ.real (tailSet q) ≤ κ ^ 4 := ENNReal.toReal_le_of_le_ofReal (by positivity) hA
    have h3 : μ.real (tailSet q) / κ ^ 2 ≤ κ ^ 2 := by
      rw [div_le_iff₀ hK]; nlinarith
    have h4 : ∫ x in tailSet q, x ^ 2 ∂μ ≤ 1 + C0 := by nlinarith
    have h5 : κ ^ 2 * ∫ x in tailSet q, x ^ 2 ∂μ ≤ κ ^ 2 * (1 + C0) :=
      mul_le_mul_of_nonneg_left h4 hK.le
    nlinarith
  have hmq : |m| ≤ q⁻¹ := abs_truncMean_le hq0 hint
  have hd : ∀ x, diagMap q μ x = trunc q x - m := fun x => rfl
  have hV : ∫ x, diagMap q μ x ^ 2 ∂μ = ∫ x, trunc q x ^ 2 ∂μ - m ^ 2 :=
    integral_sub_mean_sq (integrable_trunc hint) (integrable_trunc_sq hx2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp_rw [hd]
    rw [integral_sub (integrable_trunc hint) (integrable_const _), integral_const]
    simp [hm_def, truncMean]
  · have hV0 : 0 ≤ ∫ x, diagMap q μ x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have hVle : ∫ x, diagMap q μ x ^ 2 ∂μ ≤ (1 + C0) * n⁻¹ := by
      rw [hV, integral_trunc_sq hx2]; nlinarith [sq_nonneg m]
    have hmax1 : C0 ≤ max C0 1 := le_max_left _ _
    have hmax2 : 1 ≤ max C0 1 := le_max_right _ _
    rw [abs_le]
    constructor <;> nlinarith
  · intro x
    rw [hd]
    calc |trunc q x - m| ≤ |trunc q x| + |m| := abs_sub _ _
      _ ≤ q⁻¹ + q⁻¹ := add_le_add (abs_trunc_le hq0 x) hmq
      _ = 2 * q⁻¹ := by ring
  · intro x hx
    rw [hd, trunc_of_le hx, sub_sub_cancel]
    exact hmabs

/-! ### Measures of coordinate events -/

private lemma law_coord_diag {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) (i : Fin N) {A : Set ℝ}
    (hA : MeasurableSet A) : L.law {ω | ω.1 i ∈ A} = L.diag i A := by
  have := hL.diag
  have := hL.off
  have e : {ω : Entries N | ω.1 i ∈ A} = (Function.eval i ⁻¹' A) ×ˢ Set.univ := by
    ext ω; simp
  rw [e, EntryLaws.law, Measure.prod_prod, measure_univ, mul_one,
    (measurePreserving_eval L.diag i).measure_preimage hA.nullMeasurableSet]

private lemma law_coord_off {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) (p : OffDiag N)
    {A : Set ℝ} (hA : MeasurableSet A) : L.law {ω | ω.2 p ∈ A} = L.off p A := by
  have := hL.diag
  have := hL.off
  have e : {ω : Entries N | ω.2 p ∈ A} = Set.univ ×ˢ (Function.eval p ⁻¹' A) := by
    ext ω; simp
  rw [e, EntryLaws.law, Measure.prod_prod, measure_univ, one_mul,
    (measurePreserving_eval L.off p).measure_preimage hA.nullMeasurableSet]

/-! ### The truncation theorem -/

/-- `N exp(-N^c/4) → 0`. -/
private lemma tendsto_mul_exp_neg_rpow {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.exp (-(N : ℝ) ^ c / 4)) atTop (𝓝 0) := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero c⁻¹ (1 / 4) (by norm_num)
  have h2 : Tendsto (fun N : ℕ => (N : ℝ) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  refine (h1.comp h2).congr fun N => ?_
  simp only [Function.comp_apply]
  rw [Real.rpow_rpow_inv (Nat.cast_nonneg N) hc.ne']
  congr 2
  ring

/-- Truncation: reduction to almost surely bounded entries with exact
off-diagonal variance `N⁻¹`, through one measurable coordinatewise map. -/
theorem exists_truncation {C0 c : ℝ} (hC0 : 0 ≤ C0) (hc : 0 < c) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (L : EntryLaws N) (q : ℝ), L.IsGenWigner C0 →
      L.SupportParam 1 c q → ∃ (L' : EntryLaws N) (T : Entries N → Entries N),
        Measurable T ∧ L.law.map T = L'.law ∧ L'.IsGenWigner (max C0 1) ∧
        L'.BoundedSupportAS (q / 2) ∧
        L.law {ω | ∃ i j, Real.exp (-(N : ℝ) ^ c / 4) <
          |symOfEntries ω i j - symOfEntries (T ω) i j|} ≤
          ENNReal.ofReal (2 * (N : ℝ) ^ 2 * Real.exp (-(N : ℝ) ^ c)) := by
  have hpos : (0 : ℝ) < 1 / (12 + C0) := by positivity
  obtain ⟨N1, hN1⟩ := eventually_atTop.1
    ((tendsto_mul_exp_neg_rpow hc).eventually (gt_mem_nhds hpos))
  refine ⟨max N1 1, fun N hN L q hG hS => ?_⟩
  have hNN1 : N1 ≤ N := le_of_max_le_left hN
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
  set κ := Real.exp (-(N : ℝ) ^ c / 4) with hκ_def
  have hκ0 : 0 < κ := Real.exp_pos _
  have hκ1 : κ ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ (N : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg N) c
    linarith)
  have hτ : Real.exp (-(N : ℝ) ^ c) = κ ^ 4 := by
    rw [hκ_def, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hmaster : (12 + C0) * ((N : ℝ) * κ) < 1 := by
    have := hN1 N hNN1
    rw [lt_div_iff₀ (by positivity)] at this
    linarith
  have hNκ : (10 * (N : ℝ) + 2 + C0) * κ ≤ 1 := by
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hN1') (by linarith : (0 : ℝ) ≤ 2 + C0))
      hκ0.le]
  have hκ4 : κ ^ 4 ≤ κ ^ 2 := pow_le_pow_of_le_one hκ0.le hκ1 (by norm_num)
  have hκ2 : κ ^ 2 ≤ κ := pow_le_of_le_one hκ0.le hκ1 (by norm_num)
  have h6 : 6 * (N : ℝ) * κ ^ 4 ≤ 1 := by nlinarith
  have hoffκ : (4 * (N : ℝ) + 2) * κ ^ 4 ≤ κ := by nlinarith
  have hdiagκ : (2 + C0) * κ ≤ 2 := by nlinarith
  obtain ⟨hq1, hBS, hTV⟩ := hS
  unfold EntryLaws.BoundedSupport at hBS
  unfold EntryLaws.TailVarOff at hTV
  rw [hτ] at hBS hTV
  have hP := hG.isProb
  have hPd := hP.diag
  have hPo := hP.off
  have hq0 : 0 ≤ q := by linarith
  -- the entry-wise facts
  have hoff : ∀ p, _ := fun p => off_facts (N := N) (q := q) (τ := κ ^ 4) (κ := κ)
    (hG.sq_int_off p) (hG.mean_off p) (hG.var_off p) (hBS.2 p) (hTV p) hq1 hN1'
    (by positivity) h6 hoffκ
  have hdiag : ∀ i, _ := fun i => diag_facts (N := N) (q := q) (C0 := C0) (κ := κ)
    (hG.sq_int_diag i) (hG.mean_diag i) (hG.var_diag i) (hBS.1 i) hq1 hN1' hC0 hκ0 hdiagκ
  have hmd : ∀ i, Measurable (diagMap q (L.diag i)) := fun i => measurable_diagMap q _
  have hmo : ∀ p, Measurable (offMap N q (L.off p)) := fun p => measurable_offMap N q _
  have hTd : Measurable (fun (f : Fin N → ℝ) i => diagMap q (L.diag i) (f i)) :=
    Measurable.of_eval fun i => (hmd i).comp (measurable_pi_apply i)
  have hTo : Measurable (fun (f : OffDiag N → ℝ) p => offMap N q (L.off p) (f p)) :=
    Measurable.of_eval fun p => (hmo p).comp (measurable_pi_apply p)
  refine ⟨boundedLaws q L, boundedMap q L, hTd.prodMap hTo, ?_, ?_, ?_, ?_⟩
  · -- the law of the truncated entries
    change ((Measure.pi L.diag).prod (Measure.pi L.off)).map
      (Prod.map (fun (f : Fin N → ℝ) i => diagMap q (L.diag i) (f i))
        (fun (f : OffDiag N → ℝ) p => offMap N q (L.off p) (f p))) = _
    rw [← Measure.map_prod_map _ _ hTd hTo,
      Measure.pi_map_pi (fun i => (hmd i).aemeasurable),
      Measure.pi_map_pi (fun p => (hmo p).aemeasurable)]
    rfl
  · -- the truncated laws are generalized Wigner laws
    refine ⟨⟨fun i => ?_, fun p => ?_⟩, fun i => ?_, fun p => ?_, fun i => ?_, fun p => ?_,
      fun p => ?_, fun i => ?_⟩
    · change IsProbabilityMeasure ((L.diag i).map _); infer_instance
    · change IsProbabilityMeasure ((L.off p).map _); infer_instance
    · exact integrable_sq_map (hmd i) (hdiag i).2.2.1
    · exact integrable_sq_map (hmo p) (hoff p).2.2.1
    · change ∫ x, x ∂((L.diag i).map _) = 0
      rw [integral_map_eq (hmd i) (f := fun x => x) continuous_id]; exact (hdiag i).1
    · change ∫ x, x ∂((L.off p).map _) = 0
      rw [integral_map_eq (hmo p) (f := fun x => x) continuous_id]; exact (hoff p).1
    · change ∫ x, x ^ 2 ∂((L.off p).map _) = _
      rw [integral_map_eq (hmo p) (continuous_pow 2)]; exact (hoff p).2.1
    · change |∫ x, x ^ 2 ∂((L.diag i).map _) - _| ≤ _
      rw [integral_map_eq (hmd i) (continuous_pow 2)]; exact (hdiag i).2.1
  · -- almost surely bounded support `2 / q`
    exact ⟨fun i => map_tail_eq_zero (hmd i) (hdiag i).2.2.1,
      fun p => map_tail_eq_zero (hmo p) (hoff p).2.2.1⟩
  · -- the bad event lies in the union of the coordinate tails
    have hsub : {ω : Entries N | ∃ i j, κ <
        |symOfEntries ω i j - symOfEntries (boundedMap q L ω) i j|} ⊆
        (⋃ i, {ω : Entries N | ω.1 i ∈ tailSet q}) ∪
          ⋃ p, {ω : Entries N | ω.2 p ∈ tailSet q} := by
      rintro ω ⟨i, j, hij⟩
      by_contra hω
      simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, tailSet, not_or, not_exists,
        not_lt] at hω
      obtain ⟨hω1, hω2⟩ := hω
      refine absurd hij (not_lt.mpr ?_)
      unfold symOfEntries boundedMap
      split_ifs
      · exact (hdiag _).2.2.2 _ (hω1 _)
      · exact (hoff _).2.2.2 _ (hω2 _)
      · exact (hoff _).2.2.2 _ (hω2 _)
    have hcard : (Fintype.card (OffDiag N) : ℝ) ≤ (N : ℝ) ^ 2 := by
      have h := Fintype.card_subtype_le (fun p : Fin N × Fin N => p.1 < p.2)
      rw [Fintype.card_prod, Fintype.card_fin] at h
      have h' : ((Fintype.card (OffDiag N) : ℕ) : ℝ) ≤ ((N * N : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      nlinarith
    have hs := measurableSet_tailSet q
    calc L.law {ω | ∃ i j, κ < |symOfEntries ω i j - symOfEntries (boundedMap q L ω) i j|}
        ≤ L.law ((⋃ i, {ω : Entries N | ω.1 i ∈ tailSet q}) ∪
            ⋃ p, {ω : Entries N | ω.2 p ∈ tailSet q}) := measure_mono hsub
      _ ≤ L.law (⋃ i, {ω : Entries N | ω.1 i ∈ tailSet q}) +
            L.law (⋃ p, {ω : Entries N | ω.2 p ∈ tailSet q}) := measure_union_le _ _
      _ ≤ (∑ i, L.law {ω : Entries N | ω.1 i ∈ tailSet q}) +
            ∑ p, L.law {ω : Entries N | ω.2 p ∈ tailSet q} :=
          add_le_add (measure_iUnion_fintype_le _ _) (measure_iUnion_fintype_le _ _)
      _ = (∑ i, L.diag i (tailSet q)) + ∑ p, L.off p (tailSet q) := by
          simp_rw [law_coord_diag hP _ hs, law_coord_off hP _ hs]
      _ ≤ (∑ _i : Fin N, ENNReal.ofReal (κ ^ 4)) + ∑ _p : OffDiag N, ENNReal.ofReal (κ ^ 4) :=
          add_le_add (Finset.sum_le_sum fun i _ => hBS.1 i)
            (Finset.sum_le_sum fun p _ => hBS.2 p)
      _ = ENNReal.ofReal (((N : ℝ) + Fintype.card (OffDiag N)) * κ ^ 4) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
              (by positivity), add_mul]
      _ ≤ ENNReal.ofReal (2 * (N : ℝ) ^ 2 * Real.exp (-(N : ℝ) ^ c)) := by
          rw [hτ]
          refine ENNReal.ofReal_le_ofReal ?_
          have : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
          nlinarith [pow_pos hκ0 4]

/-! ### A generalized Wigner law with a nonempty tail

Every entry has the law `((1 - r)/2)(δ_a + δ_{-a}) + (r/2)(δ_1 + δ_{-1})` with
`r = exp(-N^{1/2}) / N` and `a² = (N⁻¹ - r)/(1 - r)`. For `N ≥ 4` and `q = 2` the atoms `±1`
lie in the tail `{|x| > q⁻¹}` and carry mass `r > 0`, so the truncation is not the identity. -/

/-- The four-atom law `((1 - r)/2)(δ_a + δ_{-a}) + (r/2)(δ_1 + δ_{-1})`. -/
private def exMeasure (r a : ℝ) : Measure ℝ :=
  ENNReal.ofReal ((1 - r) / 2) • (Measure.dirac a + Measure.dirac (-a)) +
    ENNReal.ofReal (r / 2) • (Measure.dirac 1 + Measure.dirac (-1))

private lemma exMeasure_integrable (r a : ℝ) (f : ℝ → ℝ) : Integrable f (exMeasure r a) := by
  have hi : ∀ b : ℝ, Integrable f (Measure.dirac b) := fun b => integrable_dirac (by simp)
  exact (((hi a).add_measure (hi (-a))).smul_measure (by simp)).add_measure
    (((hi 1).add_measure (hi (-1))).smul_measure (by simp))

private lemma exMeasure_integral {r a : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (f : ℝ → ℝ) :
    ∫ x, f x ∂(exMeasure r a) = (1 - r) / 2 * (f a + f (-a)) + r / 2 * (f 1 + f (-1)) := by
  have hi : ∀ b : ℝ, Integrable f (Measure.dirac b) := fun b => integrable_dirac (by simp)
  unfold exMeasure
  rw [integral_add_measure (((hi a).add_measure (hi (-a))).smul_measure (by simp))
      (((hi 1).add_measure (hi (-1))).smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure,
    integral_add_measure (hi a) (hi (-a)), integral_add_measure (hi 1) (hi (-1)),
    integral_dirac, integral_dirac, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
  simp only [smul_eq_mul]

private lemma ofReal_mul_two (w : ℝ) :
    ENNReal.ofReal w * (1 + 1) = ENNReal.ofReal (2 * w) := by
  rw [ENNReal.ofReal_mul (by norm_num), one_add_one_eq_two, ENNReal.ofReal_ofNat, mul_comm]

private lemma exMeasure_prob {r a : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    IsProbabilityMeasure (exMeasure r a) := by
  refine ⟨?_⟩
  simp only [exMeasure, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul]
  rw [ofReal_mul_two _, ofReal_mul_two _,
    ← ENNReal.ofReal_add (by linarith) (by linarith)]
  ring_nf
  exact ENNReal.ofReal_one

/-- The tail `{|x| > 2⁻¹}` has mass `r` when `|a| ≤ 2⁻¹`. -/
private lemma exMeasure_tail {r a : ℝ} (ha : |a| ≤ 2⁻¹) :
    exMeasure r a {x | (2 : ℝ)⁻¹ < |x|} = ENNReal.ofReal r := by
  have hm : MeasurableSet {x : ℝ | (2 : ℝ)⁻¹ < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have h1 : a ∉ {x : ℝ | (2 : ℝ)⁻¹ < |x|} := by simpa using ha
  have h2 : -a ∉ {x : ℝ | (2 : ℝ)⁻¹ < |x|} := by simpa using ha
  have h3 : (1 : ℝ) ∈ {x : ℝ | (2 : ℝ)⁻¹ < |x|} := by norm_num
  have h4 : (-1 : ℝ) ∈ {x : ℝ | (2 : ℝ)⁻¹ < |x|} := by norm_num
  simp only [exMeasure, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hm,
    Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, Set.indicator_of_mem h3,
    Set.indicator_of_mem h4, Pi.one_apply, add_zero, mul_zero, zero_add, smul_eq_mul]
  rw [ofReal_mul_two _]
  ring_nf

/-- The tail variance `∫_{|x| > 2⁻¹} x²` is `r` when `|a| ≤ 2⁻¹`. -/
private lemma exMeasure_tailVar {r a : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ha : |a| ≤ 2⁻¹) :
    ∫ x in {x : ℝ | (2 : ℝ)⁻¹ < |x|}, x ^ 2 ∂(exMeasure r a) = r := by
  have hm : MeasurableSet {x : ℝ | (2 : ℝ)⁻¹ < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have h1 : a ∉ {x : ℝ | (2 : ℝ)⁻¹ < |x|} := by simpa using ha
  have h2 : -a ∉ {x : ℝ | (2 : ℝ)⁻¹ < |x|} := by simpa using ha
  have h3 : (1 : ℝ) ∈ {x : ℝ | (2 : ℝ)⁻¹ < |x|} := by norm_num
  have h4 : (-1 : ℝ) ∈ {x : ℝ | (2 : ℝ)⁻¹ < |x|} := by norm_num
  rw [← integral_indicator hm, exMeasure_integral hr0 hr1, Set.indicator_of_notMem h1,
    Set.indicator_of_notMem h2, Set.indicator_of_mem h3, Set.indicator_of_mem h4]
  ring

/-- The tail mass `r = exp(-N^{1/2}) / N`. -/
private def exR (N : ℕ) : ℝ := Real.exp (-(N : ℝ) ^ (1 / 2 : ℝ)) / N

/-- The bulk amplitude `a = ((N⁻¹ - r)/(1 - r))^{1/2}`. -/
private def exA (N : ℕ) : ℝ := Real.sqrt (((N : ℝ)⁻¹ - exR N) / (1 - exR N))

/-- Every entry of size `N` has the law `exMeasure (exR N) (exA N)`. -/
private def exLaws (N : ℕ) : EntryLaws N :=
  ⟨fun _ => exMeasure (exR N) (exA N), fun _ => exMeasure (exR N) (exA N)⟩

/-- For `N ≥ 4`, `exLaws N` is a generalized Wigner law (`C0 = 0`) with admissible support
parameter `q = 2` (`Q = 1`, `c = 1/2`), and its tail `{|x| > 2⁻¹}` has positive mass. -/
private lemma exLaws_hyp {N : ℕ} (hN : 4 ≤ N) :
    (exLaws N).IsGenWigner 0 ∧ (exLaws N).SupportParam 1 (1 / 2) 2 ∧
      ∀ p, 0 < (exLaws N).off p {x | (2 : ℝ)⁻¹ < |x|} := by
  have hN' : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  set τ := Real.exp (-(N : ℝ) ^ (1 / 2 : ℝ)) with hτ_def
  have hτ0 : 0 < τ := Real.exp_pos _
  have hτ1 : τ ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hn0.le _
    linarith)
  have hr : exR N = τ / N := rfl
  have hr0 : 0 < exR N := by rw [hr]; positivity
  have hrτ : exR N ≤ τ := by rw [hr, div_le_iff₀ hn0]; nlinarith
  have hrN : exR N ≤ (N : ℝ)⁻¹ := by rw [hr, div_eq_mul_inv]; nlinarith [inv_pos.mpr hn0]
  have hNi : (N : ℝ)⁻¹ ≤ 1 / 4 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hN'
  have hr1 : exR N ≤ 1 := by linarith
  have hr1' : 0 < 1 - exR N := by linarith
  have hq : (0 : ℝ) ≤ ((N : ℝ)⁻¹ - exR N) / (1 - exR N) := div_nonneg (by linarith) hr1'.le
  have ha2 : exA N ^ 2 = ((N : ℝ)⁻¹ - exR N) / (1 - exR N) := Real.sq_sqrt hq
  have ha2N : exA N ^ 2 ≤ (N : ℝ)⁻¹ := by
    rw [ha2, div_le_iff₀ hr1']
    have := mul_nonneg (inv_pos.mpr hn0).le hr0.le
    nlinarith
  have ha : |exA N| ≤ 2⁻¹ := by
    rw [← Real.sqrt_sq_eq_abs, ha2]
    rw [Real.sqrt_le_left (by norm_num)]
    rw [← ha2]; nlinarith
  have hint := exMeasure_integral (a := exA N) hr0.le hr1
  have hvar : ∫ x, x ^ 2 ∂(exMeasure (exR N) (exA N)) = (N : ℝ)⁻¹ := by
    rw [hint]
    have : (1 - exR N) * exA N ^ 2 = (N : ℝ)⁻¹ - exR N := by
      rw [ha2]; field_simp
    nlinarith
  have hmean : ∫ x, x ∂(exMeasure (exR N) (exA N)) = 0 := by rw [hint]; ring
  have hP := exMeasure_prob (a := exA N) hr0.le hr1
  refine ⟨⟨⟨fun _ => hP, fun _ => hP⟩, fun _ => exMeasure_integrable _ _ _,
    fun _ => exMeasure_integrable _ _ _, fun _ => hmean, fun _ => hmean, fun _ => hvar,
    fun _ => ?_⟩, ⟨by norm_num, ⟨fun _ => ?_, fun _ => ?_⟩, fun _ => ?_⟩, fun _ => ?_⟩
  · change |∫ x, x ^ 2 ∂(exMeasure (exR N) (exA N)) - _| ≤ _
    rw [hvar]; simp
  · change exMeasure (exR N) (exA N) {x | (2 : ℝ)⁻¹ < |x|} ≤ _
    rw [exMeasure_tail ha]; exact ENNReal.ofReal_le_ofReal hrτ
  · change exMeasure (exR N) (exA N) {x | (2 : ℝ)⁻¹ < |x|} ≤ _
    rw [exMeasure_tail ha]; exact ENNReal.ofReal_le_ofReal hrτ
  · change ∫ x in {x : ℝ | (2 : ℝ)⁻¹ < |x|}, x ^ 2 ∂(exMeasure (exR N) (exA N)) ≤ _
    rw [exMeasure_tailVar hr0.le hr1 ha]; exact hrτ
  · change 0 < exMeasure (exR N) (exA N) {x | (2 : ℝ)⁻¹ < |x|}
    rw [exMeasure_tail ha]; exact ENNReal.ofReal_pos.mpr hr0

/-- `exists_truncation` at `C0 = 0`, `c = 1/2`, `q = 2`, at the concrete size `N = 4`: all
hypotheses on the law hold at once, the tail has positive mass, and two distinct upper
entries exist. -/
example : (exLaws 4).IsGenWigner 0 ∧ (exLaws 4).SupportParam 1 (1 / 2) 2 ∧
    0 < (exLaws 4).off ⟨(0, 1), by decide⟩ {x | (2 : ℝ)⁻¹ < |x|} ∧
    (⟨(0, 1), by decide⟩ : OffDiag 4) ≠ ⟨(2, 3), by decide⟩ :=
  ⟨(exLaws_hyp le_rfl).1, (exLaws_hyp le_rfl).2.1, (exLaws_hyp le_rfl).2.2 _, by decide⟩

/-- `exists_truncation` applied to the family `exLaws N` (`C0 = 0`, `c = 1/2`, `q = 2`):
for all large `N` the conclusion holds. -/
example : ∀ᶠ N in atTop, ∃ (L' : EntryLaws N) (T : Entries N → Entries N),
    Measurable T ∧ (exLaws N).law.map T = L'.law ∧ L'.IsGenWigner (max 0 1) ∧
    L'.BoundedSupportAS (2 / 2) ∧
    (exLaws N).law {ω | ∃ i j, Real.exp (-(N : ℝ) ^ (1 / 2 : ℝ) / 4) <
      |symOfEntries ω i j - symOfEntries (T ω) i j|} ≤
      ENNReal.ofReal (2 * (N : ℝ) ^ 2 * Real.exp (-(N : ℝ) ^ (1 / 2 : ℝ))) := by
  obtain ⟨N0, hN0⟩ := exists_truncation (C0 := 0) (c := 1 / 2) le_rfl (by norm_num)
  filter_upwards [eventually_ge_atTop (max N0 4)] with N hN
  have h := exLaws_hyp (le_of_max_le_right hN)
  exact hN0 N (le_of_max_le_left hN) (exLaws N) 2 h.1 h.2.1

/-! ### Checks -/

#print axioms exists_truncation

end WEdgeNS
