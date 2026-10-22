import WEdgeNS.E1.Tail
import WEdgeNS.Model.General

/-!
# Tails and centrings of the cut-off entries
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

private lemma measurableSet_tail (T : ℝ) : MeasurableSet {x : ℝ | T < |x|} :=
  measurableSet_lt measurable_const continuous_abs.measurable

/-- The part of `∫ x² dμ` beyond `T` tends to `0` as `T → ∞`. -/
private lemma tendsto_setIntegral_sq_tail {μ : Measure ℝ}
    (h : Integrable (fun x : ℝ => x ^ 2) μ) :
    Tendsto (fun T : ℝ => ∫ x in {x : ℝ | T < |x|}, x ^ 2 ∂μ) atTop (𝓝 0) := by
  have key : Tendsto (fun T : ℝ => ∫ x, ({x : ℝ | T < |x|}).indicator (fun x => x ^ 2) x ∂μ)
      atTop (𝓝 (∫ _x, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => x ^ 2) ?_ ?_ h ?_
    · exact Eventually.of_forall fun T =>
        (h.1.indicator (measurableSet_tail T))
    · refine Eventually.of_forall fun T => Eventually.of_forall fun x => ?_
      by_cases hx : T < |x|
      · simp [Set.indicator_of_mem (show x ∈ {x : ℝ | T < |x|} from hx)]
      · simp [Set.indicator_of_notMem (show x ∉ {x : ℝ | T < |x|} from hx)]
        positivity
    · refine Eventually.of_forall fun x => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop |x|] with T hT
      simp [Set.indicator_of_notMem (show x ∉ {x : ℝ | T < |x|} from not_lt.mpr hT)]
  simp only [integral_zero] at key
  refine key.congr fun T => ?_
  exact integral_indicator (measurableSet_tail T)


private lemma sq_mul_measure_le {μ : Measure ℝ} [IsFiniteMeasure μ]
    (h : Integrable (fun x : ℝ => x ^ 2) μ) {T : ℝ} (hT : 0 ≤ T) :
    T ^ 2 * (μ {x : ℝ | T < |x|}).toReal ≤ ∫ x in {x : ℝ | T < |x|}, x ^ 2 ∂μ := by
  have h1 : ∫ _x in {x : ℝ | T < |x|}, T ^ 2 ∂μ ≤ ∫ x in {x : ℝ | T < |x|}, x ^ 2 ∂μ := by
    refine setIntegral_mono_on (integrableOn_const (by simp [measure_ne_top])) h.integrableOn
      (measurableSet_tail T) fun x hx => ?_
    have hx' : T < |x| := hx
    rw [← sq_abs x]
    exact pow_le_pow_left₀ hT hx'.le 2
  rw [setIntegral_const, smul_eq_mul, measureReal_def] at h1
  linarith

private lemma mul_abs_setIntegral_le {μ : Measure ℝ} [IsFiniteMeasure μ]
    (h : Integrable (fun x : ℝ => x ^ 2) μ) {T : ℝ} (hT : 0 ≤ T) :
    T * |∫ x in {x : ℝ | T < |x|}, x ∂μ| ≤ ∫ x in {x : ℝ | T < |x|}, x ^ 2 ∂μ := by
  have hxint : Integrable (fun x : ℝ => x) μ :=
    ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr h).integrable one_le_two
  have h1 : |∫ x in {x : ℝ | T < |x|}, x ∂μ| ≤ ∫ x in {x : ℝ | T < |x|}, |x| ∂μ := by
    simpa using norm_integral_le_integral_norm (μ := μ.restrict {x : ℝ | T < |x|}) (fun x => x)
  have h2 : T * ∫ x in {x : ℝ | T < |x|}, |x| ∂μ ≤ ∫ x in {x : ℝ | T < |x|}, x ^ 2 ∂μ := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hxint.abs.const_mul T).integrableOn h.integrableOn
      (measurableSet_tail T) fun x hx => ?_
    have hx' : T < |x| := hx
    rw [← sq_abs x, sq]
    exact mul_le_mul_of_nonneg_right hx'.le (abs_nonneg x)
  exact le_trans (mul_le_mul_of_nonneg_left h1 hT) h2

/-- For a law with a finite second moment, `T² μ(|x| > T) → 0`. -/
private lemma tendsto_sq_mul_measure {μ : Measure ℝ} [IsFiniteMeasure μ]
    (h : Integrable (fun x : ℝ => x ^ 2) μ) :
    Tendsto (fun T : ℝ => T ^ 2 * (μ {x : ℝ | T < |x|}).toReal) atTop (𝓝 0) :=
  squeeze_zero' (Eventually.of_forall fun T => by positivity)
    ((eventually_ge_atTop (0 : ℝ)).mono fun T hT => sq_mul_measure_le h hT)
    (tendsto_setIntegral_sq_tail h)

/-- For a law with a finite second moment, `T |∫_{|x| > T} x dμ| → 0`. -/
private lemma tendsto_mul_abs_setIntegral {μ : Measure ℝ} [IsFiniteMeasure μ]
    (h : Integrable (fun x : ℝ => x ^ 2) μ) :
    Tendsto (fun T : ℝ => T * |∫ x in {x : ℝ | T < |x|}, x ∂μ|) atTop (𝓝 0) :=
  squeeze_zero' ((eventually_ge_atTop (0 : ℝ)).mono fun T hT => by positivity)
    ((eventually_ge_atTop (0 : ℝ)).mono fun T hT => mul_abs_setIntegral_le h hT)
    (tendsto_setIntegral_sq_tail h)


private lemma shell_term_le (p : ℕ) (hp : p ≤ 3) {u T δ : ℝ} (hu : 1 ≤ u) (hT : 0 < T)
    (hδ : 0 ≤ δ) :
    (2 * u * T) ^ p * (δ / (u * T) ^ 4) ≤ 8 * δ * T ^ p / T ^ 4 * u⁻¹ := by
  have hu0 : 0 < u := by linarith
  have key : 2 ^ p * u ^ p / u ^ 4 ≤ 8 * u⁻¹ := by
    rw [div_le_iff₀ (by positivity)]
    have : 8 * u⁻¹ * u ^ 4 = 8 * u ^ 3 := by field_simp
    rw [this]
    interval_cases p <;> nlinarith [pow_pos hu0 2, pow_pos hu0 3]
  calc (2 * u * T) ^ p * (δ / (u * T) ^ 4)
      = δ * T ^ p / T ^ 4 * (2 ^ p * u ^ p / u ^ 4) := by
        rw [mul_pow, mul_pow]
        field_simp
    _ ≤ δ * T ^ p / T ^ 4 * (8 * u⁻¹) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = 8 * δ * T ^ p / T ^ 4 * u⁻¹ := by ring

/-- Shell decomposition of the tail beyond `T`: if `s⁴ μ(|x| ≥ s) ≤ δ` for all `s ≥ T`, then
`∫_{|x| > T} |x|^p dμ ≤ 16 δ T^{p-4}` for `p ≤ 3`. -/
private lemma setIntegral_pow_tail_le {μ : Measure ℝ} [IsFiniteMeasure μ] (p : ℕ) (hp : p ≤ 3)
    (hint : Integrable (fun x : ℝ => |x| ^ p) μ) {T δ : ℝ} (hT : 0 < T)
    (hδ : ∀ s : ℝ, T ≤ s → s ^ 4 * (μ {x : ℝ | s ≤ |x|}).toReal ≤ δ) :
    ∫ x in {x : ℝ | T < |x|}, |x| ^ p ∂μ ≤ 16 * δ * T ^ p / T ^ 4 := by
  have hδ0 : 0 ≤ δ := le_trans (by positivity) (hδ T le_rfl)
  set A : ℕ → Set ℝ := fun k => {x : ℝ | 2 ^ k * T < |x| ∧ |x| ≤ 2 ^ (k + 1) * T} with hA
  have hm : ∀ k, MeasurableSet (A k) := fun k =>
    (measurableSet_tail _).inter (measurableSet_le continuous_abs.measurable measurable_const)
  have hd : Pairwise (Function.onFun Disjoint A) := by
    have key : ∀ j k : ℕ, j < k → Disjoint (A j) (A k) := by
      intro j k hjk
      rw [Set.disjoint_left]
      intro x hxj hxk
      have h1 : (2 : ℝ) ^ (j + 1) ≤ 2 ^ k :=
        pow_le_pow_right₀ (by norm_num) hjk
      have := hxj.2
      have := hxk.1
      nlinarith
    intro j k hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact key j k h
    · exact (key k j h).symm
  have hU : (⋃ k, A k) = {x : ℝ | T < |x|} := by
    ext x
    simp only [Set.mem_iUnion, hA]
    constructor
    · rintro ⟨k, hk, -⟩
      have : T ≤ 2 ^ k * T := by
        have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        nlinarith
      show T < |x|
      linarith
    · intro hx
      have hx : T < |x| := hx
      have hr : 1 < |x| / T := by rw [lt_div_iff₀ hT]; linarith
      have hex : ∃ n : ℕ, |x| / T ≤ 2 ^ n := by
        obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (|x| / T) (show (1 : ℝ) < 2 by norm_num)
        exact ⟨n, hn.le⟩
      classical
      set n := Nat.find hex with hn
      have hn1 : |x| / T ≤ 2 ^ n := Nat.find_spec hex
      have hn0 : n ≠ 0 := by
        intro h0
        rw [h0] at hn1
        simp at hn1
        linarith
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      refine ⟨k, ?_, ?_⟩
      · have hlt : ¬ |x| / T ≤ 2 ^ k := Nat.find_min hex (by omega)
        push Not at hlt
        rw [lt_div_iff₀ hT] at hlt
        linarith
      · rw [hk] at hn1
        rw [div_le_iff₀ hT] at hn1
        exact hn1
  have hS := hasSum_integral_iUnion (μ := μ) (f := fun x : ℝ => |x| ^ p) hm hd
    (by rw [hU]; exact hint.integrableOn)
  rw [hU] at hS
  have hg : HasSum (fun k : ℕ => (8 * δ * T ^ p / T ^ 4) * (1 / 2 : ℝ) ^ k)
      ((8 * δ * T ^ p / T ^ 4) * 2) := hasSum_geometric_two.mul_left _
  have hle := hasSum_le (fun k => ?_) hS hg
  · calc _ ≤ _ := hle
      _ = 16 * δ * T ^ p / T ^ 4 := by ring
  · have hu : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    set u : ℝ := 2 ^ k with hu_def
    have hu0 : 0 < u := by linarith
    have h1 : ∫ x in A k, |x| ^ p ∂μ ≤ (2 * u * T) ^ p * μ.real (A k) := by
      have := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := A k)
        (f := fun x : ℝ => |x| ^ p) (C := (2 * u * T) ^ p) (measure_lt_top _ _) (fun x hx => ?_)
      · exact le_trans (le_abs_self _) this
      · have hx' := hx.2
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have : (2 : ℝ) ^ (k + 1) * T = 2 * u * T := by rw [hu_def]; ring
        rw [this] at hx'
        exact pow_le_pow_left₀ (abs_nonneg x) hx' p
    have h2 : μ.real (A k) ≤ δ / (u * T) ^ 4 := by
      have hsub : A k ⊆ {x : ℝ | u * T ≤ |x|} := fun x hx => hx.1.le
      have := hδ (u * T) (by nlinarith)
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact le_trans (mul_le_mul_of_nonneg_left
        (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)) (by positivity)) this
    calc ∫ x in A k, |x| ^ p ∂μ ≤ (2 * u * T) ^ p * μ.real (A k) := h1
      _ ≤ (2 * u * T) ^ p * (δ / (u * T) ^ 4) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 8 * δ * T ^ p / T ^ 4 * u⁻¹ := shell_term_le p hp hu hT hδ0
      _ = (8 * δ * T ^ p / T ^ 4) * (1 / 2 : ℝ) ^ k := by
          rw [hu_def]; simp [one_div, inv_pow]


/-- `T^q ∫_{|x| > T} |x|^p dν → 0` for `p + q = 4`, `p ≤ 3`, from (1.4). -/
private lemma tendsto_pow_mul_setIntegral_pow {ν : Measure ℝ} [IsFiniteMeasure ν] (p q : ℕ)
    (hp : p ≤ 3) (hpq : p + q = 4) (hint : Integrable (fun x : ℝ => |x| ^ p) ν)
    (h14 : TailCond ν) :
    Tendsto (fun T : ℝ => T ^ q * ∫ x in {x : ℝ | T < |x|}, |x| ^ p ∂ν) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    refine lt_of_lt_of_le ha (mul_nonneg (by positivity) (integral_nonneg fun x => by positivity))
  · have hδ : (0 : ℝ) < b / 32 := by positivity
    have hev := h14.eventually (eventually_le_nhds hδ)
    obtain ⟨s0, hs0⟩ := eventually_atTop.1 hev
    filter_upwards [eventually_ge_atTop (max s0 1)] with T hT
    have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT
    have hT0 : 0 < T := by linarith
    have hb' := setIntegral_pow_tail_le p hp hint hT0 fun s hs =>
      hs0 s (le_trans (le_trans (le_max_left _ _) hT) hs)
    have hq : T ^ q * (16 * (b / 32) * T ^ p / T ^ 4) = b / 2 := by
      have : T ^ 4 = T ^ q * T ^ p := by rw [← pow_add]; congr 1; omega
      rw [this]
      field_simp
      ring
    calc T ^ q * ∫ x in {x : ℝ | T < |x|}, |x| ^ p ∂ν
        ≤ T ^ q * (16 * (b / 32) * T ^ p / T ^ 4) :=
          mul_le_mul_of_nonneg_left hb' (by positivity)
      _ = b / 2 := hq
      _ < b := by linarith

private lemma abs_setIntegral_le {μ : Measure ℝ} (T : ℝ) :
    |∫ x in {x : ℝ | T < |x|}, x ∂μ| ≤ ∫ x in {x : ℝ | T < |x|}, |x| ^ 1 ∂μ := by
  simpa using norm_integral_le_integral_norm (μ := μ.restrict {x : ℝ | T < |x|}) (fun x => x)

private lemma rpow_pow_eq (N : ℕ) (a : ℝ) (k : ℕ) (b : ℝ) (h : b = a * k) :
    (N : ℝ) ^ b = ((N : ℝ) ^ a) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N), h]

private lemma tendsto_cutoff (ε : ℝ) (hε : ε < 1 / 2) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 2 - ε)) atTop atTop :=
  (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop

/-- The centring `m = E[x | |x| ≤ T]` of (4.14), taken from the conditional law. -/
def cutoffMean (ν : Measure ℝ) (T : ℝ) : ℝ := ∫ y, y ∂(cond ν {x | |x| ≤ T})

/-- (4.12)–(4.13) in little-o form: `α = o(N^{-2+4ε})`, `α̃ = o(N^{-1+2ε})`,
`β = o(N^{-3/2+3ε})`, `β̃ = o(N^{-1/2+ε})`, and `E[x²; |x| > T] = o(N^{-1+2ε})`. -/
theorem cutoff_tail_bounds {ν ν' : Measure ℝ} (hW : WignerLaws ν ν') (h14 : TailCond ν)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (2 - 4 * ε) *
        (ν {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}).toReal) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - 2 * ε) *
        (ν' {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}).toReal) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => (N : ℝ) ^ ((3 : ℝ) / 2 - 3 * ε) *
        |∫ x in {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}, x ∂ν|) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 2 - ε) *
        |∫ x in {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}, x ∂ν'|) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - 2 * ε) *
        ∫ x in {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}, x ^ 2 ∂ν) atTop (𝓝 0) := by
  have := hW.prob
  have := hW.prob'
  have hT := tendsto_cutoff ε hε
  have e4 : ∀ N : ℕ, (N : ℝ) ^ (2 - 4 * ε) = ((N : ℝ) ^ (1 / 2 - ε)) ^ 4 := fun N =>
    rpow_pow_eq N _ 4 _ (by push_cast; ring)
  have e3 : ∀ N : ℕ, (N : ℝ) ^ ((3 : ℝ) / 2 - 3 * ε) = ((N : ℝ) ^ (1 / 2 - ε)) ^ 3 := fun N =>
    rpow_pow_eq N _ 3 _ (by push_cast; ring)
  have e2 : ∀ N : ℕ, (N : ℝ) ^ (1 - 2 * ε) = ((N : ℝ) ^ (1 / 2 - ε)) ^ 2 := fun N =>
    rpow_pow_eq N _ 2 _ (by push_cast; ring)
  have hint2 : Integrable (fun x : ℝ => |x| ^ 2) ν := by simpa [sq_abs] using hW.sq_int
  have hint1 : Integrable (fun x : ℝ => |x| ^ 1) ν := by
    have : Integrable (fun x : ℝ => x) ν :=
      ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hW.sq_int).integrable one_le_two
    simpa using this.abs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [e4]
    refine squeeze_zero' (Eventually.of_forall fun N => by positivity)
      (Eventually.of_forall fun N => mul_le_mul_of_nonneg_left
        (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun x hx => show _ ≤ |x| from le_of_lt hx))
        (by positivity)) (h14.comp hT)
  · simp only [e2]
    exact (tendsto_sq_mul_measure hW.sq_int').comp hT
  · simp only [e3]
    refine squeeze_zero' (Eventually.of_forall fun N => by positivity)
      (Eventually.of_forall fun N => mul_le_mul_of_nonneg_left (abs_setIntegral_le _)
        (by positivity))
      ((tendsto_pow_mul_setIntegral_pow 1 3 (by norm_num) (by norm_num) hint1 h14).comp hT)
  · exact (tendsto_mul_abs_setIntegral hW.sq_int').comp hT
  · have := (tendsto_pow_mul_setIntegral_pow 2 2 (by norm_num) (by norm_num) hint2 h14).comp hT
    refine this.congr fun N => ?_
    simp only [Function.comp, sq_abs, e2]

/-- The centring is `-∫_{|x| > T} x dμ / μ(|x| ≤ T)`, so it is at most twice that integral
once `μ(|x| > T) ≤ 1/2`. -/
private lemma abs_cutoffMean_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x) μ) (hmean : ∫ x, x ∂μ = 0) {T : ℝ}
    (hα : (μ {x : ℝ | T < |x|}).toReal ≤ 1 / 2) :
    |cutoffMean μ T| ≤ 2 * |∫ x in {x : ℝ | T < |x|}, x ∂μ| := by
  have hc : {x : ℝ | |x| ≤ T} = {x : ℝ | T < |x|}ᶜ := by
    ext x; simp
  have hS : MeasurableSet {x : ℝ | |x| ≤ T} :=
    measurableSet_le continuous_abs.measurable measurable_const
  have hm : (μ {x : ℝ | |x| ≤ T}).toReal = 1 - (μ {x : ℝ | T < |x|}).toReal := by
    rw [hc, prob_compl_eq_one_sub (measurableSet_tail T), ENNReal.toReal_sub_of_le prob_le_one
      ENNReal.one_ne_top]
    simp
  have hpos : 1 / 2 ≤ (μ {x : ℝ | |x| ≤ T}).toReal := by rw [hm]; linarith
  have hne : μ {x : ℝ | |x| ≤ T} ≠ 0 := by
    intro h; rw [h] at hpos; simp at hpos; linarith
  have hsplit : ∫ x in {x : ℝ | |x| ≤ T}, x ∂μ = -∫ x in {x : ℝ | T < |x|}, x ∂μ := by
    have := integral_add_compl hS hint
    rw [hmean, hc, compl_compl] at this
    rw [hc]
    have h2 : ∫ x in {x : ℝ | T < |x|}ᶜ, x ∂μ + ∫ x in {x : ℝ | T < |x|}, x ∂μ = 0 := by
      have := integral_add_compl (measurableSet_tail T) hint
      rw [hmean] at this
      linarith
    linarith
  have hcm : cutoffMean μ T =
      ((μ {x : ℝ | |x| ≤ T})⁻¹).toReal * ∫ x in {x : ℝ | |x| ≤ T}, x ∂μ := by
    unfold cutoffMean ProbabilityTheory.cond
    rw [integral_smul_measure, smul_eq_mul]
  rw [hcm, hsplit, ENNReal.toReal_inv, abs_mul, abs_neg, abs_of_nonneg (by positivity)]
  have hp' : 0 < (μ {x : ℝ | |x| ≤ T}).toReal := by linarith
  calc ((μ {x : ℝ | |x| ≤ T}).toReal)⁻¹ * |∫ x in {x : ℝ | T < |x|}, x ∂μ|
      ≤ 2 * |∫ x in {x : ℝ | T < |x|}, x ∂μ| := by
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        rw [inv_le_comm₀ hp' (by norm_num)]
        linarith
    _ = _ := rfl

/-- If `a_N ≥ 0` and `N^e a_N → 0` with `e ≥ 0`, then `a_N → 0`. -/
private lemma tendsto_of_rpow_mul {a : ℕ → ℝ} {e : ℝ} (he : 0 ≤ e) (ha : ∀ N, 0 ≤ a N)
    (h : Tendsto (fun N : ℕ => (N : ℝ) ^ e * a N) atTop (𝓝 0)) : Tendsto a atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall ha) ?_ h
  filter_upwards [eventually_ge_atTop 1] with N hN
  have : (1 : ℝ) ≤ (N : ℝ) ^ e := Real.one_le_rpow (by exact_mod_cast hN) he
  nlinarith [ha N]

/-- The centrings of (4.14)–(4.15): `m = o(N^{-3/2+3ε})`, `m̃ = o(N^{-1/2+ε})`. -/
theorem cutoffMean_bounds {ν ν' : Measure ℝ} (hW : WignerLaws ν ν') (h14 : TailCond ν)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ ((3 : ℝ) / 2 - 3 * ε) *
        |cutoffMean ν ((N : ℝ) ^ (1 / 2 - ε))|) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 2 - ε) *
        |cutoffMean ν' ((N : ℝ) ^ (1 / 2 - ε))|) atTop (𝓝 0) := by
  have := hW.prob
  have := hW.prob'
  obtain ⟨h1, h2, h3, h4, -⟩ := cutoff_tail_bounds hW h14 hε0 hε
  have hα : Tendsto (fun N : ℕ => (ν {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}).toReal) atTop (𝓝 0) :=
    tendsto_of_rpow_mul (by linarith) (fun N => ENNReal.toReal_nonneg) h1
  have hα' : Tendsto (fun N : ℕ => (ν' {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}).toReal) atTop
      (𝓝 0) :=
    tendsto_of_rpow_mul (by linarith) (fun N => ENNReal.toReal_nonneg) h2
  have hxint : Integrable (fun x : ℝ => x) ν :=
    ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hW.sq_int).integrable one_le_two
  have hxint' : Integrable (fun x : ℝ => x) ν' :=
    ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hW.sq_int').integrable one_le_two
  have hsmall := hα.eventually (eventually_le_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have hsmall' := hα'.eventually (eventually_le_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  constructor
  · have := h3.const_mul 2
    rw [mul_zero] at this
    refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ this
    filter_upwards [hsmall] with N hN
    calc (N : ℝ) ^ ((3 : ℝ) / 2 - 3 * ε) * |cutoffMean ν ((N : ℝ) ^ (1 / 2 - ε))|
        ≤ (N : ℝ) ^ ((3 : ℝ) / 2 - 3 * ε) *
            (2 * |∫ x in {x : ℝ | (N : ℝ) ^ (1 / 2 - ε) < |x|}, x ∂ν|) :=
          mul_le_mul_of_nonneg_left (abs_cutoffMean_le hxint hW.mean hN) (by positivity)
      _ = 2 * ((N : ℝ) ^ ((3 : ℝ) / 2 - 3 * ε) *
            |∫ x in {x : ℝ | (N : ℝ) ^ (1 / 2 - ε) < |x|}, x ∂ν|) := by ring
  · have := h4.const_mul 2
    rw [mul_zero] at this
    refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ this
    filter_upwards [hsmall'] with N hN
    calc (N : ℝ) ^ (1 / 2 - ε) * |cutoffMean ν' ((N : ℝ) ^ (1 / 2 - ε))|
        ≤ (N : ℝ) ^ (1 / 2 - ε) *
            (2 * |∫ x in {x : ℝ | (N : ℝ) ^ (1 / 2 - ε) < |x|}, x ∂ν'|) :=
          mul_le_mul_of_nonneg_left (abs_cutoffMean_le hxint' hW.mean' hN) (by positivity)
      _ = 2 * ((N : ℝ) ^ (1 / 2 - ε) *
            |∫ x in {x : ℝ | (N : ℝ) ^ (1 / 2 - ε) < |x|}, x ∂ν'|) := by ring

/-- A probability measure charges `{|x| ≤ t}` for large `t`. -/
private lemma exists_measure_abs_le_ne_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∃ n : ℕ, μ {x : ℝ | |x| ≤ n} ≠ 0 := by
  by_contra h
  push Not at h
  have hU : (⋃ n : ℕ, {x : ℝ | |x| ≤ n}) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact exists_nat_ge |x|
  have := measure_iUnion_null (μ := μ) (s := fun n : ℕ => {x : ℝ | |x| ≤ n}) h
  rw [hU] at this
  simp at this

/-- For large `N` both cut-off events `|x| ≤ T` have positive mass. -/
theorem eventually_cutoff_mass_ne_zero {ν ν' : Measure ℝ} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] {ε : ℝ} (hε : ε < 1 / 2) :
    ∀ᶠ N : ℕ in atTop, ν {x | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)} ≠ 0 ∧
      ν' {x | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)} ≠ 0 := by
  obtain ⟨n, hn⟩ := exists_measure_abs_le_ne_zero ν
  obtain ⟨n', hn'⟩ := exists_measure_abs_le_ne_zero ν'
  have hT := tendsto_cutoff ε hε
  filter_upwards [hT.eventually_ge_atTop (max n n' : ℝ)] with N hN
  refine ⟨fun h => hn ?_, fun h => hn' ?_⟩
  · exact measure_mono_null (fun x hx => le_trans hx
      (le_trans (le_max_left (n : ℝ) n') hN)) h
  · exact measure_mono_null (fun x hx => le_trans hx
      (le_trans (le_max_right (n : ℝ) n') hN)) h

/-! ### Non-vacuity at Rademacher off-diagonal entries and `N(0, 2)` diagonal entries,
`ε = 1/100` -/

example := cutoff_tail_bounds rademacher_wignerLaws rademacher_tailCond
  (ε := 1 / 100) (by norm_num) (by norm_num)

example := cutoffMean_bounds rademacher_wignerLaws rademacher_tailCond
  (ε := 1 / 100) (by norm_num) (by norm_num)

example : ∀ᶠ N : ℕ in atTop,
    rademacher {x | |x| ≤ (N : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))} ≠ 0 ∧
      gaussianReal 0 2 {x | |x| ≤ (N : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))} ≠ 0 := by
  have := rademacher_wignerLaws.prob
  have := rademacher_wignerLaws.prob'
  exact eventually_cutoff_mass_ne_zero (by norm_num)

private lemma one_le_cutoff_thousand :
    (1 : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ)) :=
  Real.one_le_rpow (by norm_num) (by norm_num)

/-- At `N = 1000` the cut-off event has positive Rademacher mass. -/
example : rademacher {x : ℝ | |x| ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))} ≠ 0 := by
  have h1 : Measure.dirac (1 : ℝ)
      {x : ℝ | |x| ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))} = 1 :=
    Measure.dirac_apply_of_mem (by simpa using one_le_cutoff_thousand)
  simp only [rademacher, Measure.smul_apply, Measure.add_apply, h1, smul_eq_mul]
  simp

/-- At `N = 1000` the cut-off event has positive `N(0, 2)` mass. -/
example : gaussianReal 0 2 {x : ℝ | |x| ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))} ≠ 0 := by
  intro h
  have h0 := gaussianReal_absolutelyContinuous' 0 (by norm_num : (2 : NNReal) ≠ 0) h
  have hsub : Set.Icc (-1 : ℝ) 1 ⊆
      {x : ℝ | |x| ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))} := fun x hx =>
    (abs_le.mpr ⟨hx.1, hx.2⟩).trans one_le_cutoff_thousand
  have := measure_mono_null hsub h0
  rw [Real.volume_Icc] at this
  norm_num at this

/-- At `N = 1000` the tail `ν{|x| > T}` of Rademacher is empty, so the centring vanishes. -/
example : cutoffMean rademacher (((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))) = 0 := by
  have hW := rademacher_wignerLaws
  have := hW.prob
  have hxint : Integrable (fun x : ℝ => x) rademacher :=
    ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hW.sq_int).integrable one_le_two
  have h0 : rademacher {x : ℝ | ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ)) < |x|} = 0 := by
    have hT' : (1 : ℝ) ≤ (1000 : ℝ) ^ ((2 : ℝ)⁻¹ - (100 : ℝ)⁻¹) :=
      Real.one_le_rpow (by norm_num) (by norm_num)
    simp only [rademacher, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply,
      smul_eq_mul]
    simp [hT']
  have := abs_cutoffMean_le hxint hW.mean
    (T := ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))) (by rw [h0]; norm_num)
  rw [setIntegral_measure_zero _ h0] at this
  simpa using this

#print axioms cutoffMean
#print axioms cutoff_tail_bounds
#print axioms cutoffMean_bounds
#print axioms eventually_cutoff_mass_ne_zero

end WEdgeNS
