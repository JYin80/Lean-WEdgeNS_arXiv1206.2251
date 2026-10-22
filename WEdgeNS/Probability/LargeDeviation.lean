import WEdgeNS.Probability.MomentsLinear
import WEdgeNS.Probability.MomentsQuadratic
import WEdgeNS.Probability.MomentsBilinear

/-!
# Large deviation bounds for linear and quadratic forms in independent bounded variables
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- Markov's inequality at the even order `m`: a bound `R` on the `m`-th absolute moment gives
`μ {t B ≤ |X|} ≤ R / (t B) ^ m`. -/
private lemma largeDev_markov_pow {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X μ) {B t : ℝ} (hB : 0 < B) (ht : 0 < t) (m : ℕ) {R : ℝ}
    (hmom : ∫⁻ ω, ENNReal.ofReal (|X ω| ^ m) ∂μ ≤ ENNReal.ofReal R) :
    μ {ω | t * B ≤ |X ω|} ≤ ENNReal.ofReal (R / (t * B) ^ m) := by
  have hpos : 0 < (t * B) ^ m := by positivity
  have hf : AEMeasurable (fun ω => ENNReal.ofReal (|X ω| ^ m)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((continuous_abs.measurable.comp_aemeasurable hX).pow_const m)
  have h1 := mul_meas_ge_le_lintegral₀ hf (ENNReal.ofReal ((t * B) ^ m))
  have hsub : {ω | t * B ≤ |X ω|} ⊆
      {ω | ENNReal.ofReal ((t * B) ^ m) ≤ ENNReal.ofReal (|X ω| ^ m)} := by
    intro ω hω
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hω m)
  rw [ENNReal.ofReal_div_of_pos hpos]
  refine (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hpos).ne')
    (Or.inl ENNReal.ofReal_ne_top)).2 ?_
  calc μ {ω | t * B ≤ |X ω|} * ENNReal.ofReal ((t * B) ^ m)
      = ENNReal.ofReal ((t * B) ^ m) * μ {ω | t * B ≤ |X ω|} := mul_comm _ _
    _ ≤ ENNReal.ofReal ((t * B) ^ m) *
        μ {ω | ENNReal.ofReal ((t * B) ^ m) ≤ ENNReal.ofReal (|X ω| ^ m)} := by
          gcongr
    _ ≤ _ := h1
    _ ≤ _ := hmom

/-- The optimised Markov exponent: with `s = t ^ (1 / r)` and `p = ⌊s / (e K)⌋ ≥ 1`, the bound
`((K p) ^ r / t) ^ (2 p)` is at most `C exp (-s / C)`, where `C = e ^ (2 r) + 3 + 3 K + 3 K / r`. -/
private lemma largeDev_real_bound {K r : ℝ} (hK : 0 < K) (hr : 0 < r) {t : ℝ} (ht : 0 < t)
    {p : ℕ} (hp1 : (p : ℝ) ≤ t ^ (1 / r) / (Real.exp 1 * K))
    (hp2 : t ^ (1 / r) / (Real.exp 1 * K) < p + 1) :
    ((K * p) ^ r / t) ^ (2 * p) ≤
      (Real.exp (2 * r) + 3 + 3 * K + 3 * K / r) *
        Real.exp (-t ^ (1 / r) / (Real.exp (2 * r) + 3 + 3 * K + 3 * K / r)) := by
  set s : ℝ := t ^ (1 / r) with hs
  set e : ℝ := Real.exp 1 with he
  set C : ℝ := Real.exp (2 * r) + 3 + 3 * K + 3 * K / r with hC
  have hs0 : 0 < s := Real.rpow_pos_of_pos ht _
  have he0 : 0 < e := Real.exp_pos 1
  have he3 : e < 3 := by
    have := Real.exp_one_lt_d9
    rw [he]; linarith
  have hsr : s ^ r = t := by
    rw [hs, ← Real.rpow_mul ht.le, one_div, inv_mul_cancel₀ hr.ne', Real.rpow_one]
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hC0 : 0 < C := by positivity
  have hKp : K * p ≤ s * Real.exp (-1) := by
    have h1 : K * p ≤ K * (s / (e * K)) := by gcongr
    have h2 : K * (s / (e * K)) = s * Real.exp (-1) := by
      rw [Real.exp_neg, ← he]
      field_simp
    exact h1.trans h2.le
  have h1 : (K * p) ^ r ≤ t * Real.exp (-r) := by
    calc (K * p) ^ r ≤ (s * Real.exp (-1)) ^ r :=
          Real.rpow_le_rpow (by positivity) hKp hr.le
      _ = s ^ r * (Real.exp (-1)) ^ r := Real.mul_rpow hs0.le (Real.exp_pos _).le
      _ = t * Real.exp (-r) := by
          rw [hsr, ← Real.exp_mul]
          ring_nf
  have h2 : (K * p) ^ r / t ≤ Real.exp (-r) := by
    rw [div_le_iff₀ ht]
    linarith
  have h3 : ((K * p) ^ r / t) ^ (2 * p) ≤ Real.exp (-r) ^ (2 * p) :=
    pow_le_pow_left₀ (by positivity) h2 _
  have h4 : Real.exp (-r) ^ (2 * p) = Real.exp (-(2 * r * p)) := by
    rw [← Real.exp_nat_mul]
    push_cast
    ring_nf
  have h5 : s / C ≤ 2 * r * (s / (e * K)) := by
    have h6 : e * K ≤ 2 * r * C := by
      have : 2 * r * (3 * K / r) = 6 * K := by field_simp; ring
      have h7 : 0 ≤ 2 * r * (Real.exp (2 * r) + 3 + 3 * K) := by positivity
      nlinarith
    rw [div_le_iff₀ hC0]
    have : 2 * r * (s / (e * K)) * C = s * (2 * r * C) / (e * K) := by
      field_simp
    rw [this, le_div_iff₀ (by positivity)]
    nlinarith
  have h8 : Real.exp (-(2 * r * p)) ≤ Real.exp (2 * r) * Real.exp (-s / C) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have : -s / C = -(s / C) := by ring
    rw [this]
    nlinarith
  have h9 : Real.exp (2 * r) ≤ C := by
    have : 0 ≤ 3 + 3 * K + 3 * K / r := by positivity
    rw [hC]; linarith
  calc ((K * p) ^ r / t) ^ (2 * p) ≤ Real.exp (-r) ^ (2 * p) := h3
    _ = Real.exp (-(2 * r * p)) := h4
    _ ≤ Real.exp (2 * r) * Real.exp (-s / C) := h8
    _ ≤ C * Real.exp (-s / C) := by gcongr

/-- The bound `C exp (-s / C)` is at least one when `s < e K`. -/
private lemma largeDev_small_bound {K r : ℝ} (hK : 0 < K) (hr : 0 < r) {s : ℝ}
    (hs : s < Real.exp 1 * K) :
    1 ≤ (Real.exp (2 * r) + 3 + 3 * K + 3 * K / r) *
        Real.exp (-s / (Real.exp (2 * r) + 3 + 3 * K + 3 * K / r)) := by
  set C : ℝ := Real.exp (2 * r) + 3 + 3 * K + 3 * K / r with hC
  have he3 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hC0 : 0 < C := by positivity
  have hCK : 3 * K ≤ C := by
    have : 0 < Real.exp (2 * r) + 3 + 3 * K / r := by positivity
    rw [hC]; linarith
  have hC3 : 3 ≤ C := by
    have : 0 < Real.exp (2 * r) + 3 * K + 3 * K / r := by positivity
    rw [hC]; linarith
  have h1 : s / C ≤ 1 := by
    rw [div_le_one hC0]
    nlinarith
  have h2 : Real.exp (-1) ≤ Real.exp (-s / C) := by
    apply Real.exp_le_exp.2
    have : -s / C = -(s / C) := by ring
    rw [this]; linarith
  have h3 : 1 ≤ C * Real.exp (-1) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, one_le_div (Real.exp_pos 1)]
    linarith
  calc (1 : ℝ) ≤ C * Real.exp (-1) := h3
    _ ≤ C * Real.exp (-s / C) := by gcongr

/-- A nonnegative measurable function that is a.e. bounded and whose `m`-th power has
Bochner integral at most `R` has lower integral of `|Y| ^ m` at most `R`. -/
private lemma largeDev_lintegral_le {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hm : Measurable Y) (h0 : ∀ ω, 0 ≤ Y ω) {M : ℝ}
    (hb : ∀ᵐ ω ∂μ, Y ω ≤ M) (m : ℕ) {R : ℝ} (h : ∫ ω, Y ω ^ m ∂μ ≤ R) :
    ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ m) ∂μ ≤ ENNReal.ofReal R := by
  have hint : Integrable (fun ω => Y ω ^ m) μ :=
    Integrable.of_bound (hm.pow_const m).aestronglyMeasurable (M ^ m) (by
      filter_upwards [hb] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (h0 ω) m)]
      exact pow_le_pow_left₀ (h0 ω) hω m)
  simp only [abs_of_nonneg (h0 _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => pow_nonneg (h0 ω) m)]
  exact ENNReal.ofReal_le_ofReal h

/-- High-moment Markov with optimised exponent: moments growing like
`(K p)^{2 r p} B^{2p}` give a tail `C exp(-t^{1/r}/C)`. -/
theorem measure_ge_le_of_moment_growth (K r : ℝ) (hK : 0 < K) (hr : 0 < r) :
    ∃ C > 0, ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : Ω → ℝ) (B : ℝ), AEMeasurable X μ → 0 < B →
      (∀ p : ℕ, 1 ≤ p → ∫⁻ ω, ENNReal.ofReal (|X ω| ^ (2 * p)) ∂μ ≤
        ENNReal.ofReal ((K * p) ^ (2 * r * p) * B ^ (2 * p))) →
      ∀ t : ℝ, 0 < t → μ {ω | t * B ≤ |X ω|} ≤ ENNReal.ofReal (C * Real.exp (-t ^ (1 / r) / C)) := by
  refine ⟨Real.exp (2 * r) + 3 + 3 * K + 3 * K / r, by positivity, ?_⟩
  intro Ω _ μ _ X B hX hB hmom t ht
  by_cases hp : 1 ≤ t ^ (1 / r) / (Real.exp 1 * K)
  · set p : ℕ := ⌊t ^ (1 / r) / (Real.exp 1 * K)⌋₊ with hpdef
    have hp1 : 1 ≤ p := Nat.le_floor (by simpa using hp)
    have hs0 : 0 < t ^ (1 / r) := Real.rpow_pos_of_pos ht _
    have hp0 : 0 ≤ t ^ (1 / r) / (Real.exp 1 * K) := by positivity
    refine (largeDev_markov_pow hX hB ht (2 * p) (hmom p hp1)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hpos : (0 : ℝ) < K * p := by
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp1
      positivity
    have e1 : (K * p) ^ (2 * r * p) = ((K * p) ^ r) ^ (2 * p) := by
      rw [← Real.rpow_natCast ((K * p) ^ r) (2 * p), ← Real.rpow_mul hpos.le]
      congr 1
      push_cast
      ring
    have e2 : (K * p) ^ (2 * r * p) * B ^ (2 * p) / (t * B) ^ (2 * p) =
        ((K * p) ^ r / t) ^ (2 * p) := by
      rw [e1, mul_pow, div_pow, mul_div_mul_right _ _ (pow_ne_zero _ hB.ne')]
    rw [e2]
    exact largeDev_real_bound hK hr ht (Nat.floor_le hp0) (Nat.lt_floor_add_one _)
  · have hlt : t ^ (1 / r) < Real.exp 1 * K := by
      have h := not_le.1 hp
      rwa [div_lt_one (by positivity)] at h
    exact prob_le_one.trans (ENNReal.one_le_ofReal.2 (largeDev_small_bound hK hr hlt))

/-- Large deviation for linear forms ((3.17)–(3.19) of [15]). -/
theorem largeDev_linear : ∃ C > 0, ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (n : ℕ) (a : Fin n → Ω → ℝ), iIndepFun a μ →
    (∀ i, Measurable (a i)) → (∀ i, ∫ ω, a i ω ∂μ = 0) → ∀ q s2 : ℝ, 0 < q →
    (∀ i, ∀ᵐ ω ∂μ, |a i ω| ≤ q⁻¹) → (∀ i, ∫ ω, a i ω ^ 2 ∂μ ≤ s2) → ∀ (A : Fin n → ℂ),
    0 < (⨆ i, ‖A i‖) / q + Real.sqrt (s2 * ∑ i, ‖A i‖ ^ 2) → ∀ t : ℝ, 0 < t →
      μ {ω | t * ((⨆ i, ‖A i‖) / q + Real.sqrt (s2 * ∑ i, ‖A i‖ ^ 2)) ≤ ‖∑ i, A i * a i ω‖} ≤
        ENNReal.ofReal (C * Real.exp (-t / C)) := by
  obtain ⟨C₁, hC₁, hlin⟩ := moment_linear_le
  obtain ⟨C, hC, hM⟩ := measure_ge_le_of_moment_growth C₁ 1 hC₁ one_pos
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ _ n a hind hmeas h0 q s2 hq hbd hvar A hpos t ht
  have hall : ∀ᵐ ω ∂μ, ∀ i, |a i ω| ≤ q⁻¹ := ae_all_iff.2 hbd
  have hXm : Measurable fun ω => ‖∑ i, A i * (a i ω : ℂ)‖ :=
    (Finset.measurable_sum _ fun i _ =>
      (Complex.measurable_ofReal.comp (hmeas i)).const_mul (A i)).norm
  have hXb : ∀ᵐ ω ∂μ, ‖∑ i, A i * (a i ω : ℂ)‖ ≤ ∑ i, ‖A i‖ * q⁻¹ := by
    filter_upwards [hall] with ω hω
    calc ‖∑ i, A i * (a i ω : ℂ)‖ ≤ ∑ i, ‖A i * (a i ω : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖A i‖ * q⁻¹ := Finset.sum_le_sum fun i _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hω i) (norm_nonneg _)
  have h := hM μ (fun ω => ‖∑ i, A i * (a i ω : ℂ)‖)
    ((⨆ i, ‖A i‖) / q + Real.sqrt (s2 * ∑ i, ‖A i‖ ^ 2)) hXm.aemeasurable hpos (by
      intro p hp
      have e : (C₁ * (p : ℝ)) ^ (2 * (1 : ℝ) * (p : ℝ)) = (C₁ * p) ^ (2 * p) := by
        rw [show 2 * (1 : ℝ) * (p : ℝ) = ((2 * p : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      rw [e]
      exact largeDev_lintegral_le hXm (fun _ => norm_nonneg _) hXb (2 * p)
        (hlin μ n a hind hmeas h0 q s2 hq hbd hvar A p hp)) t ht
  have e : t ^ (1 / (1 : ℝ)) = t := by norm_num
  rw [e] at h
  simpa only [abs_norm] using h

/-- Large deviation for off-diagonal quadratic forms ((3.21) of [15]). -/
theorem largeDev_quadratic (K : ℝ) (hK : 0 < K) : ∃ C > 0, ∀ {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n N : ℕ) (a : Fin n → Ω → ℝ), iIndepFun a μ →
    (∀ i, Measurable (a i)) → (∀ i, ∫ ω, a i ω ∂μ = 0) → ∀ q : ℝ, 0 < q → 1 ≤ q → n ≤ N →
    (∀ i, ∀ᵐ ω ∂μ, |a i ω| ≤ q⁻¹) → (∀ i, ∫ ω, a i ω ^ 2 ∂μ ≤ K / N) →
    ∀ (B : Fin n → Fin n → ℂ),
    0 < (⨆ i, ⨆ j, if i = j then 0 else ‖B i j‖) / q +
      Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, if i = j then 0 else ‖B i j‖ ^ 2) →
    ∀ t : ℝ, 0 < t →
      μ {ω | t * ((⨆ i, ⨆ j, if i = j then 0 else ‖B i j‖) / q +
          Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, if i = j then 0 else ‖B i j‖ ^ 2)) ≤
        ‖∑ i, ∑ j, (if i = j then 0 else B i j * a i ω * a j ω)‖} ≤
        ENNReal.ofReal (C * Real.exp (-Real.sqrt t / C)) := by
  obtain ⟨C₂, hC₂, hquad⟩ := moment_quadratic_le K hK
  obtain ⟨C, hC, hM⟩ := measure_ge_le_of_moment_growth C₂ 2 hC₂ two_pos
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ _ n N a hind hmeas h0 q hq hq1 hnN hbd hvar B hpos t ht
  have hall : ∀ᵐ ω ∂μ, ∀ i, |a i ω| ≤ q⁻¹ := ae_all_iff.2 hbd
  have hXm : Measurable fun ω =>
      ‖∑ i, ∑ j, (if i = j then 0 else B i j * (a i ω : ℂ) * (a j ω : ℂ))‖ := by
    refine (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_).norm
    by_cases hij : i = j
    · simp only [hij, ite_true]
      exact measurable_const
    · simp only [hij, ite_false]
      exact (((Complex.measurable_ofReal.comp (hmeas i)).const_mul (B i j))).mul
        (Complex.measurable_ofReal.comp (hmeas j))
  have hXb : ∀ᵐ ω ∂μ,
      ‖∑ i, ∑ j, (if i = j then 0 else B i j * (a i ω : ℂ) * (a j ω : ℂ))‖ ≤
        ∑ i, ∑ j, ‖B i j‖ * q⁻¹ * q⁻¹ := by
    filter_upwards [hall] with ω hω
    calc ‖∑ i, ∑ j, (if i = j then 0 else B i j * (a i ω : ℂ) * (a j ω : ℂ))‖
        ≤ ∑ i, ‖∑ j, (if i = j then 0 else B i j * (a i ω : ℂ) * (a j ω : ℂ))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖(if i = j then 0 else B i j * (a i ω : ℂ) * (a j ω : ℂ))‖ :=
          Finset.sum_le_sum fun i _ => norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖B i j‖ * q⁻¹ * q⁻¹ := Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => by
            have hqi : 0 ≤ q⁻¹ := inv_nonneg.2 hq.le
            split_ifs
            · simp only [norm_zero]
              positivity
            · rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
                Real.norm_eq_abs]
              exact mul_le_mul (mul_le_mul_of_nonneg_left (hω i) (norm_nonneg _)) (hω j)
                (abs_nonneg _) (by positivity)
  have h := hM μ (fun ω => ‖∑ i, ∑ j, (if i = j then 0 else B i j * (a i ω : ℂ) * (a j ω : ℂ))‖)
    ((⨆ i, ⨆ j, if i = j then 0 else ‖B i j‖) / q +
      Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, if i = j then 0 else ‖B i j‖ ^ 2))
    hXm.aemeasurable hpos (by
      intro p hp
      have e : (C₂ * (p : ℝ)) ^ (2 * (2 : ℝ) * (p : ℝ)) = (C₂ * p) ^ (4 * p) := by
        rw [show 2 * (2 : ℝ) * (p : ℝ) = ((4 * p : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      rw [e]
      exact largeDev_lintegral_le hXm (fun _ => norm_nonneg _) hXb (2 * p)
        (hquad μ n N a hind hmeas h0 q hq hq1 hnN hbd hvar B p hp)) t ht
  have e : t ^ (1 / (2 : ℝ)) = Real.sqrt t := (Real.sqrt_eq_rpow t).symm
  rw [e] at h
  simpa only [abs_norm] using h

/-- (3.22) of [15] in tail form, with the Hilbert–Schmidt term over all `(i, j)`. -/
theorem largeDev_bilinear (K : ℝ) (hK : 0 < K) : ∃ C > 0, ∀ {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n N : ℕ) (a b : Fin n → Ω → ℝ),
    iIndepFun (Sum.elim a b) μ → (∀ i, Measurable (a i)) → (∀ i, Measurable (b i)) →
    (∀ i, ∫ ω, a i ω ∂μ = 0) → (∀ i, ∫ ω, b i ω ∂μ = 0) → ∀ q : ℝ, 0 < q → 1 ≤ q → n ≤ N →
    (∀ i, ∀ᵐ ω ∂μ, |a i ω| ≤ q⁻¹) → (∀ i, ∀ᵐ ω ∂μ, |b i ω| ≤ q⁻¹) →
    (∀ i, ∫ ω, a i ω ^ 2 ∂μ ≤ K / N) → (∀ i, ∫ ω, b i ω ^ 2 ∂μ ≤ K / N) →
    ∀ (B : Fin n → Fin n → ℂ),
    0 < (⨆ i, ‖B i i‖) / q ^ 2 + (⨆ i, ⨆ j, if i = j then 0 else ‖B i j‖) / q +
      Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, ‖B i j‖ ^ 2) → ∀ t : ℝ, 0 < t →
      μ {ω | t * ((⨆ i, ‖B i i‖) / q ^ 2 + (⨆ i, ⨆ j, if i = j then 0 else ‖B i j‖) / q +
          Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, ‖B i j‖ ^ 2)) ≤
        ‖∑ i, ∑ j, B i j * a i ω * b j ω‖} ≤ ENNReal.ofReal (C * Real.exp (-Real.sqrt t / C)) := by
  obtain ⟨C₃, hC₃, hbil⟩ := moment_bilinear_le K hK
  obtain ⟨C, hC, hM⟩ := measure_ge_le_of_moment_growth C₃ 2 hC₃ two_pos
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ _ n N a b hind ha hb ha0 hb0 q hq hq1 hnN hbda hbdb hvara hvarb B hpos t ht
  have halla : ∀ᵐ ω ∂μ, ∀ i, |a i ω| ≤ q⁻¹ := ae_all_iff.2 hbda
  have hallb : ∀ᵐ ω ∂μ, ∀ i, |b i ω| ≤ q⁻¹ := ae_all_iff.2 hbdb
  have hXm : Measurable fun ω => ‖∑ i, ∑ j, B i j * (a i ω : ℂ) * (b j ω : ℂ)‖ :=
    (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      (((Complex.measurable_ofReal.comp (ha i)).const_mul (B i j))).mul
        (Complex.measurable_ofReal.comp (hb j))).norm
  have hXb : ∀ᵐ ω ∂μ, ‖∑ i, ∑ j, B i j * (a i ω : ℂ) * (b j ω : ℂ)‖ ≤
      ∑ i, ∑ j, ‖B i j‖ * q⁻¹ * q⁻¹ := by
    filter_upwards [halla, hallb] with ω hωa hωb
    calc ‖∑ i, ∑ j, B i j * (a i ω : ℂ) * (b j ω : ℂ)‖
        ≤ ∑ i, ‖∑ j, B i j * (a i ω : ℂ) * (b j ω : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖B i j * (a i ω : ℂ) * (b j ω : ℂ)‖ :=
          Finset.sum_le_sum fun i _ => norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖B i j‖ * q⁻¹ * q⁻¹ := Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => by
            have hqi : 0 ≤ q⁻¹ := inv_nonneg.2 hq.le
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs]
            exact mul_le_mul (mul_le_mul_of_nonneg_left (hωa i) (norm_nonneg _)) (hωb j)
              (abs_nonneg _) (by positivity)
  have h := hM μ (fun ω => ‖∑ i, ∑ j, B i j * (a i ω : ℂ) * (b j ω : ℂ)‖)
    ((⨆ i, ‖B i i‖) / q ^ 2 + (⨆ i, ⨆ j, if i = j then 0 else ‖B i j‖) / q +
      Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, ‖B i j‖ ^ 2))
    hXm.aemeasurable hpos (by
      intro p hp
      have e : (C₃ * (p : ℝ)) ^ (2 * (2 : ℝ) * (p : ℝ)) = (C₃ * p) ^ (4 * p) := by
        rw [show 2 * (2 : ℝ) * (p : ℝ) = ((4 * p : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      rw [e]
      exact largeDev_lintegral_le hXm (fun _ => norm_nonneg _) hXb (2 * p)
        (hbil μ n N a b hind ha hb ha0 hb0 q hq hq1 hnN hbda hbdb hvara hvarb B p hp)) t ht
  have e : t ^ (1 / (2 : ℝ)) = Real.sqrt t := (Real.sqrt_eq_rpow t).symm
  rw [e] at h
  simpa only [abs_norm] using h

/-! ### Checks -/

/-- The fair coin law on `Bool`. -/
private def largeDevCoin : Measure Bool := (2 : ENNReal)⁻¹ • Measure.count

private instance : IsProbabilityMeasure largeDevCoin := by
  constructor
  simp only [largeDevCoin, Measure.smul_apply, Measure.count_univ, smul_eq_mul]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- The Rademacher sign attached to a coin. -/
private def largeDevSign (b : Bool) : ℝ := if b then 1 else -1

private lemma largeDev_integral_coin (f : Bool → ℝ) :
    ∫ b, f b ∂largeDevCoin = (f true + f false) / 2 := by
  rw [largeDevCoin, integral_smul_measure, integral_count]
  simp
  ring

private lemma largeDev_integral_rad {ι : Type} [Fintype ι] (i : ι)
    (f : ℝ → ℝ) :
    ∫ ω, f (largeDevSign (ω i)) ∂(Measure.pi fun _ : ι => largeDevCoin) =
      (f 1 + f (-1)) / 2 := by
  classical
  have := integral_comp_eval (μ := fun _ : ι => largeDevCoin) (i := i)
    (f := fun b => f (largeDevSign b)) (Measurable.of_discrete).aestronglyMeasurable
  rw [this, largeDev_integral_coin]
  simp [largeDevSign]

private lemma largeDev_sign_abs (b : Bool) : |largeDevSign b| = 1 := by
  cases b <;> simp [largeDevSign]

/-- Nondegenerate instance of the Markov step: a fair sign `X = ±1`, `B = 1`, `K = r = 1`
(the moment bound is attained at `p = 1`). -/
example : ∃ C > 0, ∀ t : ℝ, 0 < t →
    largeDevCoin {b | t * 1 ≤ |largeDevSign b|} ≤
      ENNReal.ofReal (C * Real.exp (-t ^ (1 / (1 : ℝ)) / C)) := by
  obtain ⟨C, hC, h⟩ := measure_ge_le_of_moment_growth 1 1 one_pos one_pos
  refine ⟨C, hC, fun t ht => h largeDevCoin largeDevSign 1
    (Measurable.of_discrete).aemeasurable one_pos ?_ t ht⟩
  intro p hp
  simp only [largeDev_sign_abs, one_pow, lintegral_const, measure_univ, mul_one,
    ENNReal.ofReal_one]
  refine ENNReal.one_le_ofReal.2 ?_
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  simpa using Real.one_le_rpow (by simpa using hp1) (by positivity : (0 : ℝ) ≤ 2 * 1 * (p : ℝ))

/-- Nondegenerate instance of the linear bound: two independent fair signs (`n = 2`), `q = 1`,
`s2 = 1` (both bounds attained), coefficients `(1, 1)`. -/
example : ∃ C > 0, ∀ t : ℝ, 0 < t →
    (Measure.pi fun _ : Fin 2 => largeDevCoin)
      {ω | t * ((⨆ i, ‖![(1 : ℂ), 1] i‖) / 1 + Real.sqrt (1 * ∑ i, ‖![(1 : ℂ), 1] i‖ ^ 2)) ≤
        ‖∑ i, ![(1 : ℂ), 1] i * largeDevSign (ω i)‖} ≤
      ENNReal.ofReal (C * Real.exp (-t / C)) := by
  obtain ⟨C, hC, h⟩ := largeDev_linear
  refine ⟨C, hC, fun t ht => h (Measure.pi fun _ : Fin 2 => largeDevCoin) 2
    (fun i ω => largeDevSign (ω i)) ?_ ?_ ?_ 1 1 one_pos ?_ ?_ ![(1 : ℂ), 1] ?_ t ht⟩
  · exact iIndepFun_pi (μ := fun _ : Fin 2 => largeDevCoin) (X := fun _ => largeDevSign)
      (fun _ => (Measurable.of_discrete).aemeasurable)
  · intro i; exact (Measurable.of_discrete (f := largeDevSign)).comp (measurable_pi_apply i)
  · intro i
    simpa using largeDev_integral_rad i id
  · intro i
    refine Eventually.of_forall fun ω => ?_
    simp [largeDev_sign_abs]
  · intro i
    rw [largeDev_integral_rad i (fun x => x ^ 2)]
    norm_num
  · refine add_pos_of_nonneg_of_pos
      (div_nonneg (Real.iSup_nonneg fun i => norm_nonneg _) zero_le_one) (Real.sqrt_pos.2 ?_)
    simp [Fin.sum_univ_two]

/-- Nondegenerate instance of the quadratic bound: two independent fair signs (`n = N = 2`),
`K = 2`, `q = 1` (the bounds `|a i| ≤ q⁻¹` and `E a i ^ 2 ≤ K / N` are both attained), the
off-diagonal matrix `![![0, 1], ![1, 0]]`. -/
example : ∃ C > 0, ∀ t : ℝ, 0 < t →
    (Measure.pi fun _ : Fin 2 => largeDevCoin)
      {ω | t * ((⨆ i, ⨆ j, if i = j then 0 else ‖![![(0 : ℂ), 1], ![1, 0]] i j‖) / 1 +
          Real.sqrt ((((2 : ℕ) : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, if i = j then 0 else
            ‖![![(0 : ℂ), 1], ![1, 0]] i j‖ ^ 2)) ≤
        ‖∑ i, ∑ j, (if i = j then 0 else ![![(0 : ℂ), 1], ![1, 0]] i j *
          largeDevSign (ω i) * largeDevSign (ω j))‖} ≤
      ENNReal.ofReal (C * Real.exp (-Real.sqrt t / C)) := by
  obtain ⟨C, hC, h⟩ := largeDev_quadratic 2 two_pos
  refine ⟨C, hC, fun t ht => h (Measure.pi fun _ : Fin 2 => largeDevCoin) 2 2
    (fun i ω => largeDevSign (ω i)) ?_ ?_ ?_ 1 one_pos le_rfl le_rfl ?_ ?_ _ ?_ t ht⟩
  · exact iIndepFun_pi (μ := fun _ : Fin 2 => largeDevCoin) (X := fun _ => largeDevSign)
      (fun _ => (Measurable.of_discrete).aemeasurable)
  · intro i; exact (Measurable.of_discrete (f := largeDevSign)).comp (measurable_pi_apply i)
  · intro i
    simpa using largeDev_integral_rad i id
  · intro i
    refine Eventually.of_forall fun ω => ?_
    simp [largeDev_sign_abs]
  · intro i
    rw [largeDev_integral_rad i (fun x => x ^ 2)]
    norm_num
  · refine add_pos_of_nonneg_of_pos
      (div_nonneg (Real.iSup_nonneg fun i => Real.iSup_nonneg fun j => by split_ifs <;> simp)
        zero_le_one) (Real.sqrt_pos.2 ?_)
    simp [Fin.sum_univ_two]

/-- Nondegenerate instance of the bilinear bound: four independent fair signs (`n = N = 2`),
`K = 2`, `q = 1` (the bounds `|a i| ≤ q⁻¹` and `E a i ^ 2 ≤ K / N` are both attained), the matrix
of ones (so that the diagonal, off-diagonal and Hilbert–Schmidt terms are all nonzero). -/
example : ∃ C > 0, ∀ t : ℝ, 0 < t →
    (Measure.pi fun _ : Fin 2 ⊕ Fin 2 => largeDevCoin)
      {ω | t * ((⨆ i, ‖![![(1 : ℂ), 1], ![1, 1]] i i‖) / 1 ^ 2 +
          (⨆ i, ⨆ j, if i = j then 0 else ‖![![(1 : ℂ), 1], ![1, 1]] i j‖) / 1 +
          Real.sqrt ((((2 : ℕ) : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, ‖![![(1 : ℂ), 1], ![1, 1]] i j‖ ^ 2)) ≤
        ‖∑ i, ∑ j, ![![(1 : ℂ), 1], ![1, 1]] i j * largeDevSign (ω (Sum.inl i)) *
          largeDevSign (ω (Sum.inr j))‖} ≤
      ENNReal.ofReal (C * Real.exp (-Real.sqrt t / C)) := by
  obtain ⟨C, hC, h⟩ := largeDev_bilinear 2 two_pos
  refine ⟨C, hC, fun t ht => h (Measure.pi fun _ : Fin 2 ⊕ Fin 2 => largeDevCoin) 2 2
    (fun i ω => largeDevSign (ω (Sum.inl i))) (fun i ω => largeDevSign (ω (Sum.inr i)))
    ?_ ?_ ?_ ?_ ?_ 1 one_pos le_rfl le_rfl ?_ ?_ ?_ ?_ _ ?_ t ht⟩
  · have h := iIndepFun_pi (ι := Fin 2 ⊕ Fin 2) (μ := fun _ => largeDevCoin)
      (X := fun _ => largeDevSign) (fun _ => (Measurable.of_discrete).aemeasurable)
    have e : Sum.elim (fun (i : Fin 2) (ω : Fin 2 ⊕ Fin 2 → Bool) =>
        largeDevSign (ω (Sum.inl i))) (fun (i : Fin 2) (ω : Fin 2 ⊕ Fin 2 → Bool) =>
        largeDevSign (ω (Sum.inr i))) =
        fun (s : Fin 2 ⊕ Fin 2) (ω : Fin 2 ⊕ Fin 2 → Bool) => largeDevSign (ω s) := by
      ext s ω
      rcases s with i | i <;> rfl
    rw [e]
    exact h
  · intro i; exact (Measurable.of_discrete (f := largeDevSign)).comp
      (measurable_pi_apply (Sum.inl i))
  · intro i; exact (Measurable.of_discrete (f := largeDevSign)).comp
      (measurable_pi_apply (Sum.inr i))
  · intro i
    simpa using largeDev_integral_rad (Sum.inl i) id
  · intro i
    simpa using largeDev_integral_rad (Sum.inr i) id
  · intro i
    refine Eventually.of_forall fun ω => ?_
    simp [largeDev_sign_abs]
  · intro i
    refine Eventually.of_forall fun ω => ?_
    simp [largeDev_sign_abs]
  · intro i
    rw [largeDev_integral_rad (Sum.inl i) (fun x => x ^ 2)]
    norm_num
  · intro i
    rw [largeDev_integral_rad (Sum.inr i) (fun x => x ^ 2)]
    norm_num
  · refine add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg ?_ ?_) (Real.sqrt_nonneg _)
    · refine div_pos ?_ (by norm_num)
      have h0 : (0 : ℝ) < ‖![![(1 : ℂ), 1], ![1, 1]] 0 0‖ := by simp
      exact h0.trans_le (le_ciSup (f := fun i => ‖![![(1 : ℂ), 1], ![1, 1]] i i‖)
        (Finite.bddAbove_range _) 0)
    · exact div_nonneg (Real.iSup_nonneg fun i => Real.iSup_nonneg fun j => by split_ifs <;> simp)
        zero_le_one

#print axioms measure_ge_le_of_moment_growth
#print axioms largeDev_linear
#print axioms largeDev_quadratic
#print axioms largeDev_bilinear

end WEdgeNS
