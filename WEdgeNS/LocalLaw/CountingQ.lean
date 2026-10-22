import WEdgeNS.Semicircle.Counting

/-!
# Counting function from the averaged local law with the `q`-terms
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-! ### The Stieltjes transform of `H` as a sum over eigenvalues -/

/-! ### The semicircle side -/

private lemma countingQ_continuous_rhoSc : Continuous rhoSc := by
  unfold rhoSc
  fun_prop

private lemma countingQ_integrable_rhoSc : Integrable rhoSc := by
  refine countingQ_continuous_rhoSc.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := -2) (b := 2)) fun x hx => ?_
  unfold rhoSc
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rw [Real.sqrt_eq_zero_of_nonpos (by rcases hx with h | h <;> nlinarith), zero_div]

/-! ### The empirical side -/

/-! ### Elementary facts on `n_sc` and `n` -/

/-- `n_sc(b) - n_sc(a) = ∫_a^b ρ_sc`. -/
private lemma countingQ_nsc_sub (a b : ℝ) : nsc b - nsc a = ∫ x in a..b, rhoSc x := by
  have h := intervalIntegral.integral_Iic_sub_Iic (f := rhoSc) (μ := volume) (a := a) (b := b)
    countingQ_integrable_rhoSc.integrableOn countingQ_integrable_rhoSc.integrableOn
  unfold nsc
  exact h

private lemma countingQ_rhoSc_nonneg (x : ℝ) : 0 ≤ rhoSc x := by
  unfold rhoSc
  positivity

private lemma countingQ_nsc_nonneg (E : ℝ) : 0 ≤ nsc E :=
  setIntegral_nonneg measurableSet_Iic fun x _ => countingQ_rhoSc_nonneg x

private lemma countingQ_nsc_le_one (E : ℝ) : nsc E ≤ 1 := by
  have h := countingQ_nsc_sub E (max E 2)
  have h1 : 0 ≤ ∫ x in E..max E 2, rhoSc x :=
    intervalIntegral.integral_nonneg (le_max_left _ _) fun x _ => countingQ_rhoSc_nonneg x
  rw [nsc_eq_one (le_max_right _ _)] at h
  linarith

private lemma countingQ_countFn_nonneg {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (E : ℝ) : 0 ≤ countFn hH E := by
  unfold countFn
  positivity

private lemma countingQ_countFn_le_one {N : ℕ} (hN : 0 < N) {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (E : ℝ) : countFn hH E ≤ 1 := by
  unfold countFn
  rw [div_le_one (by exact_mod_cast hN)]
  exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)

/-- `|∫_c^d Im m_sc(x + iη) dx - π (n_sc(d) - n_sc(c))| ≤ 2η`. -/
private lemma countingQ_sc_nsc (c d : ℝ) {η : ℝ} (hη : 0 < η) :
    |(∫ x in c..d, (msc (x + η * Complex.I)).im) - Real.pi * (nsc d - nsc c)| ≤ 2 * η := by
  rw [countingQ_nsc_sub]
  exact abs_integral_im_msc_sub_pi_mul_integral_rhoSc_le c d hη

/-- `π |n_sc(E ± t) - n_sc(E)| ≤ t`, since `ρ_sc ≤ 1/π`. -/
private lemma countingQ_nsc_shift (E t : ℝ) (ht : 0 ≤ t) :
    |Real.pi * (nsc (E + t) - nsc E)| ≤ t ∧ |Real.pi * (nsc (E - t) - nsc E)| ≤ t := by
  rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, countingQ_nsc_sub, countingQ_nsc_sub]
  constructor
  · refine (pi_mul_abs_integral_rhoSc_le _ _).trans_eq ?_
    rw [add_sub_cancel_left, abs_of_nonneg ht]
  · refine (pi_mul_abs_integral_rhoSc_le _ _).trans_eq ?_
    rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg ht]

/-- `|u| ≤ M` from `π u ≤ M` and `-π u ≤ M`. -/
private lemma countingQ_abs_le_of_pi {u M : ℝ} (h1 : Real.pi * u ≤ M)
    (h2 : Real.pi * (-u) ≤ M) : |u| ≤ M := by
  have hpi := Real.pi_gt_three
  rcases le_or_gt 0 u with h | h
  · rw [abs_of_nonneg h]
    nlinarith
  · rw [abs_of_neg h]
    nlinarith

/-! ### Elementary inequalities -/

/-- `p² t ≤ p³ + t³` for `p, t ≥ 0`. -/
private lemma countingQ_pow3 {p t : ℝ} (hp : 0 ≤ p) (ht : 0 ≤ t) :
    p ^ 2 * t ≤ p ^ 3 + t ^ 3 := by
  rcases le_total t p with h | h
  · nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg p), pow_nonneg ht 3]
  · nlinarith [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp h 2) ht, pow_nonneg hp 3]

/-- `(√x)³ ≤ x` for `0 ≤ x ≤ 1`. -/
private lemma countingQ_sqrt_cube {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sqrt x ^ 3 ≤ x := by
  have h1 : Real.sqrt x ≤ 1 := (Real.sqrt_le_sqrt hx1).trans_eq Real.sqrt_one
  have h2 := Real.sq_sqrt hx
  have h3 := Real.sqrt_nonneg x
  have e : Real.sqrt x ^ 3 = Real.sqrt x ^ 2 * Real.sqrt x := by ring
  rw [e, h2]
  nlinarith

/-- If `U t² > 1/2` with `U ≥ 1` and `t ≥ 0`, then `3 U² t³ ≥ 1`. -/
private lemma countingQ_cube {U t : ℝ} (hU : 1 ≤ U) (ht : 0 ≤ t) (h : 1 / 2 < U * t ^ 2) :
    1 ≤ 3 * U ^ 2 * t ^ 3 := by
  have h3 : (1 / 2 : ℝ) ^ 3 < (U * t ^ 2) ^ 3 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  have hv : 0 ≤ (U * t ^ 2) ^ 3 := by positivity
  have e : (U ^ 2 * t ^ 3) ^ 2 = U * (U * t ^ 2) ^ 3 := by ring
  have h4 : (U * t ^ 2) ^ 3 ≤ (U ^ 2 * t ^ 3) ^ 2 := by
    rw [e]
    nlinarith
  have hw : 0 ≤ U ^ 2 * t ^ 3 := by positivity
  nlinarith

/-- `∫_a^b (√y)⁻¹ dy = 2√b - 2√a` for `0 < a ≤ b`. -/
private lemma countingQ_integral_inv_sqrt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ y in a..b, (Real.sqrt y)⁻¹ = 2 * Real.sqrt b - 2 * Real.sqrt a := by
  have hpos : ∀ y ∈ Set.uIcc a b, 0 < y := by
    intro y hy
    rw [Set.uIcc_of_le hab] at hy
    exact lt_of_lt_of_le ha hy.1
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y => 2 * Real.sqrt y)
    (fun y hy => ?_) ?_
  · have h := (Real.hasDerivAt_sqrt (hpos y hy).ne').const_mul 2
    refine h.congr_deriv ?_
    have : 0 < Real.sqrt y := Real.sqrt_pos.2 (hpos y hy)
    field_simp
  · exact intervalIntegral.intervalIntegrable_inv
      (fun y hy => (Real.sqrt_pos.2 (hpos y hy)).ne') Real.continuous_sqrt.continuousOn

/-! ### The bound on `m - m_sc` below `y0` -/

/-- A bound `B` on `‖m - m_sc‖` at height `y0` gives `‖m - m_sc‖(x + iy) ≤ (2B + 3) y0 / y`
for `0 < y ≤ y0`, by the monotonicity of `y ↦ y Im m(x + iy)` (the argument of [15] §8 in the
proof of Lemma 8.1, and of [26] (5.4)–(5.8)). -/
private lemma countingQ_below {N : ℕ} (hN : 0 < N) {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {B x y y0 : ℝ} (hB : 0 ≤ B)
    (h0 : ‖stieltjesM H (x + y0 * Complex.I) - msc (x + y0 * Complex.I)‖ ≤ B)
    (hy : 0 < y) (hyy0 : y ≤ y0) :
    ‖stieltjesM H (x + y * Complex.I) - msc (x + y * Complex.I)‖ ≤ (2 * B + 3) * (y0 / y) := by
  have hy0 : 0 < y0 := lt_of_lt_of_le hy hyy0
  have hz : 0 < ((x : ℂ) + y * Complex.I).im := by simpa using hy
  have hz0 : 0 < ((x : ℂ) + y0 * Complex.I).im := by simpa using hy0
  have h1 : ‖stieltjesM H (x + y * Complex.I) - stieltjesM H (x + y0 * Complex.I)‖ ≤
      y0 / y * (stieltjesM H (x + y0 * Complex.I)).im := by
    rw [im_stieltjesM_eq hH hz0, stieltjesM_eq_sum hH hz,
      stieltjesM_eq_sum hH hz0, ← mul_sub, ← Finset.sum_sub_distrib, norm_mul,
      norm_inv, Complex.norm_natCast]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
      Complex.mul_im, zero_add]
    calc (N : ℝ)⁻¹ * ‖∑ α, (((hH.eigenvalues α : ℂ) - (x + y * Complex.I))⁻¹ -
          ((hH.eigenvalues α : ℂ) - (x + y0 * Complex.I))⁻¹)‖
        ≤ (N : ℝ)⁻¹ * ∑ α, ‖((hH.eigenvalues α : ℂ) - (x + y * Complex.I))⁻¹ -
          ((hH.eigenvalues α : ℂ) - (x + y0 * Complex.I))⁻¹‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ (N : ℝ)⁻¹ * ∑ α, y0 / y * (y0 / ((hH.eigenvalues α - x) ^ 2 + y0 ^ 2)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun α _ =>
            norm_resolvent_term_sub_le _ x hy hyy0) (by positivity)
      _ = y0 / y * ((N : ℝ)⁻¹ * ∑ α, y0 / ((hH.eigenvalues α - x) ^ 2 + y0 ^ 2)) := by
          rw [← Finset.mul_sum]; ring
  have h3 := (norm_msc_eq_inv_and_lt_one hz0).2
  have h4 := (norm_msc_eq_inv_and_lt_one hz).2
  have h5 : (stieltjesM H (x + y0 * Complex.I)).im ≤ 1 + B := by
    have e1 := Complex.abs_im_le_norm (stieltjesM H (x + y0 * Complex.I) -
      msc (x + y0 * Complex.I))
    have e2 := Complex.abs_im_le_norm (msc (x + y0 * Complex.I))
    rw [Complex.sub_im] at e1
    have := (abs_le.1 e1).2
    have := (abs_le.1 e2).2
    linarith
  have htri : ‖stieltjesM H (x + y * Complex.I) - msc (x + y * Complex.I)‖ ≤
      ‖stieltjesM H (x + y * Complex.I) - stieltjesM H (x + y0 * Complex.I)‖ +
      ‖stieltjesM H (x + y0 * Complex.I) - msc (x + y0 * Complex.I)‖ +
      ‖msc (x + y0 * Complex.I)‖ + ‖msc (x + y * Complex.I)‖ := by
    have e : stieltjesM H (x + y * Complex.I) - msc (x + y * Complex.I) =
        (stieltjesM H (x + y * Complex.I) - stieltjesM H (x + y0 * Complex.I)) +
        (stieltjesM H (x + y0 * Complex.I) - msc (x + y0 * Complex.I)) +
        msc (x + y0 * Complex.I) - msc (x + y * Complex.I) := by ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    gcongr
    refine (norm_add_le _ _).trans ?_
    gcongr
    exact norm_add_le _ _
  have hp : 1 ≤ y0 / y := by rw [le_div_iff₀ hy]; linarith
  have h6 : y0 / y * (stieltjesM H (x + y0 * Complex.I)).im ≤ y0 / y * (1 + B) :=
    mul_le_mul_of_nonneg_left h5 (by positivity)
  nlinarith [mul_nonneg (sub_nonneg.2 hp) (by linarith : (0 : ℝ) ≤ B + 2)]

/-! ### Edges of the rectangle -/

/-- A vertical edge: `‖∫_η^h F(c + iy) dy‖ ≤ A log(h/η) + 2B√h` when
`‖F(c + iy)‖ ≤ A / y + B / √y` on `(η, h]`. -/
private lemma countingQ_vert {F : ℂ → ℂ} {A B c η h : ℝ} (hB : 0 ≤ B)
    (hη : 0 < η) (hηh : η ≤ h)
    (hF : ∀ y, η < y → y ≤ h → ‖F (c + y * Complex.I)‖ ≤ A * y⁻¹ + B * (Real.sqrt y)⁻¹) :
    ‖∫ y in η..h, F (c + y * Complex.I)‖ ≤ A * Real.log (h / η) + B * (2 * Real.sqrt h) := by
  have hpos : ∀ y ∈ Set.uIcc η h, 0 < y := by
    intro y hy
    rw [Set.uIcc_of_le hηh] at hy
    exact lt_of_lt_of_le hη hy.1
  have hi1 : IntervalIntegrable (fun y : ℝ => y⁻¹) volume η h :=
    intervalIntegral.intervalIntegrable_inv (fun y hy => (hpos y hy).ne') continuousOn_id
  have hi2 : IntervalIntegrable (fun y : ℝ => (Real.sqrt y)⁻¹) volume η h :=
    intervalIntegral.intervalIntegrable_inv (fun y hy => (Real.sqrt_pos.2 (hpos y hy)).ne')
      Real.continuous_sqrt.continuousOn
  have hg : IntervalIntegrable (fun y : ℝ => A * y⁻¹ + B * (Real.sqrt y)⁻¹) volume η h :=
    (hi1.const_mul A).add (hi2.const_mul B)
  have hI := intervalIntegral.norm_integral_le_of_norm_le hηh
    (Eventually.of_forall fun y (hy : y ∈ Set.Ioc η h) => hF y hy.1 hy.2) hg
  rw [intervalIntegral.integral_add (hi1.const_mul A) (hi2.const_mul B),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_inv_of_pos hη (hη.trans_le hηh), countingQ_integral_inv_sqrt hη hηh] at hI
  have := Real.sqrt_nonneg η
  nlinarith [mul_nonneg hB this]

/-- A horizontal edge: `‖∫_c^d F(x + ih) dx‖ ≤ B (d - c)` when `‖F(x + ih)‖ ≤ B` on `(c, d]`. -/
private lemma countingQ_top {F : ℂ → ℂ} {c d h B : ℝ} (hcd : c ≤ d)
    (hF : ∀ x, c < x → x ≤ d → ‖F (x + h * Complex.I)‖ ≤ B) :
    ‖∫ x in c..d, F (x + h * Complex.I)‖ ≤ B * (d - c) := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (C := B)
    (f := fun x : ℝ => F (x + h * Complex.I)) (a := c) (b := d) (fun x hx => by
      rw [Set.uIoc_of_le hcd] at hx
      exact hF x hx.1 hx.2)
  rwa [abs_of_nonneg (sub_nonneg.2 hcd)] at this

/-- Cauchy's theorem for `m - m_sc` on `[a, b] × [η, h]`: the bottom edge is bounded by the top
edge plus the two vertical edges. -/
private lemma countingQ_diff {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {a b η h T V : ℝ} (hη : 0 < η) (hηh : η ≤ h)
    (htop : ‖∫ x in a..b, (stieltjesM H (x + h * Complex.I) - msc (x + h * Complex.I))‖ ≤ T)
    (hva : ‖∫ y in η..h, (stieltjesM H (a + y * Complex.I) - msc (a + y * Complex.I))‖ ≤ V)
    (hvb : ‖∫ y in η..h, (stieltjesM H (b + y * Complex.I) - msc (b + y * Complex.I))‖ ≤ V) :
    |(∫ x in a..b, (stieltjesM H (x + η * Complex.I)).im) -
        ∫ x in a..b, (msc (x + η * Complex.I)).im| ≤ T + 2 * V := by
  set f : ℂ → ℂ := fun z => stieltjesM H z - msc z with hf
  have hfd : DifferentiableOn ℂ f {z | 0 < z.im} :=
    (differentiableOn_stieltjesM_upperHalfPlane hH).sub differentiableOn_msc_upperHalfPlane
  have hcm :=
    continuous_horizontal_of_differentiableOn (differentiableOn_stieltjesM_upperHalfPlane hH) hη
  have hcs := continuous_horizontal_of_differentiableOn differentiableOn_msc_upperHalfPlane hη
  have hsub : (∫ x in a..b, (stieltjesM H (x + η * Complex.I)).im) -
      ∫ x in a..b, (msc (x + η * Complex.I)).im =
        (∫ x in a..b, f (x + η * Complex.I)).im := by
    have e := Complex.imCLM.intervalIntegral_comp_comm
      ((hcm.sub hcs).intervalIntegrable (μ := volume) a b)
    simp only [Complex.imCLM_apply, Pi.sub_apply] at e
    change _ = (∫ x in a..b, (stieltjesM H (x + η * Complex.I) - msc (x + η * Complex.I))).im
    have hi1 : IntervalIntegrable (fun x : ℝ => (stieltjesM H (x + η * Complex.I)).im)
        volume a b := (Complex.continuous_im.comp hcm).intervalIntegrable a b
    have hi2 : IntervalIntegrable (fun x : ℝ => (msc (x + η * Complex.I)).im)
        volume a b := (Complex.continuous_im.comp hcs).intervalIntegrable a b
    rw [← e, ← intervalIntegral.integral_sub hi1 hi2]
    simp
  rw [hsub]
  refine (Complex.abs_im_le_norm _).trans ?_
  have hrect := integral_rect_eq_zero_of_differentiableOn hfd a b hη hηh
  have heq : (∫ x in a..b, f (x + η * Complex.I)) =
      (∫ x in a..b, f (x + h * Complex.I)) -
        (Complex.I • (∫ y in η..h, f (b + y * Complex.I)) -
          Complex.I • (∫ y in η..h, f (a + y * Complex.I))) := by
    linear_combination hrect
  rw [heq]
  calc ‖(∫ x in a..b, f (x + h * Complex.I)) -
        (Complex.I • (∫ y in η..h, f (b + y * Complex.I)) -
          Complex.I • (∫ y in η..h, f (a + y * Complex.I)))‖
      ≤ ‖∫ x in a..b, f (x + h * Complex.I)‖ +
        (‖Complex.I • (∫ y in η..h, f (b + y * Complex.I))‖ +
          ‖Complex.I • (∫ y in η..h, f (a + y * Complex.I))‖) :=
        (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
    _ = ‖∫ x in a..b, f (x + h * Complex.I)‖ +
        (‖∫ y in η..h, f (b + y * Complex.I)‖ + ‖∫ y in η..h, f (a + y * Complex.I)‖) := by
        rw [norm_smul, norm_smul, Complex.norm_I, one_mul, one_mul]
    _ ≤ T + (V + V) := add_le_add htop (add_le_add hvb hva)
    _ = T + 2 * V := by ring

/-! ### The comparison on an interval, with the `q`-terms -/

private lemma countingQ_one_le_of_sq {σ : ℝ} (hσ : 0 ≤ σ) (h : 1 < σ ^ 2) : 1 ≤ σ := by
  nlinarith

/-- The top edge at height `h = min(1, max(y0, ℓ))` over an interval of length `ℓ ≤ 10`, with
`σ² ≥ max(ℓ, y0)`: `ℓ ≤ 10 σ √h` and `ℓ ≤ 10 h`. -/
private lemma countingQ_len {y0 ℓ σ : ℝ} (hy01 : y0 ≤ 1) (hℓ : ℓ ≤ 10)
    (hσ : 0 ≤ σ) (hσ1 : ℓ ≤ σ ^ 2) (hσ2 : y0 ≤ σ ^ 2) (hy0 : 0 < y0) :
    ℓ ≤ 10 * (σ * Real.sqrt (min 1 (max y0 ℓ))) ∧ ℓ ≤ 10 * min 1 (max y0 ℓ) := by
  have hhpos : 0 < min 1 (max y0 ℓ) := lt_min one_pos (lt_max_of_lt_left hy0)
  have hhσ : min 1 (max y0 ℓ) ≤ σ ^ 2 := (min_le_right _ _).trans (max_le hσ2 hσ1)
  have hsqh : Real.sqrt (min 1 (max y0 ℓ)) ≤ σ := by rw [Real.sqrt_le_left hσ]; exact hhσ
  have hsqhpos : 0 ≤ Real.sqrt (min 1 (max y0 ℓ)) := Real.sqrt_nonneg _
  rcases le_or_gt ℓ 1 with h1 | h1
  · have hheq : min 1 (max y0 ℓ) = max y0 ℓ := min_eq_right (max_le hy01 h1)
    have hdc : ℓ ≤ min 1 (max y0 ℓ) := by rw [hheq]; exact le_max_right _ _
    have hs : min 1 (max y0 ℓ) ≤ σ * Real.sqrt (min 1 (max y0 ℓ)) :=
      calc min 1 (max y0 ℓ)
          = Real.sqrt (min 1 (max y0 ℓ)) * Real.sqrt (min 1 (max y0 ℓ)) :=
            (Real.mul_self_sqrt hhpos.le).symm
        _ ≤ σ * Real.sqrt (min 1 (max y0 ℓ)) := mul_le_mul_of_nonneg_right hsqh hsqhpos
    exact ⟨by linarith, by linarith⟩
  · have hheq : min 1 (max y0 ℓ) = 1 := min_eq_left (le_max_of_le_right h1.le)
    have hσ1' : 1 ≤ σ := countingQ_one_le_of_sq hσ (by linarith)
    rw [hheq, Real.sqrt_one]
    exact ⟨by linarith, by linarith⟩

/-- `‖m - m_sc‖(x + iy) ≤ (7 U y0 + U/N) / y + (U/q²) / √y` for `y > 0`, from the bound
`U (q⁻² y^{-1/2} + (N y)⁻¹)` for `y ≥ y0` and the bound `2U` at height `y0`. -/
private lemma countingQ_pointwise {N : ℕ} (hN : 0 < N) {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {U q y0 x y : ℝ} (hU : 1 ≤ U) (hy0 : 0 < y0)
    (hpt : y0 ≤ y → ‖stieltjesM H (x + y * Complex.I) - msc (x + y * Complex.I)‖ ≤
        U * (1 / (q ^ 2 * Real.sqrt y) + 1 / (N * y)))
    (hpt0 : ‖stieltjesM H (x + y0 * Complex.I) - msc (x + y0 * Complex.I)‖ ≤ 2 * U)
    (hy : 0 < y) :
    ‖stieltjesM H (x + y * Complex.I) - msc (x + y * Complex.I)‖ ≤
      (7 * U * y0 + U / N) * y⁻¹ + U / q ^ 2 * (Real.sqrt y)⁻¹ := by
  have hi : 0 ≤ y⁻¹ := inv_nonneg.2 hy.le
  have hA1 : 0 ≤ U / N * y⁻¹ := by
    have : 0 ≤ U / N := div_nonneg (by linarith) (Nat.cast_nonneg _)
    positivity
  have hB1 : 0 ≤ U / q ^ 2 * (Real.sqrt y)⁻¹ := by
    have : 0 ≤ U / q ^ 2 := div_nonneg (by linarith) (sq_nonneg _)
    have : 0 ≤ (Real.sqrt y)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg y)
    positivity
  have hA2 : 0 ≤ 7 * U * y0 * y⁻¹ := by
    have : 0 ≤ U := by linarith
    positivity
  rw [add_mul]
  rcases lt_or_ge y y0 with hlt | hge
  · have hb := countingQ_below hN hH (B := 2 * U) (by linarith) hpt0 hy hlt.le
    have h1 : 0 ≤ y0 * y⁻¹ := mul_nonneg hy0.le hi
    have e : (2 * (2 * U) + 3) * (y0 / y) ≤ 7 * U * y0 * y⁻¹ := by
      rw [div_eq_mul_inv]
      have := mul_le_mul_of_nonneg_right (by linarith : 2 * (2 * U) + 3 ≤ 7 * U) h1
      linarith
    linarith
  · have hb := hpt hge
    have e : U * (1 / (q ^ 2 * Real.sqrt y) + 1 / (N * y)) =
        U / N * y⁻¹ + U / q ^ 2 * (Real.sqrt y)⁻¹ := by ring
    rw [e] at hb
    linarith

/-- On `[c, d] ⊆ [-5, 5]`, with `η = N⁻²` and `σ² ≥ max(d - c, y0)`:
`|∫_c^d Im (m - m_sc)(x + iη) dx| ≤ 14 U σ / q² + 24 U log N / N + 28 U y0 log N`. The top
edge of the rectangle is at height `min(1, max(y0, d - c))`. -/
private lemma countingQ_rect_bound {N : ℕ} (hN : 2 ≤ N) {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {U q y0 c d σ η : ℝ} (hU : 1 ≤ U) (hq : 1 ≤ q) (hy0 : 1 / N ≤ y0)
    (hy01 : y0 ≤ 1) (hη : η = 1 / (N : ℝ) ^ 2)
    (hpt : ∀ x y : ℝ, |x| ≤ 5 → y0 ≤ y → y ≤ 1 →
      ‖stieltjesM H (x + y * Complex.I) - msc (x + y * Complex.I)‖ ≤
        U * (1 / (q ^ 2 * Real.sqrt y) + 1 / (N * y)))
    (hpt0 : ∀ x : ℝ, |x| ≤ 5 →
      ‖stieltjesM H (x + y0 * Complex.I) - msc (x + y0 * Complex.I)‖ ≤ 2 * U)
    (hcd : c ≤ d) (hc : -5 ≤ c) (hd : d ≤ 5) (hσ : 0 ≤ σ) (hσ1 : d - c ≤ σ ^ 2)
    (hσ2 : y0 ≤ σ ^ 2) :
    |(∫ x in c..d, (stieltjesM H (x + η * Complex.I)).im) -
        ∫ x in c..d, (msc (x + η * Complex.I)).im| ≤
      14 * U * (σ / q ^ 2) + 24 * U * Real.log N / N + 28 * U * y0 * Real.log N := by
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hy0pos : 0 < y0 := lt_of_lt_of_le (by positivity) hy0
  have hL : 1 / 2 ≤ Real.log N := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_le_log (by norm_num) hN2
    norm_num at h1
    linarith
  have hU0 : 0 ≤ U := by linarith
  have hq0 : 0 < q := by linarith
  have hηpos : 0 < η := by rw [hη]; positivity
  have hηy0 : η ≤ y0 := by
    refine le_trans ?_ hy0
    rw [hη]
    apply one_div_le_one_div_of_le hNr
    have := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ N) hNr.le
    rw [mul_one] at this
    rw [sq]
    exact this
  obtain ⟨hlen1, hlen2⟩ := countingQ_len hy01 (by linarith) hσ hσ1 hσ2 hy0pos
  set h : ℝ := min 1 (max y0 (d - c)) with hh
  have hy0h : y0 ≤ h := le_min hy01 (le_max_left _ _)
  have hh1 : h ≤ 1 := min_le_left _ _
  have hhpos : 0 < h := lt_of_lt_of_le hy0pos hy0h
  have hhσ : h ≤ σ ^ 2 := (min_le_right _ _).trans (max_le hσ2 hσ1)
  have hsqh : Real.sqrt h ≤ σ := by rw [Real.sqrt_le_left hσ]; exact hhσ
  have hsqhpos : 0 < Real.sqrt h := Real.sqrt_pos.2 hhpos
  -- the top edge
  have htop := countingQ_top (F := fun z => stieltjesM H z - msc z) (h := h) hcd
    (fun x hx1 hx2 => hpt x h (abs_le.2 ⟨by linarith, by linarith⟩) hy0h hh1)
  have e1 : 1 / (q ^ 2 * Real.sqrt h) * (d - c) ≤ 10 * (σ / q ^ 2) := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    have : 10 * (σ / q ^ 2) * (q ^ 2 * Real.sqrt h) = 10 * (σ * Real.sqrt h) := by
      field_simp
    rw [this]
    exact hlen1
  have e2 : 1 / (N * h) * (d - c) ≤ 10 / N := by
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hNr]
    have := mul_le_mul_of_nonneg_right hlen2 hNr.le
    have e : 10 * ((N : ℝ) * h) = 10 * h * N := by ring
    rw [e]
    exact this
  have htop2 : ‖∫ x in c..d, (stieltjesM H (x + h * Complex.I) - msc (x + h * Complex.I))‖ ≤
      U * (10 * (σ / q ^ 2) + 10 / N) := by
    refine htop.trans ?_
    calc U * (1 / (q ^ 2 * Real.sqrt h) + 1 / (N * h)) * (d - c)
        = U * (1 / (q ^ 2 * Real.sqrt h) * (d - c) + 1 / (N * h) * (d - c)) := by ring
      _ ≤ U * (10 * (σ / q ^ 2) + 10 / N) :=
        mul_le_mul_of_nonneg_left (add_le_add e1 e2) hU0
  -- the vertical edges
  have hlog : Real.log (h / η) ≤ 2 * Real.log N := by
    have e : h / η = h * (N : ℝ) ^ 2 := by rw [hη, div_div_eq_mul_div, div_one]
    have h2 : h / η ≤ (N : ℝ) ^ 2 := by
      rw [e]
      have := mul_le_mul_of_nonneg_right hh1 (sq_nonneg (N : ℝ))
      linarith
    calc Real.log (h / η) ≤ Real.log ((N : ℝ) ^ 2) :=
          Real.log_le_log (div_pos hhpos hηpos) h2
      _ = 2 * Real.log N := by rw [Real.log_pow]; push_cast; ring
  have hvert : ∀ c' : ℝ, |c'| ≤ 5 →
      ‖∫ y in η..h, (stieltjesM H (c' + y * Complex.I) - msc (c' + y * Complex.I))‖ ≤
        (7 * U * y0 + U / N) * (2 * Real.log N) + U / q ^ 2 * (2 * σ) := by
    intro c' hc'
    have hv := countingQ_vert (F := fun z => stieltjesM H z - msc z) (c := c')
      (A := 7 * U * y0 + U / N) (B := U / q ^ 2) (div_nonneg hU0 (sq_nonneg _)) hηpos
      (hηy0.trans hy0h) (fun y hy1 hy2 =>
        countingQ_pointwise hN0 hH hU hy0pos (fun hge => hpt c' y hc' hge (hy2.trans hh1))
          (hpt0 c' hc') (hηpos.trans hy1))
    refine hv.trans (add_le_add ?_ ?_)
    · have : 0 ≤ 7 * U * y0 + U / N := by positivity
      exact mul_le_mul_of_nonneg_left hlog this
    · have h2 : 2 * Real.sqrt h ≤ 2 * σ := by linarith
      exact mul_le_mul_of_nonneg_left h2 (div_nonneg hU0 (sq_nonneg _))
  have hD := countingQ_diff hH hηpos (hηy0.trans hy0h) htop2
    (hvert c (abs_le.2 ⟨hc, by linarith⟩)) (hvert d (abs_le.2 ⟨by linarith, hd⟩))
  refine hD.trans ?_
  have key : U / N ≤ 2 * (U * Real.log N / N) := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hNr]
    have := mul_le_mul_of_nonneg_left hL hU0
    linarith
  have e : U * (10 * (σ / q ^ 2) + 10 / N) +
      2 * ((7 * U * y0 + U / N) * (2 * Real.log N) + U / q ^ 2 * (2 * σ)) =
      14 * U * (σ / q ^ 2) + 10 * (U / N) + 4 * (U * Real.log N / N) +
        28 * U * y0 * Real.log N := by ring
  rw [e]
  have e2 : 24 * U * Real.log N / N = 24 * (U * Real.log N / N) := by ring
  rw [e2]
  linarith

/-! ### Arithmetic of the error terms -/

/-- The regime `U (p² + s²) > 1`: then `1 ≤ 180 U² L R` when `p³ ≤ R`, `s³ ≤ R` and
`L ≥ 1/2`. -/
private lemma countingQ_trivial {U p s R L : ℝ} (hU : 1 ≤ U) (hp : 0 ≤ p) (hs : 0 ≤ s)
    (hδ : 1 < U * (p ^ 2 + s ^ 2)) (hRp : p ^ 3 ≤ R) (hRs : s ^ 3 ≤ R) (hL : 1 / 2 ≤ L) :
    1 ≤ 180 * U ^ 2 * L * R := by
  have hU0 : 0 ≤ U ^ 2 := by positivity
  have h3 : 1 ≤ 3 * U ^ 2 * R := by
    rcases lt_or_ge (1 / 2) (U * p ^ 2) with hc | hc
    · have h := countingQ_cube hU hp hc
      have := mul_le_mul_of_nonneg_left hRp hU0
      linarith
    · have hc' : 1 / 2 < U * s ^ 2 := by rw [mul_add] at hδ; linarith
      have h := countingQ_cube hU hs hc'
      have := mul_le_mul_of_nonneg_left hRs hU0
      linarith
  have hUR : 0 ≤ U ^ 2 * R := by nlinarith
  have := mul_le_mul_of_nonneg_left hL hUR
  have e : 180 * U ^ 2 * L * R = 180 * (U ^ 2 * R * L) := by ring
  rw [e]
  linarith

/-- `σ² ≥ κ + U (p² + s²) + t + y` for `σ = √κ + U (p + s) + √t + √y`. -/
private lemma countingQ_sigma_sq {κ U p s t y : ℝ} (hκ : 0 ≤ κ) (hU : 1 ≤ U) (hp : 0 ≤ p)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hy : 0 ≤ y) :
    κ + U * (p ^ 2 + s ^ 2) + t + y ≤
      (Real.sqrt κ + U * (p + s) + Real.sqrt t + Real.sqrt y) ^ 2 := by
  have e1 := Real.sq_sqrt hκ
  have e2 := Real.sq_sqrt ht
  have e3 := Real.sq_sqrt hy
  have a1 := Real.sqrt_nonneg κ
  have a2 := Real.sqrt_nonneg t
  have a3 := Real.sqrt_nonneg y
  have a4 : 0 ≤ U * (p + s) := by
    have : 0 ≤ U := by linarith
    positivity
  have hps : p ^ 2 + s ^ 2 ≤ (p + s) ^ 2 := by nlinarith [mul_nonneg hp hs]
  have hUd : U * (p ^ 2 + s ^ 2) ≤ (U * (p + s)) ^ 2 := by
    have h1 : U * (p ^ 2 + s ^ 2) ≤ U * (p + s) ^ 2 :=
      mul_le_mul_of_nonneg_left hps (by linarith)
    have h2 : U * (p + s) ^ 2 ≤ U * U * (p + s) ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
    nlinarith
  nlinarith [mul_nonneg a1 a4, mul_nonneg a1 a2, mul_nonneg a1 a3, mul_nonneg a4 a2,
    mul_nonneg a4 a3, mul_nonneg a2 a3]

/-- `(√κ + U (p + s) + √t + √y) p² ≤ 4 U (n + y + p³ + √κ p²)` when `s³ = n`, `t ≤ 2n`,
`t ≤ 1`, `y ≤ 1` and `U ≥ 1`. -/
private lemma countingQ_sigma_p {κ U p s t y n : ℝ} (hU : 1 ≤ U) (hp : 0 ≤ p)
    (hs : 0 ≤ s) (hs3 : s ^ 3 = n) (ht : 0 ≤ t) (htn : t ≤ 2 * n) (ht1 : t ≤ 1)
    (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    (Real.sqrt κ + U * (p + s) + Real.sqrt t + Real.sqrt y) * p ^ 2 ≤
      4 * U * (n + y + p ^ 3 + Real.sqrt κ * p ^ 2) := by
  have e1 := countingQ_pow3 hp hs
  have e2 := countingQ_pow3 hp (Real.sqrt_nonneg t)
  have e3 := countingQ_pow3 hp (Real.sqrt_nonneg y)
  have c2 := countingQ_sqrt_cube ht ht1
  have c3 := countingQ_sqrt_cube hy hy1
  have hU0 : 0 ≤ U := by linarith
  have hn : 0 ≤ n := by rw [← hs3]; positivity
  have k1 : Real.sqrt κ * p ^ 2 ≤ U * (Real.sqrt κ * p ^ 2) :=
    le_mul_of_one_le_left (by positivity) hU
  have k2 : p ^ 3 ≤ U * p ^ 3 := le_mul_of_one_le_left (by positivity) hU
  have k3 : n ≤ U * n := le_mul_of_one_le_left hn hU
  have k4 : y ≤ U * y := le_mul_of_one_le_left hy hU
  have k0 : 0 ≤ Real.sqrt κ * p ^ 2 := by positivity
  have k5 := mul_le_mul_of_nonneg_left e1 hU0
  rw [hs3] at k5
  have e : (Real.sqrt κ + U * (p + s) + Real.sqrt t + Real.sqrt y) * p ^ 2 =
      Real.sqrt κ * p ^ 2 + U * p ^ 3 + U * (p ^ 2 * s) + p ^ 2 * Real.sqrt t +
        p ^ 2 * Real.sqrt y := by ring
  rw [e]
  linarith

/-- The total error: `14 U σ' + 24 U L n + 28 U y L + 5 n ≤ 180 U² L R` when `σ' ≤ 4 U R`,
`n ≤ R`, `y ≤ R` and `L ≥ 1/2`. -/
private lemma countingQ_total {U σ' L n y R : ℝ} (hU : 1 ≤ U) (hσ : σ' ≤ 4 * U * R)
    (hn : n ≤ R) (hy : y ≤ R) (hL : 1 / 2 ≤ L) (hn0 : 0 ≤ n) :
    14 * U * σ' + 24 * U * L * n + 28 * U * y * L + 5 * n ≤ 180 * U ^ 2 * L * R := by
  have hU0 : 0 ≤ U := by linarith
  have hR0 : 0 ≤ R := hn0.trans hn
  have hL0 : 0 ≤ L := by linarith
  have hUU : U ≤ U ^ 2 := by nlinarith
  have hU2 : 1 ≤ U ^ 2 := by nlinarith
  have hLR : 0 ≤ L * R := mul_nonneg hL0 hR0
  have hU2R : 0 ≤ U ^ 2 * R := by positivity
  have a1 : 14 * U * σ' ≤ 56 * U ^ 2 * R := by
    have := mul_le_mul_of_nonneg_left hσ hU0
    nlinarith
  have a2 : U ^ 2 * R ≤ 2 * (U ^ 2 * R * L) := by
    have := mul_le_mul_of_nonneg_left hL hU2R
    linarith
  have hUL : 0 ≤ U * L := mul_nonneg hU0 hL0
  have a3 : U * L * n ≤ U ^ 2 * (L * R) := by
    have h1 := mul_le_mul_of_nonneg_left hn hUL
    have h2 := mul_le_mul_of_nonneg_right hUU hLR
    nlinarith
  have a4 : U * y * L ≤ U ^ 2 * (L * R) := by
    have h1 := mul_le_mul_of_nonneg_left hy hUL
    have h2 := mul_le_mul_of_nonneg_right hUU hLR
    nlinarith
  have a5 : n ≤ 2 * (U ^ 2 * (L * R)) := by
    have h1 := mul_le_mul_of_nonneg_left hL hR0
    have h2 := mul_le_mul_of_nonneg_right hU2 hLR
    nlinarith
  have e : 180 * U ^ 2 * L * R = 180 * (U ^ 2 * (L * R)) := by ring
  have e' : U ^ 2 * R * L = U ^ 2 * (L * R) := by ring
  rw [e]
  rw [e'] at a2
  nlinarith

/-! ### The two rectangles -/

/-- `N ≤ t / η` for `η = N⁻²` and `t ≥ 1/N`. -/
private lemma countingQ_div {N : ℕ} (hN : 0 < N) {η t : ℝ} (hη : η = 1 / (N : ℝ) ^ 2)
    (ht : 1 / N ≤ t) : (N : ℝ) ≤ t / η := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hηpos : 0 < η := by rw [hη]; positivity
  rw [le_div_iff₀ hηpos, hη]
  calc (N : ℝ) * (1 / (N : ℝ) ^ 2) = 1 / N := by field_simp
    _ ≤ t := ht

/-- `2η ≤ 1/N` for `η = N⁻²`, `N ≥ 2`. -/
private lemma countingQ_two_eta {N : ℕ} (hN : 2 ≤ N) {η : ℝ} (hη : η = 1 / (N : ℝ) ^ 2) :
    2 * η ≤ 1 / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rw [hη, mul_one_div, div_le_div_iff₀ (by positivity) hNr, one_mul, sq]
  exact mul_le_mul_of_nonneg_right hN2 hNr.le

/-- The case `-2 - δ ≤ E ≤ 0`: rectangles over `[-2 - δ - 1/N, E ± 1/N]`. A bound `K` on the
comparison over every subinterval `[c, d] ⊆ [-5, 5]` of length at most `σ²` gives
`|n(E) - n_sc(E)| ≤ K + 5/N`. -/
private lemma countingQ_left {N : ℕ} (hN : 2 ≤ N) {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {δ σ η E K : ℝ} (hevl : ∀ α, -2 - δ ≤ hH.eigenvalues α)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hE : -2 - δ ≤ E) (hE0 : E ≤ 0) (hη : η = 1 / (N : ℝ) ^ 2)
    (hσ : kappa E + δ + 2 * (1 / N) ≤ σ ^ 2)
    (hRB : ∀ c d : ℝ, c ≤ d → -5 ≤ c → d ≤ 5 → d - c ≤ σ ^ 2 →
      |(∫ x in c..d, (stieltjesM H (x + η * Complex.I)).im) -
        ∫ x in c..d, (msc (x + η * Complex.I)).im| ≤ K) :
    |countFn hH E - nsc E| ≤ K + 5 * (1 / N) := by
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hinvN0 : 0 < 1 / (N : ℝ) := by positivity
  have hinvN : 1 / (N : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hNr (by norm_num)]
    linarith
  have hηpos : 0 < η := by rw [hη]; positivity
  have hη2 := countingQ_two_eta hN hη
  have hκE : E + 2 ≤ kappa E := by
    unfold kappa
    rw [abs_of_nonpos hE0]
    have := neg_le_abs (-E - 2)
    linarith
  have h22 : (2 : ℝ) / N = 2 * (1 / N) := by ring
  have hI1 : Real.pi * countFn hH E - 2 / N ≤
      ∫ x in (-2 - δ - 1 / N)..(E + 1 / N), (stieltjesM H (x + η * Complex.I)).im :=
    pi_mul_countFn_sub_two_div_le_integral_im_stieltjesM hN0 hH hηpos (by linarith)
      (fun α hα => countingQ_div hN0 hη (by linarith))
      (fun α => countingQ_div hN0 hη (by linarith [hevl α]))
  have hI2 : ∫ x in (-2 - δ - 1 / N)..(E - 1 / N), (stieltjesM H (x + η * Complex.I)).im ≤
      Real.pi * countFn hH E + 1 / N :=
    integral_im_stieltjesM_le_pi_mul_countFn_add_inv hN0 hH hηpos
      (fun α hα => countingQ_div hN0 hη (by linarith))
  obtain ⟨hD1a, hD1b⟩ := abs_le.1 (hRB (-2 - δ - 1 / N) (E + 1 / N) (by linarith)
    (by linarith) (by linarith) (by linarith))
  obtain ⟨hD2a, hD2b⟩ := abs_le.1 (hRB (-2 - δ - 1 / N) (E - 1 / N) (by linarith)
    (by linarith) (by linarith) (by linarith))
  have hna : nsc (-2 - δ - 1 / N) = 0 := nsc_eq_zero (by linarith)
  have hS1 := countingQ_sc_nsc (-2 - δ - 1 / N) (E + 1 / N) hηpos
  have hS2 := countingQ_sc_nsc (-2 - δ - 1 / N) (E - 1 / N) hηpos
  rw [hna, sub_zero] at hS1 hS2
  obtain ⟨hS1a, hS1b⟩ := abs_le.1 hS1
  obtain ⟨hS2a, hS2b⟩ := abs_le.1 hS2
  have hsh := countingQ_nsc_shift E (1 / N) hinvN0.le
  obtain ⟨hsh1a, hsh1b⟩ := abs_le.1 hsh.1
  obtain ⟨hsh2a, hsh2b⟩ := abs_le.1 hsh.2
  apply countingQ_abs_le_of_pi
  · rw [mul_sub]
    rw [mul_sub] at hsh1b
    linarith
  · rw [neg_sub, mul_sub]
    rw [mul_sub] at hsh2a
    linarith

/-- The case `0 < E ≤ 2 + δ`: rectangles over `[E ± 1/N, 2 + δ + 1/N]`. -/
private lemma countingQ_right {N : ℕ} (hN : 2 ≤ N) {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {δ σ η E K : ℝ} (hevl : ∀ α, -2 - δ ≤ hH.eigenvalues α)
    (hevu : ∀ α, hH.eigenvalues α ≤ 2 + δ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hE0 : 0 < E) (hE' : E ≤ 2 + δ) (hη : η = 1 / (N : ℝ) ^ 2)
    (hσ : kappa E + δ + 2 * (1 / N) ≤ σ ^ 2)
    (hRB : ∀ c d : ℝ, c ≤ d → -5 ≤ c → d ≤ 5 → d - c ≤ σ ^ 2 →
      |(∫ x in c..d, (stieltjesM H (x + η * Complex.I)).im) -
        ∫ x in c..d, (msc (x + η * Complex.I)).im| ≤ K) :
    |countFn hH E - nsc E| ≤ K + 5 * (1 / N) := by
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hinvN0 : 0 < 1 / (N : ℝ) := by positivity
  have hinvN : 1 / (N : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hNr (by norm_num)]
    linarith
  have hηpos : 0 < η := by rw [hη]; positivity
  have hη2 := countingQ_two_eta hN hη
  have hκE : 2 - E ≤ kappa E := by
    unfold kappa
    rw [abs_of_pos hE0]
    have := neg_le_abs (E - 2)
    linarith
  have h22 : (2 : ℝ) / N = 2 * (1 / N) := by ring
  have hI1 : Real.pi * countFn hH E - 2 / N ≤
      ∫ x in (-2 - δ - 1 / N)..(E + 1 / N), (stieltjesM H (x + η * Complex.I)).im :=
    pi_mul_countFn_sub_two_div_le_integral_im_stieltjesM hN0 hH hηpos (by linarith)
      (fun α hα => countingQ_div hN0 hη (by linarith))
      (fun α => countingQ_div hN0 hη (by linarith [hevl α]))
  have hI2 : ∫ x in (-2 - δ - 1 / N)..(E - 1 / N), (stieltjesM H (x + η * Complex.I)).im ≤
      Real.pi * countFn hH E + 1 / N :=
    integral_im_stieltjesM_le_pi_mul_countFn_add_inv hN0 hH hηpos
      (fun α hα => countingQ_div hN0 hη (by linarith))
  have hT1 : Real.pi * countFn hH (2 + δ + 1 / N) - 2 / N ≤
      ∫ x in (-2 - δ - 1 / N)..(2 + δ + 1 / N), (stieltjesM H (x + η * Complex.I)).im :=
    pi_mul_countFn_sub_two_div_le_integral_im_stieltjesM hN0 hH hηpos (by linarith)
      (fun α _ => countingQ_div hN0 hη (by linarith [hevu α]))
      (fun α => countingQ_div hN0 hη (by linarith [hevl α]))
  have hT2 : ∫ x in (-2 - δ - 1 / N)..(2 + δ + 1 / N),
      (stieltjesM H (x + η * Complex.I)).im ≤
        Real.pi * countFn hH (2 + δ + 1 / N) + 1 / N :=
    integral_im_stieltjesM_le_pi_mul_countFn_add_inv hN0 hH hηpos
      (fun α hα => absurd hα (not_lt.2 (by linarith [hevu α])))
  have hc1 : countFn hH (2 + δ + 1 / N) = 1 := by
    unfold countFn
    rw [Finset.filter_true_of_mem fun α _ => (hevu α).trans (by linarith)]
    simp only [Finset.card_univ, Fintype.card_fin]
    field_simp
  rw [hc1, mul_one] at hT1 hT2
  have hcont : Continuous fun x : ℝ => (stieltjesM H (x + η * Complex.I)).im :=
    Complex.continuous_im.comp
      (continuous_horizontal_of_differentiableOn
        (differentiableOn_stieltjesM_upperHalfPlane hH) hηpos)
  have hA1 := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) (-2 - δ - 1 / N) (E + 1 / N))
    (hcont.intervalIntegrable (μ := volume) (E + 1 / N) (2 + δ + 1 / N))
  have hA2 := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) (-2 - δ - 1 / N) (E - 1 / N))
    (hcont.intervalIntegrable (μ := volume) (E - 1 / N) (2 + δ + 1 / N))
  obtain ⟨hD1a, hD1b⟩ := abs_le.1 (hRB (E + 1 / N) (2 + δ + 1 / N) (by linarith)
    (by linarith) (by linarith) (by linarith))
  obtain ⟨hD2a, hD2b⟩ := abs_le.1 (hRB (E - 1 / N) (2 + δ + 1 / N) (by linarith)
    (by linarith) (by linarith) (by linarith))
  have hna : nsc (2 + δ + 1 / N) = 1 := nsc_eq_one (by linarith)
  have hS1 := countingQ_sc_nsc (E + 1 / N) (2 + δ + 1 / N) hηpos
  have hS2 := countingQ_sc_nsc (E - 1 / N) (2 + δ + 1 / N) hηpos
  rw [hna, mul_sub, mul_one] at hS1 hS2
  obtain ⟨hS1a, hS1b⟩ := abs_le.1 hS1
  obtain ⟨hS2a, hS2b⟩ := abs_le.1 hS2
  have hsh := countingQ_nsc_shift E (1 / N) hinvN0.le
  obtain ⟨hsh1a, hsh1b⟩ := abs_le.1 hsh.1
  obtain ⟨hsh2a, hsh2b⟩ := abs_le.1 hsh.2
  rw [mul_sub] at hsh1a hsh1b hsh2a hsh2b
  apply countingQ_abs_le_of_pi
  · rw [mul_sub]
    linarith
  · rw [neg_sub, mul_sub]
    linarith

/-! ### The counting estimate with the `q`-terms -/

/-- Counting function from the averaged law with the `q`-terms (Lemma 8.1 and
Theorem 2.12 of [15]); `U` collects the `φ^C` factors. -/
theorem abs_countFn_sub_nsc_le_q : ∃ C > 0, ∀ (N : ℕ), 2 ≤ N →
    ∀ (H : Matrix (Fin N) (Fin N) ℝ) (hH : H.IsHermitian) (U q y0 : ℝ), 1 ≤ U → 1 ≤ q →
    1 / N ≤ y0 → y0 ≤ 1 →
    (∀ α, |hH.eigenvalues α| ≤ 2 + U * (1 / q ^ 2 + (N : ℝ) ^ (-(2 : ℝ) / 3))) →
    (∀ x y : ℝ, |x| ≤ 5 → y0 ≤ y → y ≤ 1 → ‖stieltjesM H ⟨x, y⟩ - msc ⟨x, y⟩‖ ≤
      U * (min (1 / (q ^ 2 * Real.sqrt (kappa x + y))) (1 / q) + 1 / (N * y))) →
    ∀ E : ℝ, |countFn hH E - nsc E| ≤
      C * U ^ C * Real.log N * (1 / N + y0 + 1 / q ^ 3 + Real.sqrt (kappa E) / q ^ 2) := by
  refine ⟨200, by norm_num, ?_⟩
  intro N hN H hH U q y0 hU hq hy0 hy01 hev hyp E
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hy0pos : 0 < y0 := lt_of_lt_of_le (by positivity) hy0
  have hNy0 : 1 ≤ (N : ℝ) * y0 := by
    have h := hy0
    rw [div_le_iff₀ hNr] at h
    linarith
  have hL : 1 / 2 ≤ Real.log N := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_le_log (by norm_num) hN2
    norm_num at h1
    linarith
  have hqpos : 0 < q := by linarith
  have hinvN0 : 0 < 1 / (N : ℝ) := by positivity
  have hinvN : 1 / (N : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hNr (by norm_num)]
    linarith
  -- `p = 1/q` and `s = N^{-1/3}`
  have hp0 : 0 < 1 / q := by positivity
  have hp1 : 1 / q ≤ 1 := by rw [div_le_one hqpos]; exact hq
  have hp2 : 1 / q ^ 2 = (1 / q) ^ 2 := by rw [div_pow, one_pow]
  have hp3 : 1 / q ^ 3 = (1 / q) ^ 3 := by rw [div_pow, one_pow]
  have hs0 : 0 < (N : ℝ) ^ (-(1 : ℝ) / 3) := Real.rpow_pos_of_pos hNr _
  have hs2 : (N : ℝ) ^ (-(2 : ℝ) / 3) = ((N : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
    norm_num
  have hs3 : ((N : ℝ) ^ (-(1 : ℝ) / 3)) ^ 3 = 1 / N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le,
      show (-(1 : ℝ) / 3) * ((3 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one, one_div]
  set p : ℝ := 1 / q with hp
  set s : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 3) with hs
  have hκ0 : 0 ≤ kappa E := by unfold kappa; positivity
  have hsk0 := Real.sqrt_nonneg (kappa E)
  have hRk : Real.sqrt (kappa E) / q ^ 2 = Real.sqrt (kappa E) * p ^ 2 := by
    rw [← hp2]; ring
  have hReq : 1 / N + y0 + 1 / q ^ 3 + Real.sqrt (kappa E) / q ^ 2 =
      1 / N + y0 + p ^ 3 + Real.sqrt (kappa E) * p ^ 2 := by
    rw [hp3, hRk]
  rw [hReq]
  set R : ℝ := 1 / N + y0 + p ^ 3 + Real.sqrt (kappa E) * p ^ 2 with hR
  have hkp : 0 ≤ Real.sqrt (kappa E) * p ^ 2 := by positivity
  have hp3' : 0 ≤ p ^ 3 := by positivity
  have hR0 : 0 ≤ R := by positivity
  have hRN : 1 / (N : ℝ) ≤ R := by linarith
  have hRy : y0 ≤ R := by linarith
  have hRp : p ^ 3 ≤ R := by linarith
  have hLR : 0 ≤ Real.log N * R := mul_nonneg (by linarith) hR0
  suffices hmain : |countFn hH E - nsc E| ≤ 180 * U ^ 2 * Real.log N * R by
    refine hmain.trans ?_
    have hU2 : U ^ 2 ≤ U ^ (200 : ℝ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hU (by norm_num)
    calc 180 * U ^ 2 * Real.log N * R = 180 * U ^ 2 * (Real.log N * R) := by ring
      _ ≤ 200 * U ^ (200 : ℝ) * (Real.log N * R) := by
          apply mul_le_mul_of_nonneg_right _ hLR
          have : 0 ≤ U ^ 2 := by positivity
          linarith
      _ = 200 * U ^ (200 : ℝ) * Real.log N * R := by ring
  have hRHS : 0 ≤ 180 * U ^ 2 * Real.log N * R := by
    have : 0 ≤ U ^ 2 := by positivity
    have e : 180 * U ^ 2 * Real.log N * R = 180 * U ^ 2 * (Real.log N * R) := by ring
    rw [e]
    positivity
  have hn0 := countingQ_countFn_nonneg hH E
  have hn1 := countingQ_countFn_le_one hN0 hH E
  have hs0' := countingQ_nsc_nonneg E
  have hs1' := countingQ_nsc_le_one E
  have hδeq : U * (1 / q ^ 2 + (N : ℝ) ^ (-(2 : ℝ) / 3)) = U * (p ^ 2 + s ^ 2) := by
    rw [hp2, hs2]
  simp only [hδeq] at hev
  set δ : ℝ := U * (p ^ 2 + s ^ 2) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  rcases le_or_gt δ 1 with hδ1 | hδ1
  swap
  -- the regime `δ > 1`: `|n - n_sc| ≤ 1` suffices
  · have hdiff1 : |countFn hH E - nsc E| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    refine hdiff1.trans ?_
    exact countingQ_trivial hU hp0.le hs0.le hδ1 hRp (by rw [hs3]; exact hRN) hL
  -- the regime `δ ≤ 1`
  have hevl : ∀ α, -2 - δ ≤ hH.eigenvalues α := fun α => by linarith [(abs_le.1 (hev α)).1]
  have hevu : ∀ α, hH.eigenvalues α ≤ 2 + δ := fun α => (abs_le.1 (hev α)).2
  rcases lt_or_ge E (-2 - δ) with hE | hE
  · have h1 : countFn hH E = 0 := by
      unfold countFn
      rw [Finset.filter_false_of_mem fun α _ => not_le.2 (lt_of_lt_of_le hE (hevl α))]
      simp
    rw [h1, nsc_eq_zero (by linarith), sub_zero, abs_zero]
    exact hRHS
  rcases lt_or_ge (2 + δ) E with hE' | hE'
  · have h1 : countFn hH E = 1 := by
      unfold countFn
      rw [Finset.filter_true_of_mem fun α _ => (hevu α).trans hE'.le]
      simp only [Finset.card_univ, Fintype.card_fin]
      field_simp
    rw [h1, nsc_eq_one (by linarith), sub_self, abs_zero]
    exact hRHS
  -- the local law in the form used on the rectangles
  have hpt : ∀ x y : ℝ, |x| ≤ 5 → y0 ≤ y → y ≤ 1 →
      ‖stieltjesM H (x + y * Complex.I) - msc (x + y * Complex.I)‖ ≤
        U * (1 / (q ^ 2 * Real.sqrt y) + 1 / (N * y)) := by
    intro x y hx hy hy1
    have h := hyp x y hx hy hy1
    rw [Complex.mk_eq_add_mul_I] at h
    refine h.trans (mul_le_mul_of_nonneg_left (add_le_add ((min_le_left _ _).trans ?_) le_rfl)
      (by linarith))
    have hypos : 0 < y := lt_of_lt_of_le hy0pos hy
    have hkx : 0 ≤ kappa x := by unfold kappa; positivity
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by positivity)
  have hpt0 : ∀ x : ℝ, |x| ≤ 5 →
      ‖stieltjesM H (x + y0 * Complex.I) - msc (x + y0 * Complex.I)‖ ≤ 2 * U := by
    intro x hx
    have h := hyp x y0 hx le_rfl hy01
    rw [Complex.mk_eq_add_mul_I] at h
    refine h.trans ?_
    have h1 : min (1 / (q ^ 2 * Real.sqrt (kappa x + y0))) p ≤ 1 :=
      (min_le_right _ _).trans hp1
    have h2 : 1 / (N * y0) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact hNy0
    have h3 : min (1 / (q ^ 2 * Real.sqrt (kappa x + y0))) p + 1 / (N * y0) ≤ 2 := by linarith
    have := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ U)
    linarith
  -- the scale `σ`, with `σ² ≥ κ_E + δ + 2/N + y0` and `σ / q² ≤ 4 U R`
  have h2N0 : (0 : ℝ) ≤ 2 / N := by positivity
  have h2N1 : (2 : ℝ) / N ≤ 1 := by
    rw [div_le_one hNr]
    exact hN2
  have h22 : (2 : ℝ) / N = 2 * (1 / N) := by ring
  have hσsq := countingQ_sigma_sq hκ0 hU hp0.le hs0.le h2N0 hy0pos.le
  have hσp := countingQ_sigma_p (κ := kappa E) hU hp0.le hs0.le hs3 h2N0 (by linarith) h2N1
    hy0pos.le hy01
  set σ : ℝ := Real.sqrt (kappa E) + U * (p + s) + Real.sqrt (2 / N) + Real.sqrt y0 with hσ
  have hσ0 : 0 ≤ σ := by
    have : 0 ≤ U * (p + s) := by
      have : 0 ≤ U := by linarith
      positivity
    have := Real.sqrt_nonneg (2 / (N : ℝ))
    have := Real.sqrt_nonneg y0
    linarith
  have hσq : σ / q ^ 2 = σ * p ^ 2 := by rw [div_eq_mul_one_div, hp2]
  have hK : 14 * U * (σ / q ^ 2) + 24 * U * Real.log N / N + 28 * U * y0 * Real.log N +
      5 / N ≤ 180 * U ^ 2 * Real.log N * R := by
    have h := countingQ_total hU (hσq ▸ hσp) hRN hRy hL hinvN0.le
    have e : 14 * U * (σ / q ^ 2) + 24 * U * Real.log N / N + 28 * U * y0 * Real.log N +
        5 / N = 14 * U * (σ / q ^ 2) + 24 * U * Real.log N * (1 / N) +
          28 * U * y0 * Real.log N + 5 * (1 / N) := by ring
    rw [e]
    exact h
  -- the two rectangles
  set η : ℝ := 1 / (N : ℝ) ^ 2 with hη
  have hy0σ : y0 ≤ σ ^ 2 := by linarith
  have hRB : ∀ c d : ℝ, c ≤ d → -5 ≤ c → d ≤ 5 → d - c ≤ σ ^ 2 →
      |(∫ x in c..d, (stieltjesM H (x + η * Complex.I)).im) -
        ∫ x in c..d, (msc (x + η * Complex.I)).im| ≤
      14 * U * (σ / q ^ 2) + 24 * U * Real.log N / N + 28 * U * y0 * Real.log N :=
    fun c d h1 h2 h3 h4 =>
      countingQ_rect_bound hN hH hU hq hy0 hy01 hη hpt hpt0 h1 h2 h3 hσ0 h4 hy0σ
  have hσ' : kappa E + δ + 2 * (1 / N) ≤ σ ^ 2 := by linarith
  have h55 : (5 : ℝ) / N = 5 * (1 / N) := by ring
  rw [h55] at hK
  rcases le_or_gt E 0 with hE0 | hE0
  · exact (countingQ_left hN hH hevl hδ0 hδ1 hE hE0 hη hσ' hRB).trans hK
  · exact (countingQ_right hN hH hevl hevu hδ0 hδ1 hE0 hE' hη hσ' hRB).trans hK

/-! ### Compiled check at a concrete nondegenerate point

`N = 2`, `H = [[0, 1], [1, 0]]` (symmetric, eigenvalues `-1` and `1`), `U = 8`, `q = 2`,
`y0 = 3/4`, `E = 1`. The hypothesis on `m - m_sc` holds because `‖m(z)‖ ≤ 1 / Im z` and
`‖m_sc(z)‖ < 1` ((2.10)), while `κ_x + y ≤ 4` for `|x| ≤ 5`, `y ≤ 1`, so that the `min` is at
least `1/8`. -/

private def countingQCheckMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

private lemma countingQCheckMatrix_isHermitian : countingQCheckMatrix.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [countingQCheckMatrix]

/-- The eigenvalues of `[[0, 1], [1, 0]]` satisfy `λ² = 1`, hence `|λ| ≤ 1`. -/
private lemma countingQCheckMatrix_eigenvalues (α : Fin 2) :
    |countingQCheckMatrix_isHermitian.eigenvalues α| ≤ 1 := by
  have h := countingQCheckMatrix_isHermitian.eigenvalues_mem_spectrum_real α
  set r := countingQCheckMatrix_isHermitian.eigenvalues α
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    Algebra.algebraMap_eq_smul_one, Matrix.det_fin_two] at h
  simp [countingQCheckMatrix] at h
  rw [abs_le]
  constructor <;> nlinarith

example : ∃ C > 0, |countFn countingQCheckMatrix_isHermitian 1 - nsc 1| ≤
    C * (8 : ℝ) ^ C * Real.log ((2 : ℕ) : ℝ) *
      (1 / ((2 : ℕ) : ℝ) + 3 / 4 + 1 / (2 : ℝ) ^ 3 + Real.sqrt (kappa 1) / (2 : ℝ) ^ 2) := by
  obtain ⟨C, hC, h⟩ := abs_countFn_sub_nsc_le_q
  refine ⟨C, hC, h 2 le_rfl countingQCheckMatrix countingQCheckMatrix_isHermitian 8 2 (3 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun α => ?_) ?_ 1⟩
  · have h1 := (abs_le.1 (countingQCheckMatrix_eigenvalues α)).2
    have h1' := (abs_le.1 (countingQCheckMatrix_eigenvalues α)).1
    have h2 : 0 ≤ ((2 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg (by norm_num) _
    rw [abs_le]
    constructor <;> nlinarith
  · intro x y hx hy hy1
    rw [Complex.mk_eq_add_mul_I]
    have hy0 : 0 < y := by linarith
    have hz : 0 < ((x : ℂ) + y * Complex.I).im := by simpa using hy0
    have h1 := norm_stieltjesM_le_inv_im (by norm_num) countingQCheckMatrix_isHermitian hz
    have h2 := (norm_msc_eq_inv_and_lt_one hz).2
    have him : ((x : ℂ) + y * Complex.I).im = y := by simp
    rw [him] at h1
    have hk : kappa x ≤ 3 := by
      unfold kappa
      rw [abs_le]
      have := abs_nonneg x
      constructor <;> linarith
    have hk0 : 0 ≤ kappa x := by unfold kappa; positivity
    have hsq : Real.sqrt (kappa x + y) ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      linarith
    have hsqpos : 0 < Real.sqrt (kappa x + y) := Real.sqrt_pos.2 (by linarith)
    have hm1 : 1 / 8 ≤ 1 / ((2 : ℝ) ^ 2 * Real.sqrt (kappa x + y)) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have hmin : 1 / 8 ≤ min (1 / ((2 : ℝ) ^ 2 * Real.sqrt (kappa x + y))) (1 / 2) :=
      le_min hm1 (by norm_num)
    have hinv : 0 ≤ 1 / y := by positivity
    have e : (8 : ℝ) * (1 / (((2 : ℕ) : ℝ) * y)) = 4 * (1 / y) := by
      push_cast
      field_simp
      ring
    calc ‖stieltjesM countingQCheckMatrix (x + y * Complex.I) - msc (x + y * Complex.I)‖
        ≤ ‖stieltjesM countingQCheckMatrix (x + y * Complex.I)‖ + ‖msc (x + y * Complex.I)‖ :=
          norm_sub_le _ _
      _ ≤ 8 * (min (1 / ((2 : ℝ) ^ 2 * Real.sqrt (kappa x + y))) (1 / 2) +
          1 / (((2 : ℕ) : ℝ) * y)) := by
          rw [mul_add, e]
          nlinarith

#print axioms abs_countFn_sub_nsc_le_q

end WEdgeNS
