import WEdgeNS.Semicircle.Stieltjes
import WEdgeNS.Semicircle.Bounds
import WEdgeNS.Resolvent.Spectral

/-!
# Counting function from the Stieltjes transform ([26] §5, Helffer–Sjöstrand)
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-! ### The Stieltjes transform of `H` as a sum over eigenvalues -/

/-- `m` is holomorphic on the upper half-plane. -/
lemma differentiableOn_stieltjesM_upperHalfPlane {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) : DifferentiableOn ℂ (stieltjesM H) {z : ℂ | 0 < z.im} := by
  have hd : DifferentiableOn ℂ
      (fun z : ℂ => (N : ℂ)⁻¹ * ∑ α, ((hH.eigenvalues α : ℂ) - z)⁻¹) {z : ℂ | 0 < z.im} := by
    refine DifferentiableOn.const_mul ?_ _
    refine DifferentiableOn.fun_sum fun α _ => ?_
    exact ((differentiableOn_const _).sub differentiableOn_id).inv
      fun z hz => eigenvalue_sub_ne_zero_of_im_pos hH hz α
  exact hd.congr fun z hz => stieltjesM_eq_sum hH hz

/-- `m_sc` is holomorphic on the upper half-plane. -/
lemma differentiableOn_msc_upperHalfPlane : DifferentiableOn ℂ msc {z : ℂ | 0 < z.im} := by
  have := isProbabilityMeasure_semicircle
  have h := (analyticOn_resolventTransform (μ := semicircle)).differentiableOn
  have hsub : {z : ℂ | 0 < z.im} ⊆ (algebraMap ℝ ℂ '' semicircle.support)ᶜ := by
    intro z hz
    rintro ⟨x, -, rfl⟩
    simp at hz
  exact (h.mono hsub).congr fun z hz => msc_eq_resolventTransform hz

/-- A function holomorphic on the upper half-plane is continuous along each horizontal line
`Im z = η > 0`. -/
lemma continuous_horizontal_of_differentiableOn {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im}) {η : ℝ} (hη : 0 < η) :
    Continuous (fun x : ℝ => f (x + η * Complex.I)) := by
  have hc : Continuous (fun x : ℝ => (x : ℂ) + η * Complex.I) := by fun_prop
  refine hf.continuousOn.comp_continuous hc fun x => ?_
  simpa using hη

/-! ### Cauchy's theorem on a rectangle in the upper half-plane -/

/-- Cauchy's theorem on the rectangle `[a, b] × [η, h]` in the upper half-plane: for `f`
holomorphic there, the signed integral of `f` over the boundary vanishes. -/
lemma integral_rect_eq_zero_of_differentiableOn {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (a b : ℝ) {η h : ℝ} (hη : 0 < η) (hηh : η ≤ h) :
    (∫ x : ℝ in a..b, f (x + η * Complex.I)) - (∫ x : ℝ in a..b, f (x + h * Complex.I)) +
      Complex.I • (∫ y : ℝ in η..h, f (b + y * Complex.I)) -
      Complex.I • (∫ y : ℝ in η..h, f (a + y * Complex.I)) = 0 := by
  have hsub : Set.uIcc (⟨a, η⟩ : ℂ).re (⟨b, h⟩ : ℂ).re ×ℂ
      Set.uIcc (⟨a, η⟩ : ℂ).im (⟨b, h⟩ : ℂ).im ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    have h2 := hz.2
    simp only [Set.uIcc_of_le hηh, Set.mem_Icc] at h2
    exact lt_of_lt_of_le hη h2.1
  have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨a, η⟩ ⟨b, h⟩
    (hf.mono hsub)
  simpa using this

/-! ### Extension of the bound below `y0` ((5.4)–(5.8)) -/

/-- Termwise integrated form of (5.5)–(5.7): for `0 < y ≤ y0`,
`‖(λ - x - iy)⁻¹ - (λ - x - iy0)⁻¹‖ ≤ (y0 / y) · y0 / ((λ - x)² + y0²)`. -/
lemma norm_resolvent_term_sub_le (l x : ℝ) {y y0 : ℝ} (hy : 0 < y) (hyy0 : y ≤ y0) :
    ‖((l : ℂ) - (x + y * Complex.I))⁻¹ - ((l : ℂ) - (x + y0 * Complex.I))⁻¹‖ ≤
      y0 / y * (y0 / ((l - x) ^ 2 + y0 ^ 2)) := by
  have hy0 : 0 < y0 := lt_of_lt_of_le hy hyy0
  set w : ℂ := (l : ℂ) - (x + y * Complex.I) with hw
  set w0 : ℂ := (l : ℂ) - (x + y0 * Complex.I) with hw0
  have hwn : ‖w‖ ^ 2 = (l - x) ^ 2 + y ^ 2 := by
    rw [hw, Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hw0n : ‖w0‖ ^ 2 = (l - x) ^ 2 + y0 ^ 2 := by
    rw [hw0, Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hwne : w ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp [hw] at this; linarith
  have hw0ne : w0 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp [hw0] at this; linarith
  have hA : 0 < ‖w‖ := norm_pos_iff.2 hwne
  have hB : 0 < ‖w0‖ := norm_pos_iff.2 hw0ne
  have hww0 : w0 - w = ((y - y0 : ℝ) : ℂ) * Complex.I := by
    rw [hw, hw0]; push_cast; ring
  rw [inv_sub_inv hwne hw0ne, norm_div, norm_mul, hww0, norm_mul, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith), mul_one, ← hw0n]
  have key : y * ‖w0‖ ≤ y0 * ‖w‖ := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 : (y0 * ‖w‖) ^ 2 < (y * ‖w0‖) ^ 2 := by
      have := mul_pos hy0 hA
      nlinarith
    rw [mul_pow, mul_pow, hwn, hw0n] at h1
    nlinarith [sq_nonneg (l - x), mul_le_mul hyy0 hyy0 hy.le hy0.le]
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : (y0 - y) * ‖w0‖ * (y * ‖w0‖) ≤ (y0 - y) * ‖w0‖ * (y0 * ‖w‖) :=
    mul_le_mul_of_nonneg_left key (mul_nonneg (by linarith) hB.le)
  have h3 : 0 ≤ y * ‖w0‖ * (y0 * ‖w‖) := by positivity
  nlinarith

/-- (5.4)–(5.8): a bound `U / (N y)` on `[y0, 1]` extends to `3 (U + N y0) / (N y)` on `(0, 1]`. -/
private lemma counting_ext {N : ℕ} (hN : 0 < N) {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {U y0 : ℝ} (hU : 0 ≤ U) (hy0 : 0 < y0)
    (hyp : ∀ x y : ℝ, |x| ≤ 4 → y0 ≤ y → y ≤ 1 →
      ‖stieltjesM H (x + y * Complex.I) - msc (x + y * Complex.I)‖ ≤ U / (N * y))
    (hy01 : y0 ≤ 1) {x y : ℝ} (hx : |x| ≤ 4) (hy : 0 < y) (hy1 : y ≤ 1) :
    ‖stieltjesM H (x + y * Complex.I) - msc (x + y * Complex.I)‖ ≤
      3 * (U + N * y0) / (N * y) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rcases le_or_gt y0 y with hle | hlt
  · refine (hyp x y hx hle hy1).trans ?_
    gcongr
    nlinarith [mul_pos hNr hy0]
  · have hz : 0 < ((x : ℂ) + y * Complex.I).im := by simpa using hy
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
              norm_resolvent_term_sub_le _ x hy hlt.le) (by positivity)
        _ = y0 / y * ((N : ℝ)⁻¹ * ∑ α, y0 / ((hH.eigenvalues α - x) ^ 2 + y0 ^ 2)) := by
            rw [← Finset.mul_sum]; ring
    have h2 := hyp x y0 hx le_rfl hy01
    have h3 := (norm_msc_eq_inv_and_lt_one hz0).2
    have h4 := (norm_msc_eq_inv_and_lt_one hz).2
    have h5 : (stieltjesM H (x + y0 * Complex.I)).im ≤ 1 + U / (N * y0) := by
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
    have hq : U / (N * y0) ≤ U / (N * y) := by gcongr
    have hq0 : 0 ≤ U / (N * y) := by positivity
    have heq1 : y0 / y * (1 + U / (N * y0)) = y0 / y + U / (N * y) := by
      field_simp
    have heq2 : 3 * (U + N * y0) / (N * y) = 3 * (U / (N * y)) + 3 * (y0 / y) := by
      field_simp
    have h6 : y0 / y * (stieltjesM H (x + y0 * Complex.I)).im ≤ y0 / y + U / (N * y) := by
      rw [← heq1]
      exact mul_le_mul_of_nonneg_left h5 (by positivity)
    rw [heq2]
    linarith

/-! ### Cauchy's theorem applied to `m - m_sc` -/

/-- `∫_a^b Im m(x + iη) dx` and `∫_a^b Im m_sc(x + iη) dx` (`π` times the Poisson-smoothed counts
of `H` and of `ρ_sc` on `[a, b]`) differ by at most `V / N · (b - a) + 2 V / N · log(1 / η)` when
`‖m - m_sc‖ ≤ V / (N y)` on `|x| ≤ 4`, `0 < y ≤ 1` (the analogue of (5.9) of [26] §5). -/
private lemma counting_diff {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {V : ℝ}
    (hext : ∀ x y : ℝ, |x| ≤ 4 → 0 < y → y ≤ 1 →
      ‖stieltjesM H (x + y * Complex.I) - msc (x + y * Complex.I)‖ ≤ V / (N * y))
    {a b η : ℝ} (ha : -4 ≤ a) (hab : a ≤ b) (hb : b ≤ 4) (hη : 0 < η) (hη1 : η ≤ 1) :
    |(∫ x in a..b, (stieltjesM H (x + η * Complex.I)).im) -
        ∫ x in a..b, (msc (x + η * Complex.I)).im| ≤
      V / N * (b - a) + 2 * (V / N * Real.log (1 / η)) := by
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
  have hrect := integral_rect_eq_zero_of_differentiableOn hfd a b hη hη1
  have heq : (∫ x in a..b, f (x + η * Complex.I)) =
      (∫ x in a..b, f (x + (1 : ℝ) * Complex.I)) -
        (Complex.I • (∫ y in η..1, f (b + y * Complex.I)) -
          Complex.I • (∫ y in η..1, f (a + y * Complex.I))) := by
    linear_combination hrect
  rw [heq]
  have hh : ‖∫ x in a..b, f (x + (1 : ℝ) * Complex.I)‖ ≤ V / N * (b - a) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (C := V / (N * 1))
      (f := fun x : ℝ => f (x + (1 : ℝ) * Complex.I)) (a := a) (b := b) (fun x hx => by
        rw [Set.uIoc_of_le hab] at hx
        exact hext x 1 (abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩) one_pos le_rfl)
    rw [mul_one, abs_of_nonneg (sub_nonneg.2 hab)] at this
    exact this
  have hv : ∀ c : ℝ, |c| ≤ 4 → ‖∫ y in η..1, f (c + y * Complex.I)‖ ≤
      V / N * Real.log (1 / η) := by
    intro c hc
    have hg : IntervalIntegrable (fun y : ℝ => V / N * y⁻¹) volume η 1 := by
      refine (intervalIntegral.intervalIntegrable_inv (fun y hy => ?_)
        continuousOn_id).const_mul _
      rw [Set.uIcc_of_le hη1] at hy
      exact (lt_of_lt_of_le hη hy.1).ne'
    have := intervalIntegral.norm_integral_le_of_norm_le hη1
      (Eventually.of_forall fun y (hy : y ∈ Set.Ioc η 1) =>
        (hext c y hc (hη.trans hy.1) hy.2).trans_eq
          (by rw [div_mul_eq_div_div, div_eq_mul_inv])) hg
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hη one_pos] at this
    exact this
  calc ‖(∫ x in a..b, f (x + (1 : ℝ) * Complex.I)) -
        (Complex.I • (∫ y in η..1, f (b + y * Complex.I)) -
          Complex.I • (∫ y in η..1, f (a + y * Complex.I)))‖
      ≤ ‖∫ x in a..b, f (x + (1 : ℝ) * Complex.I)‖ +
        (‖Complex.I • (∫ y in η..1, f (b + y * Complex.I))‖ +
          ‖Complex.I • (∫ y in η..1, f (a + y * Complex.I))‖) :=
        (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
    _ = ‖∫ x in a..b, f (x + (1 : ℝ) * Complex.I)‖ +
        (‖∫ y in η..1, f (b + y * Complex.I)‖ + ‖∫ y in η..1, f (a + y * Complex.I)‖) := by
        rw [norm_smul, norm_smul, Complex.norm_I, one_mul, one_mul]
    _ ≤ V / N * (b - a) + (V / N * Real.log (1 / η) + V / N * Real.log (1 / η)) :=
        add_le_add hh (add_le_add (hv b (abs_le.2 ⟨by linarith, hb⟩))
          (hv a (abs_le.2 ⟨ha, by linarith⟩)))
    _ = V / N * (b - a) + 2 * (V / N * Real.log (1 / η)) := by ring

/-! ### The semicircle side -/

/-- `|∫_a^b Im m_sc(x + iη) dx - π ∫_a^b ρ_sc| ≤ 2η`, from Cauchy's theorem on
`[a, b] × [η', η]`, `|m_sc| < 1` ((2.10)) and `π⁻¹ Im m_sc(x + iη') → ρ_sc(x)`. -/
lemma abs_integral_im_msc_sub_pi_mul_integral_rhoSc_le (a b : ℝ) {η : ℝ} (hη : 0 < η) :
    |(∫ x in a..b, (msc (x + η * Complex.I)).im) - Real.pi * ∫ x in a..b, rhoSc x| ≤ 2 * η := by
  have hJ : ∀ η' : ℝ, 0 < η' → η' ≤ η →
      |(∫ x in a..b, (msc (x + η' * Complex.I)).im) -
        ∫ x in a..b, (msc (x + η * Complex.I)).im| ≤ 2 * η := by
    intro η' hη' hle
    have hc' := continuous_horizontal_of_differentiableOn differentiableOn_msc_upperHalfPlane hη'
    have hc := continuous_horizontal_of_differentiableOn differentiableOn_msc_upperHalfPlane hη
    have e1 := Complex.imCLM.intervalIntegral_comp_comm (hc'.intervalIntegrable (μ := volume) a b)
    have e2 := Complex.imCLM.intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) a b)
    simp only [Complex.imCLM_apply] at e1 e2
    rw [e1, e2, ← Complex.sub_im]
    refine (Complex.abs_im_le_norm _).trans ?_
    have hrect :=
      integral_rect_eq_zero_of_differentiableOn differentiableOn_msc_upperHalfPlane a b hη' hle
    have heq : (∫ x in a..b, msc (x + η' * Complex.I)) - ∫ x in a..b, msc (x + η * Complex.I) =
        -(Complex.I • (∫ y in η'..η, msc (b + y * Complex.I)) -
          Complex.I • (∫ y in η'..η, msc (a + y * Complex.I))) := by
      linear_combination hrect
    rw [heq, norm_neg]
    have hv : ∀ c : ℝ, ‖∫ y in η'..η, msc (c + y * Complex.I)‖ ≤ η := by
      intro c
      have := intervalIntegral.norm_integral_le_of_norm_le_const (C := 1)
        (f := fun y : ℝ => msc (c + y * Complex.I)) (a := η') (b := η) (fun y hy => by
          rw [Set.uIoc_of_le hle] at hy
          exact (norm_msc_eq_inv_and_lt_one (by simpa using hη'.trans hy.1)).2.le)
      rw [one_mul, abs_of_nonneg (by linarith)] at this
      linarith
    calc ‖Complex.I • (∫ y in η'..η, msc (b + y * Complex.I)) -
          Complex.I • (∫ y in η'..η, msc (a + y * Complex.I))‖
        ≤ ‖Complex.I • (∫ y in η'..η, msc (b + y * Complex.I))‖ +
          ‖Complex.I • (∫ y in η'..η, msc (a + y * Complex.I))‖ := norm_sub_le _ _
      _ = ‖∫ y in η'..η, msc (b + y * Complex.I)‖ + ‖∫ y in η'..η, msc (a + y * Complex.I)‖ := by
          rw [norm_smul, norm_smul, Complex.norm_I, one_mul, one_mul]
      _ ≤ η + η := add_le_add (hv b) (hv a)
      _ = 2 * η := by ring
  have hlim : Tendsto (fun η' : ℝ => ∫ x in a..b, (msc (x + η' * Complex.I)).im) (𝓝[>] 0)
      (𝓝 (∫ x in a..b, Real.pi * rhoSc x)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
      ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [self_mem_nhdsWithin] with η' hη'
      exact (Complex.continuous_im.comp (continuous_horizontal_of_differentiableOn
        differentiableOn_msc_upperHalfPlane hη')).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with η' hη'
      refine Eventually.of_forall fun x _ => ?_
      rw [Real.norm_eq_abs]
      exact (Complex.abs_im_le_norm _).trans
        (norm_msc_eq_inv_and_lt_one (by simpa using hη')).2.le
    · refine Eventually.of_forall fun x _ => ?_
      have := (tendsto_im_msc x).const_mul Real.pi
      refine this.congr' (Eventually.of_forall fun η' => ?_)
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      simp only
      field_simp
  rw [intervalIntegral.integral_const_mul] at hlim
  have hlim2 := (hlim.sub_const (∫ x in a..b, (msc (x + η * Complex.I)).im)).abs
  have hfin := le_of_tendsto hlim2 (by
    filter_upwards [Ioo_mem_nhdsGT hη] with η' hη' using hJ η' hη'.1 hη'.2.le)
  rw [abs_sub_comm]
  exact hfin

/-- `π |∫_c^d ρ_sc| ≤ |d - c|`, since `ρ_sc ≤ 1/π` ((2.9)). -/
lemma pi_mul_abs_integral_rhoSc_le (c d : ℝ) :
    Real.pi * |∫ x in c..d, rhoSc x| ≤ |d - c| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := d)
    (C := 1 / Real.pi) (f := rhoSc) (fun x _ => by
      have hs : Real.sqrt (4 - x ^ 2) ≤ 2 := by
        calc Real.sqrt (4 - x ^ 2) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
          _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [Real.norm_eq_abs, abs_of_nonneg (by unfold rhoSc; positivity)]
      unfold rhoSc
      rw [div_le_div_iff₀ (by positivity) Real.pi_pos]
      nlinarith [Real.pi_pos])
  rw [Real.norm_eq_abs] at h
  calc Real.pi * |∫ x in c..d, rhoSc x| ≤ Real.pi * (1 / Real.pi * |d - c|) :=
        mul_le_mul_of_nonneg_left h Real.pi_pos.le
    _ = |d - c| := by field_simp

private lemma counting_continuous_rhoSc : Continuous rhoSc := by
  unfold rhoSc
  fun_prop

private lemma counting_integrable_rhoSc : Integrable rhoSc := by
  refine counting_continuous_rhoSc.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := -2) (b := 2)) fun x hx => ?_
  unfold rhoSc
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rw [Real.sqrt_eq_zero_of_nonpos (by rcases hx with h | h <;> nlinarith), zero_div]

/-- `n_sc(E) = ∫_{-4}^E ρ_sc`. -/
private lemma counting_nsc_eq (E : ℝ) : nsc E = ∫ x in (-4 : ℝ)..E, rhoSc x := by
  have h := intervalIntegral.integral_Iic_sub_Iic (f := rhoSc) (μ := volume) (a := -4) (b := E)
    counting_integrable_rhoSc.integrableOn counting_integrable_rhoSc.integrableOn
  have h0 : nsc (-4) = 0 := nsc_eq_zero (by norm_num)
  unfold nsc at h0 ⊢
  rw [← h, h0, sub_zero]

/-! ### The empirical side -/

/-- `∫_a^b Im m(x + iη) dx = N⁻¹ Σ_α (arctan((b - λ_α)/η) - arctan((a - λ_α)/η))`. -/
lemma integral_im_stieltjesM_eq_sum_arctan {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (a b : ℝ) {η : ℝ} (hη : 0 < η) :
    ∫ x in a..b, (stieltjesM H (x + η * Complex.I)).im =
      (N : ℝ)⁻¹ * ∑ α, (Real.arctan ((b - hH.eigenvalues α) / η) -
        Real.arctan ((a - hH.eigenvalues α) / η)) := by
  have hpt : ∀ x : ℝ, (stieltjesM H (x + η * Complex.I)).im =
      (N : ℝ)⁻¹ * ∑ α, η / ((hH.eigenvalues α - x) ^ 2 + η ^ 2) := by
    intro x
    rw [im_stieltjesM_eq hH (by simpa using hη)]
    simp
  have hc : ∀ α : Fin N, Continuous fun x : ℝ => η / ((hH.eigenvalues α - x) ^ 2 + η ^ 2) :=
    fun α => continuous_const.div (by fun_prop) fun x => by positivity
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum fun α _ => (hc α).intervalIntegrable a b]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [show (a - hH.eigenvalues α) / η = (fun x => (x - hH.eigenvalues α) / η) a by rfl,
    show (b - hH.eigenvalues α) / η = (fun x => (x - hH.eigenvalues α) / η) b by rfl]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => Real.arctan ((x - hH.eigenvalues α) / η)) (fun x _ => ?_)
    ((hc α).intervalIntegrable a b)
  have h1 : HasDerivAt (fun x : ℝ => (x - hH.eigenvalues α) / η) (1 / η) x :=
    ((hasDerivAt_id x).sub_const _).div_const η
  have h2 : HasDerivAt (fun x => Real.arctan ((x - hH.eigenvalues α) / η))
      (1 / (1 + ((x - hH.eigenvalues α) / η) ^ 2) * (1 / η)) x :=
    h1.arctan
  refine h2.congr_deriv ?_
  rw [div_pow]
  field_simp
  ring

/-- `π/2 - 1/t ≤ arctan s` for `0 < t ≤ s`. -/
lemma pi_div_two_sub_inv_le_arctan {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) :
    Real.pi / 2 - 1 / t ≤ Real.arctan s := by
  have h1 := Real.arctan_inv_of_pos ht
  have h2 := Real.arctan_le_self (inv_nonneg.2 ht.le)
  have h3 := Real.arctan_strictMono.monotone hts
  rw [one_div]
  linarith

/-- Lower bound: `π n(E) - 2/N ≤ ∫_a^b Im m(x + iη) dx` when every eigenvalue is at least `η N`
to the right of `a`, and every eigenvalue `≤ E` is at least `η N` to the left of `b`. -/
lemma pi_mul_countFn_sub_two_div_le_integral_im_stieltjesM {N : ℕ} (hN : 0 < N)
    {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) {E a b η : ℝ} (hη : 0 < η) (hab : a ≤ b)
    (hb : ∀ α, hH.eigenvalues α ≤ E → (N : ℝ) ≤ (b - hH.eigenvalues α) / η)
    (ha : ∀ α, (N : ℝ) ≤ (hH.eigenvalues α - a) / η) :
    Real.pi * countFn hH E - 2 / N ≤ ∫ x in a..b, (stieltjesM H (x + η * Complex.I)).im := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [integral_im_stieltjesM_eq_sum_arctan hH a b hη]
  have hterm : ∀ α, (if hH.eigenvalues α ≤ E then Real.pi - 2 / N else 0) ≤
      Real.arctan ((b - hH.eigenvalues α) / η) - Real.arctan ((a - hH.eigenvalues α) / η) := by
    intro α
    have hmono : Real.arctan ((a - hH.eigenvalues α) / η) ≤
        Real.arctan ((b - hH.eigenvalues α) / η) :=
      Real.arctan_strictMono.monotone (div_le_div_of_nonneg_right (by linarith) hη.le)
    split_ifs with h
    · have h1 := pi_div_two_sub_inv_le_arctan hNr (hb α h)
      have h2 := pi_div_two_sub_inv_le_arctan hNr (ha α)
      have h3 : (a - hH.eigenvalues α) / η = -((hH.eigenvalues α - a) / η) := by ring
      rw [h3, Real.arctan_neg]
      have h4 : (2 : ℝ) / N = 2 * (1 / N) := by ring
      linarith
    · linarith
  have hsum := Finset.sum_le_sum fun α (_ : α ∈ Finset.univ) => hterm α
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul] at hsum
  set c : ℝ := ((Finset.univ.filter (fun α => hH.eigenvalues α ≤ E)).card : ℝ) with hc
  have hcN : c ≤ N := by
    rw [hc]
    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  have hc0 : 0 ≤ c := by positivity
  unfold countFn
  rw [← hc]
  have e : (N : ℝ)⁻¹ * (c * (Real.pi - 2 / N)) = Real.pi * (c / N) - 2 / N * (c / N) := by
    field_simp
  have hcN' : c / N ≤ 1 := by rw [div_le_one hNr]; exact hcN
  have h2N : 2 / N * (c / N) ≤ 2 / N := by
    have := mul_le_mul_of_nonneg_left hcN' (by positivity : (0 : ℝ) ≤ 2 / N)
    linarith
  have := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹)
  linarith

/-- Upper bound: `∫_a^b Im m(x + iη) dx ≤ π n(E) + 1/N` when every eigenvalue `> E` is at least
`η N` to the right of `b`. -/
lemma integral_im_stieltjesM_le_pi_mul_countFn_add_inv {N : ℕ} (hN : 0 < N)
    {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) {E a b η : ℝ} (hη : 0 < η)
    (hb : ∀ α, E < hH.eigenvalues α → (N : ℝ) ≤ (hH.eigenvalues α - b) / η) :
    ∫ x in a..b, (stieltjesM H (x + η * Complex.I)).im ≤ Real.pi * countFn hH E + 1 / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [integral_im_stieltjesM_eq_sum_arctan hH a b hη]
  have hterm : ∀ α, Real.arctan ((b - hH.eigenvalues α) / η) -
      Real.arctan ((a - hH.eigenvalues α) / η) ≤
        (if hH.eigenvalues α ≤ E then Real.pi else 1 / N) := by
    intro α
    have h0 := Real.neg_pi_div_two_lt_arctan ((a - hH.eigenvalues α) / η)
    split_ifs with h
    · have := Real.arctan_lt_pi_div_two ((b - hH.eigenvalues α) / η)
      linarith
    · have h1 := pi_div_two_sub_inv_le_arctan hNr (hb α (not_le.1 h))
      have h3 : (b - hH.eigenvalues α) / η = -((hH.eigenvalues α - b) / η) := by ring
      rw [h3, Real.arctan_neg]
      linarith
  have hsum := Finset.sum_le_sum fun α (_ : α ∈ Finset.univ) => hterm α
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul] at hsum
  set c : ℝ := ((Finset.univ.filter (fun α => hH.eigenvalues α ≤ E)).card : ℝ) with hc
  set c' : ℝ := ((Finset.univ.filter (fun α => ¬hH.eigenvalues α ≤ E)).card : ℝ) with hc'
  have hcN : c' ≤ N := by
    rw [hc']
    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  unfold countFn
  rw [← hc]
  have e : (N : ℝ)⁻¹ * (c * Real.pi + c' * (1 / N)) =
      Real.pi * (c / N) + c' / N * (1 / N) := by
    field_simp
  have hcN' : c' / N ≤ 1 := by rw [div_le_one hNr]; exact hcN
  have h2N : c' / N * (1 / N) ≤ 1 / N := by
    have := mul_le_mul_of_nonneg_right hcN' (by positivity : (0 : ℝ) ≤ 1 / N)
    linarith
  have := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹)
  linarith

/-! ### The counting estimate -/

/-- [26] §5, (5.4)–(5.11) with `K = 3`: a Stieltjes-transform bound on `y ≥ y0` gives a
bound on `|n(E) - n_sc(E)|`. -/
theorem abs_countFn_sub_nsc_le : ∃ C > 0, ∀ N : ℕ, 2 ≤ N →
    ∀ (H : Matrix (Fin N) (Fin N) ℝ) (hH : H.IsHermitian) (U y0 : ℝ), 1 ≤ U → 1 / N ≤ y0 →
    y0 ≤ 1 → (∀ α, |hH.eigenvalues α| ≤ 3) →
    (∀ x y : ℝ, |x| ≤ 4 → y0 ≤ y → y ≤ 1 →
      ‖stieltjesM H (x + y * Complex.I) - msc (x + y * Complex.I)‖ ≤ U / (N * y)) →
    ∀ E : ℝ, |countFn hH E - nsc E| ≤ C * (U + N * y0) * Real.log N / N := by
  refine ⟨100, by norm_num, ?_⟩
  intro N hN H hH U y0 hU hy0 hy01 hev hyp E
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hy0pos : 0 < y0 := lt_of_lt_of_le (by positivity) hy0
  have hNy0 : 1 ≤ N * y0 := by
    rw [div_le_iff₀ hNr] at hy0
    linarith
  set W := U + N * y0 with hW
  have hW2 : 2 ≤ W := by linarith
  have hL : 1 / 2 ≤ Real.log N := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_le_log (by norm_num) hN2
    norm_num at h1
    linarith
  have hRHS : 0 ≤ 100 * W * Real.log N / N :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) hNr.le
  have hevl : ∀ α, -3 ≤ hH.eigenvalues α := fun α => (abs_le.1 (hev α)).1
  have hevu : ∀ α, hH.eigenvalues α ≤ 3 := fun α => (abs_le.1 (hev α)).2
  rcases lt_or_ge E (-3) with hE | hE
  · have h1 : countFn hH E = 0 := by
      unfold countFn
      rw [Finset.filter_false_of_mem fun α _ => not_le.2 (lt_of_lt_of_le hE (hevl α))]
      simp
    rw [h1, nsc_eq_zero (by linarith), sub_zero, abs_zero]
    exact hRHS
  rcases lt_or_ge 3 E with hE' | hE'
  · have h1 : countFn hH E = 1 := by
      unfold countFn
      rw [Finset.filter_true_of_mem fun α _ => (hevu α).trans hE'.le]
      simp only [Finset.card_univ, Fintype.card_fin]
      field_simp
    rw [h1, nsc_eq_one (by linarith), sub_self, abs_zero]
    exact hRHS
  -- the main case `-3 ≤ E ≤ 3`
  set V := 3 * W with hV
  have hext : ∀ x y : ℝ, |x| ≤ 4 → 0 < y → y ≤ 1 →
      ‖stieltjesM H (x + y * Complex.I) - msc (x + y * Complex.I)‖ ≤ V / (N * y) :=
    fun x y hx hy hy1 => counting_ext hN0 hH (by linarith) hy0pos hyp hy01 hx hy hy1
  set η : ℝ := 1 / (N : ℝ) ^ 2 with hη
  have hηpos : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_one (by positivity)]
    nlinarith
  have hlogη : Real.log (1 / η) = 2 * Real.log N := by
    rw [hη, one_div_one_div, Real.log_pow]
    push_cast
    ring
  have hη2 : 2 * η ≤ 1 / N := by
    rw [hη, mul_one_div, div_le_div_iff₀ (by positivity) hNr]
    nlinarith
  have hinvN : 1 / (N : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hNr (by norm_num)]
    linarith
  have hinvN0 : 0 < 1 / (N : ℝ) := by positivity
  have hdiv : ∀ t : ℝ, 1 / N ≤ t → (N : ℝ) ≤ t / η := by
    intro t ht
    rw [le_div_iff₀ hηpos, hη]
    calc (N : ℝ) * (1 / (N : ℝ) ^ 2) = 1 / N := by field_simp
      _ ≤ t := ht
  set bp := E + 1 / N with hbp
  set bm := E - 1 / N with hbm
  -- the empirical side
  have hI1 : Real.pi * countFn hH E - 2 / N ≤
      ∫ x in (-4 : ℝ)..bp, (stieltjesM H (x + η * Complex.I)).im :=
    pi_mul_countFn_sub_two_div_le_integral_im_stieltjesM hN0 hH hηpos (by linarith)
      (fun α hα => hdiv _ (by linarith)) (fun α => hdiv _ (by linarith [hevl α]))
  have hI2 : ∫ x in (-4 : ℝ)..bm, (stieltjesM H (x + η * Complex.I)).im ≤
      Real.pi * countFn hH E + 1 / N :=
    integral_im_stieltjesM_le_pi_mul_countFn_add_inv hN0 hH hηpos (fun α hα => hdiv _ (by linarith))
  -- the comparison of the two Stieltjes transforms
  have hD1 := counting_diff hH hext (le_refl (-4)) (by linarith : (-4 : ℝ) ≤ bp)
    (by linarith : bp ≤ 4) hηpos hη1
  have hD2 := counting_diff hH hext (le_refl (-4)) (by linarith : (-4 : ℝ) ≤ bm)
    (by linarith : bm ≤ 4) hηpos hη1
  -- the semicircle side
  have hS1 := abs_integral_im_msc_sub_pi_mul_integral_rhoSc_le (-4) bp hηpos
  have hS2 := abs_integral_im_msc_sub_pi_mul_integral_rhoSc_le (-4) bm hηpos
  have hR1 : Real.pi * |(∫ x in (-4 : ℝ)..bp, rhoSc x) - nsc E| ≤ 1 / N := by
    rw [counting_nsc_eq E, intervalIntegral.integral_interval_sub_left
      (counting_continuous_rhoSc.intervalIntegrable _ _)
      (counting_continuous_rhoSc.intervalIntegrable _ _)]
    refine (pi_mul_abs_integral_rhoSc_le _ _).trans_eq ?_
    rw [hbp, add_sub_cancel_left, abs_of_pos hinvN0]
  have hR2 : Real.pi * |(∫ x in (-4 : ℝ)..bm, rhoSc x) - nsc E| ≤ 1 / N := by
    rw [counting_nsc_eq E, intervalIntegral.integral_interval_sub_left
      (counting_continuous_rhoSc.intervalIntegrable _ _)
      (counting_continuous_rhoSc.intervalIntegrable _ _)]
    refine (pi_mul_abs_integral_rhoSc_le _ _).trans_eq ?_
    rw [hbm, sub_sub_cancel_left, abs_neg, abs_of_pos hinvN0]
  rw [hlogη] at hD1 hD2
  -- assembling the estimates
  have hVN : 0 ≤ V / N := by positivity
  have hX1 : V / N * (bp - -4) ≤ V / N * 8 :=
    mul_le_mul_of_nonneg_left (by linarith) hVN
  have hX2 : V / N * (bm - -4) ≤ V / N * 8 :=
    mul_le_mul_of_nonneg_left (by linarith) hVN
  set n := countFn hH E
  set s := nsc E
  set M := V / N * 8 + 4 * (V / N * Real.log N) + 4 * (1 / N) with hM
  have hlin : V / N * (2 * Real.log N) = 2 * (V / N * Real.log N) := by ring
  have hR1' := (abs_le.1 (show |Real.pi * ((∫ x in (-4 : ℝ)..bp, rhoSc x) - s)| ≤ 1 / N by
    rw [abs_mul, abs_of_pos Real.pi_pos]; exact hR1)).2
  have hR2' := (abs_le.1 (show |Real.pi * ((∫ x in (-4 : ℝ)..bm, rhoSc x) - s)| ≤ 1 / N by
    rw [abs_mul, abs_of_pos Real.pi_pos]; exact hR2)).1
  rw [mul_sub] at hR1' hR2'
  have hup : Real.pi * (n - s) ≤ M := by
    have a1 := (abs_le.1 hD1).2
    have a2 := (abs_le.1 hS1).2
    have h22 : (2 : ℝ) / N = 2 * (1 / N) := by ring
    rw [mul_sub, hM]
    linarith
  have hdown : Real.pi * (s - n) ≤ M := by
    have a1 := (abs_le.1 hD2).1
    have a2 := (abs_le.1 hS2).1
    rw [mul_sub, hM]
    linarith
  have hM0 : 0 ≤ M := by
    rw [hM]
    have : 0 ≤ Real.log N := by linarith
    positivity
  have habs : |n - s| ≤ M := by
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    rw [abs_le]
    constructor
    · rcases le_or_gt 0 (s - n) with h | h
      · have := le_mul_of_one_le_left h hpi
        linarith
      · linarith
    · rcases le_or_gt 0 (n - s) with h | h
      · have := le_mul_of_one_le_left h hpi
        linarith
      · linarith
  refine habs.trans ?_
  have eM : M = (24 * W + 12 * W * Real.log N + 4) / N := by
    rw [hM, hV]
    field_simp
    ring
  rw [eM]
  refine div_le_div_of_nonneg_right ?_ hNr.le
  have h1 : 2 * (1 / 2) ≤ W * Real.log N := mul_le_mul hW2 hL (by norm_num) (by linarith)
  have h2 : W * 1 ≤ W * (2 * Real.log N) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have e1 : 12 * W * Real.log N = 12 * (W * Real.log N) := by ring
  have e2 : 100 * W * Real.log N = 100 * (W * Real.log N) := by ring
  have e3 : W * (2 * Real.log N) = 2 * (W * Real.log N) := by ring
  rw [e1, e2]
  rw [e3, mul_one] at h2
  linarith

/-! ### Compiled check at a concrete nondegenerate point

`N = 2`, `H = [[0, 1], [1, 0]]` (symmetric, eigenvalues `-1` and `1`), `U = 4`, `y0 = 1/2`,
`E = 1`. The hypothesis on `m - m_sc` holds because `‖m(z)‖ ≤ 1 / Im z` and `‖m_sc(z)‖ < 1`
((2.10)), so `‖m - m_sc‖ ≤ 2 / y = U / (N y)` for `0 < y ≤ 1`. -/

private def countingCheckMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

private lemma countingCheckMatrix_isHermitian : countingCheckMatrix.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [countingCheckMatrix]

/-- The eigenvalues of `[[0, 1], [1, 0]]` satisfy `λ² = 1`, hence `|λ| ≤ 3`. -/
private lemma countingCheckMatrix_eigenvalues (α : Fin 2) :
    |countingCheckMatrix_isHermitian.eigenvalues α| ≤ 3 := by
  have h := countingCheckMatrix_isHermitian.eigenvalues_mem_spectrum_real α
  set r := countingCheckMatrix_isHermitian.eigenvalues α
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    Algebra.algebraMap_eq_smul_one, Matrix.det_fin_two] at h
  simp [countingCheckMatrix] at h
  rw [abs_le]
  constructor <;> nlinarith

/-- `‖m(z)‖ ≤ 1 / Im z` for `Im z > 0`. -/
lemma norm_stieltjesM_le_inv_im {N : ℕ} (hN : 0 < N) {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) : ‖stieltjesM H z‖ ≤ 1 / z.im := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [stieltjesM_eq_sum hH hz, norm_mul, norm_inv, Complex.norm_natCast]
  have hterm : ∀ α, ‖((hH.eigenvalues α : ℂ) - z)⁻¹‖ ≤ 1 / z.im := by
    intro α
    rw [norm_inv, one_div]
    refine inv_anti₀ hz ?_
    have := Complex.abs_im_le_norm ((hH.eigenvalues α : ℂ) - z)
    rw [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg, abs_of_pos hz] at this
    exact this
  calc (N : ℝ)⁻¹ * ‖∑ α, ((hH.eigenvalues α : ℂ) - z)⁻¹‖
      ≤ (N : ℝ)⁻¹ * ∑ α : Fin N, (1 / z.im) :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => hterm α))
          (by positivity)
    _ = 1 / z.im := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

example : ∃ C > 0, |countFn countingCheckMatrix_isHermitian 1 - nsc 1| ≤
    C * (4 + ((2 : ℕ) : ℝ) * (1 / 2)) * Real.log ((2 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) := by
  obtain ⟨C, hC, h⟩ := abs_countFn_sub_nsc_le
  refine ⟨C, hC, h 2 le_rfl countingCheckMatrix countingCheckMatrix_isHermitian 4 (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) countingCheckMatrix_eigenvalues ?_ 1⟩
  intro x y _ hy hy1
  have hy0 : 0 < y := by linarith
  have hz : 0 < ((x : ℂ) + y * Complex.I).im := by simpa using hy0
  have h1 := norm_stieltjesM_le_inv_im (by norm_num) countingCheckMatrix_isHermitian hz
  have h2 := (norm_msc_eq_inv_and_lt_one hz).2
  have him : ((x : ℂ) + y * Complex.I).im = y := by simp
  rw [him] at h1
  have h3 : (1 : ℝ) ≤ 1 / y := by rw [le_div_iff₀ hy0]; linarith
  have e : (4 : ℝ) / (((2 : ℕ) : ℝ) * y) = 2 * (1 / y) := by
    push_cast
    field_simp
    ring
  rw [e]
  calc ‖stieltjesM countingCheckMatrix (x + y * Complex.I) - msc (x + y * Complex.I)‖
      ≤ ‖stieltjesM countingCheckMatrix (x + y * Complex.I)‖ + ‖msc (x + y * Complex.I)‖ :=
        norm_sub_le _ _
    _ ≤ 2 * (1 / y) := by linarith

#print axioms abs_countFn_sub_nsc_le

end WEdgeNS
