import WEdgeNS.Semicircle.Density

/-!
# m_sc is the Stieltjes transform of the semicircle law
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- For `Im z > 0` and real `t`, `t - z ≠ 0`. -/
private lemma stieltjes_ofReal_sub_ne_zero {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    (t : ℂ) - z ≠ 0 := by
  intro h
  have h1 : ((t : ℂ) - z).im = 0 := by rw [h]; rfl
  simp at h1
  linarith

/-- `√(z² - 4)` of (2.8) does not vanish on the upper half-plane. -/
private lemma stieltjes_sqrtZ4_ne_zero {z : ℂ} (hz : 0 < z.im) : sqrtZ4 z ≠ 0 := by
  intro h
  have hsq := sqrtZ4_sq z
  rw [h] at hsq
  have h2 : (z - 2) * (z + 2) = 0 := by linear_combination -hsq
  rcases mul_eq_zero.1 h2 with h3 | h3
  · have h4 : z = 2 := by linear_combination h3
    rw [h4] at hz
    simp at hz
  · have h4 : z = -2 := by linear_combination h3
    rw [h4] at hz
    simp at hz

/-- `∫₀^{2π} (2 cos θ - z)⁻¹ dθ = -2π / √(z² - 4)` for `Im z > 0`, with the branch of (2.8). -/
private lemma stieltjes_integral_inv_two_cos_sub {z : ℂ} (hz : 0 < z.im) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, (((2 * Real.cos θ : ℝ) : ℂ) - z)⁻¹ =
      -(2 * Real.pi) / sqrtZ4 z := by
  set m : ℂ := msc z with hm
  set a : ℂ := -m with ha
  set b : ℂ := z + m with hb
  have hmul : m * b = -1 := by
    have hsq := sqrtZ4_sq z
    rw [hb, hm]
    unfold msc
    linear_combination (1 / 4 : ℂ) * hsq
  have hm1 : ‖m‖ < 1 := (norm_msc_eq_inv_and_lt_one hz).2
  have hnb : ‖m‖ * ‖b‖ = 1 := by
    rw [← norm_mul, hmul]
    simp
  have hb1 : 1 < ‖b‖ := by
    have hm0 : 0 ≤ ‖m‖ := norm_nonneg _
    by_contra hle
    rw [not_lt] at hle
    nlinarith
  have hfd : DiffContOnCl ℂ (fun w : ℂ => (w - b)⁻¹) (Metric.ball 0 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) one_ne_zero]
    refine (differentiableOn_id.sub_const b).inv ?_
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    intro h
    have : w = b := sub_eq_zero.1 h
    rw [this] at hw
    linarith
  have ha1 : a ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, ha, norm_neg]
    exact hm1
  have hC := hfd.circleIntegral_sub_inv_smul ha1
  rw [circleIntegral] at hC
  have hcongr : ∀ θ : ℝ, deriv (circleMap 0 1) θ •
      ((circleMap 0 1 θ - a)⁻¹ • (circleMap 0 1 θ - b)⁻¹) =
      Complex.I * (((2 * Real.cos θ : ℝ) : ℂ) - z)⁻¹ := by
    intro θ
    rw [deriv_circleMap]
    have hw : circleMap 0 1 θ = Complex.exp (θ * Complex.I) := by simp [circleMap]
    rw [hw]
    set w : ℂ := Complex.exp (θ * Complex.I) with hwdef
    have hw0 : w ≠ 0 := Complex.exp_ne_zero _
    have hcos : ((2 * Real.cos θ : ℝ) : ℂ) = w + w⁻¹ := by
      push_cast
      rw [Complex.two_cos, hwdef, ← Complex.exp_neg]
      ring_nf
    have hc0 := stieltjes_ofReal_sub_ne_zero hz (2 * Real.cos θ)
    rw [hcos] at hc0 ⊢
    have hprod : (w - a) * (w - b) = w * (w + w⁻¹ - z) := by
      rw [ha, hb]
      field_simp
      linear_combination (-1 : ℂ) * hmul
    rw [smul_eq_mul, smul_eq_mul, ← mul_inv, hprod]
    field_simp
  simp_rw [hcongr] at hC
  rw [intervalIntegral.integral_const_mul] at hC
  have hab : a - b = -sqrtZ4 z := by
    rw [ha, hb, hm]
    unfold msc
    ring
  rw [hab, smul_eq_mul] at hC
  have hs := stieltjes_sqrtZ4_ne_zero hz
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hC' : Complex.I * (∫ θ in (0 : ℝ)..2 * Real.pi, (((2 * Real.cos θ : ℝ) : ℂ) - z)⁻¹) =
      Complex.I * (-(2 * Real.pi) / sqrtZ4 z) := by
    rw [hC]
    field_simp
  exact mul_left_cancel₀ hI hC'

/-- The integrand `sin²θ (2 cos θ - z)⁻¹` obtained from `ρ_sc(x) (x - z)⁻¹ dx` under
`x = 2 cos θ`. -/
private def stieltjesK (z : ℂ) (θ : ℝ) : ℂ :=
  ((Real.sin θ : ℝ) : ℂ) ^ 2 * (((2 * Real.cos θ : ℝ) : ℂ) - z)⁻¹

private lemma stieltjes_continuous_inv {z : ℂ} (hz : 0 < z.im) :
    Continuous (fun θ : ℝ => (((2 * Real.cos θ : ℝ) : ℂ) - z)⁻¹) :=
  Continuous.inv₀ (by fun_prop) (fun θ => stieltjes_ofReal_sub_ne_zero hz _)

private lemma stieltjes_continuous_K {z : ℂ} (hz : 0 < z.im) : Continuous (stieltjesK z) := by
  unfold stieltjesK
  exact (by fun_prop : Continuous fun θ : ℝ => ((Real.sin θ : ℝ) : ℂ) ^ 2).mul
    (stieltjes_continuous_inv hz)

/-- `∫₀^{2π} sin²θ (2 cos θ - z)⁻¹ dθ = π m_sc(z)` for `Im z > 0`. -/
private lemma stieltjes_integral_K_two_pi {z : ℂ} (hz : 0 < z.im) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, stieltjesK z θ = Real.pi * msc z := by
  have hpt : ∀ θ : ℝ, stieltjesK z θ =
      (1 / 4 * (4 - z ^ 2)) * (((2 * Real.cos θ : ℝ) : ℂ) - z)⁻¹ -
        (1 / 4 * (((2 * Real.cos θ : ℝ) : ℂ)) + 1 / 4 * z) := by
    intro θ
    have hc := stieltjes_ofReal_sub_ne_zero hz (2 * Real.cos θ)
    have hsc : ((Real.sin θ : ℝ) : ℂ) ^ 2 + ((Real.cos θ : ℝ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq θ
    have hc2 : ((2 * Real.cos θ : ℝ) : ℂ) = 2 * ((Real.cos θ : ℝ) : ℂ) := by
      exact_mod_cast rfl
    unfold stieltjesK
    rw [hc2] at hc ⊢
    generalize ((Real.sin θ : ℝ) : ℂ) = S at hsc ⊢
    generalize ((Real.cos θ : ℝ) : ℂ) = C at hsc hc ⊢
    field_simp
    linear_combination 4 * hsc
  have hfun : stieltjesK z = fun θ : ℝ =>
      (1 / 4 * (4 - z ^ 2)) * (((2 * Real.cos θ : ℝ) : ℂ) - z)⁻¹ -
        (1 / 4 * (((2 * Real.cos θ : ℝ) : ℂ)) + 1 / 4 * z) := funext hpt
  have hi1 : IntervalIntegrable (fun θ : ℝ =>
      (1 / 4 * (4 - z ^ 2)) * (((2 * Real.cos θ : ℝ) : ℂ) - z)⁻¹) volume 0 (2 * Real.pi) :=
    (continuous_const.mul (stieltjes_continuous_inv hz)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun θ : ℝ => 1 / 4 * (((2 * Real.cos θ : ℝ) : ℂ)))
      volume 0 (2 * Real.pi) :=
    (by fun_prop : Continuous fun θ : ℝ => 1 / 4 * (((2 * Real.cos θ : ℝ) : ℂ))).intervalIntegrable
      _ _
  have hcos : ∫ θ in (0 : ℝ)..2 * Real.pi, (((2 * Real.cos θ : ℝ) : ℂ)) = 0 := by
    rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul, integral_cos]
    simp
  rw [hfun, intervalIntegral.integral_sub hi1 (hi2.add intervalIntegrable_const),
    intervalIntegral.integral_add hi2 intervalIntegrable_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hcos, stieltjes_integral_inv_two_cos_sub hz,
    intervalIntegral.integral_const]
  have hs := stieltjes_sqrtZ4_ne_zero hz
  have hsq := sqrtZ4_sq z
  unfold msc
  rw [Complex.real_smul]
  push_cast
  field_simp
  linear_combination (-4 * (Real.pi : ℂ)) * hsq

/-- `∫₀^π sin²θ (2 cos θ - z)⁻¹ dθ = (π/2) m_sc(z)` for `Im z > 0`, by the symmetry `θ ↦ 2π - θ`. -/
private lemma stieltjes_integral_K_pi {z : ℂ} (hz : 0 < z.im) :
    ∫ θ in (0 : ℝ)..Real.pi, stieltjesK z θ = Real.pi / 2 * msc z := by
  have hK := stieltjes_continuous_K hz
  have h2 : ∫ θ in Real.pi..2 * Real.pi, stieltjesK z θ =
      ∫ θ in (0 : ℝ)..Real.pi, stieltjesK z θ := by
    have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := Real.pi) (stieltjesK z)
      (2 * Real.pi)
    rw [show 2 * Real.pi - Real.pi = Real.pi by ring, sub_zero] at h
    rw [← h]
    congr 1
    funext θ
    simp [stieltjesK, Real.cos_two_pi_sub, Real.sin_two_pi_sub]
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hK.intervalIntegrable 0 Real.pi) (hK.intervalIntegrable Real.pi (2 * Real.pi))
  rw [h2, stieltjes_integral_K_two_pi hz] at h
  linear_combination h / 2

/-! ### The Stieltjes transform of `ρ_sc`

For `Im z > 0`, `m_sc(z)` of (2.8) equals `∫ ρ_sc(x) (x - z)⁻¹ dx`, the Stieltjes transform of the
semicircle density (2.9) (Definition 2.5). -/

theorem msc_eq_resolventTransform {z : ℂ} (hz : 0 < z.im) :
    msc z = resolventTransform semicircle z := by
  set g : ℝ → ℂ := fun x => (rhoSc x : ℂ) * ((x : ℂ) - z)⁻¹ with hg
  have hrho_cont : Continuous rhoSc := by
    unfold rhoSc
    fun_prop
  have hg_cont : Continuous g :=
    (Complex.continuous_ofReal.comp hrho_cont).mul
      (Continuous.inv₀ (by fun_prop) (stieltjes_ofReal_sub_ne_zero hz))
  have h1 : resolventTransform semicircle z = ∫ x, g x := by
    rw [resolventTransform_apply, semicircle, integral_withDensity_eq_integral_toReal_smul
      hrho_cont.measurable.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    congr 1
    funext x
    rw [ENNReal.toReal_ofReal (by unfold rhoSc; positivity)]
    simp [resolvent, hg, Complex.real_smul]
  have hvan : ∀ x, x ∉ Set.Ioc (-2 : ℝ) 2 → g x = 0 := by
    intro x hx
    have h0 : rhoSc x = 0 := by
      unfold rhoSc
      rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
      rw [Real.sqrt_eq_zero_of_nonpos (by rcases hx with h | h <;> nlinarith)]
      simp
    simp [hg, h0]
  have h2 : ∫ x, g x = ∫ x in (-2 : ℝ)..2, g x := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hvan).symm
  have h3 : ∫ x in (-2 : ℝ)..2, g x =
      ∫ θ in (0 : ℝ)..Real.pi, (2 * Real.sin θ) • g (2 * Real.cos θ) := by
    have hsub := intervalIntegral.integral_deriv_smul_comp (a := Real.pi) (b := 0)
      (f := fun θ => 2 * Real.cos θ) (f' := fun θ => -(2 * Real.sin θ)) (g := g)
      (fun θ _ => by simpa using ((Real.hasDerivAt_cos θ).const_mul 2)) (by fun_prop) hg_cont
    simp only [Function.comp_apply, Real.cos_pi, Real.cos_zero] at hsub
    rw [show (2 : ℝ) * -1 = -2 by norm_num, mul_one] at hsub
    rw [← hsub, intervalIntegral.integral_symm, ← intervalIntegral.integral_neg]
    congr 1
    funext θ
    rw [neg_smul, neg_neg]
  have hrho : ∀ θ ∈ Set.Icc 0 Real.pi, rhoSc (2 * Real.cos θ) = Real.sin θ / Real.pi := by
    intro θ hθ
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
    unfold rhoSc
    rw [show (4 : ℝ) - (2 * Real.cos θ) ^ 2 = (2 * Real.sin θ) ^ 2 by
      linear_combination (-4) * Real.sin_sq_add_cos_sq θ, Real.sqrt_sq (by positivity)]
    field_simp
  have h4 : ∫ θ in (0 : ℝ)..Real.pi, (2 * Real.sin θ) • g (2 * Real.cos θ) =
      (2 / Real.pi : ℂ) * ∫ θ in (0 : ℝ)..Real.pi, stieltjesK z θ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun θ hθ => ?_)
    rw [Set.uIcc_of_le Real.pi_pos.le] at hθ
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [hg, hrho θ hθ, stieltjesK, Complex.real_smul]
    push_cast
    field_simp
  rw [h1, h2, h3, h4, stieltjes_integral_K_pi hz]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- At `z = i` the Stieltjes transform of the semicircle law is `((√5 - 1)/2) i`, a nonzero value:
`∫ ρ_sc(x) (x - i)⁻¹ dx = i ∫ ρ_sc(x) (1 + x²)⁻¹ dx = ((√5 - 1)/2) i`. -/
example : 0 < Complex.I.im ∧
    resolventTransform semicircle Complex.I = (((Real.sqrt 5 - 1) / 2 : ℝ) : ℂ) * Complex.I := by
  refine ⟨by simp, ?_⟩
  rw [← msc_eq_resolventTransform (by simp)]
  set r : ℝ := (Real.sqrt 5 - 1) / 2 with hr
  have hs : 2 < Real.sqrt 5 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hrpos : 0 < r := by rw [hr]; linarith
  have hrr : r * (1 + r) = 1 := by rw [hr]; nlinarith
  have hinv : (Complex.I + (r : ℂ) * Complex.I)⁻¹ = -((r : ℂ) * Complex.I) := by
    apply inv_eq_of_mul_eq_one_right
    have : (r : ℂ) * (1 + r) = 1 := by exact_mod_cast hrr
    linear_combination this - (r : ℂ) * (1 + r) * Complex.I_sq
  have hw : (r : ℂ) * Complex.I + (Complex.I + (r : ℂ) * Complex.I)⁻¹ = 0 := by
    rw [hinv]; ring
  exact (eq_msc_of_add_inv (by simp) hw (by simpa using hrpos)).symm

/-- A point with `Re z < -2` close to the real axis, where the principal root of `z² - 4` is not the
branch of (2.8). -/
example : 0 < (-3 + ((1 / 1000 : ℝ) : ℂ) * Complex.I).im ∧
    msc (-3 + ((1 / 1000 : ℝ) : ℂ) * Complex.I) =
      resolventTransform semicircle (-3 + ((1 / 1000 : ℝ) : ℂ) * Complex.I) :=
  ⟨by simp, msc_eq_resolventTransform (by simp)⟩

#print axioms msc_eq_resolventTransform

end WEdgeNS
