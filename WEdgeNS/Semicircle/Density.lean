import WEdgeNS.Semicircle.Msc

/-!
# Semicircle density, distribution function and classical locations ((2.9), (2.13), (5.13))
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- `ρ_sc(x) = (2π)⁻¹ √((4 - x²)₊)` of (2.9). -/
def rhoSc (x : ℝ) : ℝ := Real.sqrt (4 - x ^ 2) / (2 * Real.pi)

/-- The semicircle law `ρ_sc(x) dx`. -/
def semicircle : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (rhoSc x))

/-- `n_sc(E) = ∫_{-∞}^E ρ_sc`. -/
def nsc (E : ℝ) : ℝ := ∫ x in Set.Iic E, rhoSc x

/-- Classical location (2.13): the least `x` with `n_sc(x) ≥ j/N`. -/
def gammaLoc (N j : ℕ) : ℝ := sInf {x : ℝ | (j : ℝ) / N ≤ nsc x}

/-! ### The density -/

private lemma rhoSc_nonneg (x : ℝ) : 0 ≤ rhoSc x := by
  unfold rhoSc
  positivity

/-- The density vanishes outside `(-2, 2)`. -/
private lemma rhoSc_eq_zero {x : ℝ} (hx : 2 ≤ |x|) : rhoSc x = 0 := by
  unfold rhoSc
  have h : 4 - x ^ 2 ≤ 0 := by nlinarith [sq_abs x, abs_nonneg x]
  rw [Real.sqrt_eq_zero_of_nonpos h]
  simp

private lemma rhoSc_eq_zero_of_le {x : ℝ} (hx : x ≤ -2) : rhoSc x = 0 :=
  rhoSc_eq_zero (by rw [abs_of_neg (by linarith)]; linarith)

private lemma rhoSc_eq_zero_of_ge {x : ℝ} (hx : 2 ≤ x) : rhoSc x = 0 :=
  rhoSc_eq_zero (by rw [abs_of_pos (by linarith)]; exact hx)

/-- The density is positive on `(-2, 2)`. -/
private lemma rhoSc_pos {x : ℝ} (hx : |x| < 2) : 0 < rhoSc x := by
  unfold rhoSc
  have h : 0 < 4 - x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  positivity

private lemma continuous_rhoSc : Continuous rhoSc := by
  unfold rhoSc
  fun_prop

private lemma hasCompactSupport_rhoSc : HasCompactSupport rhoSc := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) ?_
  intro x hx
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h | h
  · exact rhoSc_eq_zero_of_le h.le
  · exact rhoSc_eq_zero_of_ge h.le

private lemma integrable_rhoSc : Integrable rhoSc :=
  continuous_rhoSc.integrable_of_hasCompactSupport hasCompactSupport_rhoSc

private lemma integral_rhoSc_interval : ∫ x in (-2 : ℝ)..2, rhoSc x = 1 := by
  have h1 : ∫ x in (-1 : ℝ)..1, Real.sqrt (4 - (2 * x) ^ 2) = Real.pi := by
    have : ∀ x : ℝ, Real.sqrt (4 - (2 * x) ^ 2) = 2 * Real.sqrt (1 - x ^ 2) := by
      intro x
      rw [show (4 : ℝ) - (2 * x) ^ 2 = 2 ^ 2 * (1 - x ^ 2) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq]
    ring
  have h2 := intervalIntegral.integral_comp_mul_left
    (fun y : ℝ => Real.sqrt (4 - y ^ 2)) (a := (-1 : ℝ)) (b := 1) (c := 2) (by norm_num)
  rw [h1] at h2
  have h3 : ∫ y in (-2 : ℝ)..2, Real.sqrt (4 - y ^ 2) = 2 * Real.pi := by
    have : (2 * (-1 : ℝ)) = -2 := by norm_num
    rw [this, show (2 * (1 : ℝ)) = 2 by norm_num, smul_eq_mul] at h2
    linarith
  unfold rhoSc
  rw [intervalIntegral.integral_div, h3]
  field_simp

private lemma integral_rhoSc : ∫ x, rhoSc x = 1 := by
  rw [← integral_rhoSc_interval, intervalIntegral.integral_of_le (by norm_num)]
  symm
  refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
  intro x hx
  rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
  rcases hx with h | h
  · exact rhoSc_eq_zero_of_le h
  · exact rhoSc_eq_zero_of_ge h.le

theorem isProbabilityMeasure_semicircle : IsProbabilityMeasure semicircle := by
  refine ⟨?_⟩
  rw [semicircle, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal integrable_rhoSc (Eventually.of_forall rhoSc_nonneg),
    integral_rhoSc]
  simp

/-! ### Boundary values of `m_sc` -/

/-- Boundary value of the principal square root from the upper half-plane at a point `x ≥ 0`. -/
private lemma tendsto_cpow_half_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun η : ℝ => ((x : ℂ) + η * Complex.I) ^ (1 / 2 : ℂ)) (𝓝[>] 0)
      (𝓝 ((Real.sqrt x : ℝ) : ℂ)) := by
  have hcont : ContinuousAt (fun w : ℂ => w ^ (1 / 2 : ℂ)) (x : ℂ) :=
    Complex.continuousAt_cpow_const_of_re_pos (Or.inl (by simpa using hx)) (by norm_num)
  have hpath : Tendsto (fun η : ℝ => (x : ℂ) + η * Complex.I) (𝓝 0) (𝓝 (x : ℂ)) := by
    have : Continuous fun η : ℝ => (x : ℂ) + η * Complex.I := by fun_prop
    simpa using this.tendsto 0
  have h := (hcont.tendsto.comp hpath).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hval : (x : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt x : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx]
    push_cast
    rfl
  rw [← hval]
  exact h

/-- Boundary value of the principal square root from the upper half-plane at a point `x < 0`. -/
private lemma tendsto_cpow_half_of_neg {x : ℝ} (hx : x < 0) :
    Tendsto (fun η : ℝ => ((x : ℂ) + η * Complex.I) ^ (1 / 2 : ℂ)) (𝓝[>] 0)
      (𝓝 (Complex.I * ((Real.sqrt (-x) : ℝ) : ℂ))) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne
  have hpath : Tendsto (fun η : ℝ => (x : ℂ) + η * Complex.I) (𝓝[>] 0)
      (𝓝[{w : ℂ | 0 ≤ w.im}] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Continuous fun η : ℝ => (x : ℂ) + η * Complex.I := by fun_prop
      simpa using (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with η hη
      simpa using le_of_lt hη
  have hlog : Tendsto (fun η : ℝ => Complex.log ((x : ℂ) + η * Complex.I)) (𝓝[>] 0)
      (𝓝 (Complex.log (x : ℂ))) :=
    (Complex.continuousWithinAt_log_of_re_neg_of_im_zero (z := (x : ℂ)) (by simpa using hx)
      (by simp)).tendsto.comp hpath
  have hexp := (hlog.mul_const (1 / 2 : ℂ)).cexp
  have hval : (x : ℂ) ^ (1 / 2 : ℂ) = Complex.I * ((Real.sqrt (-x) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow_of_nonpos hx.le, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by linarith)]
    have h1 : Complex.exp (Real.pi * Complex.I * (1 / 2 : ℂ)) = Complex.I := by
      rw [show (Real.pi : ℂ) * Complex.I * (1 / 2 : ℂ) = ((Real.pi : ℂ) / 2) * Complex.I by ring,
        Complex.exp_mul_I, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
      simp
    rw [h1]
    push_cast
    ring
  rw [← hval, Complex.cpow_def_of_ne_zero hx0]
  refine hexp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hne : (x : ℂ) + η * Complex.I ≠ 0 := by
    intro h
    have h1 : η = 0 := by simpa using congrArg Complex.im h
    exact hη.ne' h1
  rw [Complex.cpow_def_of_ne_zero hne]

/-- The imaginary part of `√(z² - 4)` tends to `√((4 - E²)₊)` as `z = E + iη`, `η ↓ 0`. -/
private lemma tendsto_im_sqrtZ4 (E : ℝ) :
    Tendsto (fun η : ℝ => (sqrtZ4 (E + η * Complex.I)).im) (𝓝[>] 0)
      (𝓝 (Real.sqrt (4 - E ^ 2))) := by
  have hrw : ∀ η : ℝ, sqrtZ4 ((E : ℂ) + η * Complex.I) =
      (((E - 2 : ℝ) : ℂ) + η * Complex.I) ^ (1 / 2 : ℂ) *
        (((E + 2 : ℝ) : ℂ) + η * Complex.I) ^ (1 / 2 : ℂ) := by
    intro η
    unfold sqrtZ4
    push_cast
    ring_nf
  simp_rw [hrw]
  have key : ∀ La Lb : ℂ,
      Tendsto (fun η : ℝ => (((E - 2 : ℝ) : ℂ) + η * Complex.I) ^ (1 / 2 : ℂ)) (𝓝[>] 0) (𝓝 La) →
      Tendsto (fun η : ℝ => (((E + 2 : ℝ) : ℂ) + η * Complex.I) ^ (1 / 2 : ℂ)) (𝓝[>] 0) (𝓝 Lb) →
      Tendsto (fun η : ℝ => ((((E - 2 : ℝ) : ℂ) + η * Complex.I) ^ (1 / 2 : ℂ) *
        (((E + 2 : ℝ) : ℂ) + η * Complex.I) ^ (1 / 2 : ℂ)).im) (𝓝[>] 0) (𝓝 (La * Lb).im) :=
    fun La Lb ha hb => (Complex.continuous_im.tendsto _).comp (ha.mul hb)
  rcases le_or_gt 2 E with h2 | h2
  · have := key _ _ (tendsto_cpow_half_of_nonneg (x := E - 2) (by linarith))
      (tendsto_cpow_half_of_nonneg (x := E + 2) (by linarith))
    have hz : Real.sqrt (4 - E ^ 2) = 0 :=
      Real.sqrt_eq_zero_of_nonpos (by nlinarith)
    rw [hz]
    convert this using 2
    rw [← Complex.ofReal_mul, Complex.ofReal_im]
  rcases le_or_gt (-2) E with h3 | h3
  · have := key _ _ (tendsto_cpow_half_of_neg (x := E - 2) (by linarith))
      (tendsto_cpow_half_of_nonneg (x := E + 2) (by linarith))
    convert this using 2
    rw [show Complex.I * ((Real.sqrt (-(E - 2)) : ℝ) : ℂ) * ((Real.sqrt (E + 2) : ℝ) : ℂ)
      = Complex.I * (((Real.sqrt (-(E - 2)) * Real.sqrt (E + 2) : ℝ)) : ℂ) by push_cast; ring,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      ← Real.sqrt_mul (by linarith)]
    simp only [zero_mul, one_mul, zero_add]
    congr 1
    ring
  · have := key _ _ (tendsto_cpow_half_of_neg (x := E - 2) (by linarith))
      (tendsto_cpow_half_of_neg (x := E + 2) (by linarith))
    have hz : Real.sqrt (4 - E ^ 2) = 0 :=
      Real.sqrt_eq_zero_of_nonpos (by nlinarith)
    rw [hz]
    convert this using 2
    set u : ℂ := ((Real.sqrt (-(E - 2)) : ℝ) : ℂ) with hu
    set v : ℂ := ((Real.sqrt (-(E + 2)) : ℝ) : ℂ) with hv
    have huv : Complex.I * u * (Complex.I * v) = (((-(Real.sqrt (-(E - 2)) *
        Real.sqrt (-(E + 2))) : ℝ)) : ℂ) := by
      push_cast
      linear_combination (u * v) * Complex.I_sq
    rw [huv, Complex.ofReal_im]

theorem tendsto_im_msc (E : ℝ) :
    Tendsto (fun η : ℝ => (msc (E + η * Complex.I)).im / Real.pi) (𝓝[>] 0) (𝓝 (rhoSc E)) := by
  have hid : Tendsto (fun η : ℝ => η) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h := (((tendsto_im_sqrtZ4 E).sub hid).div_const 2).div_const Real.pi
  have hmsc : ∀ η : ℝ, (msc ((E : ℂ) + η * Complex.I)).im =
      ((sqrtZ4 ((E : ℂ) + η * Complex.I)).im - η) / 2 := by
    intro η
    simp [msc, Complex.div_ofNat_im]
    ring
  simp_rw [hmsc]
  convert h using 2
  unfold rhoSc
  field_simp
  ring

/-! ### The distribution function -/

private lemma integrableOn_Iic_rhoSc (a : ℝ) : IntegrableOn rhoSc (Set.Iic a) :=
  integrable_rhoSc.integrableOn

/-- Increments of `n_sc` are integrals of the density. -/
private lemma nsc_sub_nsc (a b : ℝ) : nsc b - nsc a = ∫ x in a..b, rhoSc x :=
  intervalIntegral.integral_Iic_sub_Iic (integrableOn_Iic_rhoSc a) (integrableOn_Iic_rhoSc b)

theorem nsc_eq_zero {E : ℝ} (hE : E ≤ -2) : nsc E = 0 := by
  unfold nsc
  refine setIntegral_eq_zero_of_forall_eq_zero ?_
  intro x hx
  exact rhoSc_eq_zero_of_le (le_trans hx hE)

theorem nsc_eq_one {E : ℝ} (hE : 2 ≤ E) : nsc E = 1 := by
  have h0 : ∫ x in (Set.Iic E)ᶜ, rhoSc x = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero ?_
    intro x hx
    rw [Set.mem_compl_iff, Set.mem_Iic, not_le] at hx
    exact rhoSc_eq_zero_of_ge (by linarith)
  have h := integral_add_compl (measurableSet_Iic (a := E)) (f := rhoSc) (μ := volume)
    integrable_rhoSc
  rw [h0, add_zero, integral_rhoSc] at h
  exact h

theorem monotone_nsc : Monotone nsc := by
  intro a b hab
  exact setIntegral_mono_set integrable_rhoSc.integrableOn
    (Eventually.of_forall rhoSc_nonneg) (Set.Iic_subset_Iic.2 hab).eventuallyLE

theorem continuous_nsc : Continuous nsc := by
  have h : nsc = fun E => ∫ x in (-3 : ℝ)..E, rhoSc x := by
    funext E
    have h3 : nsc (-3) = 0 := nsc_eq_zero (by norm_num)
    have := nsc_sub_nsc (-3) E
    rw [h3, sub_zero] at this
    exact this
  rw [h]
  exact intervalIntegral.continuous_primitive (fun a b => continuous_rhoSc.intervalIntegrable a b) _

/-! ### Classical locations -/

private lemma nsc_lt_one {x : ℝ} (hx : x < 2) : nsc x < 1 := by
  rcases le_or_gt x (-2) with h | h
  · rw [nsc_eq_zero h]
    norm_num
  · have h2 := nsc_sub_nsc x 2
    rw [nsc_eq_one le_rfl] at h2
    have hpos : 0 < ∫ y in x..2, rhoSc y := by
      refine intervalIntegral.intervalIntegral_pos_of_pos_on
        (continuous_rhoSc.intervalIntegrable _ _) (fun y hy => rhoSc_pos ?_) hx
      rw [abs_lt]
      constructor <;> linarith [hy.1, hy.2]
    linarith

theorem nsc_gammaLoc {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) : nsc (gammaLoc N j) = j / N := by
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := lt_of_lt_of_le hj hjN
    exact_mod_cast this
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hq : (0 : ℝ) < j / N := div_pos hjpos hNpos
  have hq1 : (j : ℝ) / N ≤ 1 := by
    rw [div_le_one hNpos]
    exact_mod_cast hjN
  set S : Set ℝ := {x : ℝ | (j : ℝ) / N ≤ nsc x} with hS
  have hSclosed : IsClosed S := isClosed_le continuous_const continuous_nsc
  have hSne : S.Nonempty := by
    refine ⟨2, ?_⟩
    simp only [hS, Set.mem_ofPred_eq]
    rw [nsc_eq_one le_rfl]
    exact hq1
  have hSbdd : BddBelow S := by
    refine ⟨-2, fun x hx => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have := nsc_eq_zero hlt.le
    simp only [hS, Set.mem_ofPred_eq] at hx
    linarith
  have hmem : sInf S ∈ S := hSclosed.csInf_mem hSne hSbdd
  have hge : (j : ℝ) / N ≤ nsc (sInf S) := hmem
  change nsc (sInf S) = j / N
  refine le_antisymm ?_ hge
  by_contra hgt
  rw [not_le] at hgt
  have hev : ∀ᶠ y in 𝓝 (sInf S), (j : ℝ) / N < nsc y :=
    continuous_nsc.continuousAt.eventually (lt_mem_nhds hgt)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hy : (j : ℝ) / N < nsc (sInf S - ε / 2) := by
    refine hball ?_
    rw [Real.dist_eq]
    have : sInf S - ε / 2 - sInf S = -(ε / 2) := by ring
    rw [this, abs_neg, abs_of_pos (by linarith)]
    linarith
  have hyS : sInf S - ε / 2 ∈ S := hy.le
  have := csInf_le hSbdd hyS
  linarith

theorem gammaLoc_self {N : ℕ} (hN : 1 ≤ N) : gammaLoc N N = 2 := by
  have hNpos : (N : ℝ) ≠ 0 := by
    have : 0 < N := hN
    exact_mod_cast this.ne'
  unfold gammaLoc
  rw [div_self hNpos]
  refine IsLeast.csInf_eq ⟨?_, ?_⟩
  · simp only [Set.mem_ofPred_eq]
    rw [nsc_eq_one le_rfl]
  · intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    by_contra hlt
    rw [not_le] at hlt
    exact absurd hx (not_le.2 (nsc_lt_one hlt))

/-! ### Behaviour at the lower edge -/

/-- Two-sided bound for the density on `[-2, 1]`, where `1 ≤ 2 - x ≤ 4`. -/
private lemma rhoSc_bounds {x : ℝ} (hx : x ∈ Set.Icc (-2 : ℝ) 1) :
    Real.sqrt (x + 2) / (2 * Real.pi) ≤ rhoSc x ∧ rhoSc x ≤ Real.sqrt (x + 2) / Real.pi := by
  obtain ⟨h1, h2⟩ := hx
  have hfac : Real.sqrt (4 - x ^ 2) = Real.sqrt (x + 2) * Real.sqrt (2 - x) := by
    rw [← Real.sqrt_mul (by linarith)]
    congr 1
    ring
  have hs1 : 1 ≤ Real.sqrt (2 - x) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have hs2 : Real.sqrt (2 - x) ≤ 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by linarith⟩
  have hsq : 0 ≤ Real.sqrt (x + 2) := Real.sqrt_nonneg _
  have hpi := Real.pi_pos
  unfold rhoSc
  rw [hfac]
  constructor
  · rw [div_le_div_iff_of_pos_right (by positivity)]
    nlinarith
  · rw [show Real.sqrt (x + 2) * Real.sqrt (2 - x) / (2 * Real.pi)
      = (Real.sqrt (x + 2) * Real.sqrt (2 - x) / 2) / Real.pi by field_simp]
    rw [div_le_div_iff_of_pos_right hpi]
    nlinarith

/-- `∫_{-2}^x √(s + 2) ds = (2/3)(x + 2)^{3/2}`. -/
private lemma integral_sqrt_add_two (x : ℝ) :
    ∫ s in (-2 : ℝ)..x, Real.sqrt (s + 2) = 2 / 3 * (x + 2) ^ ((3 : ℝ) / 2) := by
  have hd : ∀ s ∈ Set.uIcc (-2 : ℝ) x,
      HasDerivAt (fun s : ℝ => 2 / 3 * (s + 2) ^ ((3 : ℝ) / 2)) (Real.sqrt (s + 2)) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => s + 2) 1 s := (hasDerivAt_id s).add_const 2
    have h2 := (h1.rpow_const (p := (3 : ℝ) / 2) (Or.inr (by norm_num))).const_mul (2 / 3)
    convert h2 using 1
    rw [show (3 : ℝ) / 2 - 1 = 1 / 2 by norm_num, Real.sqrt_eq_rpow]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by exact (by fun_prop : Continuous fun s : ℝ => Real.sqrt (s + 2)).intervalIntegrable _ _)]
  have : ((-2 : ℝ) + 2) = 0 := by norm_num
  simp only [this]
  rw [Real.zero_rpow (by norm_num)]
  ring

/-- (5.13): `n_sc(x) ∼ (x + 2)^{3/2}` and `ρ_sc(x) ∼ (x + 2)^{1/2}` on `[-2, 1]`. -/
theorem nsc_rhoSc_comparable : ∃ C ≥ (1 : ℝ), ∀ x ∈ Set.Icc (-2 : ℝ) 1,
    (C⁻¹ * (x + 2) ^ ((3 : ℝ) / 2) ≤ nsc x ∧ nsc x ≤ C * (x + 2) ^ ((3 : ℝ) / 2)) ∧
    (C⁻¹ * Real.sqrt (x + 2) ≤ rhoSc x ∧ rhoSc x ≤ C * Real.sqrt (x + 2)) := by
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_d2
  have hpi := Real.pi_pos
  refine ⟨10, by norm_num, fun x hx => ?_⟩
  obtain ⟨hx1, hx2⟩ := hx
  have hsq : 0 ≤ Real.sqrt (x + 2) := Real.sqrt_nonneg _
  have hpw : 0 ≤ (x + 2) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
  obtain ⟨hr1, hr2⟩ := rhoSc_bounds ⟨hx1, hx2⟩
  have hI := integral_sqrt_add_two x
  have hn : nsc x = ∫ s in (-2 : ℝ)..x, rhoSc s := by
    have := nsc_sub_nsc (-2) x
    rw [nsc_eq_zero le_rfl, sub_zero] at this
    exact this
  have hint : ∀ f : ℝ → ℝ, Continuous f → IntervalIntegrable f volume (-2) x :=
    fun f hf => hf.intervalIntegrable _ _
  have hlow : ∫ s in (-2 : ℝ)..x, Real.sqrt (s + 2) / (2 * Real.pi) ≤ nsc x := by
    rw [hn]
    refine intervalIntegral.integral_mono_on hx1
      (hint _ (by fun_prop)) (hint _ continuous_rhoSc) (fun s hs => ?_)
    exact (rhoSc_bounds ⟨hs.1, by linarith [hs.2]⟩).1
  have hup : nsc x ≤ ∫ s in (-2 : ℝ)..x, Real.sqrt (s + 2) / Real.pi := by
    rw [hn]
    refine intervalIntegral.integral_mono_on hx1
      (hint _ continuous_rhoSc) (hint _ (by fun_prop)) (fun s hs => ?_)
    exact (rhoSc_bounds ⟨hs.1, by linarith [hs.2]⟩).2
  rw [intervalIntegral.integral_div, hI] at hlow hup
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · refine le_trans ?_ hlow
    rw [show 2 / 3 * (x + 2) ^ ((3 : ℝ) / 2) / (2 * Real.pi)
      = (x + 2) ^ ((3 : ℝ) / 2) / (3 * Real.pi) by field_simp]
    rw [inv_mul_eq_div, div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  · refine le_trans hup ?_
    rw [div_le_iff₀ hpi]
    nlinarith
  · refine le_trans ?_ hr1
    rw [inv_mul_eq_div, div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  · refine le_trans hr2 ?_
    rw [div_le_iff₀ hpi]
    nlinarith

/-! ### Concrete instances -/

/-- At the centre of the spectrum the density equals `1/π`, so the boundary limit of `m_sc` is a
nonzero number. -/
example : Tendsto (fun η : ℝ => (msc (((0 : ℝ) : ℂ) + η * Complex.I)).im / Real.pi) (𝓝[>] 0)
    (𝓝 (1 / Real.pi)) := by
  have h := tendsto_im_msc 0
  have h0 : rhoSc 0 = 1 / Real.pi := by
    unfold rhoSc
    rw [show (4 : ℝ) - 0 ^ 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    field_simp
  rwa [h0] at h

/-- Outside the spectrum the boundary limit of `Im m_sc` vanishes. -/
example : Tendsto (fun η : ℝ => (msc (((3 : ℝ) : ℂ) + η * Complex.I)).im / Real.pi) (𝓝[>] 0)
    (𝓝 0) := by
  have h := tendsto_im_msc 3
  rwa [rhoSc_eq_zero_of_ge (by norm_num)] at h

/-- Half of the mass of `ρ_sc` lies below `0`, so `n_sc` is neither `0` nor `1` there. -/
example : nsc 0 = 1 / 2 := by
  have hsymm : ∀ x : ℝ, rhoSc (-x) = rhoSc x := by
    intro x
    unfold rhoSc
    rw [neg_sq]
  have h1 := integral_comp_neg_Iic (0 : ℝ) rhoSc
  simp_rw [hsymm, neg_zero] at h1
  have h2 := integral_add_compl (measurableSet_Iic (a := (0 : ℝ))) (f := rhoSc) (μ := volume)
    integrable_rhoSc
  rw [Set.compl_Iic, integral_rhoSc] at h2
  unfold nsc
  linarith

example : nsc (-2) = 0 := nsc_eq_zero le_rfl

example : nsc 2 = 1 := nsc_eq_one le_rfl

example : nsc (gammaLoc 4 2) = (2 : ℕ) / (4 : ℕ) := nsc_gammaLoc (by norm_num) (by norm_num)

example : gammaLoc 3 3 = 2 := gammaLoc_self (by norm_num)

example : ∃ C ≥ (1 : ℝ),
    (C⁻¹ * ((1 : ℝ) + 2) ^ ((3 : ℝ) / 2) ≤ nsc 1 ∧ nsc 1 ≤ C * ((1 : ℝ) + 2) ^ ((3 : ℝ) / 2)) ∧
    (C⁻¹ * Real.sqrt (1 + 2) ≤ rhoSc 1 ∧ rhoSc 1 ≤ C * Real.sqrt (1 + 2)) := by
  obtain ⟨C, hC, h⟩ := nsc_rhoSc_comparable
  exact ⟨C, hC, h 1 ⟨by norm_num, le_rfl⟩⟩

#print axioms rhoSc
#print axioms semicircle
#print axioms nsc
#print axioms gammaLoc
#print axioms isProbabilityMeasure_semicircle
#print axioms tendsto_im_msc
#print axioms nsc_eq_zero
#print axioms nsc_eq_one
#print axioms monotone_nsc
#print axioms continuous_nsc
#print axioms nsc_gammaLoc
#print axioms gammaLoc_self
#print axioms nsc_rhoSc_comparable

end WEdgeNS
