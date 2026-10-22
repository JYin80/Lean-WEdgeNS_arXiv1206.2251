import WEdgeNS.EdgeUniv.Apriori
import WEdgeNS.EdgeUniv.TaylorF

/-!
# Reduction to the off-diagonal Ward sums
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- Ward identity ([26] (6.31), proof of Lemma 3.5): `N Im m(z) = η Σ_{i,j} |G_ij(z)|²`. -/
theorem natCast_mul_im_stieltjesM {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) :
    (N : ℝ) * (stieltjesM H z).im = z.im * ∑ i, ∑ j, ‖resolventC H z i j‖ ^ 2 := by
  simp_rw [sum_norm_sq_resolventC hH hz, Finset.mul_sum, mul_div_cancel₀ _ hz.ne']
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have hN' : (N : ℝ) ≠ 0 := by positivity
    have h1 : ((N : ℂ)⁻¹) = ((N : ℝ)⁻¹ : ℝ) := by push_cast; rfl
    rw [stieltjesM, h1, Complex.im_ofReal_mul, ← mul_assoc, mul_inv_cancel₀ hN', one_mul]
    simp [Matrix.trace, Complex.im_sum]

/-! ### Mean value and integration -/

/-- Mean value inequality: `|F y - F x| ≤ B |y - x|` for `|x|, |y| ≤ R` when `|F′| ≤ B` on
`[-R, R]`. -/
private lemma ward_abs_sub_le {F : ℝ → ℝ} (hF : ContDiff ℝ 4 F) {R B : ℝ}
    (hB : ∀ ζ : ℝ, |ζ| ≤ R → |iteratedDeriv 1 F ζ| ≤ B) {x y : ℝ} (hx : |x| ≤ R)
    (hy : |y| ≤ R) : |F y - F x| ≤ B * |y - x| := by
  have hd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := F) (s := Set.Icc (-R) R) (C := B)
    (x := x) (y := y) (fun x _ => hd.differentiableAt)
    (fun x hx => by
      rw [← iteratedDeriv_one]
      exact hB x (abs_le.2 hx)) (convex_Icc _ _) (abs_le.1 hx) (abs_le.1 hy)
  simpa [Real.norm_eq_abs] using this

/-- Two integrable functions that differ by at most `δ` off `T` and by at most `M` everywhere have
integrals differing by at most `δ + M μ(T)`. -/
private lemma ward_integral_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    {T : Set α} {δ M : ℝ} (hδ : 0 ≤ δ)
    (hgood : ∀ ω, ω ∉ T → |f ω - g ω| ≤ δ) (hbad : ∀ ω, |f ω - g ω| ≤ M) :
    |∫ ω, f ω ∂μ - ∫ ω, g ω ∂μ| ≤ δ + M * (μ T).toReal := by
  set T' := toMeasurable μ T with hT'
  have hmeas : MeasurableSet T' := measurableSet_toMeasurable μ T
  have hpt : ∀ ω, |f ω - g ω| ≤ δ + M * T'.indicator 1 ω := by
    intro ω
    by_cases h : ω ∈ T'
    · simp only [Set.indicator_of_mem h, Pi.one_apply, mul_one]
      linarith [hbad ω]
    · have : ω ∉ T := fun hT => h (subset_toMeasurable μ T hT)
      simp only [Set.indicator_of_notMem h, mul_zero, add_zero]
      exact hgood ω this
  have h1 : Integrable (T'.indicator (1 : α → ℝ)) μ := (integrable_const (1 : ℝ)).indicator hmeas
  have hint : Integrable (fun ω => δ + M * T'.indicator (1 : α → ℝ) ω) μ :=
    (integrable_const δ).add (h1.const_mul M)
  rw [← integral_sub hf hg]
  calc |∫ ω, (f ω - g ω) ∂μ| = ‖∫ ω, (f ω - g ω) ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ ω, ‖f ω - g ω‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (δ + M * T'.indicator (1 : α → ℝ) ω) ∂μ :=
        integral_mono (hf.sub hg).norm hint fun ω => by simpa [Real.norm_eq_abs] using hpt ω
    _ = δ + M * (μ T).toReal := by
        rw [integral_add (integrable_const δ) (h1.const_mul M),
          integral_const, integral_const_mul, integral_indicator_one hmeas]
        simp [measureReal_def, hT', measure_toMeasurable]

/-- A continuous function of a continuous bounded random variable is integrable. -/
private lemma ward_integrable_comp {N : ℕ} {μ : Measure (Entries N)} [IsProbabilityMeasure μ]
    {F : ℝ → ℝ} (hF : Continuous F) {a : Entries N → ℝ} (ha : Continuous a) {R : ℝ}
    (hR : ∀ ω, |a ω| ≤ R) : Integrable (fun ω => F (a ω)) μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hF.continuousOn
  refine Integrable.of_bound (hF.comp ha).aestronglyMeasurable C (Eventually.of_forall fun ω => ?_)
  exact hC _ (abs_le.1 (hR ω))

/-- `φ` beats every power of `N`: `N^A e^{-c φ} ≤ 1` for large `N`. -/
private lemma ward_rpow_mul_exp_le (c A : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ A * Real.exp (-c * phi N) ≤ 1 := by
  have hL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  filter_upwards [eventually_ge_atTop 3, hL.eventually_ge_atTop ((|A| + 1) / c),
    hu.eventually_ge_atTop 2] with N hN3 hL1 hu2
  have hN0 : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith
  set L := Real.log N with hLdef
  have hL0 : 0 < L := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    exact Real.log_pos (by linarith)
  have hphi : L ^ 2 ≤ phi N := by
    rw [phi_eq_exp hN3]
    have h2 : L ^ 2 = Real.exp (2 * Real.log L) := by
      rw [show (2 : ℝ) * Real.log L = Real.log L + Real.log L by ring, Real.exp_add,
        Real.exp_log hL0]
      ring
    rw [h2]
    exact Real.exp_le_exp.2 (by nlinarith)
  rw [Real.rpow_def_of_pos hN0, ← Real.exp_add, ← hLdef]
  refine Real.exp_le_one_iff.2 ?_
  have h1 : (|A| + 1) ≤ c * L := by
    have := (div_le_iff₀ hc).1 hL1
    linarith
  have h2 : L * A ≤ L * |A| := mul_le_mul_of_nonneg_left (le_abs_self A) hL0.le
  nlinarith [abs_nonneg A]

/-! ### Continuity in the entries -/

private lemma ward_continuous_sumsq {N : ℕ} {η : ℝ} (hη : 0 < η) :
    Continuous (fun p : Entries N × ℝ =>
      ∑ i, ∑ j, ‖resolventC (symOfEntries p.1) (⟨p.2, η⟩ : ℂ) i j‖ ^ 2) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_resolventC_symOfEntries_prod hη i j).norm.pow 2

private lemma ward_continuous_offsum {N : ℕ} {η : ℝ} (hη : 0 < η) :
    Continuous (fun p : Entries N × ℝ => ∑ i, ∑ j, if i = j then (0 : ℝ) else
      ‖resolventC (symOfEntries p.1) (⟨p.2, η⟩ : ℂ) i j‖ ^ 2) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by
    by_cases h : i = j
    · simp only [h, ite_true]; exact continuous_const
    · simp only [h, ite_false]; exact (continuous_resolventC_symOfEntries_prod hη i j).norm.pow 2

private lemma ward_continuous_im_m {N : ℕ} {η : ℝ} (hη : 0 < η) :
    Continuous (fun p : Entries N × ℝ => (stieltjesM (symOfEntries p.1) ⟨p.2, η⟩).im) := by
  have : (fun p : Entries N × ℝ => (stieltjesM (symOfEntries p.1) ⟨p.2, η⟩).im) = fun p =>
      ((N : ℂ)⁻¹ * ∑ i, resolventC (symOfEntries p.1) (⟨p.2, η⟩ : ℂ) i i).im := by
    funext p
    simp [stieltjesM, Matrix.trace]
  rw [this]
  exact Complex.continuous_im.comp (continuous_const.mul
    (continuous_finsetSum _ fun i _ => continuous_resolventC_symOfEntries_prod hη i i))

private lemma ward_continuous_a {N : ℕ} {η : ℝ} (hη : 0 < η) (E : ℝ) :
    Continuous (fun ω : Entries N => η ^ 2 * ∑ i, ∑ j,
      ‖resolventC (symOfEntries ω) (⟨E, η⟩ : ℂ) i j‖ ^ 2) := by
  have hc : Continuous (fun ω : Entries N => (ω, E)) := continuous_id.prodMk continuous_const
  have h := (ward_continuous_sumsq (N := N) hη).comp hc
  exact continuous_const.mul h

private lemma ward_continuous_b {N : ℕ} {η : ℝ} (hη : 0 < η) (E : ℝ) :
    Continuous (fun ω : Entries N => offWard (symOfEntries ω) (⟨E, η⟩ : ℂ)) := by
  have hc : Continuous (fun ω : Entries N => (ω, E)) := continuous_id.prodMk continuous_const
  have h := (ward_continuous_offsum (N := N) hη).comp hc
  exact continuous_const.mul h

private lemma ward_continuous_a' {N : ℕ} {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) :
    Continuous (fun ω : Entries N =>
      (N : ℝ) * ∫ y in E₁..E₂, (stieltjesM (symOfEntries ω) ⟨y, η⟩).im) :=
  continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun ω y => (stieltjesM (symOfEntries ω) ⟨y, η⟩).im) (ward_continuous_im_m hη) E₁ E₂)

private lemma ward_continuous_b' {N : ℕ} {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) :
    Continuous (fun ω : Entries N => offWardInt (symOfEntries ω) η E₁ E₂) :=
  continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun ω y => ∑ i, ∑ j, if i = j then (0 : ℝ) else
      ‖resolventC (symOfEntries ω) ⟨y, η⟩ i j‖ ^ 2) (ward_continuous_offsum hη) E₁ E₂)

/-! ### Deterministic bounds -/

private lemma ward_sumsq_nonneg {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    0 ≤ ∑ i, ∑ j, ‖resolventC H z i j‖ ^ 2 :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

private lemma ward_offsum_nonneg {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    0 ≤ ∑ i, ∑ j, if i = j then (0 : ℝ) else ‖resolventC H z i j‖ ^ 2 :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

private lemma ward_offsum_le {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    (∑ i, ∑ j, if i = j then (0 : ℝ) else ‖resolventC H z i j‖ ^ 2) ≤
      ∑ i, ∑ j, ‖resolventC H z i j‖ ^ 2 :=
  Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => by
    split_ifs <;> first | positivity | exact le_rfl

/-- `η² Σ_{i,j} |G_ij|² ≤ N`. -/
private lemma ward_eta_sq_sum_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) : z.im ^ 2 * ∑ i, ∑ j, ‖resolventC H z i j‖ ^ 2 ≤ (N : ℝ) := by
  have h1 : ∀ i, ∑ j, ‖resolventC H z i j‖ ^ 2 ≤ 1 / z.im ^ 2 := by
    intro i
    rw [sum_norm_sq_resolventC hH hz i]
    have h := norm_resolventC_apply_le hH hz i i
    calc (resolventC H z i i).im / z.im ≤ ‖resolventC H z i i‖ / z.im := by
          gcongr; exact Complex.im_le_norm _
      _ ≤ (1 / z.im) / z.im := by gcongr
      _ = 1 / z.im ^ 2 := by field_simp
  calc z.im ^ 2 * ∑ i, ∑ j, ‖resolventC H z i j‖ ^ 2
      ≤ z.im ^ 2 * ∑ _i : Fin N, 1 / z.im ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h1 i) (sq_nonneg _)
    _ = (N : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- The diagonal part: `Σ_{i,j} - Σ_{i≠j} = Σ_i |G_ii|²`. -/
private lemma ward_sumsq_sub_offsum {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    (∑ i, ∑ j, ‖resolventC H z i j‖ ^ 2) -
      (∑ i, ∑ j, if i = j then (0 : ℝ) else ‖resolventC H z i j‖ ^ 2) =
      ∑ i, ‖resolventC H z i i‖ ^ 2 := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  simp [sub_ite]

/-! ### Expectation of a difference -/

/-- `E F(a) - E F(b)`: on `Ω` the Lipschitz constant `B` of `F` on `[-R₁, R₁]` times `δ`; off
`Ω` the bound of (3.16) on `[-R, R]`. -/
private lemma ward_expect_sub_le {N : ℕ} {μ : Measure (Entries N)} [IsProbabilityMeasure μ]
    {F : ℝ → ℝ} {CF : ℝ} (hF4 : ContDiff ℝ 4 F)
    (hF : ∀ n ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF)
    {a b : Entries N → ℝ} (ha : Continuous a) (hb : Continuous b) {R : ℝ} (hR0 : 0 ≤ R)
    (hRa : ∀ ω, |a ω| ≤ R) (hRb : ∀ ω, |b ω| ≤ R) {Ω : Set (Entries N)} {R₁ B δ : ℝ}
    (hB : ∀ ζ : ℝ, |ζ| ≤ R₁ → |iteratedDeriv 1 F ζ| ≤ B) (hB0 : 0 ≤ B) (hδ : 0 ≤ δ)
    (hgood : ∀ ω ∈ Ω, |a ω| ≤ R₁ ∧ |b ω| ≤ R₁ ∧ |a ω - b ω| ≤ δ) :
    |∫ ω, F (a ω) ∂μ - ∫ ω, F (b ω) ∂μ| ≤
      B * δ + CF * (1 + R) ^ CF * (2 * R) * (μ Ωᶜ).toReal := by
  have hCF : 0 ≤ CF := by
    have := hF 1 (by simp) 0
    simpa using (abs_nonneg _).trans this
  have hFc : Continuous F := hF4.continuous
  have hfa := ward_integrable_comp (μ := μ) hFc ha hRa
  have hfb := ward_integrable_comp (μ := μ) hFc hb hRb
  refine ward_integral_sub_le hfa hfb (T := Ωᶜ) (mul_nonneg hB0 hδ) (fun ω hω => ?_) (fun ω => ?_)
  · obtain ⟨h1, h2, h3⟩ := hgood ω (not_not.1 hω)
    calc |F (a ω) - F (b ω)| ≤ B * |a ω - b ω| := ward_abs_sub_le hF4 hB h2 h1
      _ ≤ B * δ := mul_le_mul_of_nonneg_left h3 hB0
  · have hB' : ∀ ζ : ℝ, |ζ| ≤ R → |iteratedDeriv 1 F ζ| ≤ CF * (1 + R) ^ CF := fun ζ hζ =>
      abs_iteratedDeriv_le_of_abs_le hF hζ 1 (by simp)
    have hdiff : |a ω - b ω| ≤ 2 * R := by
      have h1 := abs_le.1 (hRa ω)
      have h2 := abs_le.1 (hRb ω)
      exact abs_le.2 ⟨by linarith, by linarith⟩
    calc |F (a ω) - F (b ω)| ≤ CF * (1 + R) ^ CF * |a ω - b ω| :=
          ward_abs_sub_le hF4 hB' (hRb ω) (hRa ω)
      _ ≤ CF * (1 + R) ^ CF * (2 * R) :=
          mul_le_mul_of_nonneg_left hdiff (mul_nonneg hCF (Real.rpow_nonneg (by linarith) _))

/-- The polynomial factor on the bad event is beaten by `exp(-c φ)` (real exponent). -/
private lemma ward_bad_le_real {CF Cb c : ℝ} (hCF : 0 ≤ CF) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℝ, p ≤ (N : ℝ) ^ Cb * Real.exp (-c * phi N ^ (1 : ℝ)) →
      CF * (1 + 2 * (N : ℝ) ^ 2) ^ CF * (2 * (2 * (N : ℝ) ^ 2)) * p ≤
        (N : ℝ) ^ (-(1 : ℝ) / 3) := by
  filter_upwards [ward_rpow_mul_exp_le c (2 * CF + Cb + 3 + 1 / 3) hc, eventually_ge_atTop 1,
    eventually_ge_atTop ⌈4 * CF * 3 ^ CF⌉₊] with N hN hN1 hNK p hp
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < N := by linarith
  have hK : 4 * CF * 3 ^ CF ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hNK)
  rw [Real.rpow_one] at hp
  set e := Real.exp (-c * phi N) with he_def
  have he : 0 ≤ e := (Real.exp_pos _).le
  have h3 : 1 + 2 * (N : ℝ) ^ 2 ≤ 3 * (N : ℝ) ^ 2 := by nlinarith
  have hrp : (1 + 2 * (N : ℝ) ^ 2) ^ CF ≤ 3 ^ CF * (N : ℝ) ^ (2 * CF) := by
    calc (1 + 2 * (N : ℝ) ^ 2) ^ CF ≤ (3 * (N : ℝ) ^ 2) ^ CF :=
          Real.rpow_le_rpow (by positivity) h3 hCF
      _ = 3 ^ CF * ((N : ℝ) ^ 2) ^ CF := Real.mul_rpow (by norm_num) (by positivity)
      _ = 3 ^ CF * (N : ℝ) ^ (2 * CF) := by
          rw [← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_mul hn0.le]
          norm_num
  have hpow : (N : ℝ) ^ (2 * CF + 2) = (N : ℝ) ^ (2 * CF) * (N : ℝ) ^ 2 := by
    rw [Real.rpow_add hn0, Real.rpow_two]
  have hM0 : 0 ≤ CF * (1 + 2 * (N : ℝ) ^ 2) ^ CF * (2 * (2 * (N : ℝ) ^ 2)) :=
    mul_nonneg (mul_nonneg hCF (Real.rpow_nonneg (by positivity) _)) (by positivity)
  have hM : CF * (1 + 2 * (N : ℝ) ^ 2) ^ CF * (2 * (2 * (N : ℝ) ^ 2)) ≤
      (4 * CF * 3 ^ CF) * (N : ℝ) ^ (2 * CF + 2) := by
    rw [hpow]
    calc CF * (1 + 2 * (N : ℝ) ^ 2) ^ CF * (2 * (2 * (N : ℝ) ^ 2))
        ≤ CF * (3 ^ CF * (N : ℝ) ^ (2 * CF)) * (2 * (2 * (N : ℝ) ^ 2)) := by
          gcongr
      _ = (4 * CF * 3 ^ CF) * ((N : ℝ) ^ (2 * CF) * (N : ℝ) ^ 2) := by ring
  have hNe : (N : ℝ) ^ (2 * CF + 2) * (N : ℝ) ^ Cb = (N : ℝ) ^ (2 * CF + 2 + Cb) :=
    (Real.rpow_add hn0 _ _).symm
  have hfin : (N : ℝ) ^ (2 * CF + 2 + Cb) * e * (N : ℝ) ≤ (N : ℝ) ^ (-(1 : ℝ) / 3) := by
    have h1 : (N : ℝ) ^ (-(1 : ℝ) / 3) * ((N : ℝ) ^ (2 * CF + Cb + 3 + 1 / 3) * e) ≤
        (N : ℝ) ^ (-(1 : ℝ) / 3) * 1 :=
      mul_le_mul_of_nonneg_left hN (Real.rpow_nonneg hn0.le _)
    have h2 : (N : ℝ) ^ (-(1 : ℝ) / 3) * (N : ℝ) ^ (2 * CF + Cb + 3 + 1 / 3) =
        (N : ℝ) ^ (2 * CF + 2 + Cb) * (N : ℝ) := by
      have h : (N : ℝ) ^ (-(1 : ℝ) / 3 + (2 * CF + Cb + 3 + 1 / 3)) =
          (N : ℝ) ^ (2 * CF + 2 + Cb + 1) := by congr 1; ring
      rw [← Real.rpow_add hn0, h, Real.rpow_add hn0, Real.rpow_one]
    calc (N : ℝ) ^ (2 * CF + 2 + Cb) * e * (N : ℝ)
        = (N : ℝ) ^ (-(1 : ℝ) / 3) * (N : ℝ) ^ (2 * CF + Cb + 3 + 1 / 3) * e := by
          rw [h2]; ring
      _ ≤ (N : ℝ) ^ (-(1 : ℝ) / 3) := by linarith
  calc CF * (1 + 2 * (N : ℝ) ^ 2) ^ CF * (2 * (2 * (N : ℝ) ^ 2)) * p
      ≤ CF * (1 + 2 * (N : ℝ) ^ 2) ^ CF * (2 * (2 * (N : ℝ) ^ 2)) *
          ((N : ℝ) ^ Cb * e) := mul_le_mul_of_nonneg_left hp hM0
    _ ≤ ((4 * CF * 3 ^ CF) * (N : ℝ) ^ (2 * CF + 2)) * ((N : ℝ) ^ Cb * e) :=
        mul_le_mul_of_nonneg_right hM (by positivity)
    _ = (4 * CF * 3 ^ CF) * ((N : ℝ) ^ (2 * CF + 2 + Cb) * e) := by rw [← hNe]; ring
    _ ≤ (N : ℝ) * ((N : ℝ) ^ (2 * CF + 2 + Cb) * e) :=
        mul_le_mul_of_nonneg_right hK (by positivity)
    _ ≤ (N : ℝ) ^ (-(1 : ℝ) / 3) := by linarith

/-- The polynomial factor on the bad event is beaten by `exp(-c φ)`, for a natural exponent
`N^Cb` as in `HighProbOn`. -/
private lemma ward_bad_le {CF c : ℝ} {Cb : ℕ} (hCF : 0 ≤ CF) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℝ, p ≤ (N : ℝ) ^ Cb * Real.exp (-c * phi N ^ (1 : ℝ)) →
      CF * (1 + 2 * (N : ℝ) ^ 2) ^ CF * (2 * (2 * (N : ℝ) ^ 2)) * p ≤
        (N : ℝ) ^ (-(1 : ℝ) / 3) := by
  filter_upwards [ward_bad_le_real (CF := CF) (Cb := (Cb : ℝ)) hCF hc] with N hN p hp
  refine hN p ?_
  rwa [Real.rpow_natCast]

/-- `x^(k ε) = (x^ε)^k`. -/
private lemma ward_rpow_nat_mul {x : ℝ} (hx : 0 ≤ x) (ε : ℝ) (k : ℕ) :
    x ^ ((k : ℝ) * ε) = (x ^ ε) ^ k := by
  rw [mul_comm, Real.rpow_mul hx, Real.rpow_natCast]

/-! ### Exponent bookkeeping -/

private lemma ward_sq_rpow {x : ℝ} (hx : 0 ≤ x) (a : ℝ) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num [mul_comm]

/-- `η² N = N^{-1/3-2ε}` for `η = N^{-2/3-ε}`. -/
private lemma ward_eta_sq_mul {x : ℝ} (hx : 0 < x) (ε : ℝ) :
    (x ^ (-(2 : ℝ) / 3 - ε)) ^ 2 * x = x ^ (-(1 : ℝ) / 3 - 2 * ε) := by
  have h2 := Real.rpow_add hx (2 * (-(2 : ℝ) / 3 - ε)) 1
  rw [Real.rpow_one] at h2
  rw [ward_sq_rpow hx.le, ← h2]
  congr 1
  ring

/-- `η N^{-2/3+ε} N = N^{-1/3}` for `η = N^{-2/3-ε}`. -/
private lemma ward_eta_window_mul {x : ℝ} (hx : 0 < x) (ε : ℝ) :
    x ^ (-(2 : ℝ) / 3 - ε) * x ^ (-(2 : ℝ) / 3 + ε) * x = x ^ (-(1 : ℝ) / 3) := by
  have h2 := Real.rpow_add hx (-(2 : ℝ) / 3 - ε) (-(2 : ℝ) / 3 + ε)
  have h3 := Real.rpow_add hx (-(2 : ℝ) / 3 - ε + (-(2 : ℝ) / 3 + ε)) 1
  rw [Real.rpow_one] at h3
  rw [← h2, ← h3]
  congr 1
  ring

/-- `1 ≤ N η` for `η = N^{-2/3-ε}`, `ε ≤ 1/3`. -/
private lemma ward_one_le_mul_eta {x : ℝ} (hx : 1 ≤ x) {ε : ℝ} (hε : ε ≤ 1 / 3) :
    1 ≤ x * x ^ (-(2 : ℝ) / 3 - ε) := by
  have hx0 : 0 < x := by linarith
  have h := Real.rpow_add hx0 1 (-(2 : ℝ) / 3 - ε)
  rw [Real.rpow_one] at h
  rw [← h]
  exact Real.one_le_rpow hx (by linarith)

/-- The final comparison: `8 N^{(5C_F+1)ε} N^{-1/3} + N^{-1/3} ≤ N^{-1/3+(5C_F+3)ε}` once
`N^ε ≥ 9`. -/
private lemma ward_final_le {x ε CF P : ℝ} (hn1 : 1 ≤ x) (hε : 0 < ε) (hCF : 0 ≤ CF)
    (ht : 9 ≤ x ^ ε)
    (hP : P ≤ 8 * (x ^ ((5 * CF + 1) * ε) * x ^ (-(1 : ℝ) / 3)) + x ^ (-(1 : ℝ) / 3)) :
    P ≤ x ^ (-(1 : ℝ) / 3 + (5 * |CF| + 3) * ε) := by
  have hn0 : (0 : ℝ) < x := by linarith
  rw [abs_of_nonneg hCF]
  have hX : x ^ ((5 * CF + 1) * ε) * x ^ (-(1 : ℝ) / 3) =
      x ^ (-(1 : ℝ) / 3 + (5 * CF + 1) * ε) := by
    rw [← Real.rpow_add hn0]; congr 1; ring
  have hX1 : x ^ (-(1 : ℝ) / 3) ≤ x ^ (-(1 : ℝ) / 3 + (5 * CF + 1) * ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith)
  have h2 : x ^ (-(1 : ℝ) / 3 + (5 * CF + 3) * ε) =
      x ^ (2 * ε) * x ^ (-(1 : ℝ) / 3 + (5 * CF + 1) * ε) := by
    rw [← Real.rpow_add hn0]; congr 1; ring
  have h9 : 9 ≤ x ^ (2 * ε) := by
    have : x ^ (2 * ε) = (x ^ ε) ^ 2 := by
      have := ward_rpow_nat_mul hn0.le ε 2
      simpa using this
    rw [this]; nlinarith
  rw [h2]
  rw [hX] at hP
  have hpos : 0 ≤ x ^ (-(1 : ℝ) / 3 + (5 * CF + 1) * ε) := Real.rpow_nonneg hn0.le _
  nlinarith

/-! ### (3.18) -/

private lemma ward_partA {N : ℕ} {μ : Measure (Entries N)} [IsProbabilityMeasure μ]
    {ε CF : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 10) (hCF : 0 ≤ CF) (hN1 : 1 ≤ N)
    (ht : 9 ≤ (N : ℝ) ^ ε) {F : ℝ → ℝ} (hF4 : ContDiff ℝ 4 F)
    (hF : ∀ n ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF)
    (hB : ∀ ζ : ℝ, |ζ| ≤ (N : ℝ) ^ (3 * ε) → |iteratedDeriv 1 F ζ| ≤ (N : ℝ) ^ ((3 * CF + 1) * ε))
    (hbad : CF * (1 + 2 * (N : ℝ) ^ 2) ^ CF * (2 * (2 * (N : ℝ) ^ 2)) *
      (μ (aprioriEvent N ε)ᶜ).toReal ≤ (N : ℝ) ^ (-(1 : ℝ) / 3))
    {E : ℝ} (hE : |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) :
    |∫ ω, F (((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) ^ 2 * ∑ i, ∑ j,
          ‖resolventC (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i j‖ ^ 2) ∂μ -
      ∫ ω, F (offWard (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩) ∂μ| ≤
      (N : ℝ) ^ (-(1 : ℝ) / 3 + (5 * |CF| + 3) * ε) := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < N := by linarith
  set η : ℝ := (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) with hη_def
  have hη : 0 < η := Real.rpow_pos_of_pos hn0 _
  have hη2N : η ^ 2 * N = (N : ℝ) ^ (-(1 : ℝ) / 3 - 2 * ε) := ward_eta_sq_mul hn0 ε
  have hη2N1 : η ^ 2 * N ≤ 1 := by
    rw [hη2N]; exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hη2N3 : η ^ 2 * N ≤ (N : ℝ) ^ (-(1 : ℝ) / 3) := by
    rw [hη2N]; exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have ht2 : (N : ℝ) ^ (2 * ε) = ((N : ℝ) ^ ε) ^ 2 := by
    simpa using ward_rpow_nat_mul hn0.le ε 2
  have ht3 : (N : ℝ) ^ (3 * ε) = ((N : ℝ) ^ ε) ^ 3 := by
    simpa using ward_rpow_nat_mul hn0.le ε 3
  have hsum : ∀ ω : Entries N, η ^ 2 * ∑ i, ∑ j,
      ‖resolventC (symOfEntries ω) ⟨E, η⟩ i j‖ ^ 2 ≤ N := fun ω =>
    ward_eta_sq_sum_le (symOfEntries_isHermitian ω) (z := ⟨E, η⟩) hη
  have hsub : ∀ ω : Entries N, η ^ 2 * ∑ i, ∑ j,
      ‖resolventC (symOfEntries ω) ⟨E, η⟩ i j‖ ^ 2 - offWard (symOfEntries ω) ⟨E, η⟩ =
      η ^ 2 * ∑ i, ‖resolventC (symOfEntries ω) ⟨E, η⟩ i i‖ ^ 2 := fun ω =>
    ward_sub_offWard (symOfEntries ω) ⟨E, η⟩
  have hb0 : ∀ ω : Entries N, 0 ≤ offWard (symOfEntries ω) ⟨E, η⟩ := fun ω =>
    mul_nonneg (sq_nonneg _) (ward_offsum_nonneg _ _)
  have hdiag0 : ∀ ω : Entries N, 0 ≤ η ^ 2 * ∑ i, ‖resolventC (symOfEntries ω) ⟨E, η⟩ i i‖ ^ 2 :=
    fun ω => mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hRa : ∀ ω : Entries N, |η ^ 2 * ∑ i, ∑ j,
      ‖resolventC (symOfEntries ω) ⟨E, η⟩ i j‖ ^ 2| ≤ 2 * (N : ℝ) ^ 2 := by
    intro ω
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (ward_sumsq_nonneg _ _))]
    nlinarith [hsum ω]
  have hRb : ∀ ω : Entries N, |offWard (symOfEntries ω) ⟨E, η⟩| ≤ 2 * (N : ℝ) ^ 2 := by
    intro ω
    rw [abs_of_nonneg (hb0 ω)]
    nlinarith [hsum ω, hsub ω, hdiag0 ω]
  have key := ward_expect_sub_le (μ := μ) hF4 hF
    (a := fun ω => η ^ 2 * ∑ i, ∑ j, ‖resolventC (symOfEntries ω) ⟨E, η⟩ i j‖ ^ 2)
    (b := fun ω => offWard (symOfEntries ω) ⟨E, η⟩) (ward_continuous_a hη E)
    (ward_continuous_b hη E) (R := 2 * (N : ℝ) ^ 2) (by positivity) hRa hRb
    (Ω := aprioriEvent N ε) (R₁ := (N : ℝ) ^ (3 * ε)) (B := (N : ℝ) ^ ((3 * CF + 1) * ε))
    (δ := 4 * (η ^ 2 * N)) hB (Real.rpow_nonneg hn0.le _) (by positivity) ?_
  · refine ward_final_le hn1 hε hCF ht (le_trans key ?_)
    have hB1 : (N : ℝ) ^ ((3 * CF + 1) * ε) ≤ (N : ℝ) ^ ((5 * CF + 1) * ε) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith)
    have hX0 : 0 ≤ (N : ℝ) ^ ((5 * CF + 1) * ε) * (N : ℝ) ^ (-(1 : ℝ) / 3) := by positivity
    have hBd : (N : ℝ) ^ ((3 * CF + 1) * ε) * (4 * (η ^ 2 * N)) ≤
        8 * ((N : ℝ) ^ ((5 * CF + 1) * ε) * (N : ℝ) ^ (-(1 : ℝ) / 3)) := by
      calc (N : ℝ) ^ ((3 * CF + 1) * ε) * (4 * (η ^ 2 * N))
          ≤ (N : ℝ) ^ ((5 * CF + 1) * ε) * (4 * (N : ℝ) ^ (-(1 : ℝ) / 3)) :=
            mul_le_mul hB1 (by linarith) (by positivity) (by positivity)
        _ ≤ 8 * ((N : ℝ) ^ ((5 * CF + 1) * ε) * (N : ℝ) ^ (-(1 : ℝ) / 3)) := by linarith
    linarith
  · intro ω hω
    obtain ⟨b1, b2, -⟩ := aprioriEvent_bounds hN1 hε hε' hω
    obtain ⟨hb0', hb2⟩ := b2 E hE
    have hdiag : ∑ i, ‖resolventC (symOfEntries ω) ⟨E, η⟩ i i‖ ^ 2 ≤ 4 * N := by
      calc ∑ i, ‖resolventC (symOfEntries ω) ⟨E, η⟩ i i‖ ^ 2 ≤ ∑ _i : Fin N, (4 : ℝ) :=
            Finset.sum_le_sum fun i _ => by
              have : ‖resolventC (symOfEntries ω) ⟨E, η⟩ i i‖ ^ 2 ≤ 2 ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) (b1 E hE i) 2
              linarith
        _ = 4 * N := by simp [mul_comm]
    have hd : η ^ 2 * ∑ i, ‖resolventC (symOfEntries ω) ⟨E, η⟩ i i‖ ^ 2 ≤ 4 * (η ^ 2 * N) := by
      calc η ^ 2 * ∑ i, ‖resolventC (symOfEntries ω) ⟨E, η⟩ i i‖ ^ 2 ≤ η ^ 2 * (4 * N) :=
            mul_le_mul_of_nonneg_left hdiag (sq_nonneg _)
        _ = 4 * (η ^ 2 * N) := by ring
    have hab : η ^ 2 * ∑ i, ∑ j, ‖resolventC (symOfEntries ω) ⟨E, η⟩ i j‖ ^ 2 -
        offWard (symOfEntries ω) ⟨E, η⟩ =
          η ^ 2 * ∑ i, ‖resolventC (symOfEntries ω) ⟨E, η⟩ i i‖ ^ 2 :=
      hsub ω
    have hbound : η ^ 2 * ∑ i, ∑ j, ‖resolventC (symOfEntries ω) ⟨E, η⟩ i j‖ ^ 2 ≤
        (N : ℝ) ^ (3 * ε) := by
      rw [ht3]
      have hb2' : offWard (symOfEntries ω) ⟨E, η⟩ ≤ ((N : ℝ) ^ ε) ^ 2 := by rw [← ht2]; exact hb2
      nlinarith [hdiag0 ω]
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (ward_sumsq_nonneg _ _))]
      exact hbound
    · rw [abs_of_nonneg hb0']
      nlinarith [hdiag0 ω]
    · rw [hab, abs_of_nonneg (hdiag0 ω)]
      exact hd

/-! ### (3.19) -/

/-- Ward identity under the integral: `N ∫ Im m = η ∫ Σ_{i,j} |G_ij|²`. -/
private lemma ward_aTilde_eq {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) {η : ℝ}
    (hη : 0 < η) (E₁ E₂ : ℝ) :
    (N : ℝ) * ∫ y in E₁..E₂, (stieltjesM H ⟨y, η⟩).im =
      η * ∫ y in E₁..E₂, ∑ i, ∑ j, ‖resolventC H ⟨y, η⟩ i j‖ ^ 2 := by
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun y _ => natCast_mul_im_stieltjesM hH hη

/-- `|η ∫_{E₁}^{E₂} g| ≤ η K |E₂ - E₁|` when `|g| ≤ K` on the interval. -/
private lemma ward_eta_int_le {g : ℝ → ℝ} {η K : ℝ} (hη : 0 < η) {E₁ E₂ : ℝ}
    (hg : ∀ y ∈ Set.uIoc E₁ E₂, |g y| ≤ K) :
    |η * ∫ y in E₁..E₂, g y| ≤ η * (K * |E₂ - E₁|) := by
  rw [abs_mul, abs_of_pos hη]
  refine mul_le_mul_of_nonneg_left ?_ hη.le
  simpa [Real.norm_eq_abs] using
    intervalIntegral.norm_integral_le_of_norm_le_const (a := E₁) (b := E₂) (f := g)
      (fun y hy => by simpa [Real.norm_eq_abs] using hg y hy)

/-- The three integrands of `(3.19)` at a fixed `ω`: `Σ_{i,j}`, `Σ_{i≠j}` and `Σ_i |G_ii|²`
are continuous in `y`. -/
private lemma ward_continuous_y {N : ℕ} {η : ℝ} (hη : 0 < η) (ω : Entries N) :
    Continuous (fun y : ℝ => ∑ i, ∑ j, ‖resolventC (symOfEntries ω) (⟨y, η⟩ : ℂ) i j‖ ^ 2) ∧
    Continuous (fun y : ℝ => ∑ i, ∑ j, if i = j then (0 : ℝ) else
      ‖resolventC (symOfEntries ω) (⟨y, η⟩ : ℂ) i j‖ ^ 2) := by
  have hc : Continuous (fun y : ℝ => (ω, y)) := continuous_const.prodMk continuous_id
  have h1 := (ward_continuous_sumsq (N := N) hη).comp hc
  have h2 := (ward_continuous_offsum (N := N) hη).comp hc
  exact ⟨h1, h2⟩

private lemma ward_partB {N : ℕ} {μ : Measure (Entries N)} [IsProbabilityMeasure μ]
    {ε CF : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 10) (hCF : 0 ≤ CF) (hN1 : 1 ≤ N)
    (ht : 9 ≤ (N : ℝ) ^ ε) {F : ℝ → ℝ} (hF4 : ContDiff ℝ 4 F)
    (hF : ∀ n ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF)
    (hB : ∀ ζ : ℝ, |ζ| ≤ (N : ℝ) ^ (5 * ε) → |iteratedDeriv 1 F ζ| ≤ (N : ℝ) ^ ((5 * CF + 1) * ε))
    (hbad : CF * (1 + 2 * (N : ℝ) ^ 2) ^ CF * (2 * (2 * (N : ℝ) ^ 2)) *
      (μ (aprioriEvent N ε)ᶜ).toReal ≤ (N : ℝ) ^ (-(1 : ℝ) / 3))
    {E₁ E₂ : ℝ} (h1 : |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε))
    (h2 : |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) :
    |∫ ω, F (N * ∫ y in E₁..E₂,
          (stieltjesM (symOfEntries ω) ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩).im) ∂μ -
      ∫ ω, F (offWardInt (symOfEntries ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂) ∂μ| ≤
      (N : ℝ) ^ (-(1 : ℝ) / 3 + (5 * |CF| + 3) * ε) := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < N := by linarith
  set η : ℝ := (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) with hη_def
  have hη : 0 < η := Real.rpow_pos_of_pos hn0 _
  have hηN : 1 ≤ N * η := ward_one_le_mul_eta hn1 (by linarith)
  have hr1 : (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hr0 : 0 ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) := Real.rpow_nonneg hn0.le _
  have hΔ : |E₂ - E₁| ≤ 2 * (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) := by
    have a1 := abs_le.1 h1
    have a2 := abs_le.1 h2
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hηwin : η * (N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) = (N : ℝ) ^ (-(1 : ℝ) / 3) := by
    rw [mul_right_comm]; exact ward_eta_window_mul hn0 ε
  have ht2 : (N : ℝ) ^ (4 * ε) = ((N : ℝ) ^ ε) ^ 4 := by
    simpa using ward_rpow_nat_mul hn0.le ε 4
  have ht3 : (N : ℝ) ^ (5 * ε) = ((N : ℝ) ^ ε) ^ 5 := by
    simpa using ward_rpow_nat_mul hn0.le ε 5
  have hN3 : (N : ℝ) ^ (-(1 : ℝ) / 3) ≤ 1 / 9 := by
    have h3 : (N : ℝ) ^ (-(1 : ℝ) / 3) ≤ (N : ℝ) ^ (-ε) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    rw [Real.rpow_neg hn0.le] at h3
    have h4 : ((N : ℝ) ^ ε)⁻¹ ≤ 1 / 9 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) ht
    linarith
  -- pointwise facts on resolvent sums
  have hSle : ∀ (ω : Entries N) (y : ℝ),
      ∑ i, ∑ j, ‖resolventC (symOfEntries ω) (⟨y, η⟩ : ℂ) i j‖ ^ 2 ≤ N / η ^ 2 := by
    intro ω y
    have h := ward_eta_sq_sum_le (symOfEntries_isHermitian ω) (z := ⟨y, η⟩) hη
    have h' : η ^ 2 * ∑ i, ∑ j, ‖resolventC (symOfEntries ω) (⟨y, η⟩ : ℂ) i j‖ ^ 2 ≤ N := h
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hdet : η * ((N : ℝ) / η ^ 2 * |E₂ - E₁|) ≤ 2 * (N : ℝ) ^ 2 := by
    have e : η * ((N : ℝ) / η ^ 2 * |E₂ - E₁|) = N * |E₂ - E₁| / η := by
      field_simp
    rw [e, div_le_iff₀ hη]
    have hΔ2 : |E₂ - E₁| ≤ 2 := by linarith
    nlinarith
  have hA : ∀ ω : Entries N, (N : ℝ) * ∫ y in E₁..E₂,
      (stieltjesM (symOfEntries ω) ⟨y, η⟩).im = η * ∫ y in E₁..E₂,
        ∑ i, ∑ j, ‖resolventC (symOfEntries ω) (⟨y, η⟩ : ℂ) i j‖ ^ 2 :=
    fun ω => ward_aTilde_eq (symOfEntries_isHermitian ω) hη E₁ E₂
  have hBdef : ∀ ω : Entries N, offWardInt (symOfEntries ω) η E₁ E₂ = η * ∫ y in E₁..E₂,
      ∑ i, ∑ j, if i = j then (0 : ℝ) else
        ‖resolventC (symOfEntries ω) (⟨y, η⟩ : ℂ) i j‖ ^ 2 := fun ω => rfl
  have hRa : ∀ ω : Entries N, |(N : ℝ) * ∫ y in E₁..E₂,
      (stieltjesM (symOfEntries ω) ⟨y, η⟩).im| ≤ 2 * (N : ℝ) ^ 2 := by
    intro ω
    rw [hA ω]
    refine le_trans (ward_eta_int_le hη (K := (N : ℝ) / η ^ 2) fun y _ => ?_) hdet
    rw [abs_of_nonneg (ward_sumsq_nonneg _ _)]
    exact hSle ω y
  have hRb : ∀ ω : Entries N, |offWardInt (symOfEntries ω) η E₁ E₂| ≤ 2 * (N : ℝ) ^ 2 := by
    intro ω
    rw [hBdef ω]
    refine le_trans (ward_eta_int_le hη (K := (N : ℝ) / η ^ 2) fun y _ => ?_) hdet
    rw [abs_of_nonneg (ward_offsum_nonneg _ _)]
    exact (ward_offsum_le _ _).trans (hSle ω y)
  have hdiff : ∀ ω : Entries N, (N : ℝ) * (∫ y in E₁..E₂,
      (stieltjesM (symOfEntries ω) ⟨y, η⟩).im) - offWardInt (symOfEntries ω) η E₁ E₂ =
      η * ∫ y in E₁..E₂, ∑ i, ‖resolventC (symOfEntries ω) (⟨y, η⟩ : ℂ) i i‖ ^ 2 := by
    intro ω
    rw [hA ω, hBdef ω, ← mul_sub]
    congr 1
    obtain ⟨c1, c2⟩ := ward_continuous_y (N := N) hη ω
    rw [← intervalIntegral.integral_sub (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun y _ => ward_sumsq_sub_offsum _ _
  have key := ward_expect_sub_le (μ := μ) hF4 hF
    (a := fun ω => (N : ℝ) * ∫ y in E₁..E₂, (stieltjesM (symOfEntries ω) ⟨y, η⟩).im)
    (b := fun ω => offWardInt (symOfEntries ω) η E₁ E₂) (ward_continuous_a' hη E₁ E₂)
    (ward_continuous_b' hη E₁ E₂) (R := 2 * (N : ℝ) ^ 2) (by positivity) hRa hRb
    (Ω := aprioriEvent N ε) (R₁ := (N : ℝ) ^ (5 * ε))
    (B := (N : ℝ) ^ ((5 * CF + 1) * ε)) (δ := 8 * (N : ℝ) ^ (-(1 : ℝ) / 3)) hB
    (Real.rpow_nonneg hn0.le _) (by positivity) ?_
  · refine ward_final_le hn1 hε hCF ht (le_trans key ?_)
    have e : (N : ℝ) ^ ((5 * CF + 1) * ε) * (8 * (N : ℝ) ^ (-(1 : ℝ) / 3)) =
        8 * ((N : ℝ) ^ ((5 * CF + 1) * ε) * (N : ℝ) ^ (-(1 : ℝ) / 3)) := by ring
    linarith
  · intro ω hω
    obtain ⟨b1, -, b3⟩ := aprioriEvent_bounds hN1 hε hε' hω
    have hb3 : |offWardInt (symOfEntries ω) η E₁ E₂| ≤ 2 * (N : ℝ) ^ (4 * ε) := b3 E₁ E₂ h1 h2
    have hD : |(N : ℝ) * (∫ y in E₁..E₂, (stieltjesM (symOfEntries ω) ⟨y, η⟩).im) -
        offWardInt (symOfEntries ω) η E₁ E₂| ≤ 8 * (N : ℝ) ^ (-(1 : ℝ) / 3) := by
      rw [hdiff ω]
      refine le_trans (ward_eta_int_le hη (K := 4 * (N : ℝ)) fun y hy => ?_) ?_
      · have hy' := Set.uIoc_subset_uIcc hy
        have a1 := abs_le.1 h1
        have a2 := abs_le.1 h2
        have hyI : |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) := by
          rcases Set.mem_uIcc.1 hy' with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩ <;>
            exact abs_le.2 ⟨by linarith, by linarith⟩
        have hnn : 0 ≤ ∑ i, ‖resolventC (symOfEntries ω) (⟨y, η⟩ : ℂ) i i‖ ^ 2 :=
          Finset.sum_nonneg fun _ _ => sq_nonneg _
        rw [abs_of_nonneg hnn]
        calc ∑ i, ‖resolventC (symOfEntries ω) (⟨y, η⟩ : ℂ) i i‖ ^ 2 ≤ ∑ _i : Fin N, (4 : ℝ) :=
              Finset.sum_le_sum fun i _ => by
                have : ‖resolventC (symOfEntries ω) (⟨y, η⟩ : ℂ) i i‖ ^ 2 ≤ 2 ^ 2 :=
                  pow_le_pow_left₀ (norm_nonneg _) (b1 y hyI i) 2
                linarith
          _ = 4 * N := by simp [mul_comm]
      · calc η * (4 * (N : ℝ) * |E₂ - E₁|)
            ≤ η * (4 * (N : ℝ) * (2 * (N : ℝ) ^ (-(2 : ℝ) / 3 + ε))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΔ (by positivity)) hη.le
          _ = 8 * (η * (N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) := by ring
          _ = 8 * (N : ℝ) ^ (-(1 : ℝ) / 3) := by rw [hηwin]
    have ht4' : 1 ≤ ((N : ℝ) ^ ε) ^ 4 := one_le_pow₀ (by linarith)
    have h5 : 9 * ((N : ℝ) ^ ε) ^ 4 ≤ ((N : ℝ) ^ ε) ^ 5 := by
      have e : ((N : ℝ) ^ ε) ^ 5 = (N : ℝ) ^ ε * ((N : ℝ) ^ ε) ^ 4 := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right ht (by positivity)
    rw [ht2] at hb3
    refine ⟨?_, ?_, hD⟩
    · have h := abs_sub_abs_le_abs_sub ((N : ℝ) * ∫ y in E₁..E₂,
        (stieltjesM (symOfEntries ω) ⟨y, η⟩).im) (offWardInt (symOfEntries ω) η E₁ E₂)
      rw [ht3]
      linarith
    · rw [ht3]
      linarith

/-- (3.18) ⇐ (3.20) and (3.19) ⇐ its off-diagonal form, for every `H_γ` (in particular the law of
Lemma 3.5 at `γ = N(N+1)/2` and the GOE at `γ = 0`): replacing `η² Σ_{i,j} |G_ij|²` by
`η² Σ_{i ≠ j} |G_ij|²` and `N ∫ Im m` by `η ∫ Σ_{i ≠ j} |G_ij|²` changes `E F` by at most
`N^{-1/3+Cε}`; `C` depends only on `CF`. -/
theorem ward_reduction_largeQInterp {CF C0 φs : ℝ} (hC0 : 0 ≤ C0) (hφs : 1 / 3 < φs)
    (hφs' : φs ≤ 1 / 2) :
    ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < 1 / 10 → ∃ N0 : ℕ, ∀ N ≥ N0,
      ∀ L : EntryLaws N, (∃ Lv γ, LargeQClass C0 φs N Lv ∧ L = interp (lexPos N) γ Lv (goeLaws N)) →
      ∀ F : ℝ → ℝ, ContDiff ℝ 4 F →
        (∀ n ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF) →
        (∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |∫ ω, F (((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) ^ 2 * ∑ i, ∑ j,
                ‖resolventC (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i j‖ ^ 2) ∂L.law -
            ∫ ω, F (offWard (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩) ∂L.law| ≤
            (N : ℝ) ^ (-(1 : ℝ) / 3 + C * ε)) ∧
        (∀ E₁ E₂ : ℝ, |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |∫ ω, F (N * ∫ y in E₁..E₂,
                (stieltjesM (symOfEntries ω) ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩).im) ∂L.law -
            ∫ ω, F (offWardInt (symOfEntries ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂) ∂L.law| ≤
            (N : ℝ) ^ (-(1 : ℝ) / 3 + C * ε)) := by
  refine ⟨5 * |CF| + 3, by positivity, fun ε hε hε' => ?_⟩
  by_cases hCF : 0 ≤ CF
  swap
  · refine ⟨0, fun N _ L _ F _ hF => ?_⟩
    exfalso
    have h1 := hF 1 (by simp) 0
    exact hCF (by simpa using (abs_nonneg _).trans h1)
  obtain ⟨c, hc, Cb, hCb, N1, hN1⟩ := apriori_largeQInterp_event hC0 hφs hφs' ε hε hε'
  obtain ⟨N2, hN2⟩ := abs_iteratedDeriv_le_rpow_eps (CF := CF) (a := 3) (by norm_num) hε
  obtain ⟨N3, hN3⟩ := abs_iteratedDeriv_le_rpow_eps (CF := CF) (a := 5) (by norm_num) hε
  obtain ⟨N4, hN4⟩ := eventually_atTop.1 (ward_bad_le (CF := CF) (Cb := Cb) hCF hc)
  refine ⟨max N1 (max N2 (max N3 (max N4 (max ⌈(9 : ℝ) ^ (1 / ε)⌉₊ 1)))),
    fun N hN L hL F hF4 hF => ?_⟩
  have hNN1 : N1 ≤ N := le_trans (le_max_left _ _) hN
  have hNN2 : N2 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNN3 : N3 ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNN4 : N4 ≤ N := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hN
  have hNN5 : ⌈(9 : ℝ) ^ (1 / ε)⌉₊ ≤ N := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_max_right _ _))))) hN
  have hNN6 : 1 ≤ N := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_max_right _ _))))) hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hNN6
  have hn0 : (0 : ℝ) < N := by linarith
  have ht : 9 ≤ (N : ℝ) ^ ε := by
    have hle : (9 : ℝ) ^ (1 / ε) ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNN5)
    have h2 := Real.rpow_le_rpow (by positivity) hle hε.le
    rwa [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hε.ne', Real.rpow_one] at h2
  obtain ⟨Lv, γ, hv, rfl⟩ := hL
  have : IsProbabilityMeasure (interp (lexPos N) γ Lv (goeLaws N)).law :=
    isProbabilityMeasure_law (interp_isGenWigner hv.1 (goeLaws_isGenWigner N)).isProb
  have hP := hN1 N hNN1 (interp (lexPos N) γ Lv (goeLaws N)) ⟨Lv, γ, hv, rfl⟩
  have hPr : ((interp (lexPos N) γ Lv (goeLaws N)).law (aprioriEvent N ε)ᶜ).toReal ≤
      (N : ℝ) ^ Cb * Real.exp (-c * phi N ^ (1 : ℝ)) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hP
  have hbad := hN4 N hNN4 _ hPr
  have hB3 : ∀ ζ : ℝ, |ζ| ≤ (N : ℝ) ^ (3 * ε) → |iteratedDeriv 1 F ζ| ≤
      (N : ℝ) ^ ((3 * CF + 1) * ε) := fun ζ hζ => hN2 N hNN2 F hF ζ hζ 1 (by simp)
  have hB5 : ∀ ζ : ℝ, |ζ| ≤ (N : ℝ) ^ (5 * ε) → |iteratedDeriv 1 F ζ| ≤
      (N : ℝ) ^ ((5 * CF + 1) * ε) := fun ζ hζ => hN3 N hNN3 F hF ζ hζ 1 (by simp)
  exact ⟨fun E hE => ward_partA hε hε' hCF hNN6 ht hF4 hF hB3 hbad hE,
    fun E₁ E₂ h1 h2 => ward_partB hε hε' hCF hNN6 ht hF4 hF hB5 hbad h1 h2⟩

/-! ### A nondegenerate instance of the hypotheses -/

-- The entry law of Lemma 3.5 at `N = 1024` with diagonal values `±1/16, 0, 0` (variance `2/N`)
-- and off-diagonal values `±1/32` (variance `1/N`), in `LargeQClass 1 (2/5) 1024`.
open private lawA lawA_isGenWigner lawA_supp from WEdgeNS.EdgeUniv.LargeQClass

/-- `1024 ^ (-2/3 + 1/15) = 1/64`: the half-width of the window `I_ε` at `N = 1024`,
`ε = 1/15`. -/
lemma rpow_1024_window :
    ((1024 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) = 1 / 64 := by
  rw [show ((1024 : ℕ) : ℝ) = (2 : ℝ) ^ (10 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  rw [show (10 : ℝ) * (-(2 : ℝ) / 3 + 1 / 15) = -((6 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg (by norm_num), Real.rpow_natCast]
  norm_num

/-- Every hypothesis of `ward_reduction_largeQInterp` holds at one point: `N = 1024`, `C0 = 1`,
`φs = 2/5`, `ε = 1/15` (the window `I_ε` is `|E - 2| ≤ 1/64`), `L = H_γ` with `γ = 5000` between
the law above and the GOE (both entry types occur), `F = K(·/π)` for the edge cutoff `K`,
`E₁ = 2 - 1/100 < E₂ = 2 + 1/100` and `E = 2`. -/
example : ∃ CF : ℝ, 0 < CF ∧ (0 : ℝ) ≤ 1 ∧ (1 / 3 : ℝ) < 2 / 5 ∧ (2 / 5 : ℝ) ≤ 1 / 2 ∧
    (0 : ℝ) < 1 / 15 ∧ (1 / 15 : ℝ) < 1 / 10 ∧
    (∃ Lv γ, LargeQClass 1 (2 / 5) 1024 Lv ∧
      interp (lexPos 1024) 5000 lawA (goeLaws 1024) = interp (lexPos 1024) γ Lv (goeLaws 1024)) ∧
    ContDiff ℝ 4 (fun x => edgeCutoff (x / Real.pi)) ∧
    (∀ n ∈ Finset.Icc 1 4, ∀ x : ℝ,
      |iteratedDeriv n (fun x => edgeCutoff (x / Real.pi)) x| ≤ CF * (1 + |x|) ^ CF) ∧
    |(2 - 1 / 100 : ℝ) - 2| ≤ ((1024 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) ∧
    |(2 + 1 / 100 : ℝ) - 2| ≤ ((1024 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) ∧
    (2 - 1 / 100 : ℝ) < 2 + 1 / 100 ∧
    |(2 : ℝ) - 2| ≤ ((1024 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) := by
  obtain ⟨CF, hCF, h⟩ := edgeCutoff_deriv_le
  refine ⟨CF, hCF, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    ⟨lawA, 5000, ⟨lawA_isGenWigner, lawA_supp⟩, rfl⟩,
    (edgeCutoff_props.1 4).comp (contDiff_id.div_const _), h, ?_, ?_, by norm_num, ?_⟩ <;>
  · rw [rpow_1024_window]; norm_num [abs_of_nonneg, abs_of_nonpos]

#print axioms natCast_mul_im_stieltjesM
#print axioms ward_reduction_largeQInterp

end WEdgeNS
