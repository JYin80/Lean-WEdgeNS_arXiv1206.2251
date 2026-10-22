import Mathlib

/-!
# High moments of linear forms in independent bounded variables
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- For `|x| ≤ 1`, `exp x ≤ 1 + x + x ^ 2`. -/
private lemma exp_le_one_add_add_sq {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hx)).2
  linarith

/-- A measurable real function that is a.e. bounded in absolute value is integrable
for a finite measure. -/
private lemma integrable_of_ae_abs_le {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) (K : ℝ)
    (h : ∀ᵐ ω ∂μ, |f ω| ≤ K) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable K
    (by filter_upwards [h] with ω hω; simpa [Real.norm_eq_abs] using hω)

/-- Exponential moment of one centred variable bounded by `q⁻¹` with second moment at most
`s2`: `E exp (y b) ≤ exp (y ^ 2 s2)` when `|y| q⁻¹ ≤ 1`. -/
private lemma integral_exp_mul_le {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {b : Ω → ℝ} (hb : Measurable b) (h0 : ∫ ω, b ω ∂μ = 0)
    {q s2 : ℝ} (hbd : ∀ᵐ ω ∂μ, |b ω| ≤ q⁻¹) (hvar : ∫ ω, b ω ^ 2 ∂μ ≤ s2) {y : ℝ}
    (hy : |y| * q⁻¹ ≤ 1) :
    ∫ ω, Real.exp (y * b ω) ∂μ ≤ Real.exp (y ^ 2 * s2) := by
  have hint1 : Integrable b μ := integrable_of_ae_abs_le hb q⁻¹ hbd
  have hint2 : Integrable (fun ω => b ω ^ 2) μ :=
    integrable_of_ae_abs_le (hb.pow_const 2) (q⁻¹ ^ 2) (by
      filter_upwards [hbd] with ω hω
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hω 2)
  have hR1 : Integrable (fun ω => 1 + y * b ω) μ := (integrable_const 1).add (hint1.const_mul y)
  have hR : Integrable (fun ω => 1 + y * b ω + y ^ 2 * b ω ^ 2) μ :=
    hR1.add (hint2.const_mul (y ^ 2))
  calc ∫ ω, Real.exp (y * b ω) ∂μ ≤ ∫ ω, (1 + y * b ω + y ^ 2 * b ω ^ 2) ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ω => (Real.exp_pos _).le) hR ?_
        filter_upwards [hbd] with ω hω
        have hyb : |y * b ω| ≤ 1 := by
          rw [abs_mul]; exact (mul_le_mul_of_nonneg_left hω (abs_nonneg y)).trans hy
        have := exp_le_one_add_add_sq hyb
        calc Real.exp (y * b ω) ≤ 1 + y * b ω + (y * b ω) ^ 2 := this
          _ = 1 + y * b ω + y ^ 2 * b ω ^ 2 := by ring
    _ = 1 + y ^ 2 * ∫ ω, b ω ^ 2 ∂μ := by
        rw [integral_add hR1 (hint2.const_mul _), integral_add (integrable_const 1)
          (hint1.const_mul y), integral_const_mul, integral_const_mul, h0]
        simp
    _ ≤ 1 + y ^ 2 * s2 := by gcongr
    _ ≤ Real.exp (y ^ 2 * s2) := by linarith [Real.add_one_le_exp (y ^ 2 * s2)]

/-- Exponential moment of a real linear form `∑ i, c i * a i` at `B⁻¹`, under
`|c i| q⁻¹ ≤ B` and `∑ i, c i ^ 2 * s2 ≤ B ^ 2`: it is integrable and at most `e`. -/
private lemma integral_exp_sum_le {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {a : Fin n → Ω → ℝ} (hind : iIndepFun a μ)
    (hmeas : ∀ i, Measurable (a i)) (h0 : ∀ i, ∫ ω, a i ω ∂μ = 0) {q s2 : ℝ}
    (hbd : ∀ i, ∀ᵐ ω ∂μ, |a i ω| ≤ q⁻¹) (hvar : ∀ i, ∫ ω, a i ω ^ 2 ∂μ ≤ s2)
    (c : Fin n → ℝ) {B : ℝ} (hB : 0 < B) (hc : ∀ i, |c i| * q⁻¹ ≤ B)
    (hv : ∑ i, c i ^ 2 * s2 ≤ B ^ 2) :
    Integrable (fun ω => Real.exp (B⁻¹ * ∑ i, c i * a i ω)) μ ∧
      ∫ ω, Real.exp (B⁻¹ * ∑ i, c i * a i ω) ∂μ ≤ Real.exp 1 := by
  set X : Fin n → Ω → ℝ := fun i ω => c i * a i ω with hXdef
  have hXind : iIndepFun X μ :=
    hind.comp (fun i x => c i * x) (fun i => measurable_const.mul measurable_id)
  have hXmeas : ∀ i, Measurable (X i) := fun i => measurable_const.mul (hmeas i)
  have hfun : (fun ω => Real.exp (B⁻¹ * ∑ i, c i * a i ω)) =
      fun ω => Real.exp (B⁻¹ * (∑ i ∈ Finset.univ, X i) ω) := by
    funext ω; simp [X, Finset.sum_apply]
  have hy : ∀ i, |B⁻¹ * c i| * q⁻¹ ≤ 1 := by
    intro i
    rw [abs_mul, abs_of_pos (inv_pos.mpr hB), mul_assoc]
    calc B⁻¹ * (|c i| * q⁻¹) ≤ B⁻¹ * B := by gcongr; exact hc i
      _ = 1 := inv_mul_cancel₀ hB.ne'
  have hXi : ∀ i, (fun ω => Real.exp (B⁻¹ * X i ω)) =
      fun ω => Real.exp ((B⁻¹ * c i) * a i ω) := by
    intro i; funext ω; simp only [X, mul_assoc]
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Integrable (fun ω => Real.exp (B⁻¹ * X i ω)) μ := by
    intro i _
    rw [hXi i]
    refine integrable_of_ae_abs_le (measurable_const.mul (hmeas i)).exp (Real.exp 1) ?_
    filter_upwards [hbd i] with ω hω
    rw [Real.abs_exp]
    apply Real.exp_le_exp.mpr
    calc B⁻¹ * c i * a i ω ≤ |B⁻¹ * c i * a i ω| := le_abs_self _
      _ = |B⁻¹ * c i| * |a i ω| := abs_mul _ _
      _ ≤ |B⁻¹ * c i| * q⁻¹ := by gcongr
      _ ≤ 1 := hy i
  refine ⟨hfun ▸ hXind.integrable_exp_mul_sum hXmeas hint, ?_⟩
  have hmgf : mgf (∑ i ∈ Finset.univ, X i) μ B⁻¹ = ∏ i ∈ Finset.univ, mgf (X i) μ B⁻¹ :=
    hXind.mgf_sum hXmeas Finset.univ
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      mgf (X i) μ B⁻¹ ≤ Real.exp ((B⁻¹ * c i) ^ 2 * s2) := by
    intro i _
    rw [mgf, hXi i]
    exact integral_exp_mul_le (hmeas i) (h0 i) (hbd i) (hvar i) (hy i)
  calc ∫ ω, Real.exp (B⁻¹ * ∑ i, c i * a i ω) ∂μ
        = mgf (∑ i ∈ Finset.univ, X i) μ B⁻¹ := by rw [hfun, mgf]
    _ = ∏ i ∈ Finset.univ, mgf (X i) μ B⁻¹ := hmgf
    _ ≤ ∏ i ∈ Finset.univ, Real.exp ((B⁻¹ * c i) ^ 2 * s2) :=
        Finset.prod_le_prod₀ (fun i _ => mgf_nonneg) hle
    _ = Real.exp (B⁻¹ ^ 2 * ∑ i, c i ^ 2 * s2) := by
        rw [← Real.exp_sum, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ ≤ Real.exp 1 := by
        apply Real.exp_le_exp.mpr
        calc B⁻¹ ^ 2 * ∑ i, c i ^ 2 * s2 ≤ B⁻¹ ^ 2 * B ^ 2 := by gcongr
          _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hB.ne', one_pow]

/-- Pointwise bound `x ^ (2k) ≤ (2k)! B ^ (2k) (exp (B⁻¹ x) + exp (-(B⁻¹ x)))` for `B > 0`. -/
private lemma pow_two_mul_le_exp {B : ℝ} (hB : 0 < B) (x : ℝ) (k : ℕ) :
    x ^ (2 * k) ≤ (2 * k).factorial * B ^ (2 * k) *
      (Real.exp (B⁻¹ * x) + Real.exp (B⁻¹ * -x)) := by
  set u := B⁻¹ * x with hu
  have hx : x = B * u := by rw [hu, ← mul_assoc, mul_inv_cancel₀ hB.ne', one_mul]
  have hfac : (0 : ℝ) < (2 * k).factorial := by exact_mod_cast Nat.factorial_pos _
  have h1 : |u| ^ (2 * k) ≤ (2 * k).factorial * Real.exp |u| := by
    have := Real.pow_div_factorial_le_exp |u| (abs_nonneg u) (2 * k)
    rw [div_le_iff₀ hfac] at this
    linarith
  have h2 : Real.exp |u| ≤ Real.exp u + Real.exp (-u) := by
    rcases abs_cases u with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
      linarith [Real.exp_pos u, Real.exp_pos (-u)]
  have heven : |u| ^ (2 * k) = u ^ (2 * k) := (even_two_mul k).pow_abs u
  have hneg : B⁻¹ * -x = -u := by rw [hu]; ring
  rw [hneg, hx, mul_pow, ← heven]
  have hBk : 0 ≤ B ^ (2 * k) := pow_nonneg hB.le _
  calc B ^ (2 * k) * |u| ^ (2 * k) ≤ B ^ (2 * k) * ((2 * k).factorial * Real.exp |u|) := by
        gcongr
    _ ≤ B ^ (2 * k) * ((2 * k).factorial * (Real.exp u + Real.exp (-u))) := by
        gcongr
    _ = (2 * k).factorial * B ^ (2 * k) * (Real.exp u + Real.exp (-u)) := by ring

/-- Even moments of a real linear form: `E (∑ i, c i a i) ^ (2k) ≤ 2 e (2k)! B ^ (2k)`
under `|c i| q⁻¹ ≤ B` and `∑ i, c i ^ 2 * s2 ≤ B ^ 2`; the integrand is integrable. -/
private lemma moment_real_le {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {a : Fin n → Ω → ℝ} (hind : iIndepFun a μ)
    (hmeas : ∀ i, Measurable (a i)) (h0 : ∀ i, ∫ ω, a i ω ∂μ = 0) {q s2 : ℝ}
    (hbd : ∀ i, ∀ᵐ ω ∂μ, |a i ω| ≤ q⁻¹) (hvar : ∀ i, ∫ ω, a i ω ^ 2 ∂μ ≤ s2)
    (c : Fin n → ℝ) {B : ℝ} (hB : 0 < B) (hc : ∀ i, |c i| * q⁻¹ ≤ B)
    (hv : ∑ i, c i ^ 2 * s2 ≤ B ^ 2) (k : ℕ) :
    Integrable (fun ω => (∑ i, c i * a i ω) ^ (2 * k)) μ ∧
      ∫ ω, (∑ i, c i * a i ω) ^ (2 * k) ∂μ ≤
        2 * Real.exp 1 * (2 * k).factorial * B ^ (2 * k) := by
  obtain ⟨hi1, hb1⟩ := integral_exp_sum_le hind hmeas h0 hbd hvar c hB hc hv
  have hc' : ∀ i, |(-c) i| * q⁻¹ ≤ B := fun i => by simpa using hc i
  have hv' : ∑ i, (-c) i ^ 2 * s2 ≤ B ^ 2 := by simpa using hv
  obtain ⟨hi2, hb2⟩ := integral_exp_sum_le hind hmeas h0 hbd hvar (-c) hB hc' hv'
  have hneg : ∀ ω, ∑ i, (-c) i * a i ω = -∑ i, c i * a i ω := by
    intro ω; simp [Finset.sum_neg_distrib, neg_mul]
  simp_rw [hneg] at hi2 hb2
  set K : ℝ := (2 * k).factorial * B ^ (2 * k)
  have hgi : Integrable (fun ω => K * (Real.exp (B⁻¹ * ∑ i, c i * a i ω) +
      Real.exp (B⁻¹ * -∑ i, c i * a i ω))) μ := (hi1.add hi2).const_mul K
  have hpt : ∀ ω, (∑ i, c i * a i ω) ^ (2 * k) ≤ K * (Real.exp (B⁻¹ * ∑ i, c i * a i ω) +
      Real.exp (B⁻¹ * -∑ i, c i * a i ω)) := fun ω => pow_two_mul_le_exp hB _ k
  have hnn : ∀ ω, 0 ≤ (∑ i, c i * a i ω) ^ (2 * k) := fun ω => (even_two_mul k).pow_nonneg _
  have hmeasS : Measurable (fun ω => (∑ i, c i * a i ω) ^ (2 * k)) :=
    (Finset.measurable_sum _ fun i _ => measurable_const.mul (hmeas i)).pow_const _
  refine ⟨hgi.mono' hmeasS.aestronglyMeasurable (Eventually.of_forall fun ω => ?_), ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (hnn ω)]; exact hpt ω
  calc ∫ ω, (∑ i, c i * a i ω) ^ (2 * k) ∂μ
      ≤ ∫ ω, K * (Real.exp (B⁻¹ * ∑ i, c i * a i ω) +
          Real.exp (B⁻¹ * -∑ i, c i * a i ω)) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall hnn) hgi (Eventually.of_forall hpt)
    _ = K * (∫ ω, Real.exp (B⁻¹ * ∑ i, c i * a i ω) ∂μ +
          ∫ ω, Real.exp (B⁻¹ * -∑ i, c i * a i ω) ∂μ) := by
        rw [integral_const_mul, integral_add hi1 hi2]
    _ ≤ K * (Real.exp 1 + Real.exp 1) := by
        have : 0 ≤ K := by positivity
        gcongr
    _ = 2 * Real.exp 1 * (2 * k).factorial * B ^ (2 * k) := by ring

/-- `(x ^ 2 + y ^ 2) ^ p ≤ 2 ^ p (x ^ (2p) + y ^ (2p))`. -/
lemma sq_add_sq_pow_le (x y : ℝ) (p : ℕ) :
    (x ^ 2 + y ^ 2) ^ p ≤ 2 ^ p * (x ^ (2 * p) + y ^ (2 * p)) := by
  have hx : 0 ≤ x ^ 2 := sq_nonneg x
  have hy : 0 ≤ y ^ 2 := sq_nonneg y
  have hm : x ^ 2 + y ^ 2 ≤ 2 * max (x ^ 2) (y ^ 2) := by
    linarith [le_max_left (x ^ 2) (y ^ 2), le_max_right (x ^ 2) (y ^ 2)]
  have hmp : max (x ^ 2) (y ^ 2) ^ p ≤ x ^ (2 * p) + y ^ (2 * p) := by
    rw [pow_mul, pow_mul]
    rcases max_choice (x ^ 2) (y ^ 2) with h | h <;> rw [h]
    · linarith [pow_nonneg hy p]
    · linarith [pow_nonneg hx p]
  calc (x ^ 2 + y ^ 2) ^ p ≤ (2 * max (x ^ 2) (y ^ 2)) ^ p :=
        pow_le_pow_left₀ (by positivity) hm p
    _ = 2 ^ p * max (x ^ 2) (y ^ 2) ^ p := mul_pow _ _ _
    _ ≤ 2 ^ p * (x ^ (2 * p) + y ^ (2 * p)) := by gcongr

/-- High moments of linear forms (Lemma A.1 (i), (A.2) of [15]),
bounded entries with variance at most `s2`. -/
theorem moment_linear_le : ∃ C > 0, ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (n : ℕ) (a : Fin n → Ω → ℝ), iIndepFun a μ →
    (∀ i, Measurable (a i)) → (∀ i, ∫ ω, a i ω ∂μ = 0) → ∀ q s2 : ℝ, 0 < q →
    (∀ i, ∀ᵐ ω ∂μ, |a i ω| ≤ q⁻¹) → (∀ i, ∫ ω, a i ω ^ 2 ∂μ ≤ s2) →
    ∀ (A : Fin n → ℂ) (p : ℕ), 1 ≤ p →
      ∫ ω, ‖∑ i, A i * a i ω‖ ^ (2 * p) ∂μ ≤
        (C * p) ^ (2 * p) * ((⨆ i, ‖A i‖) / q + Real.sqrt (s2 * ∑ i, ‖A i‖ ^ 2)) ^ (2 * p) := by
  refine ⟨16, by norm_num, ?_⟩
  intro Ω _ μ _ n a hind hmeas h0 q s2 hq hbd hvar A p hp
  set M : ℝ := (⨆ i, ‖A i‖) / q with hMdef
  set σ : ℝ := Real.sqrt (s2 * ∑ i, ‖A i‖ ^ 2) with hσdef
  have hM0 : 0 ≤ M := div_nonneg (Real.iSup_nonneg fun i => norm_nonneg _) hq.le
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hAle : ∀ i, ‖A i‖ * q⁻¹ ≤ M := by
    intro i
    rw [hMdef, div_eq_mul_inv]
    gcongr
    exact le_ciSup (f := fun j => ‖A j‖) (Finite.bddAbove_range _) i
  have hRHS0 : 0 ≤ ((16 : ℝ) * p) ^ (2 * p) * (M + σ) ^ (2 * p) := by
    have : 0 ≤ M + σ := add_nonneg hM0 hσ0
    positivity
  rcases (add_nonneg hM0 hσ0).eq_or_lt with hB0 | hB
  · -- `M + σ = 0`: then every `A i` vanishes
    have hA : ∀ i, A i = 0 := by
      intro i
      have hM : M = 0 := by linarith
      have h := hAle i
      rw [hM] at h
      have hqi : 0 < q⁻¹ := inv_pos.mpr hq
      have : ‖A i‖ ≤ 0 := by nlinarith [norm_nonneg (A i)]
      exact norm_le_zero_iff.mp this
    have hp0 : 2 * p ≠ 0 := by omega
    simp only [hA, zero_mul, Finset.sum_const_zero, norm_zero, zero_pow hp0, integral_zero]
    exact hRHS0
  set B : ℝ := M + σ with hBdef
  have hv : ∀ c : Fin n → ℝ, (∀ i, |c i| ≤ ‖A i‖) → ∑ i, c i ^ 2 * s2 ≤ B ^ 2 := by
    intro c hc
    by_cases hs : 0 ≤ s2
    · calc ∑ i, c i ^ 2 * s2 ≤ ∑ i, ‖A i‖ ^ 2 * s2 := by
            refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ hs
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hc i) 2
        _ = σ ^ 2 := by
            rw [hσdef, Real.sq_sqrt (mul_nonneg hs (Finset.sum_nonneg fun i _ => by positivity)),
              Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => mul_comm _ _
        _ ≤ B ^ 2 := pow_le_pow_left₀ hσ0 (by linarith) 2
    · push Not at hs
      calc ∑ i, c i ^ 2 * s2 ≤ ∑ _i : Fin n, (0 : ℝ) := by
            exact Finset.sum_le_sum fun i _ =>
              mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hs.le
        _ = 0 := Finset.sum_const_zero
        _ ≤ B ^ 2 := sq_nonneg _
  have hcB : ∀ c : Fin n → ℝ, (∀ i, |c i| ≤ ‖A i‖) → ∀ i, |c i| * q⁻¹ ≤ B := by
    intro c hc i
    calc |c i| * q⁻¹ ≤ ‖A i‖ * q⁻¹ := by gcongr; exact hc i
      _ ≤ M := hAle i
      _ ≤ B := by linarith
  have hre : ∀ i, |(A i).re| ≤ ‖A i‖ := fun i => Complex.abs_re_le_norm _
  have him : ∀ i, |(A i).im| ≤ ‖A i‖ := fun i => Complex.abs_im_le_norm _
  obtain ⟨hiX, hX⟩ := moment_real_le hind hmeas h0 hbd hvar (fun i => (A i).re) hB
    (hcB _ hre) (hv _ hre) p
  obtain ⟨hiY, hY⟩ := moment_real_le hind hmeas h0 hbd hvar (fun i => (A i).im) hB
    (hcB _ him) (hv _ him) p
  have hpt : ∀ ω, ‖∑ i, A i * a i ω‖ ^ (2 * p) ≤
      2 ^ p * ((∑ i, (A i).re * a i ω) ^ (2 * p) + (∑ i, (A i).im * a i ω) ^ (2 * p)) := by
    intro ω
    have hre' : (∑ i, A i * (a i ω : ℂ)).re = ∑ i, (A i).re * a i ω := by
      simp [Complex.re_sum, Complex.mul_re]
    have him' : (∑ i, A i * (a i ω : ℂ)).im = ∑ i, (A i).im * a i ω := by
      simp [Complex.im_sum, Complex.mul_im]
    have hn : ‖∑ i, A i * (a i ω : ℂ)‖ ^ 2 =
        (∑ i, (A i).re * a i ω) ^ 2 + (∑ i, (A i).im * a i ω) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre', him']; ring
    rw [pow_mul, hn]
    exact sq_add_sq_pow_le _ _ p
  have hgi : Integrable (fun ω => 2 ^ p * ((∑ i, (A i).re * a i ω) ^ (2 * p) +
      (∑ i, (A i).im * a i ω) ^ (2 * p))) μ := (hiX.add hiY).const_mul _
  have hfac : ((2 * p).factorial : ℝ) ≤ ((2 * p : ℕ) : ℝ) ^ (2 * p) := by
    exact_mod_cast Nat.factorial_le_pow (2 * p)
  have he : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
  have h32 : (32 : ℝ) ≤ 32 ^ p := le_self_pow₀ (by norm_num) (by omega)
  have hBp : 0 ≤ B ^ (2 * p) := pow_nonneg hB.le _
  calc ∫ ω, ‖∑ i, A i * a i ω‖ ^ (2 * p) ∂μ
      ≤ ∫ ω, 2 ^ p * ((∑ i, (A i).re * a i ω) ^ (2 * p) +
          (∑ i, (A i).im * a i ω) ^ (2 * p)) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => by positivity) hgi
          (Eventually.of_forall hpt)
    _ = 2 ^ p * (∫ ω, (∑ i, (A i).re * a i ω) ^ (2 * p) ∂μ +
          ∫ ω, (∑ i, (A i).im * a i ω) ^ (2 * p) ∂μ) := by
        rw [integral_const_mul, integral_add hiX hiY]
    _ ≤ 2 ^ p * (2 * Real.exp 1 * (2 * p).factorial * B ^ (2 * p) +
          2 * Real.exp 1 * (2 * p).factorial * B ^ (2 * p)) := by
        gcongr
    _ = (4 * Real.exp 1) * 2 ^ p * (2 * p).factorial * B ^ (2 * p) := by ring
    _ ≤ (2 ^ p * 32 ^ p) * ((2 * p : ℕ) : ℝ) ^ (2 * p) * B ^ (2 * p) := by
        have h2p : (0 : ℝ) ≤ 2 ^ p := by positivity
        have hf0 : (0 : ℝ) ≤ (2 * p).factorial := by positivity
        have h1 : 4 * Real.exp 1 * 2 ^ p ≤ 2 ^ p * 32 ^ p := by nlinarith
        gcongr
    _ = ((16 : ℝ) * p) ^ (2 * p) * B ^ (2 * p) := by
        congr 1
        rw [← mul_pow, show (2 : ℝ) * 32 = 8 ^ 2 by norm_num, ← pow_mul, ← mul_pow]
        push_cast
        ring

/-! ### Checks -/

/-- The fair coin law on `Bool`. -/
private def momentsLinearCoin : Measure Bool := (2 : ENNReal)⁻¹ • Measure.count

private instance : IsProbabilityMeasure momentsLinearCoin := by
  constructor
  simp only [momentsLinearCoin, Measure.smul_apply, Measure.count_univ,
    smul_eq_mul]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- The Rademacher sign attached to a coin. -/
private def momentsLinearSign (b : Bool) : ℝ := if b then 1 else -1

/-- Two independent Rademacher variables on `Fin 2 → Bool` with the product law. -/
private def momentsLinearRad : Fin 2 → (Fin 2 → Bool) → ℝ := fun i ω => momentsLinearSign (ω i)

private lemma momentsLinear_integral_coin (f : Bool → ℝ) :
    ∫ b, f b ∂momentsLinearCoin = (f true + f false) / 2 := by
  rw [momentsLinearCoin, integral_smul_measure, integral_count]
  simp
  ring

private lemma momentsLinear_integral_rad (i : Fin 2) (f : ℝ → ℝ) :
    ∫ ω, f (momentsLinearRad i ω) ∂(Measure.pi fun _ => momentsLinearCoin) =
      (f 1 + f (-1)) / 2 := by
  have := integral_comp_eval (μ := fun _ : Fin 2 => momentsLinearCoin) (i := i)
    (f := fun b => f (momentsLinearSign b)) (Measurable.of_discrete).aestronglyMeasurable
  simp only [momentsLinearRad]
  rw [this, momentsLinear_integral_coin]
  simp [momentsLinearSign]

/-- Nondegenerate instance: two independent Rademacher signs (`n = 2`), `q = 1`, `s2 = 1`
(both bounds attained), complex coefficients `(1, i)`, moment order `2 * 2`. -/
example : ∃ C > 0,
    ∫ ω, ‖∑ i, ![(1 : ℂ), Complex.I] i * momentsLinearRad i ω‖ ^ (2 * 2)
        ∂(Measure.pi fun _ => momentsLinearCoin) ≤
      (C * (2 : ℕ)) ^ (2 * 2) * ((⨆ i, ‖![(1 : ℂ), Complex.I] i‖) / 1 +
        Real.sqrt (1 * ∑ i, ‖![(1 : ℂ), Complex.I] i‖ ^ 2)) ^ (2 * 2) := by
  obtain ⟨C, hC, h⟩ := moment_linear_le
  refine ⟨C, hC, h (Measure.pi fun _ => momentsLinearCoin) 2 momentsLinearRad ?_ ?_ ?_ 1 1
    one_pos ?_ ?_ ![(1 : ℂ), Complex.I] 2 (by norm_num)⟩
  · exact iIndepFun_pi (X := fun _ => momentsLinearSign)
      (fun _ => (Measurable.of_discrete).aemeasurable)
  · intro i; exact (Measurable.of_discrete).comp (measurable_pi_apply i)
  · intro i
    have := momentsLinear_integral_rad i id
    simpa using this
  · intro i
    refine Eventually.of_forall fun ω => ?_
    simp only [momentsLinearRad, momentsLinearSign, inv_one]
    split_ifs <;> norm_num
  · intro i
    have := momentsLinear_integral_rad i (fun x => x ^ 2)
    rw [this]; norm_num

#print axioms moment_linear_le

end WEdgeNS
