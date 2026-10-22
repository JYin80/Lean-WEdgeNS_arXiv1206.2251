import WEdgeNS.EdgeUniv.ImMscIntegral
import WEdgeNS.LocalLaw.Class

/-!
# Counting functions against smoothed traces (Lemma 6.1 of [26])
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- The chain (6.10) → (6.11) for the counting function: for `η ≤ ℓ₁ ≤ (E_L - E)/2`,
`|N(E,E_L) - Tr χ_E ∗ θ_η(H)| ≤ 4 Σ_α f(λ_α) + 12 (η/ℓ₁) N(E,E_L) + 10 N(E-ℓ₁,E+ℓ₁)
+ 10 N(E_L-ℓ₁,∞)`. -/
private lemma count_chain {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {η ℓ₁ E EL : ℝ} (hη : 0 < η) (hηℓ : η ≤ ℓ₁) (hℓE : 2 * ℓ₁ ≤ EL - E) :
    |(countIcc hH E EL : ℝ) - smoothCount hH η E EL| ≤
      4 * ∑ α, (η * (EL - E) / ((|hH.eigenvalues α - EL| + η) * (|hH.eigenvalues α - E| + η)) *
          (if hH.eigenvalues α ≤ E - ℓ₁ then (1 : ℝ) else 0)) +
        12 * (η / ℓ₁) * (countIcc hH E EL : ℝ) + 10 * (countIcc hH (E - ℓ₁) (E + ℓ₁) : ℝ) +
        10 * (countIci hH (EL - ℓ₁) : ℝ) := by
  have hℓ : 0 < ℓ₁ := lt_of_lt_of_le hη hηℓ
  have hEE : E ≤ EL := by linarith
  have hc : ∀ a b : ℝ, (countIcc hH a b : ℝ) =
      ∑ α, if a ≤ hH.eigenvalues α ∧ hH.eigenvalues α ≤ b then (1 : ℝ) else 0 := by
    intro a b
    simp [countIcc]
  have hc' : (countIci hH (EL - ℓ₁) : ℝ) =
      ∑ α, if EL - ℓ₁ ≤ hH.eigenvalues α then (1 : ℝ) else 0 := by
    simp [countIci]
  have hsc : (countIcc hH E EL : ℝ) - smoothCount hH η E EL = ∑ α,
      ((if E ≤ hH.eigenvalues α ∧ hH.eigenvalues α ≤ EL then (1 : ℝ) else 0) -
        ∫ y in E..EL, thetaEta η (hH.eigenvalues α - y)) := by
    rw [hc, smoothCount, Finset.sum_sub_distrib]
  rw [hsc]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun α _ =>
    (abs_indicator_sub_integral_thetaEta_le hη hEE (hH.eigenvalues α)).trans
      (poisson_bridge_pointwise hη hηℓ hℓE (hH.eigenvalues α))).trans (le_of_eq ?_)
  rw [hc E EL, hc (E - ℓ₁) (E + ℓ₁), hc', Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

/-- (6.16) in window form: for `x ≤ E - ℓ₁` the function `f` of (6.12) is at most
`5π η (E_L - E) ∫_{-ℓ₁}^{ℓ₁} g_{ℓ₁}(y) θ_{ℓ₁}(E - x - y) dy`. -/
private lemma f_le_window {η ℓ₁ E EL x : ℝ} (hη : 0 < η) (hℓ : 0 < ℓ₁) (hEE : E ≤ EL) (hx : x ≤ E - ℓ₁) :
    η * (EL - E) / ((|x - EL| + η) * (|x - E| + η)) ≤
      5 * Real.pi * (η * (EL - E)) *
        ∫ y in (-ℓ₁)..ℓ₁, 1 / (y ^ 2 + ℓ₁ ^ 2) * thetaEta ℓ₁ ((E - x) - y) := by
  have ha : ℓ₁ ≤ |E - x| := by rw [abs_of_nonneg (by linarith)]; linarith
  have hw := inv_sq_le_window_conv hℓ ha
  have h1 : (E - x) ≤ |x - E| + η := by rw [abs_sub_comm]; linarith [le_abs_self (E - x)]
  have h2 : (E - x) ≤ |x - EL| + η := by
    have := neg_abs_le (x - EL)
    linarith
  have hpos : 0 < E - x := by linarith
  have hd : (E - x) ^ 2 ≤ (|x - EL| + η) * (|x - E| + η) := by
    rw [sq]; exact mul_le_mul h2 h1 hpos.le (by linarith [abs_nonneg (x - EL)])
  have hne : 0 ≤ η * (EL - E) := mul_nonneg hη.le (by linarith)
  calc η * (EL - E) / ((|x - EL| + η) * (|x - E| + η))
      ≤ η * (EL - E) / (E - x) ^ 2 := by
        apply div_le_div_of_nonneg_left hne (by positivity) hd
    _ = (η * (EL - E)) * (1 / (E - x) ^ 2) := by ring
    _ ≤ (η * (EL - E)) * (5 * Real.pi * ∫ y in (-ℓ₁)..ℓ₁, 1 / (y ^ 2 + ℓ₁ ^ 2) *
          thetaEta ℓ₁ ((E - x) - y)) := by
        exact mul_le_mul_of_nonneg_left hw hne
    _ = _ := by ring

/-- The sum over the spectrum of the window convolution is the window integral of `Im m`:
`Σ_α ∫_{-ℓ}^{ℓ} g_ℓ(y) θ_ℓ(E - λ_α - y) dy = (N/π) ∫_{-ℓ}^{ℓ} g_ℓ(y) Im m(E - y + iℓ) dy`
([26] (6.16)-(6.17)). -/
private lemma sum_window_eq {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (E : ℝ) :
    ∑ α, ∫ y in (-ℓ)..ℓ, 1 / (y ^ 2 + ℓ ^ 2) * thetaEta ℓ ((E - hH.eigenvalues α) - y) =
      N / Real.pi * ∫ y in (-ℓ)..ℓ, 1 / (y ^ 2 + ℓ ^ 2) * (stieltjesM H ⟨E - y, ℓ⟩).im := by
  have hden : ∀ y : ℝ, y ^ 2 + ℓ ^ 2 ≠ 0 := fun y => by positivity
  have hcont : ∀ α, Continuous fun y : ℝ =>
      1 / (y ^ 2 + ℓ ^ 2) * thetaEta ℓ ((E - hH.eigenvalues α) - y) := by
    intro α
    unfold thetaEta
    refine Continuous.mul (Continuous.div continuous_const (by fun_prop) hden)
      (Continuous.div continuous_const (by fun_prop) (fun y => by positivity))
  rw [← intervalIntegral.integral_finsetSum (fun α _ => (hcont α).intervalIntegrable _ _),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun y _ => ?_
  show _ = _
  rw [im_stieltjesM_eq hH (z := ⟨E - y, ℓ⟩) hℓ]
  have hth : ∀ α, thetaEta ℓ ((E - hH.eigenvalues α) - y) =
      Real.pi⁻¹ * (ℓ / ((hH.eigenvalues α - (E - y)) ^ 2 + ℓ ^ 2)) := by
    intro α
    have : ((E - hH.eigenvalues α) - y) ^ 2 = (hH.eigenvalues α - (E - y)) ^ 2 := by ring
    unfold thetaEta
    rw [this]
    have : (hH.eigenvalues α - (E - y)) ^ 2 + ℓ ^ 2 ≠ 0 := by positivity
    field_simp
  simp only [hth, ← Finset.mul_sum]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have : (N : ℝ) ≠ 0 := by positivity
    field_simp

/-- (6.17) in window form: if `Im m(E - y + iℓ₁) ≤ B` for `|y| ≤ ℓ₁`, then
`Σ_α f(λ_α) ≤ 5 N η (E_L - E) B π/(2ℓ₁)`. -/
private lemma sum_f_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {ℓ₁ η E EL B : ℝ} (hη : 0 < η) (hℓ : 0 < ℓ₁) (hEE : E ≤ EL)
    (hm : ∀ y, |y| ≤ ℓ₁ → (stieltjesM H ⟨E - y, ℓ₁⟩).im ≤ B) :
    ∑ α, (η * (EL - E) / ((|hH.eigenvalues α - EL| + η) * (|hH.eigenvalues α - E| + η)) *
        (if hH.eigenvalues α ≤ E - ℓ₁ then (1 : ℝ) else 0)) ≤
      5 * N * η * (EL - E) * (B * (Real.pi / (2 * ℓ₁))) := by
  have hden : ∀ y : ℝ, y ^ 2 + ℓ₁ ^ 2 ≠ 0 := fun y => by positivity
  have hne : 0 ≤ η * (EL - E) := mul_nonneg hη.le (by linarith)
  have hWnn : ∀ a : ℝ, 0 ≤ ∫ y in (-ℓ₁)..ℓ₁, 1 / (y ^ 2 + ℓ₁ ^ 2) * thetaEta ℓ₁ (a - y) := by
    intro a
    refine intervalIntegral.integral_nonneg (by linarith) fun y _ => ?_
    unfold thetaEta
    positivity
  have h1 : ∀ α, η * (EL - E) / ((|hH.eigenvalues α - EL| + η) * (|hH.eigenvalues α - E| + η)) *
        (if hH.eigenvalues α ≤ E - ℓ₁ then (1 : ℝ) else 0) ≤
      5 * Real.pi * (η * (EL - E)) *
        ∫ y in (-ℓ₁)..ℓ₁, 1 / (y ^ 2 + ℓ₁ ^ 2) * thetaEta ℓ₁ ((E - hH.eigenvalues α) - y) := by
    intro α
    split_ifs with h
    · rw [mul_one]; exact f_le_window hη hℓ hEE h
    · rw [mul_zero]
      exact mul_nonneg (mul_nonneg (by positivity) hne) (hWnn _)
  have hcm : Continuous fun y : ℝ => (stieltjesM H ⟨E - y, ℓ₁⟩).im := by
    have : (fun y : ℝ => (stieltjesM H ⟨E - y, ℓ₁⟩).im) = fun y =>
        (N : ℝ)⁻¹ * ∑ α, ℓ₁ / ((hH.eigenvalues α - (E - y)) ^ 2 + ℓ₁ ^ 2) := by
      funext y; exact im_stieltjesM_eq hH (z := ⟨E - y, ℓ₁⟩) hℓ
    rw [this]
    refine continuous_const.mul (continuous_finsetSum _ fun α _ => ?_)
    exact Continuous.div continuous_const (by fun_prop) (fun y => by positivity)
  have hg : Continuous fun y : ℝ => 1 / (y ^ 2 + ℓ₁ ^ 2) := by
    exact Continuous.div continuous_const (by fun_prop) hden
  have hint : ∫ y in (-ℓ₁)..ℓ₁, 1 / (y ^ 2 + ℓ₁ ^ 2) * (stieltjesM H ⟨E - y, ℓ₁⟩).im ≤
      B * (Real.pi / (2 * ℓ₁)) := by
    calc ∫ y in (-ℓ₁)..ℓ₁, 1 / (y ^ 2 + ℓ₁ ^ 2) * (stieltjesM H ⟨E - y, ℓ₁⟩).im
        ≤ ∫ y in (-ℓ₁)..ℓ₁, B * (1 / (y ^ 2 + ℓ₁ ^ 2)) := by
          refine intervalIntegral.integral_mono_on (by linarith) ((hg.mul hcm).intervalIntegrable _ _)
            ((continuous_const.mul hg).intervalIntegrable _ _) fun y hy => ?_
          have := hm y (abs_le.2 ⟨hy.1, hy.2⟩)
          have hpos : 0 < 1 / (y ^ 2 + ℓ₁ ^ 2) := by positivity
          nlinarith
      _ = B * (Real.pi / (2 * ℓ₁)) := by
          rw [intervalIntegral.integral_const_mul, integral_window_inv_sq_add_sq hℓ]
  calc _ ≤ ∑ α, 5 * Real.pi * (η * (EL - E)) *
        ∫ y in (-ℓ₁)..ℓ₁, 1 / (y ^ 2 + ℓ₁ ^ 2) * thetaEta ℓ₁ ((E - hH.eigenvalues α) - y) :=
        Finset.sum_le_sum fun α _ => h1 α
    _ = 5 * Real.pi * (η * (EL - E)) * (N / Real.pi *
        ∫ y in (-ℓ₁)..ℓ₁, 1 / (y ^ 2 + ℓ₁ ^ 2) * (stieltjesM H ⟨E - y, ℓ₁⟩).im) := by
        rw [← Finset.mul_sum, sum_window_eq hH hℓ]
    _ ≤ 5 * Real.pi * (η * (EL - E)) * (N / Real.pi * (B * (Real.pi / (2 * ℓ₁)))) := by
        gcongr
    _ = _ := by field_simp

/-- The bound `B = Cm (√(2ℓ₁) + √|E - 2|) + φ^C/(Nℓ₁)` on `Im m(E - y + iℓ₁)`, `|y| ≤ ℓ₁`, from
(5.24) at `η = ℓ₁` and the window bound on `Im m_sc` (the hypothesis `hmsc`). -/
private lemma hm_of_524 {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {C ℓ₁ E Cm : ℝ}
    (hmsc : ∀ E y ℓ : ℝ, |y| ≤ ℓ → |E - y| ≤ 5 → 0 < ℓ → ℓ ≤ 10 →
      (msc ⟨E - y, ℓ⟩).im ≤ Cm * (Real.sqrt (2 * ℓ) + Real.sqrt |E - 2|))
    (h524 : ∀ z ∈ specDomain N C, z.im ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) →
      ‖stieltjesM H z - msc z‖ ≤ phi N ^ C / (N * z.im))
    (hℓ₁ : phi N ^ C / N < ℓ₁) (hℓ₁' : ℓ₁ ≤ (N : ℝ) ^ (-(2 : ℝ) / 3)) (hℓ₁1 : ℓ₁ ≤ 1)
    (hE : |E - 2| ≤ 2) :
    ∀ y, |y| ≤ ℓ₁ → (stieltjesM H ⟨E - y, ℓ₁⟩).im ≤
      Cm * (Real.sqrt (2 * ℓ₁) + Real.sqrt |E - 2|) + phi N ^ C / (N * ℓ₁) := by
  intro y hy
  have hℓpos : 0 < ℓ₁ := lt_of_le_of_lt (by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · have : (0 : ℝ) < N := by exact_mod_cast h
      have : 0 ≤ phi N ^ C := by
        unfold phi
        exact Real.rpow_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg N) _) _
      positivity) hℓ₁
  have hy1 := abs_le.1 hy
  have hE1 := abs_le.1 hE
  have hre : |E - y| ≤ 5 := abs_le.2 ⟨by linarith, by linarith⟩
  have hz : (⟨E - y, ℓ₁⟩ : ℂ) ∈ specDomain N C := ⟨hre, hℓ₁, by linarith⟩
  have h1 := h524 _ hz hℓ₁'
  have h2 := hmsc E y ℓ₁ hy hre hℓpos (by linarith)
  have h3 : (stieltjesM H ⟨E - y, ℓ₁⟩).im - (msc ⟨E - y, ℓ₁⟩).im ≤
      ‖stieltjesM H ⟨E - y, ℓ₁⟩ - msc ⟨E - y, ℓ₁⟩‖ := by
    have := Complex.abs_im_le_norm (stieltjesM H ⟨E - y, ℓ₁⟩ - msc ⟨E - y, ℓ₁⟩)
    simp only [Complex.sub_im] at this
    exact (le_abs_self _).trans this
  linarith

private lemma phi_rpow_nonneg (N : ℕ) (a : ℝ) : 0 ≤ phi N ^ a := by
  unfold phi
  exact Real.rpow_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg N) _) _

/-- `K φ^a N^{-b} ≤ N^{-c}` eventually, for `c < b`. -/
private lemma eventually_phi_mul_rpow_le (K a : ℝ) {b c : ℝ} (hbc : c < b) :
    ∀ᶠ N : ℕ in atTop, K * phi N ^ a * (N : ℝ) ^ (-b) ≤ (N : ℝ) ^ (-c) := by
  have hd : 0 < (b - c) / 2 := by linarith
  have h1 := phi_rpow_le_rpow a hd
  have h2 : ∀ᶠ N : ℕ in atTop, K ≤ (N : ℝ) ^ ((b - c) / 2) :=
    (tendsto_rpow_atTop hd |>.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K
  filter_upwards [h1, h2, eventually_ge_atTop 1] with N hN1 hN2 hN3
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN3
  have hN0 : (0 : ℝ) < N := by linarith
  calc K * phi N ^ a * (N : ℝ) ^ (-b)
      ≤ (N : ℝ) ^ ((b - c) / 2) * (N : ℝ) ^ ((b - c) / 2) * (N : ℝ) ^ (-b) := by
        gcongr
        exact phi_rpow_nonneg N a
    _ = (N : ℝ) ^ (-c) := by
        rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; congr 1; ring

/-- The bound `Σ_α f(λ_α) ≤ N^{-2ε}` of [26] (6.17)-(6.18) in exponent form, with
`η = N^{-2/3-9ε}`, `ℓ₁ = N^{-2/3-3ε}`, `E_L - E ≤ (7/2) φ^C N^{-2/3}` and `|E - 2| ≤ (3/2) φ^C N^{-2/3}`:
`5 N η (E_L - E) [Cm (√(2ℓ₁) + √|E - 2|) + φ^C/(Nℓ₁)] π/(2ℓ₁) ≤ N^{-2ε}` for `N` large. The three
terms are `φ^C N^{-15ε/2}`, `φ^{3C/2} N^{-6ε}` and `φ^{2C} N^{-3ε}`. -/
theorem trace_f_rate (Cm C ε : ℝ) (hCm : 0 ≤ Cm) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ E d : ℝ, d ≤ 7 / 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) →
      |E - 2| ≤ 3 / 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) → 0 ≤ d →
      5 * (N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε) * d *
        ((Cm * (Real.sqrt (2 * (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε)) + Real.sqrt |E - 2|) +
            phi N ^ C / ((N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε))) *
          (Real.pi / (2 * (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε)))) ≤ (N : ℝ) ^ (-2 * ε) := by
  have c1 : (2 : ℝ) * ε < 15 * ε / 2 := by linarith
  have c2 : (2 : ℝ) * ε < 6 * ε := by linarith
  have c3 : (2 : ℝ) * ε < 3 * ε := by linarith
  have k1 := eventually_phi_mul_rpow_le (3 * (35 * Real.pi / 4 * Cm * Real.sqrt 2)) C c1
  have k2 := eventually_phi_mul_rpow_le (3 * (35 * Real.pi / 4 * Cm * Real.sqrt (3 / 2))) (3 * C / 2) c2
  have k3 := eventually_phi_mul_rpow_le (3 * (35 * Real.pi / 4)) (2 * C) c3
  filter_upwards [k1, k2, k3, eventually_ge_atTop 3] with N h1 h2 h3 hN E d hd hE hd0
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hX : (0 : ℝ) < N := by linarith
  have hφ : 0 < phi N := by rw [phi_eq_exp hN]; exact Real.exp_pos _
  have hℓ : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε) := Real.rpow_pos_of_pos hX _
  have hφC : 0 < phi N ^ C := Real.rpow_pos_of_pos hφ _
  have hX23 : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hX _
  have hQ0 : 0 ≤ 3 / 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) := by positivity
  -- Step 1: reduce to the extreme values
  have hsq : Real.sqrt |E - 2| ≤ Real.sqrt (3 / 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)) :=
    Real.sqrt_le_sqrt hE
  have step1 : 5 * (N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε) * d *
        ((Cm * (Real.sqrt (2 * (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε)) + Real.sqrt |E - 2|) +
            phi N ^ C / ((N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε))) *
          (Real.pi / (2 * (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε)))) ≤
      5 * (N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε) *
        (7 / 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)) *
        ((Cm * (Real.sqrt (2 * (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε)) +
              Real.sqrt (3 / 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3))) +
            phi N ^ C / ((N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε))) *
          (Real.pi / (2 * (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε)))) := by
    gcongr
  refine step1.trans ?_
  -- Step 2: the exact monomial form
  have e1 : 5 * (N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε) *
        (7 / 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)) *
          (Real.pi / (2 * (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε))) =
      35 * Real.pi / 4 * phi N ^ C * (N : ℝ) ^ ((1 : ℝ) / 3 - 6 * ε) := by
    have hexp : (N : ℝ) ^ ((1 : ℝ) / 3 - 6 * ε) = (N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε) *
        (N : ℝ) ^ (-(2 : ℝ) / 3) / (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε) := by
      have : ((1 : ℝ) / 3 - 6 * ε) =
          (1 + (-(2 : ℝ) / 3 - 9 * ε) + (-(2 : ℝ) / 3)) - (-(2 : ℝ) / 3 - 3 * ε) := by ring
      rw [this, Real.rpow_sub hX, Real.rpow_add hX, Real.rpow_add hX, Real.rpow_one]
    rw [hexp]
    field_simp
    norm_num
  have e2 : Real.sqrt (2 * (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε)) =
      Real.sqrt 2 * (N : ℝ) ^ ((-(2 : ℝ) / 3 - 3 * ε) / 2) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow ((N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε)),
      ← Real.rpow_mul hX.le]
    congr 2; ring
  have e3 : Real.sqrt (3 / 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)) =
      Real.sqrt (3 / 2) * phi N ^ (C / 2) * (N : ℝ) ^ (-(1 : ℝ) / 3) := by
    have hφs : Real.sqrt (phi N ^ C) = phi N ^ (C / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hφ.le]; congr 1; ring
    have hXs : Real.sqrt ((N : ℝ) ^ (-(2 : ℝ) / 3)) = (N : ℝ) ^ (-(1 : ℝ) / 3) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX.le]; congr 1; ring
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), hφs, hXs]
  have e4 : phi N ^ C / ((N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε)) =
      phi N ^ C * (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) := by
    have : (N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε) = (N : ℝ) ^ ((1 : ℝ) / 3 - 3 * ε) := by
      have h : ((1 : ℝ) / 3 - 3 * ε) = 1 + (-(2 : ℝ) / 3 - 3 * ε) := by ring
      rw [h, Real.rpow_add hX, Real.rpow_one]
    rw [this, div_eq_mul_inv, ← Real.rpow_neg hX.le]
    congr 3; ring
  -- Step 3: expand and bound the three terms
  have p1 : (N : ℝ) ^ ((1 : ℝ) / 3 - 6 * ε) * (N : ℝ) ^ ((-(2 : ℝ) / 3 - 3 * ε) / 2) =
      (N : ℝ) ^ (-(15 * ε / 2)) := by
    rw [← Real.rpow_add hX]; congr 1; ring
  have p2 : (N : ℝ) ^ ((1 : ℝ) / 3 - 6 * ε) * (N : ℝ) ^ (-(1 : ℝ) / 3) = (N : ℝ) ^ (-(6 * ε)) := by
    rw [← Real.rpow_add hX]; congr 1; ring
  have p3 : (N : ℝ) ^ ((1 : ℝ) / 3 - 6 * ε) * (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) =
      (N : ℝ) ^ (-(3 * ε)) := by
    rw [← Real.rpow_add hX]; congr 1; ring
  have q2 : phi N ^ C * phi N ^ (C / 2) = phi N ^ (3 * C / 2) := by
    rw [← Real.rpow_add hφ]; congr 1; ring
  have q3 : phi N ^ C * phi N ^ C = phi N ^ (2 * C) := by
    rw [← Real.rpow_add hφ]; congr 1; ring
  have expand : 5 * (N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε) *
        (7 / 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)) *
        ((Cm * (Real.sqrt (2 * (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε)) +
              Real.sqrt (3 / 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3))) +
            phi N ^ C / ((N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε))) *
          (Real.pi / (2 * (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε)))) =
      35 * Real.pi / 4 * Cm * Real.sqrt 2 * phi N ^ C * (N : ℝ) ^ (-(15 * ε / 2)) +
      35 * Real.pi / 4 * Cm * Real.sqrt (3 / 2) * phi N ^ (3 * C / 2) * (N : ℝ) ^ (-(6 * ε)) +
      35 * Real.pi / 4 * phi N ^ (2 * C) * (N : ℝ) ^ (-(3 * ε)) := by
    rw [e2, e3, e4]
    have step : 5 * (N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε) *
          (7 / 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)) *
          ((Cm * (Real.sqrt 2 * (N : ℝ) ^ ((-(2 : ℝ) / 3 - 3 * ε) / 2) +
                Real.sqrt (3 / 2) * phi N ^ (C / 2) * (N : ℝ) ^ (-(1 : ℝ) / 3)) +
              phi N ^ C * (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) *
            (Real.pi / (2 * (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε)))) =
        (5 * (N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε) *
          (7 / 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)) *
            (Real.pi / (2 * (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε)))) *
          (Cm * (Real.sqrt 2 * (N : ℝ) ^ ((-(2 : ℝ) / 3 - 3 * ε) / 2) +
                Real.sqrt (3 / 2) * phi N ^ (C / 2) * (N : ℝ) ^ (-(1 : ℝ) / 3)) +
              phi N ^ C * (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) := by ring
    rw [step, e1]
    have step2 : 35 * Real.pi / 4 * phi N ^ C * (N : ℝ) ^ ((1 : ℝ) / 3 - 6 * ε) *
          (Cm * (Real.sqrt 2 * (N : ℝ) ^ ((-(2 : ℝ) / 3 - 3 * ε) / 2) +
                Real.sqrt (3 / 2) * phi N ^ (C / 2) * (N : ℝ) ^ (-(1 : ℝ) / 3)) +
              phi N ^ C * (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) =
        35 * Real.pi / 4 * Cm * Real.sqrt 2 * phi N ^ C *
            ((N : ℝ) ^ ((1 : ℝ) / 3 - 6 * ε) * (N : ℝ) ^ ((-(2 : ℝ) / 3 - 3 * ε) / 2)) +
          35 * Real.pi / 4 * Cm * Real.sqrt (3 / 2) * (phi N ^ C * phi N ^ (C / 2)) *
            ((N : ℝ) ^ ((1 : ℝ) / 3 - 6 * ε) * (N : ℝ) ^ (-(1 : ℝ) / 3)) +
          35 * Real.pi / 4 * (phi N ^ C * phi N ^ C) *
            ((N : ℝ) ^ ((1 : ℝ) / 3 - 6 * ε) * (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) := by ring
    rw [step2, p1, p2, p3, q2, q3]
  rw [expand]
  have hm : -2 * ε = -(2 * ε) := by ring
  rw [hm]
  linarith

/-- The term `12 (η/ℓ₁) N(E,E_L)` of (6.11), with `N(E,E_L) ≤ φ^{2C}`, is at most `N^{-2ε}`. -/
theorem bridge_term_rate (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, 12 * ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε) / (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε)) *
      phi N ^ (2 * C) ≤ (N : ℝ) ^ (-2 * ε) := by
  have h := eventually_phi_mul_rpow_le 12 (2 * C) (b := 6 * ε) (c := 2 * ε) (by linarith)
  filter_upwards [h, eventually_ge_atTop 1] with N hN hN1
  have hX : (0 : ℝ) < N := by exact_mod_cast hN1
  have e : (N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε) / (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε) =
      (N : ℝ) ^ (-(6 * ε)) := by
    rw [← Real.rpow_sub hX]; congr 1; ring
  rw [e]
  have hm : -2 * ε = -(2 * ε) := by ring
  rw [hm]
  linarith

/-- The region `|E - y| > 5` of (6.17) contributes at most `5 N η (E_L - E) π/4 ≤ N^{-2ε}`. -/
theorem far_region_rate (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℝ, d ≤ 7 / 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) → 0 ≤ d →
      5 * (N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε) * d * (Real.pi / 4) ≤ (N : ℝ) ^ (-2 * ε) := by
  have h := eventually_phi_mul_rpow_le (35 * Real.pi / 8) C (b := 1 / 3 + 9 * ε) (c := 2 * ε)
    (by linarith)
  filter_upwards [h, eventually_ge_atTop 1] with N hN hN1 d hd hd0
  have hX : (0 : ℝ) < N := by exact_mod_cast hN1
  have e : 5 * (N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε) *
      (7 / 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)) * (Real.pi / 4) =
      35 * Real.pi / 8 * phi N ^ C * (N : ℝ) ^ (-(1 / 3 + 9 * ε)) := by
    have : (N : ℝ) ^ (-(1 / 3 + 9 * ε)) = (N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε) *
        (N : ℝ) ^ (-(2 : ℝ) / 3) := by
      rw [show (-(1 / 3 + 9 * ε) : ℝ) = 1 + (-(2 : ℝ) / 3 - 9 * ε) + (-(2 : ℝ) / 3) by ring,
        Real.rpow_add hX, Real.rpow_add hX, Real.rpow_one]
    rw [this]; ring
  have hm : -2 * ε = -(2 * ε) := by ring
  rw [hm]
  calc 5 * (N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε) * d * (Real.pi / 4)
      ≤ 5 * (N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε) *
        (7 / 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)) * (Real.pi / 4) := by gcongr
    _ = _ := e
    _ ≤ _ := hN

/-- The scales `ℓ₁ = N^{-2/3-3ε}`, `η = N^{-2/3-9ε}` against the window of
Lemma 6.1, for `0 < ε < 1/10`, `C ≥ 0` and `N` large. -/
theorem window_scales {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hε1 : ε < 1 / 10) :
    ∀ᶠ N : ℕ in atTop,
      (phi N ^ C / N < (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε) ∧
        (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε) ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) ∧
        (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ 1 ∧
        (N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε) ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε)) ∧
      (∀ E : ℝ, |E - 2| ≤ 3 / 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) →
        2 * (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε) ≤ edgeEL N C - E ∧
        edgeEL N C - E ≤ 7 / 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) ∧ |E - 2| ≤ 1 / 2 ∧
        2 + phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) < edgeEL N C - (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε)) := by
  have hc : 0 < (1 / 3 - 3 * ε) / 2 := by linarith
  have hA := phi_rpow_le_rpow C hc
  have hB : ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ (N : ℝ) ^ (3 * ε) :=
    (tendsto_rpow_atTop (by linarith : 0 < 3 * ε) |>.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4
  have hD := phi_rpow_le_rpow C (c := 1 / 6) (by norm_num)
  have hF : ∀ᶠ N : ℕ in atTop, (3 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) |>.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 3
  filter_upwards [hA, hB, hD, hF, eventually_ge_atTop 3] with N hA hB hD hF hN
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hX : (0 : ℝ) < N := by linarith
  have hX1 : (1 : ℝ) < N := by linarith
  have hφ1 : 1 ≤ phi N := by rw [phi_eq_exp hN]; exact Real.one_le_exp (sq_nonneg _)
  have hφC : 1 ≤ phi N ^ C := Real.one_le_rpow hφ1 hC
  have hX23 : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hX _
  have hsplit : (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε) = (N : ℝ) ^ (-(3 * ε)) * (N : ℝ) ^ (-(2 : ℝ) / 3) := by
    rw [← Real.rpow_add hX]; congr 1; ring
  have hneg : (N : ℝ) ^ (-(3 * ε)) ≤ 1 / 4 := by
    rw [Real.rpow_neg hX.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hB
  have hneg0 : 0 ≤ (N : ℝ) ^ (-(3 * ε)) := Real.rpow_nonneg hX.le _
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun E hE => ?_⟩
  · -- φ^C / N < ℓ₁
    have h1 : phi N ^ C / N ≤ (N : ℝ) ^ ((1 / 3 - 3 * ε) / 2 - 1) := by
      rw [Real.rpow_sub hX, Real.rpow_one]
      exact div_le_div_of_nonneg_right hA hX.le
    refine h1.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hX1 ?_)
    linarith
  · exact Real.rpow_le_rpow_of_exponent_le hX1.le (by linarith)
  · exact Real.rpow_le_one_of_one_le_of_nonpos hX1.le (by norm_num)
  · exact Real.rpow_le_rpow_of_exponent_le hX1.le (by linarith)
  · have hEh := abs_le.1 hE
    have hEL : edgeEL N C - E ≥ 1 / 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) := by
      unfold edgeEL; linarith
    have hprod : 1 * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_right hφC hX23.le
    have hsmall : 3 / 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ 1 / 2 := by
      have h1 : phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ (N : ℝ) ^ ((1 : ℝ) / 6) * (N : ℝ) ^ (-(2 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_right hD hX23.le
      have h2 : (N : ℝ) ^ ((1 : ℝ) / 6) * (N : ℝ) ^ (-(2 : ℝ) / 3) = ((N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by
        rw [← Real.rpow_add hX, ← Real.rpow_neg hX.le]; congr 1; ring
      have h3 : ((N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ ≤ 1 / 3 := by
        rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hF
      linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hsplit]; nlinarith
    · unfold edgeEL; linarith
    · linarith
    · unfold edgeEL; rw [hsplit]; nlinarith

/-- [26] Lemma 6.1 on the event of Lemma 5.6 with the upper edge (5.25) included (the number
`N(E_L - ℓ₁, ∞)` of (6.11) vanishes by (5.25)): for `|E - 2| ≤ (3/2) φ^C N^{-2/3}`,
`|N(E, E_L) - Tr(χ_E * θ_η)(H)| ≤ 10 (N^{-2ε} + N(E - ℓ₁, E + ℓ₁))`,
`ℓ₁ = N^{-2/3-3ε}`, `η = N^{-2/3-9ε}`. -/
theorem abs_countIcc_sub_smoothCount_le' {C : ℝ} (hC : 0 < C) :
    ∃ C' > 0, ∀ ε : ℝ, 0 < ε → ε < 1 / 10 → ∃ N0 : ℕ, ∀ N ≥ N0, ∀ ω : Entries N,
      (∀ α, |(symOfEntries_isHermitian ω).eigenvalues α| ≤ 3) →
      (∀ z ∈ specDomain N C, z.im ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) →
        ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ phi N ^ C / (N * z.im)) →
      |(N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2)| ≤ phi N ^ C →
      ((Finset.univ.filter fun α => |(symOfEntries_isHermitian ω).eigenvalues α - 2| ≤
          2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)).card : ℝ) ≤ phi N ^ (2 * C) →
      ∀ E : ℝ, |E - 2| ≤ 3 / 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) →
        |(countIcc (symOfEntries_isHermitian ω) E (edgeEL N C) : ℝ) -
            smoothCount (symOfEntries_isHermitian ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε)) E
              (edgeEL N C)| ≤
          C' * ((N : ℝ) ^ (-2 * ε) + countIcc (symOfEntries_isHermitian ω)
            (E - (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε)) (E + (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε))) := by
  obtain ⟨Cm, hCm, hmsc⟩ := imMsc_le_window
  refine ⟨10, by norm_num, fun ε hε hε1 => ?_⟩
  have hsc := window_scales hC.le hε hε1
  have htr := trace_f_rate Cm C ε (by linarith) hε
  have hbr := bridge_term_rate C ε hε
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 (hsc.and (htr.and (hbr.and
    (Filter.eventually_ge_atTop 3))))
  refine ⟨N0, fun N hN ω hnorm h524 h525 h526 E hE => ?_⟩
  obtain ⟨⟨hQ1, hQ2, hQ3, hQ4⟩, hEq⟩ := (hN0 N hN).1
  obtain ⟨htrN, hbrN, hN3⟩ := (hN0 N hN).2
  obtain ⟨hQ5, hQ6, hQ7, hQ8⟩ := hEq E hE
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hX : (0 : ℝ) < N := by linarith
  have : NeZero N := ⟨by omega⟩
  set hH := symOfEntries_isHermitian ω with hHdef
  set η : ℝ := (N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε) with hη
  set ℓ₁ : ℝ := (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε) with hℓ₁
  have hηpos : 0 < η := Real.rpow_pos_of_pos hX _
  have hℓpos : 0 < ℓ₁ := Real.rpow_pos_of_pos hX _
  have hEE : E ≤ edgeEL N C := by
    have : 0 ≤ ℓ₁ := hℓpos.le
    linarith
  -- the chain (6.10) → (6.11)
  have hchain := count_chain hH hηpos hQ4 hQ5
  -- the term N(E_L - ℓ₁, ∞) vanishes by (5.25)
  have hlam : lambdaMax (symOfEntries ω) ≤ 2 + phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) := by
    have h1 := (abs_le.1 h525).2
    have h2 : (0 : ℝ) < (N : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hX _
    have h3 : (N : ℝ) ^ ((2 : ℝ) / 3) * (N : ℝ) ^ (-(2 : ℝ) / 3) = 1 := by
      rw [← Real.rpow_add hX]; norm_num
    have h4 : lambdaMax (symOfEntries ω) - 2 ≤ phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) := by
      have := mul_le_mul_of_nonneg_right h1 h2.le
      nlinarith [this, h3]
    linarith
  have hIci : countIci hH (edgeEL N C - ℓ₁) = 0 := by
    unfold countIci
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro α _ hα
    have := (lambdaMax_isGreatest hH).2 ⟨α, rfl⟩
    linarith
  -- Σ f
  have hB : ∀ y, |y| ≤ ℓ₁ → (stieltjesM (symOfEntries ω) ⟨E - y, ℓ₁⟩).im ≤
      Cm * (Real.sqrt (2 * ℓ₁) + Real.sqrt |E - 2|) + phi N ^ C / (N * ℓ₁) := by
    refine hm_of_524 hmsc h524 hQ1 hQ2 (by linarith) (by linarith)
  have hsumf := sum_f_le hH hηpos hℓpos hEE hB
  have hd0 : 0 ≤ edgeEL N C - E := by linarith
  have htr' := htrN E (edgeEL N C - E) hQ6 hE hd0
  -- N(E, E_L) ≤ φ^{2C}
  have hcount : (countIcc hH E (edgeEL N C) : ℝ) ≤ phi N ^ (2 * C) := by
    refine le_trans ?_ h526
    have hsub : (Finset.univ.filter fun α => E ≤ hH.eigenvalues α ∧ hH.eigenvalues α ≤ edgeEL N C) ⊆
        Finset.univ.filter fun α => |hH.eigenvalues α - 2| ≤
          2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) := by
      intro α hα
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα ⊢
      have h1 := (abs_le.1 hE).1
      have h2 : edgeEL N C = 2 + 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) := rfl
      rw [abs_le]
      constructor <;> linarith [hα.1, hα.2, h1, h2]
    exact_mod_cast Finset.card_le_card hsub
  have h12 : 12 * (η / ℓ₁) * (countIcc hH E (edgeEL N C) : ℝ) ≤ (N : ℝ) ^ (-2 * ε) := by
    refine le_trans ?_ hbrN
    have : 0 ≤ 12 * (η / ℓ₁) := by positivity
    exact mul_le_mul_of_nonneg_left hcount this
  have hNN : (0 : ℝ) ≤ (N : ℝ) ^ (-2 * ε) := Real.rpow_nonneg hX.le _
  have hcnn : (0 : ℝ) ≤ (countIcc hH (E - ℓ₁) (E + ℓ₁) : ℝ) := Nat.cast_nonneg _
  rw [hIci] at hchain
  simp only [Nat.cast_zero, mul_zero, add_zero] at hchain
  linarith

/-! ## Checks -/

/-- `count_chain` at `N = 2`, `H = 0`, `η = 1/10`, `ℓ₁ = 1/4`, `E = 1`, `E_L = 2`: both eigenvalues
are `0 ≤ E - ℓ₁`, so the `f`-term is nonzero. -/
private example :
    |(countIcc (Matrix.isHermitian_zero : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian) 1 2 : ℝ) -
        smoothCount (Matrix.isHermitian_zero : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian)
          (1 / 10) 1 2| ≤
      4 * ∑ α, ((1 / 10 : ℝ) * (2 - 1) /
          ((|(Matrix.isHermitian_zero : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian).eigenvalues α
              - 2| + 1 / 10) *
            (|(Matrix.isHermitian_zero : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian).eigenvalues α
              - 1| + 1 / 10)) *
          (if (Matrix.isHermitian_zero : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian).eigenvalues α
              ≤ 1 - 1 / 4 then (1 : ℝ) else 0)) +
        12 * ((1 / 10 : ℝ) / (1 / 4)) *
          (countIcc (Matrix.isHermitian_zero : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian) 1 2 : ℝ) +
        10 * (countIcc (Matrix.isHermitian_zero : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian)
          (1 - 1 / 4) (1 + 1 / 4) : ℝ) +
        10 * (countIci (Matrix.isHermitian_zero : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian)
          (2 - 1 / 4) : ℝ) :=
  count_chain Matrix.isHermitian_zero (by norm_num) (by norm_num) (by norm_num)

/-- The entries of `diag(2, -1, -3)` at `N = 3` (diagonal `(2, -1, -3)`, off-diagonal zero). -/
private def countApproxDiag3 : Entries 3 := (![2, -1, -3], fun _ => 0)

/-- `countApproxDiag3` gives the diagonal matrix `diag(2, -1, -3)`. -/
private lemma symOfEntries_countApproxDiag3 :
    symOfEntries countApproxDiag3 = diagonal ![2, -1, -3] := by
  ext i j
  by_cases h : i = j
  · subst h; simp [symOfEntries, countApproxDiag3]
  · by_cases h' : i < j
    · simp [symOfEntries, countApproxDiag3, h, h']
    · simp [symOfEntries, countApproxDiag3, h, h']

/-- Every eigenvalue of `diag(2, -1, -3)` is `2`, `-1` or `-3`. -/
private lemma countApproxDiag3_eig (α : Fin 3) :
    (symOfEntries_isHermitian countApproxDiag3).eigenvalues α = 2 ∨
      (symOfEntries_isHermitian countApproxDiag3).eigenvalues α = -1 ∨
      (symOfEntries_isHermitian countApproxDiag3).eigenvalues α = -3 := by
  have hs : spectrum ℝ (symOfEntries countApproxDiag3) = Set.range ![(2 : ℝ), -1, -3] := by
    rw [symOfEntries_countApproxDiag3, spectrum_diagonal]
  have h := (symOfEntries_isHermitian countApproxDiag3).eigenvalues_mem_spectrum_real α
  rw [hs] at h
  obtain ⟨i, hi⟩ := h
  fin_cases i <;> simp at hi <;> simp [← hi]

/-- The eigenvalues of `diag(2, -1, -3)` sum to its trace `-2`. -/
private lemma countApproxDiag3_trace :
    ∑ α, (symOfEntries_isHermitian countApproxDiag3).eigenvalues α = -2 := by
  have h := (symOfEntries_isHermitian countApproxDiag3).trace_eq_sum_eigenvalues
  have ht : (symOfEntries countApproxDiag3).trace = -2 := by
    rw [symOfEntries_countApproxDiag3, trace_diagonal, Fin.sum_univ_three]
    norm_num
  rw [ht] at h
  simp only [RCLike.ofReal_real_eq_id, id] at h
  linarith

/-- The hypotheses `‖H‖ ≤ 3`, (5.25) and (5.26) of `abs_countIcc_sub_smoothCount_le'` hold together
at `N = 3`, `C = 1/4`, `H = diag(2, -1, -3)`: here `λ_N = 2`, and exactly one eigenvalue lies within
`2 φ^C N^{-2/3}` of `2`. -/
example :
    (∀ α, |(symOfEntries_isHermitian countApproxDiag3).eigenvalues α| ≤ 3) ∧
      |((3 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries countApproxDiag3) - 2)| ≤
        phi 3 ^ (1 / 4 : ℝ) ∧
      ((Finset.univ.filter fun α =>
          |(symOfEntries_isHermitian countApproxDiag3).eigenvalues α - 2| ≤
            2 * phi 3 ^ (1 / 4 : ℝ) * ((3 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3)).card : ℝ) ≤
        phi 3 ^ (2 * (1 / 4 : ℝ)) := by
  set hA := symOfEntries_isHermitian countApproxDiag3
  have he := countApproxDiag3_eig
  have hs0 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  have hs1 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
  have hl0 : 0 < Real.log (Real.log 3) := Real.log_pos hs0
  have hl1 : Real.log (Real.log 3) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < Real.log 3); linarith
  have hφ : phi 3 = Real.exp (Real.log (Real.log 3) ^ 2) := by
    have := phi_eq_exp (N := 3) le_rfl
    simpa using this
  have hφ1 : 1 ≤ phi 3 := by rw [hφ]; exact Real.one_le_exp (sq_nonneg _)
  have hφq : phi 3 ^ (1 / 4 : ℝ) ≤ Real.exp (1 / 4) := by
    rw [hφ, ← Real.exp_mul]
    apply Real.exp_le_exp.2
    nlinarith
  have he4 : Real.exp (1 / 4) < 3 / 2 := by
    have h4 : Real.exp (1 / 4) ^ 4 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have := Real.exp_one_lt_d9
    have hp := Real.exp_pos (1 / 4)
    by_contra hc
    rw [not_lt] at hc
    have : (3 / 2 : ℝ) ^ 4 ≤ Real.exp (1 / 4) ^ 4 := pow_le_pow_left₀ (by norm_num) hc 4
    norm_num at this
    linarith
  have h3 : ((3 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have h3' : 0 ≤ ((3 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg (by norm_num) _
  have hr : 2 * phi 3 ^ (1 / 4 : ℝ) * ((3 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) < 3 := by
    have hq0 : 0 ≤ phi 3 ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by linarith) _
    nlinarith
  have hmax : lambdaMax (symOfEntries countApproxDiag3) = 2 := by
    have hg := lambdaMax_isGreatest hA
    apply le_antisymm
    · obtain ⟨α, hα⟩ := hg.1
      rw [← hα]
      rcases he α with h | h | h <;> rw [h] <;> norm_num
    · apply hg.2
      rw [← hA.spectrum_real_eq_range_eigenvalues, symOfEntries_countApproxDiag3,
        spectrum_diagonal]
      exact ⟨0, rfl⟩
  refine ⟨fun α => ?_, ?_, ?_⟩
  · rcases he α with h | h | h <;> rw [h] <;> norm_num
  · rw [hmax, sub_self, mul_zero, abs_zero]
    exact Real.rpow_nonneg (by linarith) _
  · have hcard : (Finset.univ.filter fun α =>
          |hA.eigenvalues α - 2| ≤
            2 * phi 3 ^ (1 / 4 : ℝ) * ((3 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3)).card ≤ 1 := by
      have h2 : ∀ α, |hA.eigenvalues α - 2| ≤
          2 * phi 3 ^ (1 / 4 : ℝ) * ((3 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) → hA.eigenvalues α = 2 := by
        intro α hα
        rcases he α with h | h | h
        · exact h
        · rw [h] at hα; norm_num at hα; linarith
        · rw [h] at hα; norm_num at hα; linarith
      have hlow : ∀ α, -3 ≤ hA.eigenvalues α := fun α => by
        rcases he α with h | h | h <;> rw [h] <;> norm_num
      have htr := countApproxDiag3_trace
      rw [Fin.sum_univ_three] at htr
      refine Finset.card_le_one.2 fun a ha b hb => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have ha2 := h2 a ha
      have hb2 := h2 b hb
      have l0 := hlow 0; have l1 := hlow 1; have l2 := hlow 2
      fin_cases a <;> fin_cases b <;> simp at ha2 hb2 ⊢ <;> linarith
    have hone : (1 : ℝ) ≤ phi 3 ^ (2 * (1 / 4 : ℝ)) := Real.one_le_rpow hφ1 (by norm_num)
    calc _ ≤ (1 : ℝ) := by exact_mod_cast hcard
      _ ≤ _ := hone

/-- The domain `S(C) ∩ {Im z ≤ N^{-2/3}}` of the hypothesis (5.24) in
`abs_countIcc_sub_smoothCount_le'` is nonempty for all large `N`: it contains `i N^{-2/3-3/20}`. -/
example {C : ℝ} (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop, ∃ z ∈ specDomain N C, z.im ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) := by
  filter_upwards [window_scales hC.le (ε := 1 / 20) (by norm_num) (by norm_num)] with N h
  obtain ⟨⟨h1, h2, h3, -⟩, -⟩ := h
  refine ⟨⟨0, (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * (1 / 20))⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · simp
  · exact h1
  · show (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * (1 / 20)) ≤ 10
    linarith
  · exact h2

#print axioms trace_f_rate
#print axioms bridge_term_rate
#print axioms far_region_rate
#print axioms window_scales
#print axioms abs_countIcc_sub_smoothCount_le'

end WEdgeNS
