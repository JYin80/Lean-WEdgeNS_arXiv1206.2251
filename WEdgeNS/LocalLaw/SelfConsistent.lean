import WEdgeNS.LocalLaw.Control

/-!
# The self-consistent equation on `Ω(z)`
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-! ### Parameter arithmetic -/

private lemma sc_one_le_phi {N : ℕ} (hN : 3 ≤ N) : 1 ≤ phi N := by
  rw [phi_eq_exp hN]
  exact Real.one_le_exp (sq_nonneg _)

private lemma sc_phi_pos {N : ℕ} (hN : 3 ≤ N) : 0 < phi N :=
  lt_of_lt_of_le one_pos (sc_one_le_phi hN)

private lemma sc_rpow_sq {x : ℝ} (hx : 0 < x) (a : ℝ) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, mul_comm]
  norm_num

/-- Larger offsets `K` give stronger hypotheses. -/
private lemma sc_rpow_mono {N : ℕ} (hN : 3 ≤ N) {a b : ℝ} (hab : a ≤ b) :
    phi N ^ a ≤ phi N ^ b :=
  Real.rpow_le_rpow_of_exponent_le (sc_one_le_phi hN) hab

private lemma sc_specDomain_mono {N : ℕ} (hN : 3 ≤ N) {K K' : ℝ} (hKK : K' ≤ K) {z : ℂ}
    (hz : z ∈ specDomain N K) : z ∈ specDomain N K' := by
  obtain ⟨h1, h2, h3⟩ := hz
  have hNr : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  refine ⟨h1, lt_of_le_of_lt ?_ h2, h3⟩
  exact div_le_div_of_nonneg_right (sc_rpow_mono hN hKK) hNr.le

/-- `specDomain` lies in the upper half plane for `N ≥ 3`, with `N η > φ^K`. -/
private lemma sc_specDomain {N : ℕ} (hN : 3 ≤ N) {K : ℝ} {z : ℂ} (hz : z ∈ specDomain N K) :
    |z.re| ≤ 5 ∧ 0 < z.im ∧ z.im ≤ 10 ∧ phi N ^ K < N * z.im := by
  obtain ⟨h1, h2, h3⟩ := hz
  have hNr : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hφ : 0 < phi N ^ K := Real.rpow_pos_of_pos (sc_phi_pos hN) K
  have h4 : phi N ^ K < N * z.im := by
    rwa [div_lt_iff₀ hNr, mul_comm] at h2
  refine ⟨h1, ?_, h3, h4⟩
  by_contra hneg
  have : N * z.im ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hNr.le (not_lt.mp hneg)
  linarith

/-- A single event of probability `C e^{-s/C}` is at most `e^{-s/(2C)}` for large `s`. -/
private lemma sc_exp_tail {C s : ℝ} (hC : 0 < C) (hs : 2 * C * |Real.log C| ≤ s) :
    C * Real.exp (-s / C) ≤ Real.exp (-(1 / (2 * C)) * s) := by
  have h1 : C * Real.exp (-s / C) = Real.exp (Real.log C + -s / C) := by
    rw [Real.exp_add, Real.exp_log hC]
  rw [h1]
  apply Real.exp_le_exp.mpr
  have h2 : |Real.log C| ≤ s / (2 * C) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h3 : -s / C + s / (2 * C) = -(s / (2 * C)) := by
    field_simp
    ring
  have h4 : -(1 / (2 * C)) * s = -(s / (2 * C)) := by ring
  rw [h4]
  linarith [le_abs_self (Real.log C)]

/-! ### Facts on `m_sc` -/

/-- `|m_sc|` is between `1/16` and `1` on `|E| ≤ 5`, `0 < η ≤ 10`. -/
private lemma sc_msc_norm {z : ℂ} (hre : |z.re| ≤ 5) (him : 0 < z.im) (hle : z.im ≤ 10) :
    1 / 16 ≤ ‖msc z‖ ∧ ‖msc z‖ ≤ 1 := by
  obtain ⟨h1, h2⟩ := norm_msc_eq_inv_and_lt_one him
  refine ⟨?_, h2.le⟩
  have hz : ‖z‖ ≤ 15 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos him] at this
    linarith
  have hsum : ‖msc z + z‖ ≤ 16 := (norm_add_le _ _).trans (by linarith)
  have hpos : 0 < ‖msc z + z‖ := by
    have hm0 : 0 < ‖msc z‖ := norm_pos_iff.mpr fun h => by
      have := im_msc_pos him
      rw [h] at this
      simp at this
    rw [h1] at hm0
    exact inv_pos.mp hm0
  rw [h1, one_div]
  exact inv_anti₀ hpos hsum

private lemma sc_msc_ne_zero {z : ℂ} (hz : 0 < z.im) : msc z ≠ 0 := fun h0 => by
  have := im_msc_pos hz
  rw [h0] at this
  simp at this

/-- `m_sc(z)⁻¹ = -z - m_sc(z)`. -/
private lemma sc_inv_msc {z : ℂ} (hz : 0 < z.im) : (msc z)⁻¹ = -z - msc z := by
  have h := msc_add_inv_eq_zero hz
  have hm := sc_msc_ne_zero hz
  have hzm : z + msc z ≠ 0 := fun h0 => by
    rw [h0, _root_.inv_zero, add_zero] at h
    exact hm h
  have h2 : msc z * (z + msc z) = -1 := by
    field_simp at h
    linear_combination h
  have h3 : (msc z)⁻¹ = -(z + msc z) :=
    inv_eq_of_mul_eq_one_right (by linear_combination -h2)
  rw [h3]
  ring

/-- `Im m_sc(z) ≥ η / 256` on `|E| ≤ 5`, `0 < η ≤ 10`. -/
private lemma sc_im_msc_ge {z : ℂ} (hre : |z.re| ≤ 5) (him : 0 < z.im) (hle : z.im ≤ 10) :
    z.im / 256 ≤ (msc z).im := by
  obtain ⟨hlo, hhi⟩ := sc_msc_norm hre him hle
  have hnorm := (norm_msc_eq_inv_and_lt_one him).1
  have h16 : ‖z + msc z‖ ≤ 16 := by
    rw [add_comm]
    have h : ‖msc z + z‖ = ‖msc z‖⁻¹ := by
      rw [hnorm, inv_inv]
    rw [h]
    calc ‖msc z‖⁻¹ ≤ (1 / 16 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hlo
      _ = 16 := by norm_num
  have hm := msc_add_inv_eq_zero him
  have himm : (msc z).im = -((z + msc z)⁻¹).im := by
    have := congrArg Complex.im hm
    rw [Complex.add_im, Complex.zero_im] at this
    linarith
  rw [Complex.inv_im, neg_div, neg_neg, Complex.add_im] at himm
  have hmi := im_msc_pos him
  have hnS : Complex.normSq (z + msc z) ≤ 256 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (z + msc z)]
  have hnS0 : 0 < Complex.normSq (z + msc z) := by
    rw [Complex.normSq_pos]
    intro h0
    rw [h0, _root_.inv_zero, add_zero] at hm
    exact sc_msc_ne_zero him hm
  have h3 : (msc z).im * Complex.normSq (z + msc z) = z.im + (msc z).im := by
    rw [eq_div_iff hnS0.ne'] at himm
    exact himm
  nlinarith [mul_le_mul_of_nonneg_left hnS hmi.le]

/-! ### Elementary bounds for the control parameters -/

private lemma sc_lamO_nonneg {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : 0 ≤ lamO H z :=
  Real.iSup_nonneg fun i => Real.iSup_nonneg fun j => by split_ifs <;> positivity

private lemma sc_lamD_nonneg {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : 0 ≤ lamD H z :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/-! ### The expansion (3.41) and its average -/

/-- (3.41) of [15] for one index: `g = m / (1 - m x)` expanded to third order. -/
private lemma sc_expand {g m x : ℂ} (hm : m ≠ 0) (hgx : g⁻¹ = m⁻¹ - x) (hx : ‖m * x‖ ≤ 1 / 3) :
    g - m = m ^ 2 * x + m ^ 3 * x ^ 2 + m ^ 4 * x ^ 3 / (1 - m * x) := by
  have h1 : 1 - m * x ≠ 0 := by
    intro h
    have h2 : m * x = 1 := by linear_combination -h
    rw [h2, norm_one] at hx
    norm_num at hx
  have h3 : g⁻¹ = (1 - m * x) / m := by
    rw [hgx]
    field_simp
  have hg : g = m / (1 - m * x) := by
    rw [← inv_inv g, h3, inv_div]
  rw [hg]
  field_simp
  ring

private lemma sc_remainder {m x : ℂ} (hm : ‖m‖ ≤ 1) (hx : ‖m * x‖ ≤ 1 / 3) :
    ‖m ^ 4 * x ^ 3 / (1 - m * x)‖ ≤ 3 / 2 * ‖x‖ ^ 3 := by
  have h1 : 2 / 3 ≤ ‖1 - m * x‖ := by
    have := norm_sub_norm_le (1 : ℂ) (m * x)
    rw [norm_one] at this
    linarith
  have h2 : ‖m‖ ^ 4 ≤ 1 := pow_le_one₀ (norm_nonneg _) hm
  rw [norm_div, norm_mul, norm_pow, norm_pow]
  have h3 : 0 ≤ ‖x‖ ^ 3 := by positivity
  rw [div_le_iff₀ (by linarith)]
  calc ‖m‖ ^ 4 * ‖x‖ ^ 3 ≤ 1 * ‖x‖ ^ 3 := by gcongr
    _ ≤ 3 / 2 * ‖x‖ ^ 3 * ‖1 - m * x‖ := by nlinarith

/-- The deterministic bound on `(1 - m²) [v] - m³ [v]² - m² [Z]` ((3.40) of [15] before the
probabilistic estimates): it is controlled by the diagonal average, `A_i`, `Υ_i` and `Λ`. -/
private lemma sc_det {N : ℕ} (hN : 0 < N) {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hzim : 0 < z.im) (hmlo : 1 / 16 ≤ ‖msc z‖) (hmhi : ‖msc z‖ ≤ 1)
    (hΩ : lamD H z + lamO H z ≤ 1 / 64) {U BA : ℝ}
    (hU : ∀ i, ‖upsilon H z i‖ ≤ U) (hA : ∀ i, ‖aCorr H z i‖ ≤ BA) :
    ‖(1 - msc z ^ 2) * (stieltjesM H z - msc z) - msc z ^ 3 * (stieltjesM H z - msc z) ^ 2 -
        msc z ^ 2 * zAvg H z‖ ≤
      ‖(N : ℂ)⁻¹ * ∑ i, (H i i : ℂ)‖ + BA + 2 * lamAvg H z * U + 37 * U ^ 2 +
        6 * lamAvg H z ^ 3 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hm0 : msc z ≠ 0 := sc_msc_ne_zero hzim
  have hD : ∀ i, ‖resolventC H z i i - msc z‖ ≤ 1 / 64 := fun i =>
    (norm_resolventC_sub_msc_le_lamD i).trans (by linarith [sc_lamO_nonneg H z])
  have hg_lo : ∀ i, 3 / 64 ≤ ‖resolventC H z i i‖ := fun i => by
    have h1 := norm_sub_norm_le (msc z) (resolventC H z i i)
    rw [norm_sub_rev] at h1
    linarith [hD i]
  have hw_eq : stieltjesM H z - msc z =
      (N : ℂ)⁻¹ * ∑ i, (resolventC H z i i - msc z) := by
    unfold stieltjesM
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Matrix.trace]
    simp only [Matrix.diag]
    field_simp
  have hΛ : lamAvg H z ≤ 1 / 64 := by
    unfold lamAvg
    rw [hw_eq, norm_mul, norm_inv, Complex.norm_natCast]
    calc (N : ℝ)⁻¹ * ‖∑ i, (resolventC H z i i - msc z)‖
        ≤ (N : ℝ)⁻¹ * (N * (1 / 64)) := by
          gcongr
          refine (norm_sum_le _ _).trans ?_
          calc ∑ i, ‖resolventC H z i i - msc z‖ ≤ ∑ _i : Fin N, (1 / 64 : ℝ) :=
                Finset.sum_le_sum fun i _ => hD i
            _ = N * (1 / 64) := by simp
      _ = 1 / 64 := by field_simp
  have hΛ0 : 0 ≤ lamAvg H z := norm_nonneg _
  -- the quantity `x_i = [v] - Υ_i`
  have hinv : ∀ i, (resolventC H z i i)⁻¹ = (msc z)⁻¹ - ((stieltjesM H z - msc z) -
      upsilon H z i) := fun i => by
    rw [inv_resolventC_diag_eq hH hzim i, sc_inv_msc hzim]
  have hmx : ∀ i, ‖msc z * ((stieltjesM H z - msc z) - upsilon H z i)‖ ≤ 1 / 3 := fun i => by
    have hgi : resolventC H z i i ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (hg_lo i))
    have e : msc z * ((stieltjesM H z - msc z) - upsilon H z i) =
        (resolventC H z i i - msc z) / resolventC H z i i := by
      have : (stieltjesM H z - msc z) - upsilon H z i =
          (msc z)⁻¹ - (resolventC H z i i)⁻¹ := by rw [hinv i]; ring
      rw [this]
      field_simp
    rw [e, norm_div, div_le_iff₀ (lt_of_lt_of_le (by norm_num) (hg_lo i))]
    linarith [hD i, hg_lo i]
  have hxn : ∀ i, ‖(stieltjesM H z - msc z) - upsilon H z i‖ ≤ 16 / 3 := fun i => by
    have h1 := hmx i
    rw [norm_mul] at h1
    have h2 : 1 / 16 * ‖(stieltjesM H z - msc z) - upsilon H z i‖ ≤
        ‖msc z‖ * ‖(stieltjesM H z - msc z) - upsilon H z i‖ :=
      mul_le_mul_of_nonneg_right hmlo (norm_nonneg _)
    linarith
  have hυn : ∀ i, ‖upsilon H z i‖ ≤ 6 := fun i => by
    have e : upsilon H z i = (stieltjesM H z - msc z) -
        ((stieltjesM H z - msc z) - upsilon H z i) := by ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖stieltjesM H z - msc z‖ ≤ 1 / 64 := hΛ
    linarith [hxn i]
  -- cubic bound on `x_i`
  have hcube : ∀ i, ‖(stieltjesM H z - msc z) - upsilon H z i‖ ^ 3 ≤
      4 * lamAvg H z ^ 3 + 24 * U ^ 2 := fun i => by
    have hx : ‖(stieltjesM H z - msc z) - upsilon H z i‖ ≤ lamAvg H z + ‖upsilon H z i‖ :=
      norm_sub_le _ _
    have hu0 := norm_nonneg (upsilon H z i)
    have hu6 := hυn i
    have hui := hU i
    have h1 : (lamAvg H z + ‖upsilon H z i‖) ^ 3 ≤
        4 * (lamAvg H z ^ 3 + ‖upsilon H z i‖ ^ 3) := by
      nlinarith [mul_nonneg (add_nonneg hΛ0 hu0) (sq_nonneg (lamAvg H z - ‖upsilon H z i‖))]
    have h2 : ‖upsilon H z i‖ ^ 3 ≤ 6 * U ^ 2 := by
      have : ‖upsilon H z i‖ ^ 2 ≤ U ^ 2 := by gcongr
      nlinarith [sq_nonneg ‖upsilon H z i‖]
    calc ‖(stieltjesM H z - msc z) - upsilon H z i‖ ^ 3 ≤ (lamAvg H z + ‖upsilon H z i‖) ^ 3 := by
          gcongr
      _ ≤ 4 * lamAvg H z ^ 3 + 24 * U ^ 2 := by linarith
  -- the expansion for each index
  obtain ⟨R, hR1, hR2⟩ : ∃ R : Fin N → ℂ,
      (∀ i, resolventC H z i i - msc z =
        msc z ^ 2 * ((stieltjesM H z - msc z) - upsilon H z i) +
        msc z ^ 3 * ((stieltjesM H z - msc z) - upsilon H z i) ^ 2 + R i) ∧
      ∀ i, ‖R i‖ ≤ 6 * lamAvg H z ^ 3 + 36 * U ^ 2 :=
    ⟨fun i => msc z ^ 4 * ((stieltjesM H z - msc z) - upsilon H z i) ^ 3 /
        (1 - msc z * ((stieltjesM H z - msc z) - upsilon H z i)),
      fun i => sc_expand hm0 (hinv i) (hmx i), fun i =>
      (sc_remainder hmhi (hmx i)).trans (by linarith [hcube i])⟩
  have hΛeq : lamAvg H z = ‖stieltjesM H z - msc z‖ := rfl
  generalize hw : stieltjesM H z - msc z = w at *
  generalize hm : msc z = m at *
  have e3 : ∑ i, (resolventC H z i i - m) = N * w := by
    rw [hw_eq]
    field_simp
  have e5 : ∑ i, upsilon H z i = ∑ i, (H i i : ℂ) - N * zAvg H z + ∑ i, aCorr H z i := by
    have hZ : (N : ℂ) * zAvg H z = ∑ i, zFluct H z i := by
      unfold zAvg
      field_simp
    rw [hZ]
    unfold upsilon
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have e6 : ∑ i, (resolventC H z i i - m) =
      N * (m ^ 2 * w + m ^ 3 * w ^ 2) - (m ^ 2 + 2 * m ^ 3 * w) * ∑ i, upsilon H z i +
        m ^ 3 * ∑ i, upsilon H z i ^ 2 + ∑ i, R i := by
    have h1 : ∀ i, resolventC H z i i - m = (m ^ 2 * w + m ^ 3 * w ^ 2) -
        (m ^ 2 + 2 * m ^ 3 * w) * upsilon H z i + m ^ 3 * upsilon H z i ^ 2 + R i := fun i => by
      rw [hR1 i]
      ring
    rw [Finset.sum_congr rfl fun i _ => h1 i]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
      ← Finset.mul_sum]
  have key : (N : ℂ) * ((1 - m ^ 2) * w - m ^ 3 * w ^ 2 - m ^ 2 * zAvg H z) =
      -(m ^ 2 * (∑ i, (H i i : ℂ) + ∑ i, aCorr H z i)) -
        2 * m ^ 3 * w * ∑ i, upsilon H z i + m ^ 3 * ∑ i, upsilon H z i ^ 2 + ∑ i, R i := by
    linear_combination e6 - e3 - m ^ 2 * e5
  -- the norm estimate
  have hsumc : ∀ c : ℝ, ∑ _i : Fin N, c = N * c := fun c => by simp
  have hS1 : ‖∑ i, upsilon H z i‖ ≤ N * U :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => hU i).trans (hsumc U).le)
  have hS2 : ‖∑ i, upsilon H z i ^ 2‖ ≤ N * U ^ 2 := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => ?_).trans (hsumc (U ^ 2)).le)
    rw [norm_pow]
    have := hU i
    gcongr
  have hSR : ‖∑ i, R i‖ ≤ N * (6 * lamAvg H z ^ 3 + 36 * U ^ 2) :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => hR2 i).trans
      (hsumc (6 * lamAvg H z ^ 3 + 36 * U ^ 2)).le)
  have hSA : ‖∑ i, aCorr H z i‖ ≤ N * BA :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => hA i).trans (hsumc BA).le)
  have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU ⟨0, hN⟩)
  have hm2 : ‖m‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hmhi
  have hm3 : ‖m‖ ^ 3 ≤ 1 := pow_le_one₀ (norm_nonneg _) hmhi
  set SH : ℂ := ∑ i, (H i i : ℂ) with hSH
  set S1 : ℂ := ∑ i, upsilon H z i with hS1d
  set S2 : ℂ := ∑ i, upsilon H z i ^ 2 with hS2d
  set SR : ℂ := ∑ i, R i with hSRd
  set SA : ℂ := ∑ i, aCorr H z i with hSAd
  have hnorm : (N : ℝ) * ‖(1 - m ^ 2) * w - m ^ 3 * w ^ 2 - m ^ 2 * zAvg H z‖ ≤
      ‖SH‖ + N * (BA + 2 * ‖w‖ * U + 37 * U ^ 2 + 6 * ‖w‖ ^ 3) := by
    have h1 : (N : ℝ) * ‖(1 - m ^ 2) * w - m ^ 3 * w ^ 2 - m ^ 2 * zAvg H z‖ =
        ‖(N : ℂ) * ((1 - m ^ 2) * w - m ^ 3 * w ^ 2 - m ^ 2 * zAvg H z)‖ := by
      rw [norm_mul, Complex.norm_natCast]
    rw [h1, key]
    have t1 : ‖-(m ^ 2 * (SH + SA))‖ ≤ ‖SH‖ + N * BA := by
      rw [norm_neg, norm_mul, norm_pow]
      calc ‖m‖ ^ 2 * ‖SH + SA‖ ≤ 1 * ‖SH + SA‖ := by gcongr
        _ ≤ ‖SH‖ + N * BA := by
            rw [one_mul]
            exact (norm_add_le _ _).trans (by linarith)
    have t2 : ‖-(2 * m ^ 3 * w * S1)‖ ≤ 2 * ‖w‖ * (N * U) := by
      rw [norm_neg, norm_mul, norm_mul, norm_mul, norm_pow]
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [h2]
      have hw0 := norm_nonneg w
      calc 2 * ‖m‖ ^ 3 * ‖w‖ * ‖S1‖ ≤ 2 * 1 * ‖w‖ * (N * U) := by gcongr
        _ = 2 * ‖w‖ * (N * U) := by ring
    have t3 : ‖m ^ 3 * S2‖ ≤ N * U ^ 2 := by
      rw [norm_mul, norm_pow]
      calc ‖m‖ ^ 3 * ‖S2‖ ≤ 1 * (N * U ^ 2) := by gcongr
        _ = N * U ^ 2 := one_mul _
    have e : -(m ^ 2 * (SH + SA)) - 2 * m ^ 3 * w * S1 + m ^ 3 * S2 + SR =
        (-(m ^ 2 * (SH + SA)) + -(2 * m ^ 3 * w * S1) + m ^ 3 * S2) + SR := by ring
    rw [e]
    calc ‖(-(m ^ 2 * (SH + SA)) + -(2 * m ^ 3 * w * S1) + m ^ 3 * S2) + SR‖
        ≤ ‖-(m ^ 2 * (SH + SA)) + -(2 * m ^ 3 * w * S1) + m ^ 3 * S2‖ + ‖SR‖ := norm_add_le _ _
      _ ≤ (‖-(m ^ 2 * (SH + SA))‖ + ‖-(2 * m ^ 3 * w * S1)‖ + ‖m ^ 3 * S2‖) + ‖SR‖ := by
          gcongr
          exact norm_add₃_le
      _ ≤ ((‖SH‖ + N * BA) + 2 * ‖w‖ * (N * U) + N * U ^ 2) +
            N * (6 * lamAvg H z ^ 3 + 36 * U ^ 2) := by gcongr
      _ = ‖SH‖ + N * (BA + 2 * ‖w‖ * U + 37 * U ^ 2 + 6 * ‖w‖ ^ 3) := by
          rw [hΛeq]
          ring
  have hfin : ‖(1 - m ^ 2) * w - m ^ 3 * w ^ 2 - m ^ 2 * zAvg H z‖ ≤
      ‖(N : ℂ)⁻¹ * SH‖ + BA + 2 * ‖w‖ * U + 37 * U ^ 2 + 6 * ‖w‖ ^ 3 := by
    have h2 : ‖SH‖ = N * ‖(N : ℂ)⁻¹ * SH‖ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      field_simp
    rw [h2] at hnorm
    have : (N : ℝ) * ‖(1 - m ^ 2) * w - m ^ 3 * w ^ 2 - m ^ 2 * zAvg H z‖ ≤
        N * (‖(N : ℂ)⁻¹ * SH‖ + BA + 2 * ‖w‖ * U + 37 * U ^ 2 + 6 * ‖w‖ ^ 3) := by
      linarith
    exact le_of_mul_le_mul_left this hNr
  rw [hΛeq]
  exact hfin

/-- `|A_i| ≤ 5/(4N) + 22 Λ_o²` on `Ω(z)` ((3.37) of [15], with the diagonal term kept). -/
private lemma sc_aCorr_le {N : ℕ} (hN : 0 < N) {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ}
    (hmlo : 1 / 16 ≤ ‖msc z‖) (hmhi : ‖msc z‖ ≤ 1) (hΩ : lamD H z + lamO H z ≤ 1 / 64)
    (i : Fin N) : ‖aCorr H z i‖ ≤ 5 / (4 * N) + 22 * lamO H z ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hO := sc_lamO_nonneg H z
  have hO' : lamO H z ≤ 1 / 64 := by linarith [sc_lamD_nonneg H z]
  have hD : ∀ j, ‖resolventC H z j j - msc z‖ ≤ 1 / 64 := fun j =>
    (norm_resolventC_sub_msc_le_lamD j).trans (by linarith [sc_lamO_nonneg H z])
  have hdiag : ∀ j, 3 / 64 ≤ ‖resolventC H z j j‖ ∧ ‖resolventC H z j j‖ ≤ 5 / 4 := fun j => by
    have h1 := norm_sub_norm_le (msc z) (resolventC H z j j)
    rw [norm_sub_rev] at h1
    have h3 := norm_add_le (resolventC H z j j - msc z) (msc z)
    rw [sub_add_cancel] at h3
    constructor <;> linarith [hD j]
  have hii := hdiag i
  have hgi : 0 < ‖resolventC H z i i‖ := lt_of_lt_of_le (by norm_num) hii.1
  unfold aCorr
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin N)).erase i,
      ‖resolventC H z i j * resolventC H z j i / resolventC H z i i‖ ≤ 22 * lamO H z ^ 2 := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have h1 : ‖resolventC H z i j‖ ≤ lamO H z := norm_resolventC_off_le_lamO (Ne.symm hji)
    have h2 : ‖resolventC H z j i‖ ≤ lamO H z := norm_resolventC_off_le_lamO hji
    rw [norm_div, norm_mul]
    calc ‖resolventC H z i j‖ * ‖resolventC H z j i‖ / ‖resolventC H z i i‖
        ≤ lamO H z * lamO H z / (3 / 64) := by gcongr; exact hii.1
      _ ≤ 22 * lamO H z ^ 2 := by nlinarith
  have hsum : ‖∑ j, resolventC H z i j * resolventC H z j i / resolventC H z i i‖ ≤
      5 / 4 + N * (22 * lamO H z ^ 2) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    refine (norm_add_le _ _).trans ?_
    have hdi : ‖resolventC H z i i * resolventC H z i i / resolventC H z i i‖ ≤ 5 / 4 := by
      rw [mul_div_cancel_right₀ _ (norm_pos_iff.mp hgi)]
      exact hii.2
    have hrest : ‖∑ j ∈ (Finset.univ : Finset (Fin N)).erase i,
        resolventC H z i j * resolventC H z j i / resolventC H z i i‖ ≤
          N * (22 * lamO H z ^ 2) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ j ∈ (Finset.univ : Finset (Fin N)).erase i,
            ‖resolventC H z i j * resolventC H z j i / resolventC H z i i‖
          ≤ ∑ _j ∈ (Finset.univ : Finset (Fin N)).erase i, 22 * lamO H z ^ 2 :=
            Finset.sum_le_sum hterm
        _ = (((Finset.univ : Finset (Fin N)).erase i).card : ℝ) * (22 * lamO H z ^ 2) := by simp
        _ ≤ N * (22 * lamO H z ^ 2) := by
            gcongr
            have : ((Finset.univ : Finset (Fin N)).erase i).card ≤ N := by
              calc _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_erase_le
                _ = N := by simp
            exact_mod_cast this
    linarith
  calc (N : ℝ)⁻¹ * ‖∑ j, resolventC H z i j * resolventC H z j i / resolventC H z i i‖
      ≤ (N : ℝ)⁻¹ * (5 / 4 + N * (22 * lamO H z ^ 2)) := by gcongr
    _ = 5 / (4 * N) + 22 * lamO H z ^ 2 := by field_simp

/-! ### The real-variable estimate behind (3.40) -/

private lemma sc_sq_add_le (a b : ℝ) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

private lemma sc_sq_add3_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

private lemma sc_young {ℓ Λ U : ℝ} (hℓ : 0 < ℓ) : 2 * Λ * U ≤ Λ ^ 2 / ℓ + ℓ * U ^ 2 := by
  rw [← sub_nonneg]
  have : Λ ^ 2 / ℓ + ℓ * U ^ 2 - 2 * Λ * U = (Λ - ℓ * U) ^ 2 / ℓ := by
    field_simp
    ring
  rw [this]
  positivity

/-- The collection of the estimates for `[A]`, `Υ_i`, the diagonal average and `Λ`, closed to the
right-hand side of (3.40) of [15]. -/
private lemma sc_chain {ℓ s q n Ψ Λ lo D C2 C3 cD : ℝ}
    (hℓ : 1 ≤ ℓ) (hs : 1 ≤ s) (hq : 1 ≤ q) (hn : 1 ≤ n) (hΨ : 0 ≤ Ψ)
    (hΛ : Λ ≤ 1 / ℓ) (hC2 : 0 < C2) (hC3 : 0 < C3) (hcD : 0 ≤ cD)
    (hΨn : 1 / n ≤ 256 * Ψ ^ 2) (hlo0 : 0 ≤ lo) (hlo : lo ≤ 1 / 64)
    (hloC : lo ≤ C2 * (1 / q + s ^ 2 * Ψ)) (hD : D ≤ s * cD / n) :
    D + (5 / (4 * n) + 22 * lo ^ 2) +
      2 * Λ * (1 / q + C3 * (s / q + s ^ 2 * Ψ) + (5 / (4 * n) + 22 * lo ^ 2)) +
      37 * (1 / q + C3 * (s / q + s ^ 2 * Ψ) + (5 / (4 * n) + 22 * lo ^ 2)) ^ 2 + 6 * Λ ^ 3 ≤
    (256 * cD + (320 + 44 * C2 ^ 2) + 38 * (3 * (1 + 2 * C3 ^ 2 + 2 * (320 + 44 * C2 ^ 2))) + 7) *
      (s ^ 2 * ℓ / q ^ 2 + s ^ 4 * ℓ * Ψ ^ 2 + Λ ^ 2 / ℓ) := by
  have hq0 : 0 < q := by linarith
  have hn0 : 0 < n := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  obtain ⟨p, hp⟩ : ∃ p : ℝ, 1 / q = p := ⟨_, rfl⟩
  have hp0 : 0 < p := by rw [← hp]; positivity
  have e1 : s / q = s * p := by rw [← hp]; ring
  have e2 : s ^ 2 * ℓ / q ^ 2 = s ^ 2 * ℓ * p ^ 2 := by rw [← hp]; ring
  rw [hp] at hloC ⊢
  rw [e1, e2]
  clear e1 e2 hp hq hq0
  obtain ⟨T0, hT0⟩ : ∃ T0 : ℝ, T0 = s ^ 2 * p ^ 2 + s ^ 4 * Ψ ^ 2 := ⟨_, rfl⟩
  have hA1 : 0 ≤ s ^ 2 * p ^ 2 := by positivity
  have hA2 : 0 ≤ s ^ 4 * Ψ ^ 2 := by positivity
  have hT0nn : 0 ≤ T0 := by rw [hT0]; positivity
  have hs2 : 1 ≤ s ^ 2 := one_le_pow₀ hs
  have hs4 : 1 ≤ s ^ 4 := one_le_pow₀ hs
  have hss : s ≤ s ^ 4 := le_self_pow₀ hs (by norm_num)
  have hΨ2 : Ψ ^ 2 ≤ T0 := by
    have : Ψ ^ 2 ≤ s ^ 4 * Ψ ^ 2 := le_mul_of_one_le_left (sq_nonneg Ψ) hs4
    linarith
  have hp2 : p ^ 2 ≤ s ^ 2 * p ^ 2 := le_mul_of_one_le_left (sq_nonneg p) hs2
  have hp2T : p ^ 2 ≤ T0 := by linarith
  have hinvn : 1 / n ≤ 256 * T0 := by linarith
  have hsΨ : s * Ψ ^ 2 ≤ T0 := by
    have : s * Ψ ^ 2 ≤ s ^ 4 * Ψ ^ 2 := mul_le_mul_of_nonneg_right hss (sq_nonneg Ψ)
    linarith
  have hDb : D ≤ 256 * cD * T0 := by
    have h1 : s * cD / n = cD * s * (1 / n) := by ring
    have h2 : cD * s * (1 / n) ≤ cD * s * (256 * Ψ ^ 2) :=
      mul_le_mul_of_nonneg_left hΨn (by positivity)
    have h4 : cD * s * (256 * Ψ ^ 2) = 256 * cD * (s * Ψ ^ 2) := by ring
    have h5 : 256 * cD * (s * Ψ ^ 2) ≤ 256 * cD * T0 :=
      mul_le_mul_of_nonneg_left hsΨ (by positivity)
    linarith
  have hlo2 : lo ^ 2 ≤ 2 * C2 ^ 2 * T0 := by
    have h1 : lo ^ 2 ≤ (C2 * (p + s ^ 2 * Ψ)) ^ 2 := by gcongr
    have h2 : (p + s ^ 2 * Ψ) ^ 2 ≤ 2 * T0 := by
      have h5 := sc_sq_add_le p (s ^ 2 * Ψ)
      have h3 : (s ^ 2 * Ψ) ^ 2 = s ^ 4 * Ψ ^ 2 := by ring
      rw [h3] at h5
      linarith
    calc lo ^ 2 ≤ (C2 * (p + s ^ 2 * Ψ)) ^ 2 := h1
      _ = C2 ^ 2 * (p + s ^ 2 * Ψ) ^ 2 := by ring
      _ ≤ C2 ^ 2 * (2 * T0) := by gcongr
      _ = 2 * C2 ^ 2 * T0 := by ring
  obtain ⟨BA, hBAd⟩ : ∃ BA : ℝ, BA = 5 / (4 * n) + 22 * lo ^ 2 := ⟨_, rfl⟩
  rw [← hBAd]
  have hBA : BA ≤ (320 + 44 * C2 ^ 2) * T0 := by
    have h1 : 5 / (4 * n) = 5 / 4 * (1 / n) := by field_simp
    rw [hBAd, h1]
    have h2 : 5 / 4 * (1 / n) ≤ 5 / 4 * (256 * T0) :=
      mul_le_mul_of_nonneg_left hinvn (by norm_num)
    have h3 : 22 * lo ^ 2 ≤ 22 * (2 * C2 ^ 2 * T0) := by linarith
    have h4 : (320 + 44 * C2 ^ 2) * T0 = 5 / 4 * (256 * T0) + 22 * (2 * C2 ^ 2 * T0) := by ring
    linarith
  have hBA0 : 0 ≤ BA := by rw [hBAd]; positivity
  have hBA2 : BA ≤ 2 := by
    have h1 : 5 / (4 * n) ≤ 5 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have h2 : lo ^ 2 ≤ 1 / 4096 := by
      have : lo ^ 2 ≤ (1 / 64) ^ 2 := by gcongr
      linarith
    rw [hBAd]; linarith
  have hBAsq : BA ^ 2 ≤ 2 * ((320 + 44 * C2 ^ 2) * T0) := by
    have : BA ^ 2 ≤ 2 * BA := by nlinarith
    linarith
  obtain ⟨cBA, hcBA⟩ : ∃ c : ℝ, c = 320 + 44 * C2 ^ 2 := ⟨_, rfl⟩
  rw [← hcBA] at hBA hBAsq ⊢
  have hcBA0 : 0 ≤ cBA := by rw [hcBA]; positivity
  obtain ⟨Zb, hZb⟩ : ∃ Zb : ℝ, Zb = C3 * (s * p + s ^ 2 * Ψ) := ⟨_, rfl⟩
  rw [← hZb]
  have hZb0 : 0 ≤ Zb := by rw [hZb]; positivity
  have hZbsq : Zb ^ 2 ≤ 2 * C3 ^ 2 * T0 := by
    have h1 := sc_sq_add_le (s * p) (s ^ 2 * Ψ)
    have h3 : (s ^ 2 * Ψ) ^ 2 = s ^ 4 * Ψ ^ 2 := by ring
    have h4 : (s * p) ^ 2 = s ^ 2 * p ^ 2 := by ring
    rw [h3, h4] at h1
    have h5 : (s * p + s ^ 2 * Ψ) ^ 2 ≤ 2 * T0 := by linarith
    calc Zb ^ 2 = C3 ^ 2 * (s * p + s ^ 2 * Ψ) ^ 2 := by rw [hZb]; ring
      _ ≤ C3 ^ 2 * (2 * T0) := by gcongr
      _ = 2 * C3 ^ 2 * T0 := by ring
  obtain ⟨U, hUd⟩ : ∃ U : ℝ, U = p + Zb + BA := ⟨_, rfl⟩
  rw [← hUd]
  have hU0 : 0 ≤ U := by rw [hUd]; positivity
  obtain ⟨cU, hcU⟩ : ∃ c : ℝ, c = 3 * (1 + 2 * C3 ^ 2 + 2 * cBA) := ⟨_, rfl⟩
  have hUsq : U ^ 2 ≤ cU * T0 := by
    have h1 : U ^ 2 ≤ 3 * (p ^ 2 + Zb ^ 2 + BA ^ 2) := by
      rw [hUd]
      exact sc_sq_add3_le p Zb BA
    have h2 : 3 * (p ^ 2 + Zb ^ 2 + BA ^ 2) ≤ 3 * (T0 + 2 * C3 ^ 2 * T0 + 2 * (cBA * T0)) := by
      linarith
    have h3 : 3 * (T0 + 2 * C3 ^ 2 * T0 + 2 * (cBA * T0)) = cU * T0 := by rw [hcU]; ring
    linarith
  rw [← hcU]
  have hcU0 : 0 ≤ cU := by rw [hcU]; positivity
  have hY := sc_young (Λ := Λ) (U := U) hℓ0
  have hΛ3 : Λ ^ 3 ≤ Λ ^ 2 / ℓ := by
    have : Λ ^ 3 = Λ ^ 2 * Λ := by ring
    rw [this, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hΛ (sq_nonneg Λ)
  have hΛℓ : 0 ≤ Λ ^ 2 / ℓ := by positivity
  have hℓT : T0 ≤ ℓ * T0 := le_mul_of_one_le_left hT0nn hℓ
  have hℓU : (ℓ + 37) * U ^ 2 ≤ 38 * ℓ * (cU * T0) := by
    have h1 : (ℓ + 37) * U ^ 2 ≤ (38 * ℓ) * U ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg U)
    calc (ℓ + 37) * U ^ 2 ≤ (38 * ℓ) * U ^ 2 := h1
      _ ≤ (38 * ℓ) * (cU * T0) := by gcongr
      _ = 38 * ℓ * (cU * T0) := by ring
  have hRHS : s ^ 2 * ℓ * p ^ 2 + s ^ 4 * ℓ * Ψ ^ 2 + Λ ^ 2 / ℓ = ℓ * T0 + Λ ^ 2 / ℓ := by
    rw [hT0]; ring
  rw [hRHS]
  have hc5 : cD * T0 ≤ cD * (ℓ * T0) := mul_le_mul_of_nonneg_left hℓT hcD
  have hc6 : cBA * T0 ≤ cBA * (ℓ * T0) := mul_le_mul_of_nonneg_left hℓT hcBA0
  have hc7 : 0 ≤ ℓ * T0 := by positivity
  have hc8 : 0 ≤ (256 * cD + cBA + 38 * cU) * (Λ ^ 2 / ℓ) := by positivity
  have hc9 : ℓ * (cU * T0) = cU * (ℓ * T0) := by ring
  have hexp : (256 * cD + cBA + 38 * cU + 7) * (ℓ * T0 + Λ ^ 2 / ℓ) =
      256 * (cD * (ℓ * T0)) + cBA * (ℓ * T0) + 38 * (cU * (ℓ * T0)) + 7 * (ℓ * T0) +
        (256 * cD + cBA + 38 * cU) * (Λ ^ 2 / ℓ) + 7 * (Λ ^ 2 / ℓ) := by ring
  rw [hexp]
  linarith [hDb, hBA, hY, hΛ3, hℓU, hc5, hc6, hc7, hc8, hc9]

/-! ### Averages and the diagonal large deviation -/

/-- An average of vectors of norm at most `b` has norm at most `b`. -/
private lemma sc_avg_le {N : ℕ} (hN : 0 < N) (f : Fin N → ℂ) {b : ℝ}
    (hf : ∀ i, ‖f i‖ ≤ b) : ‖(N : ℂ)⁻¹ * ∑ i, f i‖ ≤ b := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ i, f i‖ ≤ (N : ℝ)⁻¹ * (N * b) := by
        gcongr
        refine (norm_sum_le _ _).trans ?_
        calc ∑ i, ‖f i‖ ≤ ∑ _i : Fin N, b := Finset.sum_le_sum fun i _ => hf i
          _ = N * b := by simp
    _ = b := by field_simp

/-- `Λ ≤ Λ_d`. -/
private lemma sc_lamAvg_le_lamD {N : ℕ} (hN : 0 < N) (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    lamAvg H z ≤ lamD H z := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hw_eq : stieltjesM H z - msc z =
      (N : ℂ)⁻¹ * ∑ i, (resolventC H z i i - msc z) := by
    unfold stieltjesM
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Matrix.trace]
    simp only [Matrix.diag]
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  unfold lamAvg
  rw [hw_eq]
  exact sc_avg_le hN _ fun i => norm_resolventC_sub_msc_le_lamD i

private lemma sc_map_diag {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) (i : Fin N) :
    L.law.map (fun ω : Entries N => ω.1 i) = L.diag i := by
  have := hL.diag
  have := hL.off
  have h1 : MeasurePreserving (fun ω : Entries N => ω.1) L.law (Measure.pi L.diag) :=
    measurePreserving_fst
  exact ((measurePreserving_eval L.diag i).comp h1).map_eq

private lemma sc_ae_diag_le {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) {q : ℝ}
    (hq : L.BoundedSupportAS q) (i : Fin N) : ∀ᵐ ω ∂L.law, |ω.1 i| ≤ q⁻¹ := by
  have hm : Measurable (fun ω : Entries N => ω.1 i) := (measurable_pi_apply i).comp measurable_fst
  have hA : MeasurableSet {x : ℝ | q⁻¹ < |x|} := measurableSet_lt measurable_const measurable_abs
  rw [ae_iff]
  have : {ω : Entries N | ¬ |ω.1 i| ≤ q⁻¹} =
      (fun ω : Entries N => ω.1 i) ⁻¹' {x : ℝ | q⁻¹ < |x|} := by
    ext ω
    simp
  rw [this, ← Measure.map_apply hm hA, sc_map_diag hL i]
  exact hq.1 i

/-- Large deviation bound for the diagonal average `N⁻¹ Σ h_ii` ((3.19) of [15]). -/
private lemma sc_diag_avg :
    ∃ C > 0, ∀ {N : ℕ} {L : EntryLaws N} {C0 q : ℝ}, L.IsGenWigner C0 → L.BoundedSupportAS q →
      0 ≤ C0 → 1 ≤ q → 0 < N → ∀ s : ℝ, 0 < s →
      L.law {ω | s * ((1 + Real.sqrt (1 + C0)) / N) ≤
        ‖(N : ℂ)⁻¹ * ∑ i, (symOfEntries ω i i : ℂ)‖} ≤
        ENNReal.ofReal (C * Real.exp (-s / C)) := by
  obtain ⟨C, hC, hLD⟩ := largeDev_linear
  refine ⟨C, hC, ?_⟩
  intro N L C0 q hL hq hC0 hq1 hN s hs
  have hprob := EntryLaws.isProbabilityMeasure_law hL.isProb
  have hq0 : 0 < q := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hind : iIndepFun (fun (i : Fin N) (ω : Entries N) => ω.1 i) L.law :=
    (EntryLaws.iIndepFun_entryCoord hL.isProb).precomp (Sum.inl_injective (β := OffDiag N))
  have hmeas : ∀ i : Fin N, Measurable (fun ω : Entries N => ω.1 i) := fun i =>
    (measurable_pi_apply i).comp measurable_fst
  have hint : ∀ (i : Fin N) (f : ℝ → ℝ), AEStronglyMeasurable f (L.diag i) →
      ∫ ω, f (ω.1 i) ∂L.law = ∫ x, f x ∂(L.diag i) := fun i f hf => by
    have h := integral_map (μ := L.law) (hmeas i).aemeasurable (f := f)
      (by rw [sc_map_diag hL.isProb i]; exact hf)
    rw [sc_map_diag hL.isProb i] at h
    exact h.symm
  have h0 : ∀ i : Fin N, ∫ ω, ω.1 i ∂L.law = 0 := fun i => by
    rw [hint i (fun x => x) (by fun_prop)]
    exact hL.mean_diag i
  have hvar : ∀ i : Fin N, ∫ ω, (ω.1 i) ^ 2 ∂L.law ≤ (1 + C0) / N := fun i => by
    rw [hint i (fun x => x ^ 2) (by fun_prop)]
    have h := hL.var_diag i
    rw [abs_le] at h
    have : (1 + C0) / (N : ℝ) = (N : ℝ)⁻¹ + C0 * (N : ℝ)⁻¹ := by field_simp
    rw [this]
    linarith [h.2]
  set A : Fin N → ℂ := fun _ => (N : ℂ)⁻¹ with hA
  have hAn : ∀ i, ‖A i‖ = (N : ℝ)⁻¹ := fun i => by
    simp [hA]
  have hsup : (⨆ i, ‖A i‖) = (N : ℝ)⁻¹ := by
    simp only [hAn]
    exact ciSup_const
  have hsum : ∑ i, ‖A i‖ ^ 2 = (N : ℝ)⁻¹ := by
    simp only [hAn]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hsqrt : Real.sqrt ((1 + C0) / N * (N : ℝ)⁻¹) = Real.sqrt (1 + C0) / N := by
    have : (1 + C0) / (N : ℝ) * (N : ℝ)⁻¹ = (1 + C0) / (N : ℝ) ^ 2 := by field_simp
    rw [this, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hNr.le]
  have hbr : (⨆ i, ‖A i‖) / q + Real.sqrt ((1 + C0) / N * ∑ i, ‖A i‖ ^ 2) =
      (N : ℝ)⁻¹ / q + Real.sqrt (1 + C0) / N := by
    rw [hsup, hsum, hsqrt]
  have hpos : 0 < (⨆ i, ‖A i‖) / q + Real.sqrt ((1 + C0) / N * ∑ i, ‖A i‖ ^ 2) := by
    rw [hbr]
    have : 0 < (N : ℝ)⁻¹ / q := by positivity
    have : 0 ≤ Real.sqrt (1 + C0) / N := by positivity
    linarith
  have hLD' := hLD L.law N (fun i ω => ω.1 i) hind hmeas h0 q ((1 + C0) / N) hq0
    (fun i => sc_ae_diag_le hL.isProb hq i) hvar A hpos s hs
  refine le_trans (measure_mono ?_) hLD'
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have hS : ∑ i, A i * ((ω.1 i : ℝ) : ℂ) = (N : ℂ)⁻¹ * ∑ i, (symOfEntries ω i i : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hA, symOfEntries]
  rw [hS, hbr]
  refine le_trans (mul_le_mul_of_nonneg_left ?_ hs.le) hω
  have h1 : (N : ℝ)⁻¹ / q ≤ (N : ℝ)⁻¹ := div_le_self (by positivity) hq1
  have h2 : (1 + Real.sqrt (1 + C0)) / N = (N : ℝ)⁻¹ + Real.sqrt (1 + C0) / N := by
    field_simp
  rw [h2]
  linarith

/-- The a.e. bound on all diagonal entries. -/
private lemma sc_ae_diag_entries {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) {q : ℝ}
    (hq : L.BoundedSupportAS q) : ∀ᵐ ω ∂L.law, ∀ i : Fin N, |symOfEntries ω i i| ≤ q⁻¹ := by
  refine ae_all_iff.2 fun i => ?_
  filter_upwards [sc_ae_diag_le hL hq i] with ω hω
  simpa [symOfEntries] using hω

/-- The control parameter `Ψ` of (3.26) of [15] is comparable to `(N η)^{-1/2}` on `Ω(z)`. -/
private lemma sc_psi {N : ℕ} (hN : 0 < N) {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ}
    (hre : |z.re| ≤ 5) (him : 0 < z.im) (hle : z.im ≤ 10) (hΛ : lamAvg H z ≤ 1 / 64) :
    0 ≤ psiCtrl H z ∧ 1 / (N : ℝ) ≤ 256 * psiCtrl H z ^ 2 ∧
      psiCtrl H z ^ 2 ≤ 2 / (N * z.im) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNη : 0 < (N : ℝ) * z.im := mul_pos hNr him
  have hmi := im_msc_pos him
  have hΛ0 : 0 ≤ lamAvg H z := norm_nonneg _
  have hsq : psiCtrl H z ^ 2 = (lamAvg H z + (msc z).im) / (N * z.im) := by
    unfold psiCtrl
    rw [Real.sq_sqrt (by positivity)]
  refine ⟨Real.sqrt_nonneg _, ?_, ?_⟩
  · rw [hsq]
    have h1 := sc_im_msc_ge hre him hle
    have h2 : (msc z).im / (N * z.im) ≤ (lamAvg H z + (msc z).im) / (N * z.im) :=
      div_le_div_of_nonneg_right (by linarith) hNη.le
    have h3 : z.im / 256 / (N * z.im) ≤ (msc z).im / (N * z.im) :=
      div_le_div_of_nonneg_right h1 hNη.le
    have h4 : z.im / 256 / (N * z.im) = 1 / (256 * N) := by
      field_simp
    have h5 : 1 / (N : ℝ) = 256 * (1 / (256 * N)) := by
      field_simp
    rw [h5]
    linarith
  · rw [hsq]
    refine div_le_div_of_nonneg_right ?_ hNη.le
    have := (sc_msc_norm hre him hle).2
    have h2 := Complex.im_le_norm (msc z)
    linarith

/-! ### The parameter window -/

/-- The parameter inequalities for `s ∈ [φ^ζ, φ^{ζ+3}]`, `q ≥ φ^{4ζ+15}` and
`z ∈ S(4ζ+15)`, for all large `N`. -/
private lemma sc_params {ζ : ℝ} (hζ : 0 < ζ) {B : ℝ} (hB : 1 ≤ B) :
    ∀ᶠ N : ℕ in atTop, 3 ≤ N ∧ ∀ (q s : ℝ) (z : ℂ), phi N ^ (4 * ζ + 15) ≤ q →
      z ∈ specDomain N (4 * ζ + 15) → phi N ^ ζ ≤ s → s ≤ phi N ^ (ζ + 3) →
      1 ≤ Real.log N ∧ B ≤ s ∧ Real.log N + 1 ≤ s ∧ 1 ≤ q ∧ s * Real.log N ≤ q ∧
      (|z.re| ≤ 5 ∧ 0 < z.im ∧ z.im ≤ 10) ∧
      ∀ Ψ : ℝ, 0 ≤ Ψ → Ψ ^ 2 ≤ 2 / (N * z.im) → s ^ 2 * Real.log N * Ψ ≤ 1 := by
  filter_upwards [eventually_mul_log_add_one_le_phi_rpow hζ B,
    eventually_mul_log_add_one_le_phi_rpow (a := 1) one_pos 2] with N h1 h2
  obtain ⟨hN3, hBs⟩ := h1
  obtain ⟨-, hφ⟩ := h2
  refine ⟨hN3, fun q s z hqK hz hs1 hs2 => ?_⟩
  have hφ1 := sc_one_le_phi hN3
  have hφ0 : 0 < phi N := sc_phi_pos hN3
  have hℓ1 : 1 ≤ Real.log N := by
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hBs' : B ≤ s := by
    calc B = B * 1 := (mul_one B).symm
      _ ≤ B * (Real.log N + 1) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ ≤ phi N ^ ζ := hBs
      _ ≤ s := hs1
  have hℓs : Real.log N + 1 ≤ s := by
    calc Real.log N + 1 = 1 * (Real.log N + 1) := (one_mul _).symm
      _ ≤ B * (Real.log N + 1) := mul_le_mul_of_nonneg_right hB (by linarith)
      _ ≤ phi N ^ ζ := hBs
      _ ≤ s := hs1
  have hs0 : 0 < s := by linarith
  have hKnn : 0 ≤ 4 * ζ + 15 := by positivity
  have hq1 : 1 ≤ q := le_trans (Real.one_le_rpow hφ1 hKnn) hqK
  have hφ1' : phi N ^ (1 : ℝ) = phi N := Real.rpow_one _
  rw [hφ1'] at hφ
  have hℓφ : Real.log N ≤ phi N := by linarith
  have hφ2 : 2 ≤ phi N := by linarith
  have hsℓ : s * Real.log N ≤ q := by
    have h1 : s * Real.log N ≤ phi N ^ (ζ + 3) * phi N :=
      mul_le_mul hs2 hℓφ (by linarith) (Real.rpow_nonneg hφ0.le _)
    have h2 : phi N ^ (ζ + 3) * phi N = phi N ^ (ζ + 3 + 1) := by
      rw [Real.rpow_add hφ0 (ζ + 3) 1, Real.rpow_one]
    have h3 : phi N ^ (ζ + 3 + 1) ≤ phi N ^ (4 * ζ + 15) :=
      sc_rpow_mono hN3 (by linarith)
    linarith
  obtain ⟨hzre, hzim, hzle, hzNη⟩ := sc_specDomain hN3 hz
  refine ⟨hℓ1, hBs', hℓs, hq1, hsℓ, ⟨hzre, hzim, hzle⟩, fun Ψ hΨ hΨsq => ?_⟩
  -- `(s² ℓ Ψ)² ≤ 2/φ ≤ 1`
  set X : ℝ := phi N ^ (4 * ζ + 12) with hX
  have hXpos : 0 < X := Real.rpow_pos_of_pos hφ0 _
  have hsplit : phi N ^ (4 * ζ + 15) = X * phi N ^ 3 := by
    rw [hX, show 4 * ζ + 15 = (4 * ζ + 12) + (3 : ℕ) by push_cast; ring, Real.rpow_add hφ0,
      Real.rpow_natCast]
  have hs4 : s ^ 4 ≤ X := by
    have e : (phi N ^ (ζ + 3)) ^ 4 = X := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sc_rpow_sq hφ0, sc_rpow_sq hφ0, hX]
      ring_nf
    rw [← e]
    exact pow_le_pow_left₀ hs0.le hs2 4
  have hℓsq : Real.log N ^ 2 ≤ phi N ^ 2 := by
    have : 0 ≤ Real.log N := by linarith
    gcongr
  have hφ3 : 0 < phi N ^ 3 := by positivity
  have hNη : X * phi N ^ 3 < N * z.im := by rw [← hsplit]; exact hzNη
  have hΨb : Ψ ^ 2 ≤ 2 / (X * phi N ^ 3) :=
    hΨsq.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) hNη.le)
  have hsq : (s ^ 2 * Real.log N * Ψ) ^ 2 ≤ 1 := by
    have e : (s ^ 2 * Real.log N * Ψ) ^ 2 = s ^ 4 * Real.log N ^ 2 * Ψ ^ 2 := by ring
    rw [e]
    have h1 : s ^ 4 * Real.log N ^ 2 * Ψ ^ 2 ≤ X * phi N ^ 2 * (2 / (X * phi N ^ 3)) := by
      gcongr
    have h2 : X * phi N ^ 2 * (2 / (X * phi N ^ 3)) = 2 / phi N := by
      field_simp
    rw [h2] at h1
    have h3 : 2 / phi N ≤ 1 := by
      rw [div_le_one hφ0]
      exact hφ2
    linarith
  have hnn : 0 ≤ s ^ 2 * Real.log N * Ψ := by
    have : 0 ≤ Real.log N := by linarith
    positivity
  nlinarith

/-! ### Both estimates outside one small exceptional event -/

/-- (3.40) and (3.42) of [15] at a level `s`, outside an event of probability at most `e^{-cs}`. -/
private theorem sc_core {ζ C0 : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) :
    ∃ K > 0, ∃ C > 0, ∃ c > 0, ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (L : EntryLaws N) (q s : ℝ) (z : ℂ),
      L.IsGenWigner C0 → L.BoundedSupportAS q → phi N ^ K ≤ q → z ∈ specDomain N K →
      phi N ^ ζ ≤ s → s ≤ phi N ^ (ζ + 3) →
      ∃ Bad : Set (Entries N), L.law Bad ≤ ENNReal.ofReal (Real.exp (-c * s)) ∧
        ∀ ω : Entries N, lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ → ω ∉ Bad →
          ‖(1 - msc z ^ 2) * (stieltjesM (symOfEntries ω) z - msc z) -
            msc z ^ 3 * (stieltjesM (symOfEntries ω) z - msc z) ^ 2 -
            msc z ^ 2 * zAvg (symOfEntries ω) z‖ ≤
            C * (s ^ 2 * Real.log N / q ^ 2 +
              s ^ 4 * Real.log N * psiCtrl (symOfEntries ω) z ^ 2 +
              lamAvg (symOfEntries ω) z ^ 2 / Real.log N) ∧
          ‖(1 - msc z ^ 2) * (stieltjesM (symOfEntries ω) z - msc z) -
            msc z ^ 3 * (stieltjesM (symOfEntries ω) z - msc z) ^ 2‖ ≤
            C * (lamAvg (symOfEntries ω) z ^ 2 / Real.log N + s / q +
              s ^ 2 * psiCtrl (symOfEntries ω) z) := by
  obtain ⟨K2, hK2, C2, hC2, c2, hc2, N2, h2⟩ := lamO_le_on_omega_level hζ hC0
  obtain ⟨K3, hK3, C3, hC3, c3, hc3, N3, h3⟩ := norm_zFluct_le_on_omega hζ hC0
  obtain ⟨CD, hCD, hdiag⟩ := sc_diag_avg
  obtain ⟨cD0, hcD0d⟩ : ∃ x : ℝ, x = 1 + Real.sqrt (1 + C0) := ⟨_, rfl⟩
  have hcD0 : 0 ≤ cD0 := by rw [hcD0d]; positivity
  obtain ⟨C1, hC1⟩ : ∃ x : ℝ, x = 256 * cD0 + (320 + 44 * C2 ^ 2) +
      38 * (3 * (1 + 2 * C3 ^ 2 + 2 * (320 + 44 * C2 ^ 2))) + 7 := ⟨_, rfl⟩
  have hC1pos : 0 < C1 := by
    have h1 : 0 ≤ C2 ^ 2 := sq_nonneg _
    have h2 : 0 ≤ C3 ^ 2 := sq_nonneg _
    rw [hC1]
    linarith
  obtain ⟨c', hc'⟩ : ∃ x : ℝ, x = min c2 (min c3 (1 / (2 * CD))) := ⟨_, rfl⟩
  have hc'0 : 0 < c' := by rw [hc']; exact lt_min hc2 (lt_min hc3 (by positivity))
  have hc'2 : c' ≤ c2 := by rw [hc']; exact min_le_left _ _
  have hc'3 : c' ≤ c3 := by rw [hc']; exact (min_le_right _ _).trans (min_le_left _ _)
  have hc'4 : c' ≤ 1 / (2 * CD) := by rw [hc']; exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨B, hBd⟩ : ∃ x : ℝ, x = 64 + 4 / c' + 2 * CD * (1 + |Real.log CD|) := ⟨_, rfl⟩
  have hB4 : 4 / c' ≤ B := by
    have h2 : 0 ≤ 2 * CD * (1 + |Real.log CD|) := by positivity
    rw [hBd]; linarith
  have hB64 : 64 ≤ B := by
    have h1 : 0 ≤ 4 / c' := by positivity
    have h2 : 0 ≤ 2 * CD * (1 + |Real.log CD|) := by positivity
    rw [hBd]; linarith
  have hBLD : 2 * CD * |Real.log CD| ≤ B := by
    have h1 : 0 ≤ 4 / c' := by positivity
    have h2 : 0 ≤ 2 * CD := by positivity
    have h3 : 2 * CD * (1 + |Real.log CD|) = 2 * CD + 2 * CD * |Real.log CD| := by ring
    rw [hBd, h3]; linarith
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (sc_params hζ (B := B) (by linarith))
  refine ⟨max (max K2 K3) (4 * ζ + 15), lt_max_of_lt_right (by linarith), C1 + C3,
    by linarith, c' / 2 / 2, by positivity, max N0 (max N2 N3), ?_⟩
  intro N hN L q s z hL hq hqK hz hs1 hs2
  obtain ⟨hN3, hpar⟩ := hN0 N (le_trans (le_max_left _ _) hN)
  have hN2 : N2 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN3' : N3 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hK2le : K2 ≤ max (max K2 K3) (4 * ζ + 15) := (le_max_left _ _).trans (le_max_left _ _)
  have hK3le : K3 ≤ max (max K2 K3) (4 * ζ + 15) := (le_max_right _ _).trans (le_max_left _ _)
  have hK4le : 4 * ζ + 15 ≤ max (max K2 K3) (4 * ζ + 15) := le_max_right _ _
  have hqK2 : phi N ^ K2 ≤ q := (sc_rpow_mono hN3 hK2le).trans hqK
  have hqK3 : phi N ^ K3 ≤ q := (sc_rpow_mono hN3 hK3le).trans hqK
  have hqK' : phi N ^ (4 * ζ + 15) ≤ q := (sc_rpow_mono hN3 hK4le).trans hqK
  have hz2 : z ∈ specDomain N K2 := sc_specDomain_mono hN3 hK2le hz
  have hz3 : z ∈ specDomain N K3 := sc_specDomain_mono hN3 hK3le hz
  have hz' : z ∈ specDomain N (4 * ζ + 15) := sc_specDomain_mono hN3 hK4le hz
  obtain ⟨hℓ1, hBs, hℓs, hq1, hsℓ, ⟨hzre, hzim, hzle⟩, hΨpar⟩ := hpar q s z hqK' hz' hs1 hs2
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hs0 : 0 < s := by linarith
  have hq0 : 0 < q := by linarith
  have hℓ0 : 0 < Real.log N := by linarith
  have hs64 : 64 ≤ s := by linarith
  have hs164 : s⁻¹ ≤ 1 / 64 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) hs64
  have hsℓ' : s⁻¹ ≤ 1 / Real.log N := by
    rw [one_div]
    exact inv_anti₀ hℓ0 (by linarith)
  have hs2c : 2 / c' ≤ s := by
    have : 2 / c' ≤ 4 / c' := div_le_div_of_nonneg_right (by norm_num) hc'0.le
    linarith
  have hsLD : 2 * CD * |Real.log CD| ≤ s := by linarith
  -- the exceptional events
  set B1 : Set (Entries N) := {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
    C2 * (1 / q + s ^ 2 * psiCtrl (symOfEntries ω) z) < lamO (symOfEntries ω) z} with hB1d
  set B2 : Set (Entries N) := {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
    C3 * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) <
      ⨆ i, ‖zFluct (symOfEntries ω) z i‖} with hB2d
  set B3 : Set (Entries N) := {ω | s * ((1 + Real.sqrt (1 + C0)) / N) ≤
    ‖(N : ℂ)⁻¹ * ∑ i, (symOfEntries ω i i : ℂ)‖} with hB3d
  set B4 : Set (Entries N) := {ω | ¬ ∀ i : Fin N, |symOfEntries ω i i| ≤ q⁻¹} with hB4d
  have hT2 : L.law B1 ≤ ENNReal.ofReal (Real.exp (-c2 * s)) :=
    h2 N hN2 L q s z hL hq hqK2 hz2 hs1 hs2
  have hT3 : L.law B2 ≤ ENNReal.ofReal (Real.exp (-c3 * s)) :=
    h3 N hN3' L q s z hL hq hqK3 hz3 hs1 hs2
  have hT4 : L.law B3 ≤ ENNReal.ofReal (CD * Real.exp (-s / CD)) :=
    hdiag hL hq hC0 hq1 hNpos s hs0
  have hnull : L.law B4 = 0 := ae_iff.mp (sc_ae_diag_entries hL.isProb hq)
  refine ⟨((B1 ∪ B2) ∪ B3) ∪ B4, ?_, ?_⟩
  · have hmono : ∀ a b : ℝ, a ≤ b → Real.exp (-b * s) ≤ Real.exp (-a * s) := fun a b hab =>
      Real.exp_le_exp.mpr (by
        rw [neg_mul, neg_mul]
        exact neg_le_neg (mul_le_mul_of_nonneg_right hab hs0.le))
    have y1 : Real.exp (-c2 * s) ≤ Real.exp (-c' * s) := hmono _ _ hc'2
    have y2 : Real.exp (-c3 * s) ≤ Real.exp (-c' * s) := hmono _ _ hc'3
    have y3 : CD * Real.exp (-s / CD) ≤ Real.exp (-c' * s) :=
      (sc_exp_tail hCD hsLD).trans (hmono _ _ hc'4)
    have y3' : CD * Real.exp (-s / CD) ≤ Real.exp (-(c' / 2) * s) :=
      y3.trans (hmono _ _ (by linarith))
    have y12 := add_le_exp_neg_half_mul_of_le_exp hc'0 hs2c y1 y2
    have hs2c' : 2 / (c' / 2) ≤ s := by
      have : 2 / (c' / 2) = 4 / c' := by field_simp; ring
      rw [this]
      linarith
    have y123 := add_le_exp_neg_half_mul_of_le_exp (by positivity : 0 < c' / 2) hs2c' y12 y3'
    calc L.law (((B1 ∪ B2) ∪ B3) ∪ B4)
        ≤ L.law ((B1 ∪ B2) ∪ B3) + L.law B4 := measure_union_le _ _
      _ ≤ (L.law (B1 ∪ B2) + L.law B3) + L.law B4 := add_le_add (measure_union_le _ _) le_rfl
      _ ≤ ((L.law B1 + L.law B2) + L.law B3) + L.law B4 :=
          add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl
      _ ≤ ((ENNReal.ofReal (Real.exp (-c2 * s)) + ENNReal.ofReal (Real.exp (-c3 * s))) +
            ENNReal.ofReal (CD * Real.exp (-s / CD))) + 0 := by
          rw [hnull]
          exact add_le_add (add_le_add (add_le_add hT2 hT3) hT4) le_rfl
      _ = ENNReal.ofReal (Real.exp (-c2 * s) + Real.exp (-c3 * s) +
            CD * Real.exp (-s / CD)) := by
          rw [add_zero, ← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal (Real.exp (-(c' / 2 / 2) * s)) := ENNReal.ofReal_le_ofReal y123
  · intro ω hΩ hnb
    rw [Set.mem_union, Set.mem_union, Set.mem_union, not_or, not_or, not_or] at hnb
    obtain ⟨⟨⟨hn1, hn2⟩, hn3⟩, hn4⟩ := hnb
    have hHerm := symOfEntries_isHermitian ω
    have hΩ' : lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ 1 / 64 := hΩ.trans hs164
    have hmsc := sc_msc_norm hzre hzim hzle
    have hΛo : lamO (symOfEntries ω) z ≤
        C2 * (1 / q + s ^ 2 * psiCtrl (symOfEntries ω) z) :=
      not_lt.mp fun hlt => hn1 ⟨hΩ, hlt⟩
    have hZsup : (⨆ i, ‖zFluct (symOfEntries ω) z i‖) ≤
        C3 * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) :=
      not_lt.mp fun hlt => hn2 ⟨hΩ, hlt⟩
    have hZi : ∀ i, ‖zFluct (symOfEntries ω) z i‖ ≤
        C3 * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) := fun i =>
      (le_ciSup (f := fun i => ‖zFluct (symOfEntries ω) z i‖)
        (Set.finite_range _).bddAbove i).trans hZsup
    have hDlt : ‖(N : ℂ)⁻¹ * ∑ i, (symOfEntries ω i i : ℂ)‖ <
        s * ((1 + Real.sqrt (1 + C0)) / N) := not_le.mp hn3
    have hdq : ∀ i, |symOfEntries ω i i| ≤ q⁻¹ := not_not.mp hn4
    have hO0 := sc_lamO_nonneg (symOfEntries ω) z
    have hD0 := sc_lamD_nonneg (symOfEntries ω) z
    have hΛle : lamAvg (symOfEntries ω) z ≤ 1 / 64 :=
      (sc_lamAvg_le_lamD hNpos _ _).trans (by linarith)
    have hΛs : lamAvg (symOfEntries ω) z ≤ 1 / Real.log N :=
      (sc_lamAvg_le_lamD hNpos _ _).trans ((by linarith : lamD (symOfEntries ω) z ≤ s⁻¹).trans hsℓ')
    obtain ⟨hΨ0, hΨn, hΨ2⟩ := sc_psi hNpos hzre hzim hzle hΛle
    have hΨ1 := hΨpar _ hΨ0 hΨ2
    have hA : ∀ i, ‖aCorr (symOfEntries ω) z i‖ ≤ 5 / (4 * (N : ℝ)) +
        22 * lamO (symOfEntries ω) z ^ 2 := fun i =>
      sc_aCorr_le hNpos hmsc.1 hmsc.2 hΩ' i
    have hU : ∀ i, ‖upsilon (symOfEntries ω) z i‖ ≤
        1 / q + C3 * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) +
          (5 / (4 * (N : ℝ)) + 22 * lamO (symOfEntries ω) z ^ 2) := fun i => by
      unfold upsilon
      have h1 : ‖((symOfEntries ω i i : ℝ) : ℂ)‖ ≤ 1 / q := by
        rw [Complex.norm_real, Real.norm_eq_abs, one_div]
        exact hdq i
      have h2 := norm_sub_le ((symOfEntries ω i i : ℝ) : ℂ) (zFluct (symOfEntries ω) z i)
      have h4 := norm_add_le (((symOfEntries ω i i : ℝ) : ℂ) - zFluct (symOfEntries ω) z i)
        (aCorr (symOfEntries ω) z i)
      linarith [hZi i, hA i]
    have hdet := sc_det hNpos hHerm hzim hmsc.1 hmsc.2 hΩ' hU hA
    have hchain := sc_chain (ℓ := Real.log N) (s := s) (q := q) (n := (N : ℝ))
      (Ψ := psiCtrl (symOfEntries ω) z) (Λ := lamAvg (symOfEntries ω) z)
      (lo := lamO (symOfEntries ω) z)
      (D := ‖(N : ℂ)⁻¹ * ∑ i, (symOfEntries ω i i : ℂ)‖) (C2 := C2) (C3 := C3) (cD := cD0)
      hℓ1 (by linarith) hq1 (by exact_mod_cast hNpos) hΨ0 hΛs hC2 hC3 hcD0 hΨn hO0
      (by linarith) hΛo (by
        rw [hcD0d, mul_div_assoc]
        exact hDlt.le)
    have hE1 := hdet.trans hchain
    have hT1nn : 0 ≤ s ^ 2 * Real.log N / q ^ 2 +
        s ^ 4 * Real.log N * psiCtrl (symOfEntries ω) z ^ 2 +
        lamAvg (symOfEntries ω) z ^ 2 / Real.log N := by positivity
    rw [← hC1] at hE1
    have hE1' : ‖(1 - msc z ^ 2) * (stieltjesM (symOfEntries ω) z - msc z) -
            msc z ^ 3 * (stieltjesM (symOfEntries ω) z - msc z) ^ 2 -
            msc z ^ 2 * zAvg (symOfEntries ω) z‖ ≤
        C1 * (s ^ 2 * Real.log N / q ^ 2 +
              s ^ 4 * Real.log N * psiCtrl (symOfEntries ω) z ^ 2 +
              lamAvg (symOfEntries ω) z ^ 2 / Real.log N) := hE1
    refine ⟨hE1'.trans (mul_le_mul_of_nonneg_right (by linarith) hT1nn), ?_⟩
    -- the weak form
    have hzAvg : ‖zAvg (symOfEntries ω) z‖ ≤
        C3 * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) :=
      sc_avg_le hNpos (fun i => zFluct (symOfEntries ω) z i) hZi
    have e : (1 - msc z ^ 2) * (stieltjesM (symOfEntries ω) z - msc z) -
          msc z ^ 3 * (stieltjesM (symOfEntries ω) z - msc z) ^ 2 =
        ((1 - msc z ^ 2) * (stieltjesM (symOfEntries ω) z - msc z) -
          msc z ^ 3 * (stieltjesM (symOfEntries ω) z - msc z) ^ 2 -
          msc z ^ 2 * zAvg (symOfEntries ω) z) + msc z ^ 2 * zAvg (symOfEntries ω) z := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have hm2 : ‖msc z ^ 2 * zAvg (symOfEntries ω) z‖ ≤ ‖zAvg (symOfEntries ω) z‖ := by
      rw [norm_mul, norm_pow]
      have : ‖msc z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hmsc.2
      calc ‖msc z‖ ^ 2 * ‖zAvg (symOfEntries ω) z‖ ≤ 1 * ‖zAvg (symOfEntries ω) z‖ := by gcongr
        _ = ‖zAvg (symOfEntries ω) z‖ := one_mul _
    have hsq1 : s ^ 2 * Real.log N / q ^ 2 ≤ s / q := by
      rw [div_le_div_iff₀ (by positivity) hq0]
      calc s ^ 2 * Real.log N * q = (s * q) * (s * Real.log N) := by ring
        _ ≤ (s * q) * q := mul_le_mul_of_nonneg_left hsℓ (by positivity)
        _ = s * q ^ 2 := by ring
    have hsq2 : s ^ 4 * Real.log N * psiCtrl (symOfEntries ω) z ^ 2 ≤
        s ^ 2 * psiCtrl (symOfEntries ω) z := by
      calc s ^ 4 * Real.log N * psiCtrl (symOfEntries ω) z ^ 2 =
          (s ^ 2 * psiCtrl (symOfEntries ω) z) *
            (s ^ 2 * Real.log N * psiCtrl (symOfEntries ω) z) := by ring
        _ ≤ (s ^ 2 * psiCtrl (symOfEntries ω) z) * 1 :=
            mul_le_mul_of_nonneg_left hΨ1 (by positivity)
        _ = s ^ 2 * psiCtrl (symOfEntries ω) z := mul_one _
    have hΛℓ : 0 ≤ lamAvg (symOfEntries ω) z ^ 2 / Real.log N := by positivity
    have hT12 : s ^ 2 * Real.log N / q ^ 2 +
        s ^ 4 * Real.log N * psiCtrl (symOfEntries ω) z ^ 2 +
        lamAvg (symOfEntries ω) z ^ 2 / Real.log N ≤
        lamAvg (symOfEntries ω) z ^ 2 / Real.log N + s / q +
          s ^ 2 * psiCtrl (symOfEntries ω) z := by linarith
    have hT2nn : 0 ≤ s / q + s ^ 2 * psiCtrl (symOfEntries ω) z := by positivity
    have h1 : C1 * (s ^ 2 * Real.log N / q ^ 2 +
        s ^ 4 * Real.log N * psiCtrl (symOfEntries ω) z ^ 2 +
        lamAvg (symOfEntries ω) z ^ 2 / Real.log N) ≤
        C1 * (lamAvg (symOfEntries ω) z ^ 2 / Real.log N + s / q +
          s ^ 2 * psiCtrl (symOfEntries ω) z) := mul_le_mul_of_nonneg_left hT12 hC1pos.le
    have h2 : C3 * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) ≤
        C3 * (lamAvg (symOfEntries ω) z ^ 2 / Real.log N + s / q +
          s ^ 2 * psiCtrl (symOfEntries ω) z) := by
      apply mul_le_mul_of_nonneg_left _ hC3.le
      linarith
    linarith

/-! ### The self-consistent equations on `Ω(z)` -/

/-- (3.40) of [15] at a level `s`. -/
theorem selfConsistent_on_omega {ζ C0 : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) :
    ∃ K > 0, ∃ C > 0, ∃ c > 0, ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (L : EntryLaws N) (q s : ℝ) (z : ℂ),
      L.IsGenWigner C0 → L.BoundedSupportAS q → phi N ^ K ≤ q → z ∈ specDomain N K →
      phi N ^ ζ ≤ s → s ≤ phi N ^ (ζ + 3) →
      L.law {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        C * (s ^ 2 * Real.log N / q ^ 2 +
            s ^ 4 * Real.log N * psiCtrl (symOfEntries ω) z ^ 2 +
            lamAvg (symOfEntries ω) z ^ 2 / Real.log N) <
          ‖(1 - msc z ^ 2) * (stieltjesM (symOfEntries ω) z - msc z) -
            msc z ^ 3 * (stieltjesM (symOfEntries ω) z - msc z) ^ 2 -
            msc z ^ 2 * zAvg (symOfEntries ω) z‖} ≤ ENNReal.ofReal (Real.exp (-c * s)) := by
  obtain ⟨K, hK, C, hC, c, hc, N0, h⟩ := sc_core hζ hC0
  refine ⟨K, hK, C, hC, c, hc, N0, ?_⟩
  intro N hN L q s z hL hq hqK hz hs1 hs2
  obtain ⟨Bad, hBad, himp⟩ := h N hN L q s z hL hq hqK hz hs1 hs2
  refine le_trans (measure_mono ?_) hBad
  rintro ω ⟨hΩ, hlt⟩
  by_contra hnb
  exact absurd (himp ω hΩ hnb).1 (not_le.mpr hlt)

/-- (3.42) of [15] at a level `s`. -/
theorem selfConsistent_weak_on_omega {ζ C0 : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) :
    ∃ K > 0, ∃ C > 0, ∃ c > 0, ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (L : EntryLaws N) (q s : ℝ) (z : ℂ),
      L.IsGenWigner C0 → L.BoundedSupportAS q → phi N ^ K ≤ q → z ∈ specDomain N K →
      phi N ^ ζ ≤ s → s ≤ phi N ^ (ζ + 3) →
      L.law {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        C * (lamAvg (symOfEntries ω) z ^ 2 / Real.log N + s / q +
            s ^ 2 * psiCtrl (symOfEntries ω) z) <
          ‖(1 - msc z ^ 2) * (stieltjesM (symOfEntries ω) z - msc z) -
            msc z ^ 3 * (stieltjesM (symOfEntries ω) z - msc z) ^ 2‖} ≤
        ENNReal.ofReal (Real.exp (-c * s)) := by
  obtain ⟨K, hK, C, hC, c, hc, N0, h⟩ := sc_core hζ hC0
  refine ⟨K, hK, C, hC, c, hc, N0, ?_⟩
  intro N hN L q s z hL hq hqK hz hs1 hs2
  obtain ⟨Bad, hBad, himp⟩ := h N hN L q s z hL hq hqK hz hs1 hs2
  refine le_trans (measure_mono ?_) hBad
  rintro ω ⟨hΩ, hlt⟩
  by_contra hnb
  exact absurd (himp ω hΩ hnb).2 (not_le.mpr hlt)

/-! ### Compiled checks -/

/-- For all large `N` the hypotheses of (3.40) and (3.42) hold together for the Rademacher entry
laws, `q = N^{2/5}`, `z = i` and `s = φ^{ζ+1}`. -/
private lemma sc_rad_instance (K ζ : ℝ) : ∀ᶠ N : ℕ in atTop,
    (radLaws N).IsGenWigner 1 ∧ (radLaws N).BoundedSupportAS ((N : ℝ) ^ (2 / 5 : ℝ)) ∧
    phi N ^ K ≤ (N : ℝ) ^ (2 / 5 : ℝ) ∧ (⟨0, 1⟩ : ℂ) ∈ specDomain N K ∧
    phi N ^ ζ ≤ phi N ^ (ζ + 1) ∧ phi N ^ (ζ + 1) ≤ phi N ^ (ζ + 3) := by
  filter_upwards [phi_rpow_le_rpow K (by norm_num : (0 : ℝ) < 2 / 5), eventually_ge_atTop 32]
    with N h1 h2
  have hN : (32 : ℝ) ≤ N := by exact_mod_cast h2
  have hlt : (N : ℝ) ^ (2 / 5 : ℝ) < N := by
    calc (N : ℝ) ^ (2 / 5 : ℝ) < (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
      _ = N := Real.rpow_one _
  refine ⟨radLaws_isGenWigner (by omega), radLaws_boundedSupportAS h2, h1,
    ⟨by simp, ?_, by simp⟩, sc_rpow_mono (by omega) (by linarith),
    sc_rpow_mono (by omega) (by linarith)⟩
  change phi N ^ K / N < 1
  rw [div_lt_one (by linarith)]
  linarith

/-- (3.40) at a level: the estimate applies to the Rademacher laws for all large `N`. -/
example {ζ : ℝ} (hζ : 0 < ζ) : ∃ K > (0 : ℝ), ∃ C > 0, ∃ c > 0, ∀ᶠ N : ℕ in atTop,
    (radLaws N).law {ω | lamD (symOfEntries ω) ⟨0, 1⟩ + lamO (symOfEntries ω) ⟨0, 1⟩ ≤
        (phi N ^ (ζ + 1))⁻¹ ∧
      C * ((phi N ^ (ζ + 1)) ^ 2 * Real.log N / ((N : ℝ) ^ (2 / 5 : ℝ)) ^ 2 +
          (phi N ^ (ζ + 1)) ^ 4 * Real.log N * psiCtrl (symOfEntries ω) ⟨0, 1⟩ ^ 2 +
          lamAvg (symOfEntries ω) ⟨0, 1⟩ ^ 2 / Real.log N) <
        ‖(1 - msc ⟨0, 1⟩ ^ 2) * (stieltjesM (symOfEntries ω) ⟨0, 1⟩ - msc ⟨0, 1⟩) -
          msc ⟨0, 1⟩ ^ 3 * (stieltjesM (symOfEntries ω) ⟨0, 1⟩ - msc ⟨0, 1⟩) ^ 2 -
          msc ⟨0, 1⟩ ^ 2 * zAvg (symOfEntries ω) ⟨0, 1⟩‖} ≤
      ENNReal.ofReal (Real.exp (-c * phi N ^ (ζ + 1))) := by
  obtain ⟨K, hK, C, hC, c, hc, N0, h⟩ := selfConsistent_on_omega hζ (zero_le_one : (0 : ℝ) ≤ 1)
  refine ⟨K, hK, C, hC, c, hc, ?_⟩
  filter_upwards [sc_rad_instance K ζ, eventually_ge_atTop N0] with N hi hN
  exact h N hN (radLaws N) _ _ _ hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2

/-- (3.42) at a level: the estimate applies to the Rademacher laws for all large `N`. -/
example {ζ : ℝ} (hζ : 0 < ζ) : ∃ K > (0 : ℝ), ∃ C > 0, ∃ c > 0, ∀ᶠ N : ℕ in atTop,
    (radLaws N).law {ω | lamD (symOfEntries ω) ⟨0, 1⟩ + lamO (symOfEntries ω) ⟨0, 1⟩ ≤
        (phi N ^ (ζ + 1))⁻¹ ∧
      C * (lamAvg (symOfEntries ω) ⟨0, 1⟩ ^ 2 / Real.log N +
          phi N ^ (ζ + 1) / ((N : ℝ) ^ (2 / 5 : ℝ)) +
          (phi N ^ (ζ + 1)) ^ 2 * psiCtrl (symOfEntries ω) ⟨0, 1⟩) <
        ‖(1 - msc ⟨0, 1⟩ ^ 2) * (stieltjesM (symOfEntries ω) ⟨0, 1⟩ - msc ⟨0, 1⟩) -
          msc ⟨0, 1⟩ ^ 3 * (stieltjesM (symOfEntries ω) ⟨0, 1⟩ - msc ⟨0, 1⟩) ^ 2‖} ≤
      ENNReal.ofReal (Real.exp (-c * phi N ^ (ζ + 1))) := by
  obtain ⟨K, hK, C, hC, c, hc, N0, h⟩ :=
    selfConsistent_weak_on_omega hζ (zero_le_one : (0 : ℝ) ≤ 1)
  refine ⟨K, hK, C, hC, c, hc, ?_⟩
  filter_upwards [sc_rad_instance K ζ, eventually_ge_atTop N0] with N hi hN
  exact h N hN (radLaws N) _ _ _ hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2

#print axioms selfConsistent_on_omega
#print axioms selfConsistent_weak_on_omega

end WEdgeNS
