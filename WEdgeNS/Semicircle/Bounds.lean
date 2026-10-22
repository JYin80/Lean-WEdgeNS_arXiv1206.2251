import WEdgeNS.Semicircle.Msc

/-!
# Lemma 2.6 with explicit constants
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- The quadratic relation `m² + z m + 1 = 0` for `m = m_sc(z)`, valid for every `z`. -/
private lemma bounds_quad (z : ℂ) : msc z ^ 2 + z * msc z + 1 = 0 := by
  have h := sqrtZ4_sq z
  unfold msc
  linear_combination (1 / 4 : ℂ) * h

/-- With `s = x + iy` and `s² = z² - 4`, the squared modulus of `s` lies between `κ + η` and
`13 (κ + η)`, where `κ = ||E| - 2|` and `|E| ≤ 5`, `0 < η ≤ 10`. -/
private lemma bounds_w_sq (E η x y κ : ℝ) (hE : |E| ≤ 5) (hη : 0 < η) (hη10 : η ≤ 10)
    (hk : κ = |(|E| - 2)|) (h1 : x ^ 2 - y ^ 2 = E ^ 2 - η ^ 2 - 4) (h2 : x * y = E * η) :
    κ + η ≤ x ^ 2 + y ^ 2 ∧ x ^ 2 + y ^ 2 ≤ 13 * (κ + η) := by
  have hu0 : 0 ≤ |E| := abs_nonneg E
  have hk2 : κ ^ 2 = (|E| - 2) ^ 2 := by rw [hk, sq_abs]
  have hE2 : E ^ 2 = |E| ^ 2 := (sq_abs E).symm
  have hkn : 0 ≤ κ := by rw [hk]; exact abs_nonneg _
  have hq : (x ^ 2 + y ^ 2) ^ 2 = (κ ^ 2 + η ^ 2) * ((|E| + 2) ^ 2 + η ^ 2) := by
    have : (x ^ 2 + y ^ 2) ^ 2 = (x ^ 2 - y ^ 2) ^ 2 + 4 * (x * y) ^ 2 := by ring
    rw [this, h1, h2, hk2, mul_pow, hE2]; ring
  have hP0 : 0 ≤ κ ^ 2 + η ^ 2 := by positivity
  have hS0 : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  have hT0 : 0 ≤ κ + η := by linarith
  constructor
  · have h3 : (κ + η) ^ 2 ≤ 2 * (κ ^ 2 + η ^ 2) := by nlinarith [sq_nonneg (κ - η)]
    have h4 : 4 ≤ (|E| + 2) ^ 2 + η ^ 2 := by nlinarith [sq_nonneg η]
    have h5 : (κ + η) ^ 2 ≤ (x ^ 2 + y ^ 2) ^ 2 := by
      rw [hq]
      have := mul_le_mul_of_nonneg_left h4 hP0
      linarith
    exact (sq_le_sq₀ hT0 hS0).1 h5
  · have h3 : κ ^ 2 + η ^ 2 ≤ (κ + η) ^ 2 := by nlinarith [mul_nonneg hkn hη.le]
    have h4 : (|E| + 2) ^ 2 + η ^ 2 ≤ 169 := by nlinarith
    have h5 : (x ^ 2 + y ^ 2) ^ 2 ≤ (13 * (κ + η)) ^ 2 := by
      rw [hq]
      have h6 := mul_le_mul_of_nonneg_left h4 hP0
      have h7 := mul_le_mul_of_nonneg_right h3 (by norm_num : (0 : ℝ) ≤ 169)
      nlinarith
    exact (sq_le_sq₀ hS0 (by linarith)).1 h5

/-- Square-root form of the bounds on `‖s‖² = w²`: `t ≤ w ≤ 4 t` for `t² = κ + η`. -/
private lemma bounds_w_sqrt (T t w : ℝ) (ht : t ^ 2 = T) (ht0 : 0 < t) (hw0 : 0 ≤ w)
    (h1 : T ≤ w ^ 2) (h2 : w ^ 2 ≤ 13 * T) : t ≤ w ∧ w ≤ 4 * t := by
  constructor
  · exact (sq_le_sq₀ ht0.le hw0).1 (by rw [ht]; exact h1)
  · exact (sq_le_sq₀ hw0 (by linarith)).1 (by nlinarith)

/-- Upper bound for `Im s` near the edge, outside the bulk: if `η ≤ κ` and `2 ≤ |E|` then
`y t ≤ 4 η`. -/
private lemma bounds_edge_upper (E η x y κ t : ℝ) (hE : |E| ≤ 5) (hη : 0 < η)
    (hk : κ = |(|E| - 2)|) (h1 : x ^ 2 - y ^ 2 = E ^ 2 - η ^ 2 - 4) (h2 : x * y = E * η)
    (ht : t ^ 2 = κ + η) (ht0 : 0 < t) (hy0 : 0 ≤ y) (hηκ : η ≤ κ) (hE2 : 2 ≤ |E|) :
    y * t ≤ 4 * η := by
  have hk' : κ = |E| - 2 := by rw [hk, abs_of_nonneg (by linarith)]
  have hEsq : E ^ 2 = (κ + 2) ^ 2 := by
    have : κ + 2 = |E| := by linarith
    rw [this, sq_abs]
  have hx : 2 * t ^ 2 ≤ x ^ 2 := by nlinarith [sq_nonneg y, mul_nonneg hη.le (sub_nonneg.2 hηκ)]
  have hxy : (x * y) ^ 2 = E ^ 2 * η ^ 2 := by rw [h2, mul_pow]
  have hE25 : E ^ 2 ≤ 25 := by
    have := abs_le.1 (show |E| ≤ 5 from hE)
    nlinarith
  have h3 : y ^ 2 * (2 * t ^ 2) ≤ y ^ 2 * x ^ 2 := mul_le_mul_of_nonneg_left hx (sq_nonneg y)
  have h4 : (y * t) ^ 2 ≤ (4 * η) ^ 2 := by
    have : E ^ 2 * η ^ 2 ≤ 25 * η ^ 2 := mul_le_mul_of_nonneg_right hE25 (sq_nonneg η)
    nlinarith [sq_nonneg η]
  exact (sq_le_sq₀ (by positivity) (by positivity)).1 h4

/-- Lower bound for `Im m` in the bulk, `|E| ≤ 2`, when `η ≤ κ`: `t ≤ 16 b`. -/
private lemma bounds_bulk_lower (E η x y κ t b : ℝ) (hk : κ = |(|E| - 2)|)
    (h1 : x ^ 2 - y ^ 2 = E ^ 2 - η ^ 2 - 4) (ht : t ^ 2 = κ + η) (ht0 : 0 < t)
    (hy : y = 2 * b + η) (hb0 : 0 < b) (hηκ : η ≤ κ) (hE2 : |E| ≤ 2)
    (hyt : y ≤ 4 * t) : t ≤ 16 * b := by
  have hk' : κ = 2 - |E| := by rw [hk, abs_of_nonpos (by linarith)]; ring
  have hEsq : E ^ 2 = |E| ^ 2 := (sq_abs E).symm
  have hu0 : 0 ≤ |E| := abs_nonneg E
  have h3 : 2 * κ + η ^ 2 ≤ y ^ 2 := by nlinarith [sq_nonneg x]
  have h4 : 2 * κ ≤ 4 * b * (b + η) := by
    rw [hy] at h3; nlinarith
  have h5 : 4 * b * (b + η) ≤ 4 * b * (4 * t) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  nlinarith

/-- Lower bound for `Im m` from the identity `b (1 - r²) = r² η`. -/
private lemma bounds_lower_eta (η b r t : ℝ) (hη : 0 < η) (hb0 : 0 < b)
    (hr13 : 1 / 13 ≤ r) (hI : b * (1 - r ^ 2) = r ^ 2 * η) (hf : 1 - r ^ 2 ≤ 4 * t) :
    η ≤ 676 * t * b := by
  have hr2 : 1 / 169 ≤ r ^ 2 := by nlinarith
  have h1 : b * (1 - r ^ 2) ≤ b * (4 * t) := mul_le_mul_of_nonneg_left hf hb0.le
  have h2 : 1 / 169 * η ≤ r ^ 2 * η := mul_le_mul_of_nonneg_right hr2 hη.le
  nlinarith

/-- Real-variable form of Lemma 2.6 for `m = m_sc(z)`, with `t = √(κ + η)`. -/
private lemma bounds_main (z : ℂ) (hE : |z.re| ≤ 5) (hη : 0 < z.im) (hη10 : z.im ≤ 10) :
    (1 / 13 ≤ ‖msc z‖ ∧ ‖msc z‖ ≤ 1) ∧
    (Real.sqrt (kappa z.re + z.im) ≤ 13 * ‖1 - msc z ^ 2‖ ∧
      ‖1 - msc z ^ 2‖ ≤ 4 * Real.sqrt (kappa z.re + z.im)) ∧
    z.im ≤ 676 * Real.sqrt (kappa z.re + z.im) * (msc z).im ∧
    (z.im ≤ kappa z.re → 2 ≤ |z.re| →
      (msc z).im * Real.sqrt (kappa z.re + z.im) ≤ 2 * z.im) ∧
    (|z.re| ≤ 2 → z.im ≤ kappa z.re →
      Real.sqrt (kappa z.re + z.im) ≤ 16 * (msc z).im) ∧
    (msc z).im ≤ 2 * Real.sqrt (kappa z.re + z.im) := by
  obtain ⟨hn1, hn2⟩ := norm_msc_eq_inv_and_lt_one hη
  have hbpos := im_msc_pos hη
  have hq := bounds_quad z
  have hR1 : (msc z).re ^ 2 - (msc z).im ^ 2 + z.re * (msc z).re - z.im * (msc z).im + 1 = 0 := by
    have := congrArg Complex.re hq
    simp [pow_two] at this
    linarith
  have hR2 : 2 * (msc z).re * (msc z).im + z.re * (msc z).im + z.im * (msc z).re = 0 := by
    have := congrArg Complex.im hq
    simp [pow_two] at this
    linarith
  have hr2 : ‖msc z‖ ^ 2 = (msc z).re ^ 2 + (msc z).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hw2 : ‖2 * msc z + z‖ ^ 2 = (2 * (msc z).re + z.re) ^ 2 + (2 * (msc z).im + z.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hy : (2 * msc z + z).im = 2 * (msc z).im + z.im := by simp
  have hI : (msc z).im * (1 - ‖msc z‖ ^ 2) = ‖msc z‖ ^ 2 * z.im := by
    rw [hr2]; linear_combination (msc z).im * hR1 - (msc z).re * hR2
  have h1 : (2 * (msc z).re + z.re) ^ 2 - (2 * (msc z).im + z.im) ^ 2 =
      z.re ^ 2 - z.im ^ 2 - 4 := by linear_combination 4 * hR1
  have h2 : (2 * (msc z).re + z.re) * (2 * (msc z).im + z.im) = z.re * z.im := by
    linear_combination 2 * hR2
  have hk : kappa z.re = |(|z.re| - 2)| := rfl
  have hkn : 0 ≤ kappa z.re := abs_nonneg _
  -- `‖m‖ ≥ 1/13`
  have hz12 : ‖z‖ ≤ 12 := by
    have h : ‖z‖ ^ 2 ≤ 12 ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have := abs_le.1 hE
      nlinarith
    exact (sq_le_sq₀ (norm_nonneg _) (by norm_num)).1 h
  have hr0 : 0 < ‖msc z‖ := norm_pos_iff.2 (fun h => by
    rw [h] at hbpos; simp at hbpos)
  have hmz : 0 < ‖msc z + z‖ := inv_pos.1 (hn1 ▸ hr0)
  have hr13 : 1 / 13 ≤ ‖msc z‖ := by
    have hle : ‖msc z + z‖ ≤ 13 := by
      have := norm_add_le (msc z) z
      linarith
    rw [hn1, one_div]
    exact inv_anti₀ hmz hle
  -- the modulus of `s = 2 m + z`
  obtain ⟨hT1, hT2⟩ := bounds_w_sq z.re z.im _ _ _ hE hη hη10 hk h1 h2
  set t := Real.sqrt (kappa z.re + z.im) with ht
  have ht2 : t ^ 2 = kappa z.re + z.im := Real.sq_sqrt (by linarith)
  have ht0 : 0 < t := Real.sqrt_pos.2 (by linarith)
  have hw0 : 0 ≤ ‖2 * msc z + z‖ := norm_nonneg _
  obtain ⟨hwt1, hwt2⟩ := bounds_w_sqrt (kappa z.re + z.im) t _ ht2 ht0 hw0 (by rw [hw2]; exact hT1)
    (by rw [hw2]; exact hT2)
  have hfac : 1 - msc z ^ 2 = -(msc z * (2 * msc z + z)) := by linear_combination hq
  have hnorm : ‖1 - msc z ^ 2‖ = ‖msc z‖ * ‖2 * msc z + z‖ := by
    rw [hfac, norm_neg, norm_mul]
  have hf : 1 - ‖msc z‖ ^ 2 ≤ ‖1 - msc z ^ 2‖ := by
    have := norm_sub_norm_le (1 : ℂ) (msc z ^ 2)
    rwa [norm_one, norm_pow] at this
  have hrw : ‖msc z‖ * ‖2 * msc z + z‖ ≤ 4 * t := by
    calc ‖msc z‖ * ‖2 * msc z + z‖ ≤ 1 * ‖2 * msc z + z‖ :=
          mul_le_mul_of_nonneg_right hn2.le hw0
      _ ≤ 4 * t := by linarith
  have hyw : 2 * (msc z).im + z.im ≤ ‖2 * msc z + z‖ := by
    rw [← hy]; exact Complex.im_le_norm _
  refine ⟨⟨hr13, hn2.le⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hnorm]
    have := mul_le_mul_of_nonneg_right hr13 hw0
    linarith
  · rw [hnorm]; exact hrw
  · exact bounds_lower_eta _ _ _ t hη hbpos hr13 hI (by rw [← hnorm] at hrw; linarith)
  · intro hηκ hE2
    have := bounds_edge_upper z.re z.im _ _ (kappa z.re) t hE hη hk h1 h2 ht2 ht0
      (by linarith) hηκ hE2
    nlinarith [mul_pos hη ht0]
  · intro hE2 hηκ
    exact bounds_bulk_lower z.re z.im _ _ (kappa z.re) t (msc z).im hk h1 ht2 ht0 rfl hbpos hηκ
      hE2 (by linarith)
  · linarith

theorem msc_bounds : ∃ C ≥ (1 : ℝ), ∀ z : ℂ, |z.re| ≤ 5 → 0 < z.im → z.im ≤ 10 →
    (C⁻¹ ≤ ‖msc z‖ ∧ ‖msc z‖ ≤ C) ∧
    (C⁻¹ * Real.sqrt (kappa z.re + z.im) ≤ ‖1 - msc z ^ 2‖ ∧
      ‖1 - msc z ^ 2‖ ≤ C * Real.sqrt (kappa z.re + z.im)) ∧
    (z.im ≤ kappa z.re → 2 ≤ |z.re| →
      C⁻¹ * (z.im / Real.sqrt (kappa z.re + z.im)) ≤ (msc z).im ∧
      (msc z).im ≤ C * (z.im / Real.sqrt (kappa z.re + z.im))) ∧
    (kappa z.re ≤ z.im ∨ |z.re| ≤ 2 →
      C⁻¹ * Real.sqrt (kappa z.re + z.im) ≤ (msc z).im ∧
      (msc z).im ≤ C * Real.sqrt (kappa z.re + z.im)) := by
  refine ⟨2000, by norm_num, ?_⟩
  intro z hE hη hη10
  obtain ⟨⟨hr1, hr2⟩, ⟨hf1, hf2⟩, hL, hedge, hbulk, hb2⟩ := bounds_main z hE hη hη10
  have hkn : 0 ≤ kappa z.re := abs_nonneg _
  have ht2 : Real.sqrt (kappa z.re + z.im) ^ 2 = kappa z.re + z.im :=
    Real.sq_sqrt (by linarith)
  have ht0 : 0 < Real.sqrt (kappa z.re + z.im) := Real.sqrt_pos.2 (by linarith)
  set t := Real.sqrt (kappa z.re + z.im) with ht
  have hbpos := im_msc_pos hη
  have hC : (2000 : ℝ)⁻¹ = 1 / 2000 := by norm_num
  have hηt : 0 < z.im / t := div_pos hη ht0
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hC]; linarith
  · linarith
  · rw [hC]; linarith
  · linarith
  · intro hηκ hE2
    rw [hC]
    constructor
    · have : z.im / t ≤ 676 * (msc z).im := by
        rw [div_le_iff₀ ht0]; linarith
      linarith
    · have : (msc z).im ≤ 2 * (z.im / t) := by
        rw [mul_div_assoc', le_div_iff₀ ht0]; linarith [hedge hηκ hE2]
      linarith
  · intro hcase
    rw [hC]
    refine ⟨?_, by linarith⟩
    have hlow : t ≤ 1352 * (msc z).im ∨ t ≤ 16 * (msc z).im := by
      by_cases hκη : kappa z.re ≤ z.im
      · left
        have h1 : t ^ 2 ≤ 1352 * t * (msc z).im := by nlinarith
        nlinarith
      · right
        have hE2 : |z.re| ≤ 2 := hcase.resolve_left hκη
        exact hbulk hE2 (by linarith)
    rcases hlow with h | h <;> linarith

/-- Lemma 2.6's domain contains `z = 2 + i·10⁻³` (regime 2) and `z = 3 + i·10⁻³` (regime 1). -/
example : |(2 : ℝ)| ≤ 5 ∧ (0 : ℝ) < 1 / 1000 ∧ (1 / 1000 : ℝ) ≤ 10 ∧ kappa 2 ≤ 1 / 1000 ∧
    (1 / 1000 : ℝ) ≤ kappa 3 ∧ 2 ≤ |(3 : ℝ)| := by
  unfold kappa; norm_num [abs_of_nonneg]

/-- `msc_bounds` applied at `z = 3 + i·10⁻³` (case `η ≤ κ`, `2 ≤ |E|`) and `z = 2 + i·10⁻³` (case
`κ ≤ η`). -/
example : ∃ C ≥ (1 : ℝ),
    (C⁻¹ * ((1 / 1000 : ℝ) / Real.sqrt (kappa 3 + 1 / 1000)) ≤ (msc ⟨3, 1 / 1000⟩).im ∧
      (msc ⟨3, 1 / 1000⟩).im ≤ C * ((1 / 1000 : ℝ) / Real.sqrt (kappa 3 + 1 / 1000))) ∧
    (C⁻¹ * Real.sqrt (kappa 2 + 1 / 1000) ≤ (msc ⟨2, 1 / 1000⟩).im ∧
      (msc ⟨2, 1 / 1000⟩).im ≤ C * Real.sqrt (kappa 2 + 1 / 1000)) := by
  obtain ⟨C, hC, h⟩ := msc_bounds
  refine ⟨C, hC, ?_, ?_⟩
  · exact (h ⟨3, 1 / 1000⟩ (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num)).2.2.1
      (by unfold kappa; norm_num [abs_of_nonneg]) (by norm_num [abs_of_nonneg])
  · exact (h ⟨2, 1 / 1000⟩ (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num)).2.2.2
      (Or.inl (by unfold kappa; norm_num [abs_of_nonneg]))

#print axioms msc_bounds

end WEdgeNS
