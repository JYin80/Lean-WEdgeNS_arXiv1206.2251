import WEdgeNS.Semicircle.Rigidity

/-!
# Rigidity with the `q`-terms from the counting bound
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-! ### Facts about `ρ_sc` and `n_sc` -/

open private rho_continuous nsc_sub rpow_three_halves nsc_nonneg nsc_le_one
  from WEdgeNS.Semicircle.Rigidity

/-! ### Two-sided comparison at the lower edge -/

/-- A real `x ≥ 1` has a cube root `K ≥ 1`, and `x^{-1/3} = K⁻¹`, `x^{-2/3} = (K²)⁻¹`,
`x^{1/3} = K`. -/
private lemma exists_cube_root {x : ℝ} (hx : 1 ≤ x) :
    ∃ K : ℝ, 1 ≤ K ∧ K ^ 3 = x ∧ x ^ (-(1 : ℝ) / 3) = K⁻¹ ∧ x ^ (-(2 : ℝ) / 3) = (K ^ 2)⁻¹ ∧
      x ^ ((1 : ℝ) / 3) = K := by
  have hx0 : 0 ≤ x := by linarith
  refine ⟨x ^ ((1 : ℝ) / 3), Real.one_le_rpow hx (by norm_num), ?_, ?_, ?_, rfl⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  · rw [neg_div, Real.rpow_neg hx0]
  · rw [neg_div, Real.rpow_neg hx0, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num

/-! ### The counting bound at an eigenvalue, with an energy-dependent error -/

private lemma kappa_neg (x : ℝ) : kappa (-x) = kappa x := by
  unfold kappa
  rw [abs_neg]

private lemma continuous_kappa : Continuous kappa := by
  unfold kappa
  fun_prop

/-- Counting bound at the `j`-th eigenvalue (0-based `j`) for an error function `ε` that is
continuous: `n_sc(λ_{j+1})` lies between `(j + 1)/N - ε(λ_{j+1})` and `j/N + ε(λ_{j+1})`. -/
private lemma nsc_eigAsc_bounds_err {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (ε : ℝ → ℝ) (hε : Continuous ε)
    (hcount : ∀ E : ℝ, |countFn hH E - nsc E| ≤ ε E) (j : Fin N) :
    ((j.val : ℝ) + 1) / N - ε (eigAsc hH j) ≤ nsc (eigAsc hH j) ∧
      nsc (eigAsc hH j) ≤ (j.val : ℝ) / N + ε (eigAsc hH j) := by
  have hlow : ∀ E, eigAsc hH j ≤ E → ((j.val : ℝ) + 1) / N ≤ countFn hH E := by
    intro E hE
    unfold countFn
    rw [card_filter_eigenvalues]
    have hsub : Finset.Iic j ⊆ Finset.univ.filter (fun i => eigAsc hH i ≤ E) := by
      intro i hi
      simp only [Finset.mem_Iic] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (monotone_eigAsc hH hi).trans hE
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    have : ((j.val : ℝ) + 1) ≤ (Finset.univ.filter (fun i => eigAsc hH i ≤ E)).card := by
      exact_mod_cast hcard
    gcongr
  have hup : ∀ E, E < eigAsc hH j → countFn hH E ≤ (j.val : ℝ) / N := by
    intro E hE
    unfold countFn
    rw [card_filter_eigenvalues]
    have hsub : Finset.univ.filter (fun i => eigAsc hH i ≤ E) ⊆ Finset.Iio j := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_Iio]
      by_contra hij
      rw [not_lt] at hij
      have := monotone_eigAsc hH hij
      linarith
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    have : ((Finset.univ.filter (fun i => eigAsc hH i ≤ E)).card : ℝ) ≤ (j.val : ℝ) := by
      exact_mod_cast hcard
    gcongr
  constructor
  · have h1 := hlow _ le_rfl
    have h2 := (abs_le.1 (hcount (eigAsc hH j))).2
    linarith
  · have hlim1 : Tendsto nsc (𝓝[<] (eigAsc hH j)) (𝓝 (nsc (eigAsc hH j))) :=
      (continuous_nsc.tendsto _).mono_left nhdsWithin_le_nhds
    have hlim2 : Tendsto (fun E => (j.val : ℝ) / N + ε E) (𝓝[<] (eigAsc hH j))
        (𝓝 ((j.val : ℝ) / N + ε (eigAsc hH j))) :=
      (((continuous_const.add hε).tendsto _)).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto_of_tendsto hlim1 hlim2 (eventually_nhdsWithin_of_forall fun E hE => ?_)
    have h1 := hup E hE
    have h2 := (abs_le.1 (hcount E)).1
    linarith

/-! ### Increments of `n_sc` near the lower edge -/

/-- `∫_p^q √(s + 2) ds = (2/3)((q + 2)^{3/2} - (p + 2)^{3/2})`. -/
private lemma integral_sqrt_add_two_between (p q : ℝ) :
    ∫ s in p..q, Real.sqrt (s + 2) =
      2 / 3 * (q + 2) ^ ((3 : ℝ) / 2) - 2 / 3 * (p + 2) ^ ((3 : ℝ) / 2) := by
  have hd : ∀ s ∈ Set.uIcc p q,
      HasDerivAt (fun s : ℝ => 2 / 3 * (s + 2) ^ ((3 : ℝ) / 2)) (Real.sqrt (s + 2)) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => s + 2) 1 s := (hasDerivAt_id s).add_const 2
    have h2 := (h1.rpow_const (p := (3 : ℝ) / 2) (Or.inr (by norm_num))).const_mul (2 / 3)
    convert h2 using 1
    rw [show (3 : ℝ) / 2 - 1 = 1 / 2 by norm_num, Real.sqrt_eq_rpow]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by exact (by fun_prop : Continuous fun s : ℝ => Real.sqrt (s + 2)).intervalIntegrable _ _)]

/-- For `-2 ≤ p ≤ q ≤ 1`, the increment of `n_sc` dominates `(2/3) C0⁻¹` times the increment of
`(x + 2)^{3/2}`, written with cubes of square roots. -/
private lemma increment_cube {C0 : ℝ} (hC0 : 1 ≤ C0) (hc : EdgeComp C0) {p q : ℝ}
    (hp : -2 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) :
    2 / 3 * C0⁻¹ * (Real.sqrt (q + 2) ^ 3 - Real.sqrt (p + 2) ^ 3) ≤ nsc q - nsc p := by
  rw [nsc_sub]
  have hC0' : 0 < C0 := by linarith
  have h := intervalIntegral.integral_mono_on (μ := volume) hpq
    (f := fun s => C0⁻¹ * Real.sqrt (s + 2)) (g := rhoSc)
    ((by fun_prop : Continuous fun s : ℝ => C0⁻¹ * Real.sqrt (s + 2)).intervalIntegrable _ _)
    (rho_continuous.intervalIntegrable p q) (fun x hx => ?_)
  · rw [intervalIntegral.integral_const_mul, integral_sqrt_add_two_between,
      rpow_three_halves (by linarith), rpow_three_halves (by linarith)] at h
    calc 2 / 3 * C0⁻¹ * (Real.sqrt (q + 2) ^ 3 - Real.sqrt (p + 2) ^ 3)
        = C0⁻¹ * (2 / 3 * Real.sqrt (q + 2) ^ 3 - 2 / 3 * Real.sqrt (p + 2) ^ 3) := by ring
      _ ≤ _ := h
  · exact (hc x ⟨by linarith [hx.1], by linarith [hx.2]⟩).2.1

/-! ### Algebra for the comparison of square roots -/

/-- If `|w³ - v³| ≤ A + B w` and `v ≥ ℓ > 0`, then `|w² - v²| ≤ (4/3)(A/ℓ + B)`. -/
private lemma abs_sq_sub_sq_le {w v A B ℓ : ℝ} (hw : 0 ≤ w) (hℓ : 0 < ℓ) (hv : ℓ ≤ v)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h : |w ^ 3 - v ^ 3| ≤ A + B * w) :
    |w ^ 2 - v ^ 2| ≤ 4 / 3 * (A / ℓ + B) := by
  have hv0 : 0 < v := lt_of_lt_of_le hℓ hv
  set S := w + v with hS
  have hS0 : 0 < S := by positivity
  have hSℓ : ℓ ≤ S := by linarith
  have hfac : w ^ 3 - v ^ 3 = (w - v) * (w ^ 2 + w * v + v ^ 2) := by ring
  have hfac2 : w ^ 2 - v ^ 2 = (w - v) * S := by rw [hS]; ring
  have hq : 0 ≤ w ^ 2 + w * v + v ^ 2 := by positivity
  have h1 : |w - v| * (w ^ 2 + w * v + v ^ 2) ≤ A + B * w := by
    rw [hfac, abs_mul, abs_of_nonneg hq] at h
    exact h
  have h2 : 3 * S ^ 2 ≤ 4 * (w ^ 2 + w * v + v ^ 2) := by
    rw [hS]; nlinarith [sq_nonneg (w - v)]
  have h3 : |w ^ 2 - v ^ 2| * S ≤ 4 / 3 * (A + B * w) := by
    rw [hfac2, abs_mul, abs_of_pos hS0]
    have : |w - v| * S * S = |w - v| * S ^ 2 := by ring
    rw [this]
    have h4 : |w - v| * (3 * S ^ 2) ≤ |w - v| * (4 * (w ^ 2 + w * v + v ^ 2)) :=
      mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    nlinarith
  have h5 : |w ^ 2 - v ^ 2| * S ≤ 4 / 3 * (A + B * S) := by
    refine h3.trans ?_
    have : B * w ≤ B * S := by
      apply mul_le_mul_of_nonneg_left _ hB
      rw [hS]; linarith
    linarith
  have h6 : |w ^ 2 - v ^ 2| ≤ 4 / 3 * (A + B * S) / S := by
    rw [le_div_iff₀ hS0]
    exact h5
  refine h6.trans ?_
  have : 4 / 3 * (A + B * S) / S = 4 / 3 * (A / S + B) := by
    field_simp
  rw [this]
  have : A / S ≤ A / ℓ := div_le_div_of_nonneg_left hA hℓ hSℓ
  linarith

/-! ### The edge estimate in the cube-root variables ([15] Proposition 8.3, (3.6)) -/

/-- A cube bounded by a linear-in-`Y` quantity: `Y³ ≤ C0 (5 t² + t Y)` gives `Y ≤ 3 C0 t`. -/
private lemma le_of_cube_le_linear {C0 t Y : ℝ} (hC0 : 1 ≤ C0) (ht : 1 ≤ t) (hY0 : 0 ≤ Y)
    (h1 : Y ^ 3 ≤ C0 * (5 * t ^ 2 + t * Y)) : Y ≤ 3 * C0 * t := by
  by_contra h
  rw [not_le] at h
  have hY3 : 3 ≤ Y := by nlinarith
  have h9 : 27 * C0 ^ 3 * t ^ 3 < Y ^ 3 := by
    have : (3 * C0 * t) ^ 3 < Y ^ 3 := pow_lt_pow_left₀ h (by positivity) (by norm_num)
    nlinarith
  have h10 : C0 * t ^ 2 ≤ C0 ^ 3 * t ^ 3 := by
    have : C0 ≤ C0 ^ 3 := le_self_pow₀ hC0 (by norm_num)
    have h11 : t ^ 2 ≤ t ^ 3 := by nlinarith
    nlinarith [mul_le_mul this h11 (by positivity) (by positivity)]
  have h12 : C0 * t * Y < Y ^ 3 / 9 := by
    have h13 : 3 * C0 * t < Y := h
    have h14 : C0 * t * Y ≤ Y * Y / 3 := by nlinarith
    have h15 : Y * Y ≤ Y ^ 3 / 3 := by nlinarith [sq_nonneg Y]
    nlinarith
  nlinarith

/-- `X³ ≤ 2 C0` gives `X ≤ 2 C0`. -/
private lemma le_two_mul_of_cube_le {C0 X : ℝ} (hC0 : 1 ≤ C0)
    (h : X ^ 3 ≤ 2 * C0) : X ≤ 2 * C0 := by
  by_contra h'
  rw [not_le] at h'
  have h1 : (2 * C0) ^ 3 < X ^ 3 := pow_lt_pow_left₀ h' (by positivity) (by norm_num)
  have h5 : C0 ≤ C0 ^ 3 := le_self_pow₀ hC0 (by norm_num)
  nlinarith

/-- `K³ ≤ 2 C0 X³` gives `K ≤ 2 C0 X`. -/
private lemma le_two_mul_of_cube_le' {C0 K X : ℝ} (hC0 : 1 ≤ C0) (hX0 : 0 ≤ X)
    (h : K ^ 3 ≤ 2 * C0 * X ^ 3) : K ≤ 2 * C0 * X := by
  by_contra h'
  rw [not_le] at h'
  have h4 : (2 * C0 * X) ^ 3 < K ^ 3 := pow_lt_pow_left₀ h' (by positivity) (by norm_num)
  have h5 : (2 * C0 * X) ^ 3 = 8 * C0 ^ 3 * X ^ 3 := by ring
  have h6 : C0 ≤ C0 ^ 3 := le_self_pow₀ hC0 (by norm_num)
  have h7 : 0 ≤ X ^ 3 := by positivity
  nlinarith

/-- The lower bound for the classical location in the case `K³ ≥ 2`. -/
private lemma cube_lower_of_nsc {C0 K M v : ℝ} (hM3 : 0 < M ^ 3) (hK2 : 2 ≤ K ^ 3)
    (h : (K ^ 3 - 1) / M ^ 3 ≤ C0 * v ^ 3) : K ^ 3 ≤ 2 * C0 * (v * M) ^ 3 := by
  rw [div_le_iff₀ hM3] at h
  rw [mul_pow]
  nlinarith

/-- The upper bound for the eigenvalue in the case `K³ < 2`. -/
private lemma cube_upper_eigenvalue {C0 K M t r w ns : ℝ} (hC0 : 0 < C0) (hM : 1 ≤ M)
    (ht : 1 ≤ t) (hr : r * M ^ 2 ≤ 1) (hw0 : 0 ≤ w) (hK2 : K ^ 3 < 2)
    (h1 : C0⁻¹ * w ^ 3 ≤ ns)
    (h2 : ns ≤ (K ^ 3 - 1) / M ^ 3 + (4 * t ^ 2 / M ^ 3 + t * r * w)) :
    (w * M) ^ 3 ≤ C0 * (5 * t ^ 2 + t * (w * M)) := by
  have hM0 : 0 < M := by linarith
  have hM3 : 0 < M ^ 3 := by positivity
  have h3 : ns * M ^ 3 ≤ ((K ^ 3 - 1) / M ^ 3 + (4 * t ^ 2 / M ^ 3 + t * r * w)) * M ^ 3 :=
    mul_le_mul_of_nonneg_right h2 hM3.le
  have h4 : ((K ^ 3 - 1) / M ^ 3 + (4 * t ^ 2 / M ^ 3 + t * r * w)) * M ^ 3 =
      (K ^ 3 - 1) + 4 * t ^ 2 + t * (r * M ^ 2) * (w * M) := by
    field_simp
    ring
  rw [h4] at h3
  have h5 : t * (r * M ^ 2) * (w * M) ≤ t * (w * M) := by
    have : r * M ^ 2 * (w * M) ≤ 1 * (w * M) :=
      mul_le_mul_of_nonneg_right hr (by positivity)
    nlinarith
  have h6 : t ^ 2 ≥ 1 := by nlinarith
  have h2' : ns * M ^ 3 ≤ 5 * t ^ 2 + t * (w * M) := by nlinarith
  have h7 : C0⁻¹ * w ^ 3 * M ^ 3 ≤ ns * M ^ 3 := mul_le_mul_of_nonneg_right h1 hM3.le
  have h8 : (w * M) ^ 3 = C0 * (C0⁻¹ * w ^ 3 * M ^ 3) := by
    field_simp
  rw [h8]
  exact mul_le_mul_of_nonneg_left (h7.trans h2') hC0.le

/-- The upper bound for the classical location in the case `K³ < 2`. -/
private lemma cube_upper_location {C0 K M v ng : ℝ} (hC0 : 0 < C0) (hM : 0 < M)
    (hK2 : K ^ 3 < 2) (h1 : C0⁻¹ * v ^ 3 ≤ ng) (h2 : ng ≤ K ^ 3 / M ^ 3) :
    (v * M) ^ 3 ≤ 2 * C0 := by
  have hM3 : 0 < M ^ 3 := by positivity
  have h3 := h1.trans h2
  rw [le_div_iff₀ hM3] at h3
  have h4 : (v * M) ^ 3 = C0 * (C0⁻¹ * v ^ 3 * M ^ 3) := by
    field_simp
  rw [h4]
  have h5 : C0 * (C0⁻¹ * v ^ 3 * M ^ 3) ≤ C0 * K ^ 3 := mul_le_mul_of_nonneg_left h3 hC0.le
  nlinarith

/-- The cubes of `√(a + 2)` and `√(g + 2)` differ by at most `(3/2) C0` times the increment of
`n_sc`, for `a, g ∈ [-2, 1]`. -/
private lemma cube_gap_le {C0 : ℝ} (hC0 : 1 ≤ C0) (hc : EdgeComp C0) {a g Q : ℝ}
    (ha1 : -2 ≤ a) (ha2 : a ≤ 1) (hg1 : -2 ≤ g) (hg2 : g ≤ 1)
    (hdiff : |nsc a - nsc g| ≤ Q) :
    |Real.sqrt (a + 2) ^ 3 - Real.sqrt (g + 2) ^ 3| ≤ 3 / 2 * C0 * Q := by
  have hC0' : 0 < C0 := by linarith
  have hQ : 0 ≤ Q := (abs_nonneg _).trans hdiff
  have hw0 : 0 ≤ Real.sqrt (a + 2) := Real.sqrt_nonneg _
  have hv0 : 0 ≤ Real.sqrt (g + 2) := Real.sqrt_nonneg _
  rcases le_total a g with hle | hle
  · have h := increment_cube hC0 hc ha1 hle hg2
    have hwv : Real.sqrt (a + 2) ≤ Real.sqrt (g + 2) := Real.sqrt_le_sqrt (by linarith)
    have hwv3 : Real.sqrt (a + 2) ^ 3 ≤ Real.sqrt (g + 2) ^ 3 := pow_le_pow_left₀ hw0 hwv 3
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have h2 : Real.sqrt (g + 2) ^ 3 - Real.sqrt (a + 2) ^ 3 =
        3 / 2 * C0 * (2 / 3 * C0⁻¹ * (Real.sqrt (g + 2) ^ 3 - Real.sqrt (a + 2) ^ 3)) := by
      field_simp
    rw [h2]
    have h4 : nsc g - nsc a ≤ Q := by
      have := (abs_le.1 hdiff).1
      linarith
    exact mul_le_mul_of_nonneg_left (h.trans h4) (by positivity)
  · have h := increment_cube hC0 hc hg1 hle ha2
    have hwv : Real.sqrt (g + 2) ≤ Real.sqrt (a + 2) := Real.sqrt_le_sqrt (by linarith)
    have hwv3 : Real.sqrt (g + 2) ^ 3 ≤ Real.sqrt (a + 2) ^ 3 := pow_le_pow_left₀ hv0 hwv 3
    rw [abs_of_nonneg (by linarith)]
    have h2 : Real.sqrt (a + 2) ^ 3 - Real.sqrt (g + 2) ^ 3 =
        3 / 2 * C0 * (2 / 3 * C0⁻¹ * (Real.sqrt (a + 2) ^ 3 - Real.sqrt (g + 2) ^ 3)) := by
      field_simp
    rw [h2]
    have h4 : nsc a - nsc g ≤ Q := (abs_le.1 hdiff).2
    exact mul_le_mul_of_nonneg_left (h.trans h4) (by positivity)

/-- Case `k ≥ 2` of the edge estimate: the classical location is bounded away from the edge. -/
private lemma edgeQ_large {C0 K M t r w v : ℝ} (hC0 : 1 ≤ C0) (hK : 1 ≤ K) (hM : 1 ≤ M)
    (ht : 1 ≤ t) (hr0 : 0 ≤ r) (hw0 : 0 ≤ w)
    (hX : K ≤ 2 * C0 * (v * M))
    (hcube : |w ^ 3 - v ^ 3| ≤ 3 / 2 * C0 * (4 * t ^ 2 / M ^ 3 + t * r * w)) :
    |w ^ 2 - v ^ 2| ≤ 18 * C0 ^ 2 * t ^ 2 * ((K * M ^ 2)⁻¹ + r) := by
  have hC0' : 0 < C0 := by linarith
  have hM0 : 0 < M := by linarith
  have hK0 : 0 < K := by linarith
  have ht0 : 0 < t := by linarith
  have hvl : K / (2 * C0 * M) ≤ v := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hℓ : 0 < K / (2 * C0 * M) := by positivity
  have hA : 0 ≤ 3 / 2 * C0 * (4 * t ^ 2 / M ^ 3) := by positivity
  have hB : 0 ≤ 3 / 2 * C0 * (t * r) := by positivity
  have h := abs_sq_sub_sq_le hw0 hℓ hvl hA hB (by
    refine hcube.trans (le_of_eq ?_)
    ring)
  refine h.trans ?_
  have hAl : 3 / 2 * C0 * (4 * t ^ 2 / M ^ 3) / (K / (2 * C0 * M)) =
      12 * C0 ^ 2 * t ^ 2 * (K * M ^ 2)⁻¹ := by
    field_simp
    ring
  rw [hAl]
  have hct1 : 1 ≤ C0 * t := by nlinarith
  have hCt : C0 * t ≤ C0 ^ 2 * t ^ 2 := by
    calc C0 * t = (C0 * t) * 1 := by ring
      _ ≤ (C0 * t) * (C0 * t) := mul_le_mul_of_nonneg_left hct1 (by positivity)
      _ = C0 ^ 2 * t ^ 2 := by ring
  have e1 : 0 ≤ C0 ^ 2 * t ^ 2 * (K * M ^ 2)⁻¹ := by positivity
  have e2 : C0 * t * r ≤ C0 ^ 2 * t ^ 2 * r := mul_le_mul_of_nonneg_right hCt hr0
  linarith

/-- Case `k = 1` of the edge estimate: only upper bounds are used. -/
private lemma edgeQ_small {C0 K M t r w v : ℝ} (hC0 : 1 ≤ C0) (hK : 1 ≤ K) (hM : 1 ≤ M)
    (ht : 1 ≤ t) (hr0 : 0 ≤ r) (hw0 : 0 ≤ w) (hv0 : 0 ≤ v)
    (hK3 : K < 2) (hY : w * M ≤ 3 * C0 * t) (hXv : v * M ≤ 2 * C0) :
    |w ^ 2 - v ^ 2| ≤ 18 * C0 ^ 2 * t ^ 2 * ((K * M ^ 2)⁻¹ + r) := by
  have hC0' : 0 < C0 := by linarith
  have hM0 : 0 < M := by linarith
  have hK0 : 0 < K := by linarith
  have ht0 : 0 < t := by linarith
  have hw2' : w ^ 2 ≤ 9 * C0 ^ 2 * t ^ 2 / M ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have : w ^ 2 * M ^ 2 = (w * M) ^ 2 := by ring
    rw [this]
    have : (w * M) ^ 2 ≤ (3 * C0 * t) ^ 2 := pow_le_pow_left₀ (by positivity) hY 2
    nlinarith
  have hv2' : v ^ 2 ≤ 9 * C0 ^ 2 * t ^ 2 / M ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have : v ^ 2 * M ^ 2 = (v * M) ^ 2 := by ring
    rw [this]
    have h1 : (v * M) ^ 2 ≤ (2 * C0) ^ 2 := pow_le_pow_left₀ (by positivity) hXv 2
    have h2 : (1 : ℝ) ≤ t ^ 2 := by nlinarith
    have h3 : 0 ≤ C0 ^ 2 := sq_nonneg C0
    nlinarith
  have habs : |w ^ 2 - v ^ 2| ≤ 9 * C0 ^ 2 * t ^ 2 / M ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg w, sq_nonneg v]
  refine habs.trans ?_
  have hx : (2 * M ^ 2)⁻¹ ≤ (K * M ^ 2)⁻¹ := by
    apply inv_anti₀ (by positivity)
    nlinarith [sq_nonneg M]
  have hrr : 0 ≤ 18 * C0 ^ 2 * t ^ 2 * r := by positivity
  have : 9 * C0 ^ 2 * t ^ 2 / M ^ 2 = 18 * C0 ^ 2 * t ^ 2 * (2 * M ^ 2)⁻¹ := by
    field_simp
    ring
  rw [this]
  have h0 : 0 ≤ 18 * C0 ^ 2 * t ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hx h0]

/-- Edge estimate for an eigenvalue `a ∈ [-2, 1]` and a classical location `g ∈ [-2, 1]`, in the
cube-root variables `k = K³`, `N = M³`, with additive error `4 t²/M³ + t r √(a + 2)`. -/
private lemma edgeQ_nonneg {C0 : ℝ} (hC0 : 1 ≤ C0) (hc : EdgeComp C0) {K M t r a g : ℝ}
    (hK : 1 ≤ K) (hM : 1 ≤ M) (ht : 1 ≤ t) (hr0 : 0 ≤ r) (hr : r * M ^ 2 ≤ 1)
    (hA1 : K ^ 3 / M ^ 3 - (4 * t ^ 2 / M ^ 3 + t * r * Real.sqrt (a + 2)) ≤ nsc a)
    (hA2 : nsc a ≤ (K ^ 3 - 1) / M ^ 3 + (4 * t ^ 2 / M ^ 3 + t * r * Real.sqrt (a + 2)))
    (hG1 : (K ^ 3 - 1) / M ^ 3 ≤ nsc g) (hG2 : nsc g ≤ K ^ 3 / M ^ 3)
    (ha1 : -2 ≤ a) (ha2 : a ≤ 1) (hg1 : -2 ≤ g) (hg2 : g ≤ 1) :
    |a - g| ≤ 18 * C0 ^ 2 * t ^ 2 * ((K * M ^ 2)⁻¹ + r) := by
  have hC0' : 0 < C0 := by linarith
  have hM0 : 0 < M := by linarith
  have hK0 : 0 < K := by linarith
  have hM3 : 0 < M ^ 3 := by positivity
  have ht0 : 0 < t := by linarith
  have hw0 : 0 ≤ Real.sqrt (a + 2) := Real.sqrt_nonneg _
  have hv0 : 0 ≤ Real.sqrt (g + 2) := Real.sqrt_nonneg _
  have hw2 : Real.sqrt (a + 2) ^ 2 = a + 2 := Real.sq_sqrt (by linarith)
  have hv2 : Real.sqrt (g + 2) ^ 2 = g + 2 := Real.sq_sqrt (by linarith)
  have hag : a - g = Real.sqrt (a + 2) ^ 2 - Real.sqrt (g + 2) ^ 2 := by rw [hw2, hv2]; ring
  have hnsa : C0⁻¹ * Real.sqrt (a + 2) ^ 3 ≤ nsc a ∧ nsc a ≤ C0 * Real.sqrt (a + 2) ^ 3 := by
    have := (hc a ⟨ha1, ha2⟩).1
    rwa [rpow_three_halves (by linarith)] at this
  have hnsg : C0⁻¹ * Real.sqrt (g + 2) ^ 3 ≤ nsc g ∧ nsc g ≤ C0 * Real.sqrt (g + 2) ^ 3 := by
    have := (hc g ⟨hg1, hg2⟩).1
    rwa [rpow_three_halves (by linarith)] at this
  generalize hwd : Real.sqrt (a + 2) = w at *
  generalize hvd : Real.sqrt (g + 2) = v at *
  have hdiff : |nsc a - nsc g| ≤ 4 * t ^ 2 / M ^ 3 + t * r * w := by
    rw [abs_le]
    constructor <;> linarith
  have hcube : |w ^ 3 - v ^ 3| ≤ 3 / 2 * C0 * (4 * t ^ 2 / M ^ 3 + t * r * w) := by
    have := cube_gap_le hC0 hc ha1 ha2 hg1 hg2 hdiff
    rwa [hwd, hvd] at this
  rw [hag]
  by_cases hK2 : 2 ≤ K ^ 3
  · have hX : K ≤ 2 * C0 * (v * M) :=
      le_two_mul_of_cube_le' hC0 (by positivity)
        (cube_lower_of_nsc hM3 hK2 (hG1.trans hnsg.2))
    exact edgeQ_large hC0 hK hM ht hr0 hw0 hX hcube
  · rw [not_le] at hK2
    have hK3 : K < 2 := by
      by_contra h
      rw [not_lt] at h
      have : (2 : ℝ) ^ 3 ≤ K ^ 3 := pow_le_pow_left₀ (by norm_num) h 3
      linarith
    have hY : w * M ≤ 3 * C0 * t :=
      le_of_cube_le_linear hC0 ht (by positivity)
        (cube_upper_eigenvalue hC0' hM ht hr hw0 hK2 hnsa.1 hA2)
    have hXv : v * M ≤ 2 * C0 :=
      le_two_mul_of_cube_le hC0 (cube_upper_location hC0' hM0 hK2 hnsg.1 hG2)
    exact edgeQ_small hC0 hK hM ht hr0 hw0 hv0 hK3 hY hXv

/-! ### The edge estimate from the counting error ([15] Theorem 2.13) -/

private lemma kappa_le_two {x s : ℝ} (hs : s ≤ 2) (hx : |x| ≤ 2 + s) : kappa x ≤ 2 := by
  unfold kappa
  have h0 := abs_nonneg x
  rw [abs_le]
  constructor <;> linarith

private lemma kappa_le_add_two {x : ℝ} (h1 : -2 ≤ x) (h2 : x ≤ 1) : kappa x ≤ x + 2 := by
  unfold kappa
  have h3 : |x| ≤ 2 := abs_le.2 ⟨h1, by linarith⟩
  rw [abs_of_nonpos (by linarith)]
  linarith [neg_abs_le x]

private lemma kappa_le_of_lt {x s : ℝ} (h : x < -2) (hx : |x| ≤ 2 + s) : kappa x ≤ s := by
  unfold kappa
  have h0 : x < 0 := by linarith
  rw [abs_of_neg h0] at hx
  rw [abs_of_neg h0, abs_of_nonneg (by linarith)]
  linarith

private lemma lt_one_of_nsc_lt {a : ℝ} (h : nsc a < 3 / 4) : a < 1 := by
  by_contra h'
  rw [not_lt] at h'
  have h1 := monotone_nsc h'
  have h2 := three_quarters_le_nsc_one
  linarith

private lemma const_le_const {C0 t X : ℝ} (ht : 1 ≤ t) (hX : 0 ≤ X) :
    18 * C0 ^ 2 * t ^ 2 * X ≤ (60000 + 20 * C0 ^ 2) * t ^ 3 * X := by
  refine mul_le_mul_of_nonneg_right ?_ hX
  have h1 : t ^ 2 ≤ t ^ 3 := by nlinarith
  have h2 : 0 ≤ C0 ^ 2 := sq_nonneg C0
  nlinarith

/-- Far range `M² < 100 t`: only the norm bound is used. -/
private lemma edgeQ_far {C1 K M t r a g : ℝ} (hK : 1 ≤ K) (hM : 1 ≤ M) (hKM : K ≤ M)
    (ht : 1 ≤ t) (hr0 : 0 ≤ r) (hr : r * M ^ 2 ≤ 1) (hg1 : -2 ≤ g) (hg2 : g ≤ 2)
    (ha : |a| ≤ 2 + t * (r + (M ^ 2)⁻¹)) (hC1 : 60000 ≤ C1) (hfar : M ^ 2 < 100 * t) :
    |a - g| ≤ C1 * t ^ 3 * ((K * M ^ 2)⁻¹ + r) := by
  have hM0 : 0 < M := by linarith
  have hK0 : 0 < K := by linarith
  have ht0 : 0 < t := by linarith
  have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM
  have hu1 : (M ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hM2
  have hr1 : r ≤ (M ^ 2)⁻¹ := by
    rw [← one_div, le_div_iff₀ (by positivity)]
    exact hr
  have hg : |g| ≤ 2 := abs_le.2 ⟨hg1, hg2⟩
  have h1 : |a - g| ≤ |a| + |g| := abs_sub _ _
  have h2 : t * (r + (M ^ 2)⁻¹) ≤ 2 * t := by nlinarith
  have h3 : |a - g| ≤ 6 * t := by linarith
  have hKM2 : K * M ^ 2 ≤ (100 * t) ^ 2 := by
    have h4 : K * M ^ 2 ≤ M * M ^ 2 := by gcongr
    have h5 : M * M ^ 2 ≤ M ^ 2 * M ^ 2 := by gcongr; nlinarith
    have h6 : M ^ 2 * M ^ 2 ≤ (100 * t) ^ 2 := by
      rw [← sq]
      exact pow_le_pow_left₀ (by positivity) hfar.le 2
    linarith
  have hx : ((100 * t) ^ 2)⁻¹ ≤ (K * M ^ 2)⁻¹ := inv_anti₀ (by positivity) hKM2
  have h7 : C1 * t ^ 3 * ((100 * t) ^ 2)⁻¹ = C1 * t / 10000 := by
    field_simp
    ring
  have h8 : 6 * t ≤ C1 * t / 10000 := by nlinarith
  have h9 : C1 * t ^ 3 * ((K * M ^ 2)⁻¹) ≤ C1 * t ^ 3 * ((K * M ^ 2)⁻¹ + r) := by
    have : 0 ≤ C1 * t ^ 3 * r := by
      have : 0 ≤ C1 := by linarith
      positivity
    linarith
  have h10 : C1 * t ^ 3 * ((100 * t) ^ 2)⁻¹ ≤ C1 * t ^ 3 * ((K * M ^ 2)⁻¹) := by
    have : 0 ≤ C1 * t ^ 3 := by
      have : 0 ≤ C1 := by linarith
      positivity
    exact mul_le_mul_of_nonneg_left hx this
  rw [h7] at h10
  linarith

private lemma final_comb {C0 t x r : ℝ} (hC0 : 1 ≤ C0) (ht : 1 ≤ t) (hx : 0 ≤ x) (hr : 0 ≤ r) :
    C0 ^ 2 * t ^ 2 * r + 2 * t ^ 2 * x + 18 * C0 ^ 2 * t ^ 2 * (x + r) ≤
      (60000 + 20 * C0 ^ 2) * t ^ 3 * (x + r) := by
  have h1 : 0 ≤ C0 ^ 2 * t ^ 2 * r := by positivity
  have h2 : 0 ≤ (C0 ^ 2 - 1) * t ^ 2 * x :=
    mul_nonneg (mul_nonneg (by nlinarith) (sq_nonneg t)) hx
  have h3 : 20 * C0 ^ 2 * t ^ 2 * (x + r) ≤ (60000 + 20 * C0 ^ 2) * t ^ 3 * (x + r) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have : t ^ 2 ≤ t ^ 3 := by nlinarith
    have : 0 ≤ C0 ^ 2 := sq_nonneg C0
    nlinarith
  linarith

/-- Main range, eigenvalue in `[-2, 1)`: the error is controlled by `√(a + 2)`. -/
private lemma edgeQ_above {C0 : ℝ} (hC0 : 1 ≤ C0) (hc : EdgeComp C0) {K M t r a g : ℝ}
    (hK : 1 ≤ K) (hM : 1 ≤ M) (ht : 1 ≤ t) (hr0 : 0 ≤ r) (hr : r * M ^ 2 ≤ 1)
    (hA1 : K ^ 3 / M ^ 3 - t * (2 / M ^ 3 + Real.sqrt (kappa a) * r) ≤ nsc a)
    (hA2 : nsc a ≤ (K ^ 3 - 1) / M ^ 3 + t * (2 / M ^ 3 + Real.sqrt (kappa a) * r))
    (hG1 : (K ^ 3 - 1) / M ^ 3 ≤ nsc g) (hG2 : nsc g ≤ K ^ 3 / M ^ 3)
    (hg1 : -2 ≤ g) (hg2 : g ≤ 1) (haneg : -2 ≤ a) (ha1 : a ≤ 1) :
    |a - g| ≤ (60000 + 20 * C0 ^ 2) * t ^ 3 * ((K * M ^ 2)⁻¹ + r) := by
  have hM0 : 0 < M := by linarith
  have ht0 : 0 < t := by linarith
  have hM3 : 0 < M ^ 3 := by positivity
  have hx0 : 0 ≤ (K * M ^ 2)⁻¹ := by
    have : 0 < K := by linarith
    positivity
  have hk : kappa a ≤ a + 2 := kappa_le_add_two haneg ha1
  have hsq : Real.sqrt (kappa a) ≤ Real.sqrt (a + 2) := Real.sqrt_le_sqrt hk
  have e1 : 2 * t / M ^ 3 ≤ 4 * t ^ 2 / M ^ 3 :=
    div_le_div_of_nonneg_right (by nlinarith) hM3.le
  have e2 : t * (Real.sqrt (kappa a) * r) ≤ t * r * Real.sqrt (a + 2) := by
    have : Real.sqrt (kappa a) * r ≤ r * Real.sqrt (a + 2) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hsq hr0
    calc t * (Real.sqrt (kappa a) * r) ≤ t * (r * Real.sqrt (a + 2)) :=
          mul_le_mul_of_nonneg_left this ht0.le
      _ = t * r * Real.sqrt (a + 2) := by ring
  have e3 : t * (2 / M ^ 3 + Real.sqrt (kappa a) * r) ≤
      4 * t ^ 2 / M ^ 3 + t * r * Real.sqrt (a + 2) := by
    have : t * (2 / M ^ 3) = 2 * t / M ^ 3 := by ring
    rw [mul_add, this]
    linarith
  have h := edgeQ_nonneg hC0 hc hK hM ht hr0 hr (by linarith) (by linarith) hG1 hG2 haneg
    ha1 hg1 hg2
  exact h.trans (const_le_const ht (by positivity))

/-- Main range, eigenvalue below `-2`: the eigenvalue is replaced by the edge `-2`. -/
private lemma edgeQ_below {C0 : ℝ} (hC0 : 1 ≤ C0) (hc : EdgeComp C0) {K M t r a g : ℝ}
    (hK : 1 ≤ K) (hM : 1 ≤ M) (ht : 1 ≤ t) (hr0 : 0 ≤ r) (hr : r * M ^ 2 ≤ 1)
    (hA1 : K ^ 3 / M ^ 3 - t * (2 / M ^ 3 + Real.sqrt (kappa a) * r) ≤ nsc a)
    (hG1 : (K ^ 3 - 1) / M ^ 3 ≤ nsc g) (hG2 : nsc g ≤ K ^ 3 / M ^ 3)
    (hg1 : -2 ≤ g) (hg2 : g ≤ 1) (haneg : a < -2) (ha : |a| ≤ 2 + t * (r + (M ^ 2)⁻¹)) :
    |a - g| ≤ (60000 + 20 * C0 ^ 2) * t ^ 3 * ((K * M ^ 2)⁻¹ + r) := by
  have hC0' : 0 < C0 := by linarith
  have hM0 : 0 < M := by linarith
  have hK0 : 0 < K := by linarith
  have ht0 : 0 < t := by linarith
  have hM3 : 0 < M ^ 3 := by positivity
  have hx0 : 0 ≤ (K * M ^ 2)⁻¹ := by positivity
  have hr1 : r ≤ (M ^ 2)⁻¹ := by
    rw [← one_div, le_div_iff₀ (by positivity)]
    exact hr
  have hu0 : 0 ≤ (M ^ 2)⁻¹ := by positivity
  have hna : nsc a = 0 := nsc_eq_zero haneg.le
  have hkap : kappa a ≤ t * (r + (M ^ 2)⁻¹) := kappa_le_of_lt haneg ha
  have hs1 : t * (r + (M ^ 2)⁻¹) ≤ 2 * t * (M ^ 2)⁻¹ := by
    have := mul_le_mul_of_nonneg_left hr1 ht0.le
    calc t * (r + (M ^ 2)⁻¹) = t * r + t * (M ^ 2)⁻¹ := by ring
      _ ≤ t * (M ^ 2)⁻¹ + t * (M ^ 2)⁻¹ := by linarith
      _ = 2 * t * (M ^ 2)⁻¹ := by ring
  have hsq : Real.sqrt (kappa a) ≤ 2 * t / M := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have e2 : (2 * t / M) ^ 2 = 4 * t ^ 2 * (M ^ 2)⁻¹ := by
      rw [div_pow, div_eq_mul_inv]
      ring
    rw [e2]
    have e3 : 2 * t * (M ^ 2)⁻¹ ≤ 4 * t ^ 2 * (M ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right (by nlinarith) hu0
    linarith
  have hP : t * (2 / M ^ 3 + Real.sqrt (kappa a) * r) ≤ 4 * t ^ 2 / M ^ 3 := by
    have e1 : Real.sqrt (kappa a) * r ≤ 2 * t / M * (M ^ 2)⁻¹ :=
      mul_le_mul hsq hr1 hr0 (by positivity)
    have e2 : 2 * t / M * (M ^ 2)⁻¹ = 2 * t / M ^ 3 := by
      field_simp
    have e3 : t * (2 / M ^ 3 + Real.sqrt (kappa a) * r) ≤ t * (2 / M ^ 3 + 2 * t / M ^ 3) :=
      mul_le_mul_of_nonneg_left (by linarith) ht0.le
    have e4 : t * (2 / M ^ 3 + 2 * t / M ^ 3) = (2 * t + 2 * t ^ 2) / M ^ 3 := by
      field_simp
    have e5 : (2 * t + 2 * t ^ 2) / M ^ 3 ≤ 4 * t ^ 2 / M ^ 3 :=
      div_le_div_of_nonneg_right (by nlinarith) hM3.le
    linarith
  have hA1' : K ^ 3 / M ^ 3 - (4 * t ^ 2 / M ^ 3 + t * r * Real.sqrt (-2 + 2)) ≤ nsc (-2) := by
    rw [nsc_eq_zero le_rfl, show (-2 : ℝ) + 2 = 0 by norm_num, Real.sqrt_zero]
    rw [hna] at hA1
    linarith
  have hA2' : nsc (-2) ≤
      (K ^ 3 - 1) / M ^ 3 + (4 * t ^ 2 / M ^ 3 + t * r * Real.sqrt (-2 + 2)) := by
    rw [nsc_eq_zero le_rfl, show (-2 : ℝ) + 2 = 0 by norm_num, Real.sqrt_zero]
    have h1 : 1 ≤ K ^ 3 := one_le_pow₀ hK
    have h2 : 0 ≤ (K ^ 3 - 1) / M ^ 3 := div_nonneg (by linarith) hM3.le
    have h3 : 0 ≤ 4 * t ^ 2 / M ^ 3 := by positivity
    linarith
  have h := edgeQ_nonneg hC0 hc hK hM ht hr0 hr hA1' hA2' hG1 hG2 le_rfl (by norm_num) hg1 hg2
  have hK3 : K ^ 3 ≤ 4 * t ^ 2 := by
    have : K ^ 3 / M ^ 3 ≤ 4 * t ^ 2 / M ^ 3 := by
      rw [hna] at hA1
      linarith
    exact (div_le_div_iff_of_pos_right hM3).1 this
  have hK2t : K ≤ 2 * t := by
    by_contra h'
    rw [not_le] at h'
    have h1 := pow_lt_pow_left₀ h' (by positivity) (by norm_num : 3 ≠ 0)
    have h2 : t ^ 2 ≤ t ^ 3 := by nlinarith
    have h3 : (2 * t) ^ 3 = 8 * t ^ 3 := by ring
    have h4 : 0 < t ^ 3 := by positivity
    linarith
  have hxK : (2 * t * M ^ 2)⁻¹ ≤ (K * M ^ 2)⁻¹ := by
    apply inv_anti₀ (by positivity)
    exact mul_le_mul_of_nonneg_right hK2t (by positivity)
  have hdist : |a - -2| ≤ t * r + t * (M ^ 2)⁻¹ := by
    have hneg : a < 0 := by linarith
    rw [abs_of_neg hneg] at ha
    rw [sub_neg_eq_add, abs_of_neg (by linarith)]
    nlinarith
  have hdist2 : t * (M ^ 2)⁻¹ ≤ 2 * t ^ 2 * (K * M ^ 2)⁻¹ := by
    have e1 : t * (M ^ 2)⁻¹ = 2 * t ^ 2 * (2 * t * M ^ 2)⁻¹ := by
      field_simp
    rw [e1]
    exact mul_le_mul_of_nonneg_left hxK (by positivity)
  have htr : t * r ≤ C0 ^ 2 * t ^ 2 * r := by
    have h1 : t ≤ t ^ 2 := by nlinarith
    have h2 : t ^ 2 ≤ C0 ^ 2 * t ^ 2 := le_mul_of_one_le_left (sq_nonneg t) (one_le_pow₀ hC0)
    exact mul_le_mul_of_nonneg_right (h1.trans h2) hr0
  have h1 : |a - g| ≤ |a - -2| + |-2 - g| := abs_sub_le a (-2) g
  have h2 := final_comb hC0 ht hx0 hr0
  linarith

/-- Both ranges together, in the cube-root variables. -/
private lemma edgeQ_real {C0 : ℝ} (hC0 : 1 ≤ C0) (hc : EdgeComp C0) {K M t r a g : ℝ}
    (hK : 1 ≤ K) (hM : 1 ≤ M) (hKM : 2 * K ^ 3 ≤ M ^ 3 + 1)
    (ht : 1 ≤ t) (hr0 : 0 ≤ r) (hr : r * M ^ 2 ≤ 1)
    (hA1 : K ^ 3 / M ^ 3 - t * (2 / M ^ 3 + Real.sqrt (kappa a) * r) ≤ nsc a)
    (hA2 : nsc a ≤ (K ^ 3 - 1) / M ^ 3 + t * (2 / M ^ 3 + Real.sqrt (kappa a) * r))
    (hG1 : (K ^ 3 - 1) / M ^ 3 ≤ nsc g) (hG2 : nsc g ≤ K ^ 3 / M ^ 3)
    (hg1 : -2 ≤ g) (hg2 : g ≤ 2) (ha : |a| ≤ 2 + t * (r + (M ^ 2)⁻¹)) :
    |a - g| ≤ (60000 + 20 * C0 ^ 2) * t ^ 3 * ((K * M ^ 2)⁻¹ + r) := by
  have hM0 : 0 < M := by linarith
  have hK0 : 0 < K := by linarith
  have ht0 : 0 < t := by linarith
  have hM3 : 0 < M ^ 3 := by positivity
  have hKleM : K ≤ M := by
    by_contra h
    rw [not_le] at h
    have h1 := pow_lt_pow_left₀ h hM0.le (by norm_num : 3 ≠ 0)
    have h2 : 1 ≤ M ^ 3 := one_le_pow₀ hM
    linarith
  by_cases hfar : M ^ 2 < 100 * t
  · exact edgeQ_far hK hM hKleM ht hr0 hr hg1 hg2 ha (by linarith [sq_nonneg C0]) hfar
  · rw [not_lt] at hfar
    have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM
    have hM23 : M ^ 2 ≤ M ^ 3 := pow_le_pow_right₀ hM (by norm_num)
    have hM100 : 100 ≤ M ^ 3 := by nlinarith
    have hr1 : r ≤ (M ^ 2)⁻¹ := by
      rw [← one_div, le_div_iff₀ (by positivity)]
      exact hr
    have htu : t * (M ^ 2)⁻¹ ≤ 1 / 100 := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      linarith
    have hs1 : t * (r + (M ^ 2)⁻¹) ≤ 2 * (t * (M ^ 2)⁻¹) := by
      nlinarith [mul_le_mul_of_nonneg_left hr1 ht0.le]
    have hk2 : kappa a ≤ 2 := kappa_le_two (by linarith) ha
    have hsk2 : Real.sqrt (kappa a) ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by linarith⟩
    have hε : t * (2 / M ^ 3 + Real.sqrt (kappa a) * r) ≤ 1 / 25 := by
      have e1 : 2 / M ^ 3 ≤ 2 * (M ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv]
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hM23
      have e2 : Real.sqrt (kappa a) * r ≤ 2 * (M ^ 2)⁻¹ := by
        have : Real.sqrt (kappa a) * r ≤ 2 * r := mul_le_mul_of_nonneg_right hsk2 hr0
        linarith
      have e3 : t * (2 / M ^ 3 + Real.sqrt (kappa a) * r) ≤ t * (4 * (M ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (by linarith) ht0.le
      linarith
    have hK3M : K ^ 3 / M ^ 3 ≤ 51 / 100 := by
      rw [div_le_iff₀ hM3]
      nlinarith
    have hK3M' : (K ^ 3 - 1) / M ^ 3 ≤ K ^ 3 / M ^ 3 :=
      div_le_div_of_nonneg_right (by linarith) hM3.le
    have ha1 : a < 1 := lt_one_of_nsc_lt (by linarith)
    have hg1' : g < 1 := lt_one_of_nsc_lt (by linarith)
    by_cases haneg : -2 ≤ a
    · exact edgeQ_above hC0 hc hK hM ht hr0 hr hA1 hA2 hG1 hG2 hg1 hg1'.le haneg ha1.le
    · rw [not_le] at haneg
      exact edgeQ_below hC0 hc hK hM ht hr0 hr hA1 hG1 hG2 hg1 hg1'.le haneg ha

/-- Rigidity at the edge with the `q`-terms, for natural indices: `k` is the distance to the
nearer edge and `r` stands for `q⁻²`. -/
private lemma edge_bound_q : ∃ C > 0, ∀ (N k : ℕ) (t r a g : ℝ), 2 ≤ N → 1 ≤ k → 2 * k ≤ N + 1 →
    1 ≤ t → 0 ≤ r → r ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) →
    (k : ℝ) / N - t * (2 / N + Real.sqrt (kappa a) * r) ≤ nsc a →
    nsc a ≤ ((k : ℝ) - 1) / N + t * (2 / N + Real.sqrt (kappa a) * r) →
    ((k : ℝ) - 1) / N ≤ nsc g → nsc g ≤ (k : ℝ) / N → -2 ≤ g → g ≤ 2 →
    |a| ≤ 2 + t * (r + (N : ℝ) ^ (-(2 : ℝ) / 3)) →
    |a - g| ≤ C * t ^ 3 * ((k : ℝ) ^ (-(1 : ℝ) / 3) * (N : ℝ) ^ (-(2 : ℝ) / 3) + r) := by
  obtain ⟨C0, hC0, hc⟩ := nsc_rhoSc_comparable
  refine ⟨60000 + 20 * C0 ^ 2, by positivity, ?_⟩
  intro N k t r a g hN hk hkN ht hr0 hrN hA1 hA2 hG1 hG2 hg1 hg2 ha
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkN' : 2 * (k : ℝ) ≤ N + 1 := by exact_mod_cast hkN
  obtain ⟨K, hK, hKk, hK1, -, -⟩ := exists_cube_root hk'
  obtain ⟨M, hM, hMN, -, hM2, -⟩ := exists_cube_root hN'
  have hM0 : 0 < M := by linarith
  have hK0 : 0 < K := by linarith
  rw [hM2] at hrN ha
  rw [hK1, hM2]
  rw [← hKk, ← hMN] at hA1 hA2 hG1 hG2 hkN'
  have hr : r * M ^ 2 ≤ 1 := by
    calc r * M ^ 2 ≤ (M ^ 2)⁻¹ * M ^ 2 := mul_le_mul_of_nonneg_right hrN (by positivity)
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have h := edgeQ_real hC0 hc hK hM hkN' ht hr0 hr hA1 hA2 hG1 hG2 hg1 hg2 ha
  rwa [mul_inv] at h

/-- Deterministic step of Proposition 8.3 and Theorem 2.13 of [15], including `j = N`. -/
theorem abs_eigAsc_sub_gammaLoc_le_q : ∃ C > 0, ∀ (N : ℕ), 2 ≤ N →
    ∀ (H : Matrix (Fin N) (Fin N) ℝ) (hH : H.IsHermitian) (t q : ℝ), 1 ≤ t →
    (N : ℝ) ^ ((1 : ℝ) / 3) ≤ q →
    (∀ E, |countFn hH E - nsc E| ≤ t * (1 / N + 1 / q ^ 3 + Real.sqrt (kappa E) / q ^ 2)) →
    (∀ α, |hH.eigenvalues α| ≤ 2 + t * (1 / q ^ 2 + (N : ℝ) ^ (-(2 : ℝ) / 3))) →
    ∀ j : Fin N, |eigAsc hH j - gammaLoc N ((j : ℕ) + 1)| ≤
      C * t ^ C * ((min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ))) ^ (-(1 : ℝ) / 3) *
        (N : ℝ) ^ (-(2 : ℝ) / 3) + 1 / q ^ 2) := by
  obtain ⟨C1, hC1, hedge⟩ := edge_bound_q
  refine ⟨C1 + 3, by positivity, ?_⟩
  intro N hN H hH t q ht hq hcount hnorm j
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hjN : j.val < N := j.isLt
  have ht0 : 0 < t := by linarith
  obtain ⟨M, hM, hMN, -, hM2, hMdef⟩ := exists_cube_root hN1
  have hM0 : 0 < M := by linarith
  have hMq : M ≤ q := by rw [← hMdef]; exact hq
  have hq0 : 0 < q := by linarith
  have hr0 : 0 ≤ 1 / q ^ 2 := by positivity
  have hrN : 1 / q ^ 2 ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) := by
    rw [hM2, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hM0.le hMq 2)
  have hq3 : 1 / q ^ 3 ≤ 1 / (N : ℝ) := by
    rw [← hMN]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hM0.le hMq 3)
  -- the counting bound at the `j`-th eigenvalue
  have hε : Continuous (fun E : ℝ =>
      t * (1 / (N : ℝ) + 1 / q ^ 3 + Real.sqrt (kappa E) / q ^ 2)) := by
    have := continuous_kappa
    fun_prop
  obtain ⟨hb1, hb2⟩ := nsc_eigAsc_bounds_err hH _ hε hcount j
  obtain ⟨α, hα⟩ := exists_eigenvalue_eq_eigAsc hH j
  have hnormj : |eigAsc hH j| ≤ 2 + t * (1 / q ^ 2 + (N : ℝ) ^ (-(2 : ℝ) / 3)) := by
    rw [hα]
    exact hnorm α
  have hγ := nsc_gammaLoc (N := N) (j := j.val + 1) (by omega) (by omega)
  have hγ1 := neg_two_le_gammaLoc (N := N) (j := j.val + 1) (by omega) (by omega)
  have hγ2 := gammaLoc_le_two (N := N) (j := j.val + 1) (by omega) (by omega)
  push_cast at hγ
  have hεle : ∀ a : ℝ, t * (1 / (N : ℝ) + 1 / q ^ 3 + Real.sqrt (kappa a) / q ^ 2) ≤
      t * (2 / N + Real.sqrt (kappa a) * (1 / q ^ 2)) := by
    intro a
    refine mul_le_mul_of_nonneg_left ?_ ht0.le
    have : Real.sqrt (kappa a) / q ^ 2 = Real.sqrt (kappa a) * (1 / q ^ 2) := by
      rw [mul_one_div]
    have h2 : 2 / (N : ℝ) = 1 / N + 1 / N := by ring
    linarith
  have hC : C1 * t ^ 3 ≤ (C1 + 3) * t ^ (C1 + 3) := by
    have h1 : t ^ (3 : ℝ) ≤ t ^ (C1 + 3) :=
      Real.rpow_le_rpow_of_exponent_le ht (by linarith)
    have h2 : t ^ (3 : ℝ) = t ^ 3 := by norm_num
    rw [h2] at h1
    have h3 : 0 ≤ t ^ 3 := by positivity
    nlinarith
  generalize eigAsc hH j = a at hb1 hb2 hnormj ⊢
  generalize gammaLoc N (j.val + 1) = γ at hγ hγ1 hγ2 ⊢
  have hb1' : ((j.val : ℝ) + 1) / N - t * (2 / N + Real.sqrt (kappa a) * (1 / q ^ 2)) ≤ nsc a := by
    have := hεle a
    linarith
  have hb2' : nsc a ≤ (j.val : ℝ) / N + t * (2 / N + Real.sqrt (kappa a) * (1 / q ^ 2)) := by
    have := hεle a
    linarith
  by_cases hcase : j.val + 1 ≤ N - j.val
  · -- lower half: `k = j + 1`
    have hle : (j.val : ℝ) + 1 ≤ (N : ℝ) - j.val := by
      have h : ((j.val + 1 : ℕ) : ℝ) ≤ ((N - j.val : ℕ) : ℝ) := Nat.cast_le.2 hcase
      rw [Nat.cast_sub hjN.le] at h
      push_cast at h
      exact h
    rw [min_eq_left hle]
    have h := hedge N (j.val + 1) t (1 / q ^ 2) a γ hN (by omega) (by omega) ht hr0 hrN
      (by push_cast; exact hb1')
      (by
        push_cast
        have : (j.val : ℝ) + 1 - 1 = j.val := by ring
        rw [this]
        exact hb2')
      (by
        push_cast
        rw [hγ]
        gcongr
        linarith)
      (by
        push_cast
        exact hγ.le)
      hγ1 hγ2 hnormj
    push_cast at h
    refine h.trans ?_
    have hX : 0 ≤ ((j.val : ℝ) + 1) ^ (-(1 : ℝ) / 3) * (N : ℝ) ^ (-(2 : ℝ) / 3) + 1 / q ^ 2 := by
      positivity
    exact mul_le_mul_of_nonneg_right hC hX
  · -- upper half: `k = N - j`, by reflection `x ↦ -x`
    have hlt : (N : ℝ) - j.val ≤ (j.val : ℝ) + 1 := by
      have h : ((N - j.val : ℕ) : ℝ) ≤ ((j.val + 1 : ℕ) : ℝ) := Nat.cast_le.2 (by omega)
      rw [Nat.cast_sub hjN.le] at h
      push_cast at h
      exact h
    rw [min_eq_right hlt]
    have h := hedge N (N - j.val) t (1 / q ^ 2) (-a) (-γ) hN (by omega) (by omega) ht hr0 hrN
      (by
        rw [kappa_neg, nsc_neg, Nat.cast_sub hjN.le]
        have : ((N : ℝ) - j.val) / N = 1 - (j.val : ℝ) / N := by
          field_simp
        rw [this]
        linarith)
      (by
        rw [kappa_neg, nsc_neg, Nat.cast_sub hjN.le]
        have : ((N : ℝ) - j.val - 1) / N = 1 - ((j.val : ℝ) + 1) / N := by
          field_simp
          ring
        rw [this]
        linarith)
      (by
        rw [nsc_neg, hγ, Nat.cast_sub hjN.le]
        have : ((N : ℝ) - j.val - 1) / N = 1 - ((j.val : ℝ) + 1) / N := by
          field_simp
          ring
        rw [this])
      (by
        rw [nsc_neg, hγ, Nat.cast_sub hjN.le]
        have : ((N : ℝ) - j.val) / N = 1 - (j.val : ℝ) / N := by
          field_simp
        rw [this]
        have : (j.val : ℝ) / N ≤ ((j.val : ℝ) + 1) / N := by gcongr; linarith
        linarith)
      (by linarith) (by linarith) (by rwa [abs_neg])
    rw [neg_sub_neg, abs_sub_comm] at h
    rw [Nat.cast_sub hjN.le] at h
    refine h.trans ?_
    have hX : 0 ≤ ((N : ℝ) - j.val) ^ (-(1 : ℝ) / 3) * (N : ℝ) ^ (-(2 : ℝ) / 3) + 1 / q ^ 2 := by
      have : 0 ≤ (N : ℝ) - j.val := by
        have : (j.val : ℝ) < N := by exact_mod_cast hjN
        linarith
      positivity
    exact mul_le_mul_of_nonneg_right hC hX

/-! ### Compiled checks at a concrete nondegenerate point

`N = 2`, `H = diag(-2, 2)`, `t = 1` and `q = 2`: the counting function equals `0`, `1/2`, `1` on
`(-∞, -2)`, `[-2, 2)`, `[2, ∞)`, every eigenvalue has absolute value `2`, and `2^{1/3} ≤ 2`. -/

example : ∃ C > 0, ∀ j : Fin 2,
    |eigAsc checkDiag_isHermitian j - gammaLoc 2 ((j : ℕ) + 1)| ≤
      C * (1 : ℝ) ^ C * ((min (((j : ℕ) : ℝ) + 1) (((2 : ℕ) : ℝ) - (j : ℕ))) ^ (-(1 : ℝ) / 3) *
        ((2 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) + 1 / (2 : ℝ) ^ 2) := by
  obtain ⟨C, hC, h⟩ := abs_eigAsc_sub_gammaLoc_le_q
  have hq : ((2 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ 2 := by
    calc ((2 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ ((2 : ℕ) : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := by norm_num
  refine ⟨C, hC, h 2 le_rfl checkDiag checkDiag_isHermitian 1 2 le_rfl hq ?_ ?_⟩
  · intro E
    rw [countFn_checkDiag]
    have h0 := nsc_nonneg E
    have h1 := nsc_le_one E
    have hk : 0 ≤ Real.sqrt (kappa E) / (2 : ℝ) ^ 2 := by positivity
    have key :
        |((if -2 ≤ E then 1 else 0) + (if 2 ≤ E then 1 else 0) : ℝ) / 2 - nsc E| ≤ 1 / 2 := by
      rcases lt_or_ge E (-2) with hE | hE
      · have hE2 : ¬ (2 ≤ E) := by linarith
        rw [nsc_eq_zero hE.le]
        simp [not_le.2 hE, hE2]
      · rcases lt_or_ge E 2 with hE2 | hE2
        · simp only [hE, not_le.2 hE2, ite_true, ite_false]
          rw [abs_le]
          constructor <;> norm_num <;> linarith
        · rw [nsc_eq_one hE2]
          simp [hE, hE2]
    refine key.trans ?_
    norm_num
    linarith
  · intro α
    have : |checkDiag_isHermitian.eigenvalues α| = 2 := by
      fin_cases α
      · rcases checkDiag_eigenvalues with ⟨h0, -⟩ | ⟨h0, -⟩ <;> simp [h0]
      · rcases checkDiag_eigenvalues with ⟨-, h1⟩ | ⟨-, h1⟩ <;> simp [h1]
    rw [this]
    have h1 : (0 : ℝ) < ((2 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) := by positivity
    have h2 : (0 : ℝ) < 1 / (2 : ℝ) ^ 2 := by positivity
    linarith

#print axioms abs_eigAsc_sub_gammaLoc_le_q

end WEdgeNS
