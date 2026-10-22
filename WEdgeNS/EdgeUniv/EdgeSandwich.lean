import WEdgeNS.EdgeUniv.CountApprox

/-!
# The edge event and the smoothed-trace sandwich
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- The event of Lemma 5.6 on one matrix, with the constant `C`: `‖H‖ ≤ 3` (from (3.12) or (3.4)),
(5.24) for `η ≤ N^{-2/3}`, (5.25) and (5.26). -/
def edgeInputEvent (N : ℕ) (C : ℝ) : Set (Entries N) :=
  {ω | (∀ α, |(symOfEntries_isHermitian ω).eigenvalues α| ≤ 3) ∧
    (∀ z ∈ specDomain N C, z.im ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) →
      ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ phi N ^ C / (N * z.im)) ∧
    |(N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2)| ≤ phi N ^ C ∧
    ((Finset.univ.filter fun α => |(symOfEntries_isHermitian ω).eigenvalues α - 2| ≤
        2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)).card : ℝ) ≤ phi N ^ (2 * C)}

/-- `Tr (χ_{[y,E₂]} * θ_η)(H)` is nonincreasing in the left endpoint `y`. -/
private lemma smoothCount_anti_left {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {η : ℝ} (hη : 0 < η) {y y' : ℝ} (hy : y ≤ y') (E₂ : ℝ) :
    smoothCount hH η y' E₂ ≤ smoothCount hH η y E₂ := by
  have hcont : ∀ α, Continuous fun x : ℝ => thetaEta η (hH.eigenvalues α - x) := by
    intro α
    unfold thetaEta
    exact Continuous.div continuous_const (by fun_prop) (fun x => by positivity)
  unfold smoothCount
  refine Finset.sum_le_sum fun α _ => ?_
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((hcont α).intervalIntegrable (μ := volume) y y')
    ((hcont α).intervalIntegrable (μ := volume) y' E₂)
  have hnn : 0 ≤ ∫ x in y..y', thetaEta η (hH.eigenvalues α - x) :=
    intervalIntegral.integral_nonneg hy fun x _ => by unfold thetaEta; positivity
  linarith

/-- `N(y, E₂)` is nonincreasing in the left endpoint `y`. -/
private lemma countIcc_anti_left {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {y y' : ℝ} (hy : y ≤ y') (E₂ : ℝ) : countIcc hH y' E₂ ≤ countIcc hH y E₂ := by
  unfold countIcc
  refine Finset.card_le_card fun α hα => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα ⊢
  exact ⟨hy.trans hα.1, hα.2⟩

/-- The window count as a sum of indicators of the intervals `[λ_α - ℓ₁, λ_α + ℓ₁]`. -/
private lemma countIcc_window_eq {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    (ℓ₁ y : ℝ) :
    (countIcc hH (y - ℓ₁) (y + ℓ₁) : ℝ) = ∑ α, Set.indicator
      (Set.Icc (hH.eigenvalues α - ℓ₁) (hH.eigenvalues α + ℓ₁)) (fun _ => (1 : ℝ)) y := by
  simp only [countIcc, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs with h
  · rw [Set.indicator_of_mem]
    exact ⟨by linarith [h.2], by linarith [h.1]⟩
  · rw [Set.indicator_of_notMem]
    rintro ⟨h1, h2⟩
    exact h ⟨by linarith, by linarith⟩

private lemma indicator_Icc_intervalIntegrable (c d a b : ℝ) :
    IntervalIntegrable (Set.indicator (Set.Icc c d) (fun _ => (1 : ℝ))) volume a b := by
  refine Integrable.intervalIntegrable ?_
  refine (integrable_indicator_iff measurableSet_Icc).2 ?_
  exact integrableOn_const (by simp)

private lemma integral_indicator_Icc_le {c d : ℝ} (hcd : c ≤ d) {a b : ℝ} (hab : a ≤ b) :
    ∫ y in a..b, Set.indicator (Set.Icc c d) (fun _ => (1 : ℝ)) y ≤ d - c := by
  rw [intervalIntegral.integral_of_le hab]
  have hi : Integrable (Set.indicator (Set.Icc c d) (fun _ : ℝ => (1 : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  calc _ ≤ ∫ y, Set.indicator (Set.Icc c d) (fun _ => (1 : ℝ)) y :=
        setIntegral_le_integral hi (Filter.Eventually.of_forall fun y => by
          unfold Set.indicator; split_ifs <;> norm_num)
    _ = d - c := by
        rw [integral_indicator measurableSet_Icc]
        simp [hcd]


/-- Averaging a pointwise bound `X ≤ D + K T(y)` over `y ∈ [a, b]`. -/
private lemma avg_le {X D K a b : ℝ} {T : ℝ → ℝ} (hab : a ≤ b)
    (hT : IntervalIntegrable T volume a b)
    (h : ∀ y ∈ Set.Icc a b, X ≤ D + K * T y) :
    X * (b - a) ≤ D * (b - a) + K * ∫ y in a..b, T y := by
  have h1 : ∫ y in a..b, X ≤ ∫ y in a..b, (D + K * T y) :=
    intervalIntegral.integral_mono_on hab intervalIntegrable_const
      (intervalIntegrable_const.add (hT.const_mul K)) h
  rw [intervalIntegral.integral_add intervalIntegrable_const (hT.const_mul K),
    intervalIntegral.integral_const_mul] at h1
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h1
  linarith

/-- The window count `y ↦ N(y - ℓ₁, y + ℓ₁)` is interval integrable. -/
private lemma countIcc_window_intervalIntegrable {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (ℓ₁ a b : ℝ) :
    IntervalIntegrable (fun y : ℝ => (countIcc hH (y - ℓ₁) (y + ℓ₁) : ℝ)) volume a b := by
  have : (fun y : ℝ => (countIcc hH (y - ℓ₁) (y + ℓ₁) : ℝ)) = fun y => ∑ α, Set.indicator
      (Set.Icc (hH.eigenvalues α - ℓ₁) (hH.eigenvalues α + ℓ₁)) (fun _ => (1 : ℝ)) y := by
    funext y; exact countIcc_window_eq hH ℓ₁ y
  rw [this]
  have h := IntervalIntegrable.sum (μ := volume) (a := a) (b := b) Finset.univ
    (f := fun α : Fin N => Set.indicator
      (Set.Icc (hH.eigenvalues α - ℓ₁) (hH.eigenvalues α + ℓ₁)) (fun _ => (1 : ℝ)))
    fun α _ => indicator_Icc_intervalIntegrable _ _ a b
  convert h using 1
  funext y
  simp [Finset.sum_apply]

/-- `∫_a^b N(y - ℓ₁, y + ℓ₁) dy ≤ 2 ℓ₁ · #{α : λ_α ∈ [a - ℓ₁, b + ℓ₁]}`. -/
private lemma integral_countIcc_window_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {a b ℓ₁ : ℝ} (hab : a ≤ b) (hℓ : 0 ≤ ℓ₁) :
    ∫ y in a..b, (countIcc hH (y - ℓ₁) (y + ℓ₁) : ℝ) ≤
      2 * ℓ₁ * ((Finset.univ.filter fun α =>
        a - ℓ₁ ≤ hH.eigenvalues α ∧ hH.eigenvalues α ≤ b + ℓ₁).card : ℝ) := by
  have : (fun y : ℝ => (countIcc hH (y - ℓ₁) (y + ℓ₁) : ℝ)) = fun y => ∑ α, Set.indicator
      (Set.Icc (hH.eigenvalues α - ℓ₁) (hH.eigenvalues α + ℓ₁)) (fun _ => (1 : ℝ)) y := by
    funext y; exact countIcc_window_eq hH ℓ₁ y
  rw [this, intervalIntegral.integral_finsetSum fun α _ => indicator_Icc_intervalIntegrable _ _ a b]
  have hc : (((Finset.univ.filter fun α =>
        a - ℓ₁ ≤ hH.eigenvalues α ∧ hH.eigenvalues α ≤ b + ℓ₁).card : ℕ) : ℝ) =
      ∑ α, if a - ℓ₁ ≤ hH.eigenvalues α ∧ hH.eigenvalues α ≤ b + ℓ₁ then (1 : ℝ) else 0 := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hc, Finset.mul_sum]
  refine Finset.sum_le_sum fun α _ => ?_
  split_ifs with h
  · have := integral_indicator_Icc_le (c := hH.eigenvalues α - ℓ₁) (d := hH.eigenvalues α + ℓ₁)
      (by linarith) hab
    linarith
  · have h0 : ∫ y in a..b, Set.indicator (Set.Icc (hH.eigenvalues α - ℓ₁)
        (hH.eigenvalues α + ℓ₁)) (fun _ => (1 : ℝ)) y = ∫ y in a..b, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [Set.uIcc_of_le hab] at hy
      rw [Set.indicator_of_notMem]
      rintro ⟨h1, h2⟩
      exact h ⟨by linarith [hy.1], by linarith [hy.2]⟩
    rw [h0]
    simp


/-- The averaging step of the sandwich, for a single matrix: if the bound
`|N(y, E_L) - Tr(χ_y * θ_η)| ≤ C' (q² + N(y - ℓ₁, y + ℓ₁))` holds for `y ∈ [E - ℓ, E + ℓ]`, the
number of eigenvalues in `[a - ℓ₁, b + ℓ₁]` is at most `M` for `E - ℓ ≤ a ≤ b ≤ E + ℓ`,
`ℓ₁ = 2 q² ℓ` and `C' q² (1 + 4 M) ≤ q`, then
`Tr(χ_{E+ℓ} * θ_η) - q ≤ N(E, E_L) ≤ Tr(χ_{E-ℓ} * θ_η) + q`. -/
private lemma sandwich_avg {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {η ℓ ℓ₁ q C' M E EL : ℝ} (hη : 0 < η) (hℓ : 0 < ℓ) (hℓ₁ : 0 < ℓ₁)
    (hℓ₁ℓ : ℓ₁ = 2 * q ^ 2 * ℓ) (hC' : 0 ≤ C')
    (hApp : ∀ y, E - ℓ ≤ y → y ≤ E + ℓ →
      |(countIcc hH y EL : ℝ) - smoothCount hH η y EL| ≤
        C' * (q ^ 2 + (countIcc hH (y - ℓ₁) (y + ℓ₁) : ℝ)))
    (hcard : ∀ a b, E - ℓ ≤ a → a ≤ b → b ≤ E + ℓ →
      ((Finset.univ.filter fun α =>
        a - ℓ₁ ≤ hH.eigenvalues α ∧ hH.eigenvalues α ≤ b + ℓ₁).card : ℝ) ≤ M)
    (hconst : C' * q ^ 2 * (1 + 4 * M) ≤ q) :
    smoothCount hH η (E + ℓ) EL - q ≤ (countIcc hH E EL : ℝ) ∧
      (countIcc hH E EL : ℝ) ≤ smoothCount hH η (E - ℓ) EL + q := by
  have hint : ∀ a b, E - ℓ ≤ a → a ≤ b → b ≤ E + ℓ →
      ∫ y in a..b, (countIcc hH (y - ℓ₁) (y + ℓ₁) : ℝ) ≤ 2 * ℓ₁ * M := fun a b ha hab hb =>
    (integral_countIcc_window_le hH hab hℓ₁.le).trans
      (mul_le_mul_of_nonneg_left (hcard a b ha hab hb) (by positivity))
  have hc4 : C' * (2 * ℓ₁ * M) = C' * (4 * q ^ 2 * M) * ℓ := by rw [hℓ₁ℓ]; ring
  refine ⟨?_, ?_⟩
  · -- lower bound, averaging over `[E, E + ℓ]`
    have hpt : ∀ y ∈ Set.Icc E (E + ℓ), smoothCount hH η (E + ℓ) EL ≤
        ((countIcc hH E EL : ℝ) + C' * q ^ 2) + C' * (countIcc hH (y - ℓ₁) (y + ℓ₁) : ℝ) := by
      intro y hy
      have h1 := (abs_le.1 (hApp y (by linarith [hy.1]) hy.2)).1
      have h2 : (countIcc hH y EL : ℝ) ≤ (countIcc hH E EL : ℝ) :=
        Nat.cast_le.2 (countIcc_anti_left hH hy.1 _)
      have h3 := smoothCount_anti_left hH hη hy.2 EL
      linarith
    have havg := avg_le (T := fun y => (countIcc hH (y - ℓ₁) (y + ℓ₁) : ℝ)) (a := E)
      (b := E + ℓ) (by linarith) (countIcc_window_intervalIntegrable hH ℓ₁ _ _) hpt
    have hI := mul_le_mul_of_nonneg_left (hint E (E + ℓ) (by linarith) (by linarith) le_rfl) hC'
    have hsub : E + ℓ - E = ℓ := by ring
    rw [hsub] at havg
    have h5 : smoothCount hH η (E + ℓ) EL * ℓ ≤
        ((countIcc hH E EL : ℝ) + C' * q ^ 2 * (1 + 4 * M)) * ℓ := by
      linarith
    have h6 := le_of_mul_le_mul_right h5 hℓ
    linarith
  · -- upper bound, averaging over `[E - ℓ, E]`
    have hpt : ∀ y ∈ Set.Icc (E - ℓ) E, (countIcc hH E EL : ℝ) ≤
        (smoothCount hH η (E - ℓ) EL + C' * q ^ 2) +
          C' * (countIcc hH (y - ℓ₁) (y + ℓ₁) : ℝ) := by
      intro y hy
      have h1 := (abs_le.1 (hApp y hy.1 (by linarith [hy.2]))).2
      have h2 : (countIcc hH E EL : ℝ) ≤ (countIcc hH y EL : ℝ) :=
        Nat.cast_le.2 (countIcc_anti_left hH hy.2 _)
      have h3 := smoothCount_anti_left hH hη hy.1 EL
      linarith
    have havg := avg_le (T := fun y => (countIcc hH (y - ℓ₁) (y + ℓ₁) : ℝ)) (a := E - ℓ)
      (b := E) (by linarith) (countIcc_window_intervalIntegrable hH ℓ₁ _ _) hpt
    have hI := mul_le_mul_of_nonneg_left (hint (E - ℓ) E le_rfl (by linarith) (by linarith)) hC'
    have hsub : E - (E - ℓ) = ℓ := by ring
    rw [hsub] at havg
    have h5 : (countIcc hH E EL : ℝ) * ℓ ≤
        (smoothCount hH η (E - ℓ) EL + C' * q ^ 2 * (1 + 4 * M)) * ℓ := by
      linarith
    have h6 := le_of_mul_le_mul_right h5 hℓ
    linarith

/-- The scales of the sandwich as powers of `q = N^{-ε}` and `p = N^{-2/3}`, for `N^ε ≥ 2`. -/
private lemma sandwich_scales {N : ℕ} (hN : 3 ≤ N) {ε : ℝ} (hε2 : 2 ≤ (N : ℝ) ^ ε) :
    0 < (N : ℝ) ^ (-ε) ∧ (N : ℝ) ^ (-ε) ≤ 1 / 2 ∧ (N : ℝ) ^ ε * (N : ℝ) ^ (-ε) = 1 ∧
      (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) = (N : ℝ) ^ (-(2 : ℝ) / 3) * (N : ℝ) ^ (-ε) ∧
      (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε) = (N : ℝ) ^ (-(2 : ℝ) / 3) * ((N : ℝ) ^ (-ε)) ^ 3 ∧
      (N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε) = (N : ℝ) ^ (-(2 : ℝ) / 3) * ((N : ℝ) ^ (-ε)) ^ 9 ∧
      (N : ℝ) ^ (-2 * ε) = ((N : ℝ) ^ (-ε)) ^ 2 ∧
      (N : ℝ) ^ ((2 : ℝ) / 3) * (N : ℝ) ^ (-(2 : ℝ) / 3) = 1 := by
  have hX : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  refine ⟨Real.rpow_pos_of_pos hX _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Real.rpow_neg hX.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hε2
  · rw [← Real.rpow_add hX]; simp
  · rw [← Real.rpow_add hX]; congr 1
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le, ← Real.rpow_add hX]
    congr 1; push_cast; ring
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le, ← Real.rpow_add hX]
    congr 1; push_cast; ring
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]
    congr 1; push_cast; ring
  · rw [← Real.rpow_add hX]; norm_num

/-- [26] Corollary 6.2, (6.20), on the event: for `|E - 2| ≤ φ^C N^{-2/3}`,
`ℓ = N^{-2/3-ε}/2`, `η = N^{-2/3-9ε}`:
`Tr(χ_{E+ℓ} * θ_η) - N^{-ε} ≤ N(E, ∞) ≤ Tr(χ_{E-ℓ} * θ_η) + N^{-ε}`. -/
theorem smoothCount_sandwich {C : ℝ} (hC : 0 < C) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 10 → ∃ N0 : ℕ, ∀ N ≥ N0, ∀ ω ∈ edgeInputEvent N C,
      ∀ E : ℝ, |E - 2| ≤ phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) →
        smoothCount (symOfEntries_isHermitian ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε))
            (E + (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2) (edgeEL N C) - (N : ℝ) ^ (-ε) ≤
          countIci (symOfEntries_isHermitian ω) E ∧
        (countIci (symOfEntries_isHermitian ω) E : ℝ) ≤
          smoothCount (symOfEntries_isHermitian ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε))
            (E - (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2) (edgeEL N C) + (N : ℝ) ^ (-ε) := by
  intro ε hε hε1
  obtain ⟨C', hC'pos, hC'⟩ := abs_countIcc_sub_smoothCount_le' hC
  obtain ⟨Nℓ, hNℓ⟩ := hC' ε hε hε1
  have hε2 : 0 < ε / 2 := by linarith
  have e3 := phi_rpow_le_rpow (2 * C) hε2
  have e4 : ∀ᶠ N : ℕ in atTop, 5 * C' ≤ (N : ℝ) ^ (ε / 2) :=
    (tendsto_rpow_atTop hε2 |>.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have e5 : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ ε :=
    (tendsto_rpow_atTop hε |>.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1
    (((eventually_ge_atTop Nℓ).and (eventually_ge_atTop 3)).and (e3.and (e4.and e5)))
  refine ⟨N0, fun N hN ω hω E hE => ?_⟩
  obtain ⟨⟨hNl, hN3⟩, hφM, h5C, h2ε⟩ := hN0 N hN
  obtain ⟨hnorm, h524, h525, h526⟩ := hω
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hX : (0 : ℝ) < N := by linarith
  have : NeZero N := ⟨by omega⟩
  have hφ1 : 1 ≤ phi N := by rw [phi_eq_exp hN3]; exact Real.one_le_exp (sq_nonneg _)
  have hw1 : 1 ≤ phi N ^ C := Real.one_le_rpow hφ1 hC.le
  have hM1 : 1 ≤ phi N ^ (2 * C) := Real.one_le_rpow hφ1 (by linarith)
  obtain ⟨hq0, hq1, hNq, hℓe, hq3, hq9, hq2, hp1⟩ := sandwich_scales hN3 h2ε
  have hp0 : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hX _
  have hEL : edgeEL N C = 2 + 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) := rfl
  set hH := symOfEntries_isHermitian ω with hHdef
  set w : ℝ := phi N ^ C with hw
  set M : ℝ := phi N ^ (2 * C) with hM
  set p : ℝ := (N : ℝ) ^ (-(2 : ℝ) / 3) with hp
  set q : ℝ := (N : ℝ) ^ (-ε) with hq
  set ℓ : ℝ := (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2 with hℓ
  set ℓ₁ : ℝ := (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε) with hℓ₁
  set η : ℝ := (N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε) with hη
  have hℓ' : ℓ = p * q / 2 := by rw [hℓ, hℓe]
  have hℓpos : 0 < ℓ := by rw [hℓ']; positivity
  have hℓ₁pos : 0 < ℓ₁ := by rw [hq3]; positivity
  have hηpos : 0 < η := Real.rpow_pos_of_pos hX _
  have hℓ₁ℓ : ℓ₁ = 2 * q ^ 2 * ℓ := by rw [hq3, hℓ']; ring
  have hℓ₁le : ℓ₁ ≤ ℓ := by
    have h2q : 2 * q ^ 2 ≤ 1 := by
      calc 2 * q ^ 2 ≤ 2 * (1 / 2) ^ 2 := by gcongr
        _ ≤ 1 := by norm_num
    rw [hℓ₁ℓ]
    calc 2 * q ^ 2 * ℓ ≤ 1 * ℓ := mul_le_mul_of_nonneg_right h2q hℓpos.le
      _ = ℓ := one_mul _
  have hℓw : ℓ ≤ w * p / 2 := by
    have h1 : p * q ≤ p * (1 / 2) := mul_le_mul_of_nonneg_left hq1 hp0.le
    have h2 : p ≤ w * p := le_mul_of_one_le_left hp0.le hw1
    rw [hℓ']
    linarith
  -- the upper edge: `λ_N < E_L`, so `N(y, ∞) = N(y, E_L)`
  have hlam : lambdaMax (symOfEntries ω) ≤ 2 + w * p := by
    have h1 := (abs_le.1 h525).2
    have h4 : lambdaMax (symOfEntries ω) - 2 ≤ w * p := by
      calc lambdaMax (symOfEntries ω) - 2
          = ((N : ℝ) ^ ((2 : ℝ) / 3) * p) * (lambdaMax (symOfEntries ω) - 2) := by
            rw [hp1, one_mul]
        _ = ((N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2)) * p := by ring
        _ ≤ w * p := mul_le_mul_of_nonneg_right h1 hp0.le
    linarith
  have hwp : 0 < w * p := mul_pos (by linarith) hp0
  have hIci : (countIci hH E : ℝ) = (countIcc hH E (edgeEL N C) : ℝ) := by
    congr 1
    unfold countIci countIcc
    congr 1
    refine Finset.filter_congr fun α _ => ?_
    constructor
    · intro h
      refine ⟨h, ?_⟩
      have h1 : hH.eigenvalues α ≤ lambdaMax (symOfEntries ω) :=
        (lambdaMax_isGreatest hH).2 ⟨α, rfl⟩
      rw [hEL]
      linarith
    · exact fun h => h.1
  -- the bound of `abs_countIcc_sub_smoothCount_le'` at every `y` of the averaging windows
  have hE' := abs_le.1 hE
  have hApp : ∀ y, E - ℓ ≤ y → y ≤ E + ℓ →
      |(countIcc hH y (edgeEL N C) : ℝ) - smoothCount hH η y (edgeEL N C)| ≤
        C' * (q ^ 2 + (countIcc hH (y - ℓ₁) (y + ℓ₁) : ℝ)) := by
    intro y hy1 hy2
    have hy : |y - 2| ≤ 3 / 2 * w * p := by
      rw [abs_le]
      constructor <;> linarith [hE'.1, hE'.2]
    have h := hNℓ N hNl ω hnorm h524 h525 h526 y hy
    rwa [hq2] at h
  -- the eigenvalues met by the windows are among those counted in (5.26)
  have hcard : ∀ a b, E - ℓ ≤ a → a ≤ b → b ≤ E + ℓ →
      ((Finset.univ.filter fun α =>
        a - ℓ₁ ≤ hH.eigenvalues α ∧ hH.eigenvalues α ≤ b + ℓ₁).card : ℝ) ≤ M := by
    intro a b ha hab hb
    refine le_trans ?_ h526
    have hsub : (Finset.univ.filter fun α =>
        a - ℓ₁ ≤ hH.eigenvalues α ∧ hH.eigenvalues α ≤ b + ℓ₁) ⊆
        Finset.univ.filter fun α => |hH.eigenvalues α - 2| ≤ 2 * w * p := by
      intro α hα
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα ⊢
      rw [abs_le]
      constructor <;> linarith [hα.1, hα.2, hE'.1, hE'.2]
    exact_mod_cast Finset.card_le_card hsub
  -- the error constant: `C' q² (1 + 4M) ≤ q`
  have hconst : C' * q ^ 2 * (1 + 4 * M) ≤ q := by
    have h1 : 5 * C' * M ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul h5C hφM (by linarith) (Real.rpow_nonneg hX.le _)
    have h2 : (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) = (N : ℝ) ^ ε := by
      rw [← Real.rpow_add hX]; congr 1; ring
    have h3 : C' * (1 + 4 * M) ≤ (N : ℝ) ^ ε := by
      have h4 : C' ≤ C' * M := le_mul_of_one_le_right hC'pos.le hM1
      linarith
    have hcq : C' * (1 + 4 * M) * q ≤ 1 := by
      calc C' * (1 + 4 * M) * q ≤ (N : ℝ) ^ ε * q := mul_le_mul_of_nonneg_right h3 hq0.le
        _ = 1 := hNq
    calc C' * q ^ 2 * (1 + 4 * M) = q * (C' * (1 + 4 * M) * q) := by ring
      _ ≤ q * 1 := mul_le_mul_of_nonneg_left hcq hq0.le
      _ = q := mul_one _
  have key := sandwich_avg hH hηpos hℓpos hℓ₁pos hℓ₁ℓ hC'pos.le hApp hcard hconst
  rw [hIci]
  exact key

/-! ## Checks -/

/-- The hypotheses `‖H‖ ≤ 3`, (5.24) on its domain, (5.25) and (5.26) of
`abs_countIcc_sub_smoothCount_le'` together give membership in `edgeInputEvent`. -/
example {N : ℕ} {C : ℝ} {ω : Entries N}
    (hnorm : ∀ α, |(symOfEntries_isHermitian ω).eigenvalues α| ≤ 3)
    (h524 : ∀ z ∈ specDomain N C, z.im ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) →
      ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ phi N ^ C / (N * z.im))
    (h525 : |(N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2)| ≤ phi N ^ C)
    (h526 : ((Finset.univ.filter fun α => |(symOfEntries_isHermitian ω).eigenvalues α - 2| ≤
        2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)).card : ℝ) ≤ phi N ^ (2 * C)) :
    ω ∈ edgeInputEvent N C :=
  ⟨hnorm, h524, h525, h526⟩

/-- Conversely, the conclusion of `abs_countIcc_sub_smoothCount_le'` holds for every `ω` of the
event: the hypotheses of that lemma are the conjuncts of `edgeInputEvent`. -/
example {C : ℝ} (hC : 0 < C) :
    ∃ C' > 0, ∀ ε : ℝ, 0 < ε → ε < 1 / 10 → ∃ N0 : ℕ, ∀ N ≥ N0, ∀ ω ∈ edgeInputEvent N C,
      ∀ E : ℝ, |E - 2| ≤ 3 / 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) →
        |(countIcc (symOfEntries_isHermitian ω) E (edgeEL N C) : ℝ) -
            smoothCount (symOfEntries_isHermitian ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε)) E
              (edgeEL N C)| ≤
          C' * ((N : ℝ) ^ (-2 * ε) + countIcc (symOfEntries_isHermitian ω)
            (E - (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε)) (E + (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * ε))) := by
  obtain ⟨C', hC', h⟩ := abs_countIcc_sub_smoothCount_le' hC
  refine ⟨C', hC', fun ε hε hε1 => ?_⟩
  obtain ⟨N0, hN0⟩ := h ε hε hε1
  exact ⟨N0, fun N hN ω hω => hN0 N hN ω hω.1 hω.2.1 hω.2.2.1 hω.2.2.2⟩

/-- The entries of `diag(2, 0, …, 0)`. -/
private def edgeWitness (N : ℕ) [NeZero N] : Entries N :=
  (fun i => if i = 0 then 2 else 0, fun _ => 0)

/-- `edgeWitness N` gives the diagonal matrix `diag(2, 0, …, 0)`. -/
private lemma symOfEntries_edgeWitness (N : ℕ) [NeZero N] :
    symOfEntries (edgeWitness N) = diagonal (fun i : Fin N => if i = 0 then (2 : ℝ) else 0) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [symOfEntries, edgeWitness]
  · by_cases h' : i < j
    · simp [symOfEntries, edgeWitness, h, h']
    · simp [symOfEntries, edgeWitness, h, h']

/-- Every eigenvalue of `diag(2, 0, …, 0)` is `2` or `0`. -/
private lemma edgeWitness_eig (N : ℕ) [NeZero N] (α : Fin N) :
    (symOfEntries_isHermitian (edgeWitness N)).eigenvalues α = 2 ∨
      (symOfEntries_isHermitian (edgeWitness N)).eigenvalues α = 0 := by
  have hs : spectrum ℝ (symOfEntries (edgeWitness N)) =
      Set.range (fun i : Fin N => if i = 0 then (2 : ℝ) else 0) := by
    rw [symOfEntries_edgeWitness, spectrum_diagonal]
  have h := (symOfEntries_isHermitian (edgeWitness N)).eigenvalues_mem_spectrum_real α
  rw [hs] at h
  obtain ⟨i, hi⟩ := h
  by_cases hi0 : i = 0
  · left; simpa [hi0] using hi.symm
  · right; simpa [hi0] using hi.symm

/-- The eigenvalues of `diag(2, 0, …, 0)` sum to its trace `2`. -/
private lemma edgeWitness_trace (N : ℕ) [NeZero N] :
    ∑ α, (symOfEntries_isHermitian (edgeWitness N)).eigenvalues α = 2 := by
  have h := (symOfEntries_isHermitian (edgeWitness N)).trace_eq_sum_eigenvalues
  have ht : (symOfEntries (edgeWitness N)).trace = 2 := by
    rw [symOfEntries_edgeWitness, trace_diagonal]
    simp
  rw [ht] at h
  simp only [RCLike.ofReal_real_eq_id, id] at h
  linarith

/-- `λ_N = 2` for `diag(2, 0, …, 0)`. -/
private lemma lambdaMax_edgeWitness (N : ℕ) [NeZero N] :
    lambdaMax (symOfEntries (edgeWitness N)) = 2 := by
  have hg := lambdaMax_isGreatest (symOfEntries_isHermitian (edgeWitness N))
  apply le_antisymm
  · obtain ⟨α, hα⟩ := hg.1
    rw [← hα]
    rcases edgeWitness_eig N α with h | h <;> simp [h]
  · apply hg.2
    rw [← (symOfEntries_isHermitian (edgeWitness N)).spectrum_real_eq_range_eigenvalues,
      symOfEntries_edgeWitness, spectrum_diagonal]
    exact ⟨0, by simp⟩

/-- At most one eigenvalue of `diag(2, 0, …, 0)` lies within `r < 2` of `2`. -/
private lemma edgeWitness_card (N : ℕ) [NeZero N] {r : ℝ} (hr : r < 2) :
    (Finset.univ.filter fun α =>
      |(symOfEntries_isHermitian (edgeWitness N)).eigenvalues α - 2| ≤ r).card ≤ 1 := by
  have hnn : ∀ α, 0 ≤ (symOfEntries_isHermitian (edgeWitness N)).eigenvalues α := fun α => by
    rcases edgeWitness_eig N α with h | h <;> simp [h]
  have h2 : ∀ α, |(symOfEntries_isHermitian (edgeWitness N)).eigenvalues α - 2| ≤ r →
      (symOfEntries_isHermitian (edgeWitness N)).eigenvalues α = 2 := by
    intro α hα
    rcases edgeWitness_eig N α with h | h
    · exact h
    · rw [h] at hα; norm_num at hα; linarith
  refine Finset.card_le_one.2 fun a ha b hb => ?_
  by_contra hab
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {a, b})
    (f := fun α => (symOfEntries_isHermitian (edgeWitness N)).eigenvalues α)
    (fun α _ _ => hnn α)
  rw [Finset.sum_pair hab, h2 a ha, h2 b hb, edgeWitness_trace] at hsum
  linarith

/-- Partial witness for `edgeInputEvent`: for all large `N`, the matrix `diag(2, 0, …, 0)` has
`‖H‖ ≤ 3`, satisfies (5.25) and (5.26) (one eigenvalue within `2 φ^C N^{-2/3}` of `2`), and the
domain `{z ∈ S(C) : Im z ≤ N^{-2/3}}` of (5.24) is nonempty. -/
example {C : ℝ} (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop, ∃ ω : Entries N,
      (∀ α, |(symOfEntries_isHermitian ω).eigenvalues α| ≤ 3) ∧
      |(N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2)| ≤ phi N ^ C ∧
      ((Finset.univ.filter fun α => |(symOfEntries_isHermitian ω).eigenvalues α - 2| ≤
          2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)).card : ℝ) ≤ phi N ^ (2 * C) ∧
      ∃ z ∈ specDomain N C, z.im ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) := by
  filter_upwards [phi_rpow_le_rpow C (c := 1 / 6) (by norm_num),
    window_scales hC.le (ε := 1 / 20) (by norm_num) (by norm_num),
    eventually_ge_atTop 3] with N hφ hws hN3
  obtain ⟨⟨h1, h2, h3, -⟩, -⟩ := hws
  have : NeZero N := ⟨by omega⟩
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hX : (0 : ℝ) < N := by linarith
  have hφ1 : 1 ≤ phi N := by rw [phi_eq_exp hN3]; exact Real.one_le_exp (sq_nonneg _)
  have hw1 : 1 ≤ phi N ^ C := Real.one_le_rpow hφ1 hC.le
  have hX23 : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hX _
  refine ⟨edgeWitness N, fun α => ?_, ?_, ?_, ?_⟩
  · rcases edgeWitness_eig N α with h | h <;> rw [h] <;> norm_num
  · rw [lambdaMax_edgeWitness, sub_self, mul_zero, abs_zero]
    linarith
  · have hsmall : phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) < 1 := by
      calc phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)
          ≤ (N : ℝ) ^ ((1 : ℝ) / 6) * (N : ℝ) ^ (-(2 : ℝ) / 3) :=
            mul_le_mul_of_nonneg_right hφ hX23.le
        _ = (N : ℝ) ^ (-(1 : ℝ) / 2) := by
            rw [← Real.rpow_add hX]; congr 1; ring
        _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
    have hcard := edgeWitness_card N (r := 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3))
      (by linarith)
    have hone : (1 : ℝ) ≤ phi N ^ (2 * C) := Real.one_le_rpow hφ1 (by linarith)
    calc _ ≤ (1 : ℝ) := by exact_mod_cast hcard
      _ ≤ _ := hone
  · exact ⟨⟨0, (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * (1 / 20))⟩, ⟨by simp, h1, by
      change (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * (1 / 20)) ≤ 10
      linarith⟩, h2⟩

#print axioms edgeInputEvent
#print axioms smoothCount_sandwich

end WEdgeNS
