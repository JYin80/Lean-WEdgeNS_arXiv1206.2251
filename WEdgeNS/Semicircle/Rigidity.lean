import WEdgeNS.Semicircle.Density
import WEdgeNS.Resolvent.Basic

/-!
# Rigidity from the counting bound ([26] (5.12)–(5.15))
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-! ### Facts about `ρ_sc` and `n_sc` -/

private lemma rho_continuous : Continuous rhoSc := by
  unfold rhoSc
  fun_prop

private lemma rho_nonneg (x : ℝ) : 0 ≤ rhoSc x := by
  unfold rhoSc
  positivity

private lemma rho_eq_zero_of_le {x : ℝ} (hx : x ≤ -2) : rhoSc x = 0 := by
  unfold rhoSc
  rw [Real.sqrt_eq_zero_of_nonpos (by nlinarith)]
  simp

private lemma rho_eq_zero_of_ge {x : ℝ} (hx : 2 ≤ x) : rhoSc x = 0 := by
  unfold rhoSc
  rw [Real.sqrt_eq_zero_of_nonpos (by nlinarith)]
  simp

/-- The semicircle density is integrable. -/
lemma rho_integrable : Integrable rhoSc := by
  refine rho_continuous.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) ?_
  intro x hx
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h | h
  · exact rho_eq_zero_of_le h.le
  · exact rho_eq_zero_of_ge h.le

private lemma rho_neg (x : ℝ) : rhoSc (-x) = rhoSc x := by
  unfold rhoSc
  rw [neg_sq]

/-- Increments of `n_sc` are integrals of the density. -/
private lemma nsc_sub (a b : ℝ) : nsc b - nsc a = ∫ x in a..b, rhoSc x :=
  intervalIntegral.integral_Iic_sub_Iic rho_integrable.integrableOn rho_integrable.integrableOn

/-- The semicircle density has total mass `1`. -/
lemma integral_rho : ∫ x, rhoSc x = 1 := by
  have h := integral_add_compl (measurableSet_Iic (a := (2 : ℝ))) (f := rhoSc) (μ := volume)
    rho_integrable
  have h0 : ∫ x in (Set.Iic (2 : ℝ))ᶜ, rhoSc x = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero ?_
    intro x hx
    rw [Set.mem_compl_iff, Set.mem_Iic, not_le] at hx
    exact rho_eq_zero_of_ge hx.le
  have h1 : ∫ x in Set.Iic (2 : ℝ), rhoSc x = 1 := nsc_eq_one le_rfl
  rw [h0, add_zero, h1] at h
  exact h.symm

/-- Reflection: `n_sc(-x) = 1 - n_sc(x)`. -/
lemma nsc_neg (x : ℝ) : nsc (-x) = 1 - nsc x := by
  have h1 := integral_comp_neg_Iic (-x) rhoSc
  simp_rw [rho_neg, neg_neg] at h1
  have h2 := integral_add_compl (measurableSet_Iic (a := x)) (f := rhoSc) (μ := volume)
    rho_integrable
  rw [Set.compl_Iic, integral_rho] at h2
  unfold nsc
  linarith

private lemma nsc_zero : nsc 0 = 1 / 2 := by
  have := nsc_neg 0
  rw [neg_zero] at this
  linarith

/-- The density is at least `1/4` on `[0, 1]`. -/
lemma quarter_le_rho {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : 1 / 4 ≤ rhoSc x := by
  obtain ⟨h0, h1⟩ := hx
  have hpi := Real.pi_pos
  have hpi2 := Real.pi_lt_d2
  unfold rhoSc
  rw [le_div_iff₀ (by positivity)]
  have : Real.pi / 2 ≤ Real.sqrt (4 - x ^ 2) := by
    rw [Real.le_sqrt (by positivity) (by nlinarith)]
    nlinarith
  linarith

/-- `n_sc(1) ≥ 3/4`. -/
lemma three_quarters_le_nsc_one : 3 / 4 ≤ nsc 1 := by
  have h := nsc_sub 0 1
  rw [nsc_zero] at h
  have hl : ∫ _ in (0 : ℝ)..1, (1 / 4 : ℝ) ≤ ∫ x in (0 : ℝ)..1, rhoSc x :=
    intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
      (rho_continuous.intervalIntegrable _ _) (fun x hx => quarter_le_rho hx)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hl
  linarith

/-- Classical locations are at least `-2`. -/
lemma neg_two_le_gammaLoc {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) : -2 ≤ gammaLoc N j := by
  by_contra h
  rw [not_le] at h
  have h1 := nsc_gammaLoc hj hjN
  rw [nsc_eq_zero h.le] at h1
  have hN : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hj hjN
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have : (0 : ℝ) < j / N := div_pos hj' hN
  linarith

/-- Classical locations are at most `2`. -/
lemma gammaLoc_le_two {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) : gammaLoc N j ≤ 2 := by
  by_contra h
  rw [not_le] at h
  have h1 := nsc_gammaLoc hj hjN
  rw [nsc_eq_one h.le] at h1
  have hN : 0 < N := lt_of_lt_of_le hj hjN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h2 : (N : ℝ) = j := by
    field_simp at h1
    exact h1
  have h3 : N = j := by exact_mod_cast h2
  subst h3
  rw [gammaLoc_self hj] at h
  linarith

/-! ### From the counting function to `n_sc` at an eigenvalue -/

/-- The unordered eigenvalues are a permutation of the increasing ones. -/
lemma exists_perm_eigenvalues {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) : ∃ σ : Equiv.Perm (Fin N), ∀ α, hH.eigenvalues α = eigAsc hH (σ α) := by
  have hc : Fintype.card (Fin N) = N := Fintype.card_fin N
  refine ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)).symm.trans
    ((finCongr hc).trans Fin.revPerm), fun α => ?_⟩
  simp only [Matrix.IsHermitian.eigenvalues, eigAsc]
  congr 1
  ext
  simp

/-- The number of eigenvalues `≤ E` equals the number of increasing eigenvalues `≤ E`. -/
lemma card_filter_eigenvalues {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (E : ℝ) :
    (Finset.univ.filter (fun α => hH.eigenvalues α ≤ E)).card =
      (Finset.univ.filter (fun i => eigAsc hH i ≤ E)).card := by
  obtain ⟨σ, hσ⟩ := exists_perm_eigenvalues hH
  exact Finset.card_equiv σ (fun α => by simp [hσ])

/-- Every increasing eigenvalue is an unordered eigenvalue. -/
lemma exists_eigenvalue_eq_eigAsc {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (j : Fin N) : ∃ α, eigAsc hH j = hH.eigenvalues α := by
  obtain ⟨σ, hσ⟩ := exists_perm_eigenvalues hH
  exact ⟨σ.symm j, by rw [hσ]; simp⟩

/-- Counting bound at the `j`-th eigenvalue (0-based `j`): `n_sc(λ_{j+1})` lies between
`(j + 1 - t)/N` and `(j + t)/N`. -/
private lemma nsc_eigAsc_bounds {N : ℕ} (hN : 1 ≤ N) {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (t : ℝ) (hcount : ∀ E : ℝ, |countFn hH E - nsc E| ≤ t / N)
    (j : Fin N) :
    ((j.val : ℝ) + 1 - t) / N ≤ nsc (eigAsc hH j) ∧ nsc (eigAsc hH j) ≤ ((j.val : ℝ) + t) / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
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
    rw [sub_div]
    linarith
  · have hlim : Tendsto nsc (𝓝[<] (eigAsc hH j)) (𝓝 (nsc (eigAsc hH j))) :=
      (continuous_nsc.tendsto _).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun E hE => ?_)
    have h1 := hup E hE
    have h2 := (abs_le.1 (hcount E)).1
    rw [add_div]
    linarith

/-! ### Two-sided comparison at the lower edge -/

/-- The two-sided comparison of `n_sc` and `ρ_sc` with `(x + 2)^{3/2}` and `(x + 2)^{1/2}` on
`[-2, 1]`, with constant `C0`. -/
def EdgeComp (C0 : ℝ) : Prop := ∀ x ∈ Set.Icc (-2 : ℝ) 1,
    (C0⁻¹ * (x + 2) ^ ((3 : ℝ) / 2) ≤ nsc x ∧ nsc x ≤ C0 * (x + 2) ^ ((3 : ℝ) / 2)) ∧
    (C0⁻¹ * Real.sqrt (x + 2) ≤ rhoSc x ∧ rhoSc x ≤ C0 * Real.sqrt (x + 2))

private lemma rpow_three_halves {y : ℝ} (hy : 0 ≤ y) :
    y ^ ((3 : ℝ) / 2) = Real.sqrt y ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy]
  norm_num

/-- Increments of `n_sc` on `[p, q] ⊆ [-2, 1]` are at least `(q - p) C0⁻¹ √(p + 2)`. -/
private lemma increment_lower {C0 : ℝ} (hC0 : 1 ≤ C0) (hc : EdgeComp C0) {p q : ℝ}
    (hp : -2 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) :
    (q - p) * (C0⁻¹ * Real.sqrt (p + 2)) ≤ nsc q - nsc p := by
  rw [nsc_sub]
  have hC0' : 0 < C0 := by linarith
  have h := intervalIntegral.integral_mono_on (μ := volume) hpq
    (intervalIntegrable_const (c := C0⁻¹ * Real.sqrt (p + 2)))
    (rho_continuous.intervalIntegrable p q) (fun x hx => ?_)
  · rw [intervalIntegral.integral_const, smul_eq_mul] at h
    exact h
  · calc C0⁻¹ * Real.sqrt (p + 2) ≤ C0⁻¹ * Real.sqrt (x + 2) := by
          gcongr
          linarith [hx.1]
      _ ≤ rhoSc x := (hc x ⟨by linarith [hx.1], by linarith [hx.2]⟩).2.1

/-- If `n_sc(p) ≥ K³/(2 M³)` and the increment of `n_sc` over `[p, q]` is at most `t/M³`, then
`(q - p) K M² ≤ 2 C0² t`. -/
private lemma length_bound {C0 : ℝ} (hC0 : 1 ≤ C0) (hc : EdgeComp C0) {K M t p q : ℝ}
    (hM : 0 < M) (hp : -2 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1)
    (hnp : K ^ 3 / (2 * M ^ 3) ≤ nsc p) (hd : nsc q - nsc p ≤ t / M ^ 3) :
    (q - p) * (K * M ^ 2) ≤ 2 * C0 ^ 2 * t := by
  have hC0' : 0 < C0 := by linarith
  set w := Real.sqrt (p + 2) with hw
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hnsc : nsc p ≤ C0 * w ^ 3 := by
    have := (hc p ⟨hp, by linarith⟩).1.2
    rwa [rpow_three_halves (by linarith)] at this
  have hKw : K ≤ 2 * C0 * M * w := by
    by_contra h
    rw [not_le] at h
    have h3 : (2 * C0 * M * w) ^ 3 < K ^ 3 :=
      pow_lt_pow_left₀ h (by positivity) (by norm_num)
    have h4 : K ^ 3 ≤ 2 * C0 * (M ^ 3 * w ^ 3) := by
      have h1 := hnp
      rw [div_le_iff₀ (by positivity)] at h1
      calc K ^ 3 ≤ nsc p * (2 * M ^ 3) := h1
        _ ≤ C0 * w ^ 3 * (2 * M ^ 3) :=
          mul_le_mul_of_nonneg_right hnsc (by positivity)
        _ = 2 * C0 * (M ^ 3 * w ^ 3) := by ring
    have h5 : 0 ≤ M ^ 3 * w ^ 3 := by positivity
    have h6 : (2 * C0 * M * w) ^ 3 = 8 * C0 ^ 3 * (M ^ 3 * w ^ 3) := by ring
    have h7 : C0 ≤ C0 ^ 3 := le_self_pow₀ hC0 (by norm_num)
    nlinarith
  have hinc := increment_lower hC0 hc hp hpq hq
  have h1 : (q - p) * (C0⁻¹ * w) ≤ t / M ^ 3 := hinc.trans hd
  rw [le_div_iff₀ (by positivity)] at h1
  have h2 : (q - p) * w * M ^ 3 ≤ C0 * t := by
    have : C0 * ((q - p) * (C0⁻¹ * w) * M ^ 3) = (q - p) * w * M ^ 3 := by
      field_simp
    rw [← this]
    exact mul_le_mul_of_nonneg_left h1 hC0'.le
  have hqp : 0 ≤ q - p := by linarith
  calc (q - p) * (K * M ^ 2) ≤ (q - p) * (2 * C0 * M * w * M ^ 2) := by gcongr
    _ = 2 * C0 * ((q - p) * w * M ^ 3) := by ring
    _ ≤ 2 * C0 * (C0 * t) := by gcongr
    _ = 2 * C0 ^ 2 * t := by ring

/-- If `K³ ≤ 8t` and `n_sc(x) ≤ 9t/M³` for some `x ∈ [-2, 1]`, then `K (x + 2) M² ≤ 648 C0² t`. -/
private lemma shifted_bound {C0 : ℝ} (hC0 : 1 ≤ C0) (hc : EdgeComp C0) {K M t x : ℝ}
    (hM : 0 < M) (ht : 1 ≤ t) (hx : x ∈ Set.Icc (-2 : ℝ) 1)
    (hKt : K ^ 3 ≤ 8 * t) (hn : nsc x ≤ 9 * t / M ^ 3) :
    K * ((x + 2) * M ^ 2) ≤ 648 * C0 ^ 2 * t := by
  have hC0' : 0 < C0 := by linarith
  have hx2 : 0 ≤ x + 2 := by linarith [hx.1]
  set w := Real.sqrt (x + 2) with hw
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hw2 : w ^ 2 = x + 2 := Real.sq_sqrt hx2
  have hlow : C0⁻¹ * w ^ 3 ≤ nsc x := by
    have := (hc x hx).1.1
    rwa [rpow_three_halves hx2] at this
  have hy : (w * M) ^ 3 ≤ 9 * C0 * t := by
    have h1 : C0⁻¹ * w ^ 3 ≤ 9 * t / M ^ 3 := hlow.trans hn
    rw [le_div_iff₀ (by positivity)] at h1
    have h2 : C0 * (C0⁻¹ * w ^ 3 * M ^ 3) = w ^ 3 * M ^ 3 := by field_simp
    have h3 : C0 * (C0⁻¹ * w ^ 3 * M ^ 3) ≤ C0 * (9 * t) :=
      mul_le_mul_of_nonneg_left h1 hC0'.le
    rw [h2] at h3
    calc (w * M) ^ 3 = w ^ 3 * M ^ 3 := by ring
      _ ≤ C0 * (9 * t) := h3
      _ = 9 * C0 * t := by ring
  have hy0 : 0 ≤ (w * M) ^ 3 := by positivity
  have hy2 : ((w * M) ^ 3) ^ 2 ≤ (9 * C0 * t) ^ 2 := pow_le_pow_left₀ hy0 hy 2
  have hcube : (K * (w * M) ^ 2) ^ 3 ≤ 648 * C0 ^ 2 * t ^ 3 := by
    have : (K * (w * M) ^ 2) ^ 3 = K ^ 3 * ((w * M) ^ 3) ^ 2 := by ring
    rw [this]
    calc K ^ 3 * ((w * M) ^ 3) ^ 2 ≤ (8 * t) * (9 * C0 * t) ^ 2 := by gcongr
      _ = 648 * C0 ^ 2 * t ^ 3 := by ring
  have hgoal : K * (w * M) ^ 2 ≤ 648 * C0 ^ 2 * t := by
    by_contra h
    rw [not_le] at h
    have h3 : (648 * C0 ^ 2 * t) ^ 3 < (K * (w * M) ^ 2) ^ 3 :=
      pow_lt_pow_left₀ h (by positivity) (by norm_num)
    have hB : 1 ≤ 648 * C0 ^ 2 := by nlinarith
    have h4 : 648 * C0 ^ 2 ≤ (648 * C0 ^ 2) ^ 3 := le_self_pow₀ hB (by norm_num)
    have h5 : 0 ≤ t ^ 3 := by positivity
    have h6 : (648 * C0 ^ 2 * t) ^ 3 = (648 * C0 ^ 2) ^ 3 * t ^ 3 := by ring
    nlinarith
  calc K * ((x + 2) * M ^ 2) = K * (w * M) ^ 2 := by rw [mul_pow, hw2]
    _ ≤ 648 * C0 ^ 2 * t := hgoal

/-! ### The edge estimate -/

/-- Far range `N < 20 t`: only the norm bound is used. -/
private lemma edge_far {K M t a g : ℝ} (hK : 1 ≤ K) (hM : 1 ≤ M) (hKM : 2 * K ^ 3 ≤ M ^ 3 + 1)
    (ht : 1 ≤ t) (hg1 : -2 ≤ g) (hg2 : g ≤ 2) (ha : |a| * M ^ 2 ≤ 2 * M ^ 2 + t)
    (hcase : M ^ 3 < 20 * t) : |a - g| * (K * M ^ 2) ≤ 100 * t ^ 2 := by
  have hM0 : 0 < M := by linarith
  have hK3 : 1 ≤ K ^ 3 := one_le_pow₀ hK
  have hKleM : K ≤ M := by
    by_contra h
    rw [not_le] at h
    have := pow_lt_pow_left₀ h hM0.le (by norm_num : 3 ≠ 0)
    linarith
  have ht2 : t ≤ t ^ 2 := by nlinarith
  have hga : |g| ≤ 2 := abs_le.2 ⟨hg1, hg2⟩
  have h1 : |a - g| ≤ |a| + |g| := abs_sub _ _
  have h2 : |a - g| * M ^ 2 ≤ 4 * M ^ 2 + t := by
    nlinarith [mul_le_mul_of_nonneg_right hga (sq_nonneg M),
      mul_le_mul_of_nonneg_right h1 (sq_nonneg M)]
  have h3 : |a - g| * (K * M ^ 2) ≤ (4 * M ^ 2 + t) * K := by
    calc |a - g| * (K * M ^ 2) = (|a - g| * M ^ 2) * K := by ring
      _ ≤ (4 * M ^ 2 + t) * K := by gcongr
  have h4 : (4 * M ^ 2 + t) * K ≤ (4 * M ^ 2 + t) * M := by gcongr
  have h5 : M ≤ M ^ 3 := le_self_pow₀ hM (by norm_num)
  have h6 : t * M ≤ 20 * t ^ 2 := by nlinarith
  have h7 : 4 * M ^ 3 ≤ 80 * t ^ 2 := by nlinarith
  have h8 : (4 * M ^ 2 + t) * M = 4 * M ^ 3 + t * M := by ring
  linarith

/-- Bulk range `N ≥ 20 t`, `k ≥ 8 t`: the density is bounded below on the segment between the
eigenvalue and the classical location. -/
private lemma edge_bulk {C0 : ℝ} (hC0 : 1 ≤ C0) (hc : EdgeComp C0) {K M t a g : ℝ}
    (hM : 1 ≤ M) (hKM : 2 * K ^ 3 ≤ M ^ 3 + 1) (ht : 1 ≤ t)
    (hA1 : (K ^ 3 - t) / M ^ 3 ≤ nsc a) (hA2 : nsc a ≤ (K ^ 3 - 1 + t) / M ^ 3)
    (hG1 : (K ^ 3 - 1) / M ^ 3 ≤ nsc g) (hG2 : nsc g ≤ K ^ 3 / M ^ 3)
    (hg1 : -2 ≤ g) (hM20 : 20 * t ≤ M ^ 3) (hcase : 8 * t ≤ K ^ 3) :
    |a - g| * (K * M ^ 2) ≤ 2 * C0 ^ 2 * t := by
  have hM0 : 0 < M := by linarith
  have hM3 : 0 < M ^ 3 := by positivity
  have hnsc1 := three_quarters_le_nsc_one
  have hM3t : 1 ≤ M ^ 3 / 20 := by linarith
  have hθ : K ^ 3 / M ^ 3 ≤ 21 / 40 := by
    rw [div_le_iff₀ hM3]
    linarith
  have hKt : t ≤ K ^ 3 / 8 := by linarith
  have hA2' : nsc a ≤ 189 / 320 := by
    calc nsc a ≤ (K ^ 3 - 1 + t) / M ^ 3 := hA2
      _ ≤ (9 / 8 * K ^ 3) / M ^ 3 := by gcongr; linarith
      _ = 9 / 8 * (K ^ 3 / M ^ 3) := by ring
      _ ≤ 189 / 320 := by linarith
  have hA1' : 0 < nsc a := by
    refine lt_of_lt_of_le ?_ hA1
    apply div_pos _ hM3
    linarith
  have ha1 : a < 1 := by
    by_contra h
    rw [not_lt] at h
    have := monotone_nsc h
    linarith
  have ha2 : -2 ≤ a := by
    by_contra h
    rw [not_le] at h
    rw [nsc_eq_zero h.le] at hA1'
    exact lt_irrefl _ hA1'
  have hg3 : g ≤ 1 := by
    by_contra h
    rw [not_le] at h
    have := monotone_nsc h.le
    linarith
  have hK3' : 2 ≤ K ^ 3 := by linarith
  have hhalf : K ^ 3 / (2 * M ^ 3) ≤ (K ^ 3 - 1) / M ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) hM3]
    nlinarith
  have hhalf' : K ^ 3 / (2 * M ^ 3) ≤ (K ^ 3 - t) / M ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) hM3]
    nlinarith
  have hdiff1 : K ^ 3 / M ^ 3 - (K ^ 3 - t) / M ^ 3 = t / M ^ 3 := by ring
  have hdiff2 : (K ^ 3 - 1 + t) / M ^ 3 - (K ^ 3 - 1) / M ^ 3 = t / M ^ 3 := by ring
  rcases le_total a g with hag | hga
  · have h := length_bound hC0 hc hM0 ha2 hag hg3 (hhalf'.trans hA1)
      (by rw [← hdiff1]; linarith)
    rw [abs_of_nonpos (by linarith : a - g ≤ 0), neg_sub]
    exact h
  · have h := length_bound hC0 hc hM0 hg1 hga ha1.le (hhalf.trans hG1)
      (by rw [← hdiff2]; linarith)
    rw [abs_of_nonneg (by linarith : 0 ≤ a - g)]
    exact h

/-- Edge range `N ≥ 20 t`, `k < 8 t`: both `a + 2` and `g + 2` are of order `t^{2/3} N^{-2/3}`
or smaller. -/
private lemma edge_near {C0 : ℝ} (hC0 : 1 ≤ C0) (hc : EdgeComp C0) {K M t a g : ℝ}
    (hK : 1 ≤ K) (hM : 1 ≤ M) (ht : 1 ≤ t)
    (hA2 : nsc a ≤ (K ^ 3 - 1 + t) / M ^ 3) (hG2 : nsc g ≤ K ^ 3 / M ^ 3)
    (hg1 : -2 ≤ g) (ha : |a| * M ^ 2 ≤ 2 * M ^ 2 + t)
    (hM20 : 20 * t ≤ M ^ 3) (hcase : K ^ 3 < 8 * t) :
    |a - g| * (K * M ^ 2) ≤ (648 * C0 ^ 2 + 2) * t ^ 2 := by
  have hK0 : 0 < K := by linarith
  have hM0 : 0 < M := by linarith
  have hM3 : 0 < M ^ 3 := by positivity
  have hnsc1 := three_quarters_le_nsc_one
  have hC2 : 0 ≤ C0 ^ 2 := sq_nonneg C0
  have hX : 0 ≤ K * M ^ 2 := by positivity
  have ht2 : t ≤ t ^ 2 := by nlinarith
  have hKt : K ^ 3 ≤ 8 * t := hcase.le
  have h9 : 9 * t / M ^ 3 ≤ 9 / 20 := by
    rw [div_le_iff₀ hM3]
    linarith
  have hnA : nsc a ≤ 9 * t / M ^ 3 := by
    refine hA2.trans ?_
    gcongr
    linarith
  have hnG : nsc g ≤ 9 * t / M ^ 3 := by
    refine hG2.trans ?_
    gcongr
    linarith
  have ha1 : a < 1 := by
    by_contra h
    rw [not_lt] at h
    have := monotone_nsc h
    linarith
  have hg3 : g ≤ 1 := by
    by_contra h
    rw [not_le] at h
    have := monotone_nsc h.le
    linarith
  have hGb := shifted_bound hC0 hc hM0 ht ⟨hg1, hg3⟩ hKt hnG
  have hgnn : 0 ≤ K * ((g + 2) * M ^ 2) := by
    have : 0 ≤ g + 2 := by linarith
    positivity
  have hK2t : K ≤ 2 * t := by
    by_contra h
    rw [not_le] at h
    have h1 := pow_lt_pow_left₀ h (by positivity) (by norm_num : 3 ≠ 0)
    have h2 : t ≤ t ^ 3 := le_self_pow₀ ht (by norm_num)
    have h3 : (2 * t) ^ 3 = 8 * t ^ 3 := by ring
    linarith
  have hC648 : 648 * C0 ^ 2 * t ≤ 648 * C0 ^ 2 * t ^ 2 :=
    mul_le_mul_of_nonneg_left ht2 (by positivity)
  have hnn : 0 ≤ C0 ^ 2 * t ^ 2 := by positivity
  have hB : 648 * C0 ^ 2 * t + 2 * t ^ 2 ≤ (648 * C0 ^ 2 + 2) * t ^ 2 := by
    nlinarith
  have key : |a - g| * (K * M ^ 2) = |K * ((a + 2) * M ^ 2) - K * ((g + 2) * M ^ 2)| := by
    have : K * ((a + 2) * M ^ 2) - K * ((g + 2) * M ^ 2) = (a - g) * (K * M ^ 2) := by ring
    rw [this, abs_mul, abs_of_nonneg hX]
  rw [key]
  by_cases haa : -2 ≤ a
  · have hAb := shifted_bound hC0 hc hM0 ht ⟨haa, ha1.le⟩ hKt hnA
    have hann : 0 ≤ K * ((a + 2) * M ^ 2) := by
      have : 0 ≤ a + 2 := by linarith
      positivity
    refine abs_le.2 ⟨?_, ?_⟩ <;> linarith
  · rw [not_le] at haa
    have haM : -((a + 2) * M ^ 2) ≤ t := by
      rw [abs_of_neg (by linarith)] at ha
      nlinarith
    have hneg : -(K * ((a + 2) * M ^ 2)) ≤ 2 * t ^ 2 := by
      have : -(K * ((a + 2) * M ^ 2)) = K * (-((a + 2) * M ^ 2)) := by ring
      rw [this]
      calc K * (-((a + 2) * M ^ 2)) ≤ K * t := by gcongr
        _ ≤ 2 * t * t := by gcongr
        _ = 2 * t ^ 2 := by ring
    have hnpos : K * ((a + 2) * M ^ 2) ≤ 0 := by
      have : (a + 2) * M ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      exact mul_nonpos_of_nonneg_of_nonpos hK0.le this
    refine abs_le.2 ⟨?_, ?_⟩ <;> linarith

/-- Rigidity at the edge in cube-root variables `k = K³`, `N = M³`: the index `k` is the
distance to the nearer edge, `a` is the eigenvalue and `g` the classical location, both seen from
that edge. -/
private lemma edge_core {C0 : ℝ} (hC0 : 1 ≤ C0) (hc : EdgeComp C0) {K M t a g : ℝ}
    (hK : 1 ≤ K) (hM : 1 ≤ M) (hKM : 2 * K ^ 3 ≤ M ^ 3 + 1) (ht : 1 ≤ t)
    (hA1 : (K ^ 3 - t) / M ^ 3 ≤ nsc a) (hA2 : nsc a ≤ (K ^ 3 - 1 + t) / M ^ 3)
    (hG1 : (K ^ 3 - 1) / M ^ 3 ≤ nsc g) (hG2 : nsc g ≤ K ^ 3 / M ^ 3)
    (hg1 : -2 ≤ g) (hg2 : g ≤ 2) (ha : |a| * M ^ 2 ≤ 2 * M ^ 2 + t) :
    |a - g| * (K * M ^ 2) ≤ (100 + 700 * C0 ^ 2) * t ^ 2 := by
  have hC2 : 0 ≤ C0 ^ 2 := sq_nonneg C0
  have hnn : 0 ≤ C0 ^ 2 * t ^ 2 := by positivity
  have ht2 : t ≤ t ^ 2 := by nlinarith
  by_cases hcase1 : M ^ 3 < 20 * t
  · have := edge_far hK hM hKM ht hg1 hg2 ha hcase1
    nlinarith
  rw [not_lt] at hcase1
  by_cases hcase2 : 8 * t ≤ K ^ 3
  · have := edge_bulk hC0 hc hM hKM ht hA1 hA2 hG1 hG2 hg1 hcase1 hcase2
    nlinarith
  · rw [not_le] at hcase2
    have := edge_near hC0 hc hK hM ht hA2 hG2 hg1 ha hcase1 hcase2
    nlinarith

/-- A real `x ≥ 1` has a cube root `K ≥ 1`, and `x^{-1/3} = K⁻¹`, `x^{-2/3} = (K²)⁻¹`. -/
private lemma exists_cube_root {x : ℝ} (hx : 1 ≤ x) :
    ∃ K : ℝ, 1 ≤ K ∧ K ^ 3 = x ∧ x ^ (-(1 : ℝ) / 3) = K⁻¹ ∧ x ^ (-(2 : ℝ) / 3) = (K ^ 2)⁻¹ := by
  have hx0 : 0 ≤ x := by linarith
  refine ⟨x ^ ((1 : ℝ) / 3), Real.one_le_rpow hx (by norm_num), ?_, ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  · rw [neg_div, Real.rpow_neg hx0]
  · rw [neg_div, Real.rpow_neg hx0, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num

/-- Rigidity at the edge, for natural indices: `k` is the distance to the nearer edge. -/
private lemma edge_bound : ∃ C > 0, ∀ (N k : ℕ) (t a g : ℝ), 1 ≤ N → 1 ≤ k → 2 * k ≤ N + 1 →
    1 ≤ t → ((k : ℝ) - t) / N ≤ nsc a → nsc a ≤ ((k : ℝ) - 1 + t) / N →
    ((k : ℝ) - 1) / N ≤ nsc g → nsc g ≤ (k : ℝ) / N → -2 ≤ g → g ≤ 2 →
    |a| ≤ 2 + t * (N : ℝ) ^ (-(2 : ℝ) / 3) →
    |a - g| ≤ C * t ^ 2 * (k : ℝ) ^ (-(1 : ℝ) / 3) * (N : ℝ) ^ (-(2 : ℝ) / 3) := by
  obtain ⟨C0, hC0, hc⟩ := nsc_rhoSc_comparable
  refine ⟨100 + 700 * C0 ^ 2, by positivity, ?_⟩
  intro N k t a g hN hk hkN ht hA1 hA2 hG1 hG2 hg1 hg2 ha
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkN' : 2 * (k : ℝ) ≤ N + 1 := by exact_mod_cast hkN
  obtain ⟨K, hK, hKk, hK1, -⟩ := exists_cube_root hk'
  obtain ⟨M, hM, hMN, -, hM2⟩ := exists_cube_root hN'
  have hM0 : 0 < M := by linarith
  have hK0 : 0 < K := by linarith
  rw [hM2] at ha
  rw [hK1, hM2]
  rw [← hKk, ← hMN] at hA1 hA2 hG1 hG2 hkN'
  have ha' : |a| * M ^ 2 ≤ 2 * M ^ 2 + t := by
    have h := mul_le_mul_of_nonneg_right ha (sq_nonneg M)
    have : (2 + t * (M ^ 2)⁻¹) * M ^ 2 = 2 * M ^ 2 + t := by field_simp
    rwa [this] at h
  have h := edge_core hC0 hc hK hM hkN' ht hA1 hA2 hG1 hG2 hg1 hg2 ha'
  have hpos : 0 < K * M ^ 2 := by positivity
  rw [show (100 + 700 * C0 ^ 2) * t ^ 2 * K⁻¹ * (M ^ 2)⁻¹ =
    (100 + 700 * C0 ^ 2) * t ^ 2 / (K * M ^ 2) by
      rw [div_eq_mul_inv, mul_inv]; ring]
  rw [le_div_iff₀ hpos]
  exact h

/-- [26] (5.12)–(5.15): counting bound plus norm bound give rigidity. -/
theorem abs_eigAsc_sub_gammaLoc_le : ∃ C > 0, ∀ N : ℕ, 1 ≤ N →
    ∀ (H : Matrix (Fin N) (Fin N) ℝ) (hH : H.IsHermitian) (t : ℝ), 1 ≤ t →
    (∀ E : ℝ, |countFn hH E - nsc E| ≤ t / N) →
    (∀ α, |hH.eigenvalues α| ≤ 2 + t * (N : ℝ) ^ (-(2 : ℝ) / 3)) →
    ∀ j : Fin N, |eigAsc hH j - gammaLoc N (j.val + 1)| ≤
      C * t ^ 2 * (min (j.val + 1 : ℝ) (N - j.val)) ^ (-(1 : ℝ) / 3) * (N : ℝ) ^ (-(2 : ℝ) / 3) := by
  obtain ⟨C, hC, hedge⟩ := edge_bound
  refine ⟨C, hC, ?_⟩
  intro N hN H hH t ht hcount hnorm j
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hjN : j.val < N := j.isLt
  obtain ⟨hb1, hb2⟩ := nsc_eigAsc_bounds hN hH t hcount j
  obtain ⟨α, hα⟩ := exists_eigenvalue_eq_eigAsc hH j
  have hnormj : |eigAsc hH j| ≤ 2 + t * (N : ℝ) ^ (-(2 : ℝ) / 3) := by
    rw [hα]
    exact hnorm α
  have hγ := nsc_gammaLoc (N := N) (j := j.val + 1) (by omega) (by omega)
  have hγ1 := neg_two_le_gammaLoc (N := N) (j := j.val + 1) (by omega) (by omega)
  have hγ2 := gammaLoc_le_two (N := N) (j := j.val + 1) (by omega) (by omega)
  push_cast at hγ
  generalize eigAsc hH j = a at hb1 hb2 hnormj ⊢
  generalize gammaLoc N (j.val + 1) = γ at hγ hγ1 hγ2 ⊢
  by_cases hcase : j.val + 1 ≤ N - j.val
  · -- lower half: `k = j + 1`
    have hle : (j.val : ℝ) + 1 ≤ (N : ℝ) - j.val := by
      have h : ((j.val + 1 : ℕ) : ℝ) ≤ ((N - j.val : ℕ) : ℝ) := Nat.cast_le.2 hcase
      rw [Nat.cast_sub hjN.le] at h
      push_cast at h
      exact h
    rw [min_eq_left hle]
    have h := hedge N (j.val + 1) t a γ hN (by omega) (by omega) ht
      (by push_cast; exact hb1)
      (by
        push_cast
        have : (j.val : ℝ) + 1 - 1 + t = j.val + t := by ring
        rw [this]
        exact hb2)
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
    exact h
  · -- upper half: `k = N - j`, by reflection `x ↦ -x`
    have hlt : (N : ℝ) - j.val ≤ (j.val : ℝ) + 1 := by
      have h : ((N - j.val : ℕ) : ℝ) ≤ ((j.val + 1 : ℕ) : ℝ) := Nat.cast_le.2 (by omega)
      rw [Nat.cast_sub hjN.le] at h
      push_cast at h
      exact h
    rw [min_eq_right hlt]
    have h := hedge N (N - j.val) t (-a) (-γ) hN (by omega) (by omega) ht
      (by
        rw [nsc_neg, Nat.cast_sub hjN.le]
        have : ((N : ℝ) - j.val - t) / N = 1 - ((j.val : ℝ) + t) / N := by
          field_simp
          ring
        rw [this]
        linarith)
      (by
        rw [nsc_neg, Nat.cast_sub hjN.le]
        have : ((N : ℝ) - j.val - 1 + t) / N = 1 - ((j.val : ℝ) + 1 - t) / N := by
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
    exact h

/-! ### Compiled checks at a concrete nondegenerate point

`N = 2`, `H = diag(-2, 2)` and `t = 1`: the counting function equals `0`, `1/2`, `1` on
`(-∞, -2)`, `[-2, 2)`, `[2, ∞)`, and every eigenvalue has absolute value `2`. -/

/-- The matrix `diag(-2, 2)`. -/
def checkDiag : Matrix (Fin 2) (Fin 2) ℝ := !![-2, 0; 0, 2]

/-- `diag(-2, 2)` is Hermitian. -/
lemma checkDiag_isHermitian : checkDiag.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [checkDiag]

/-- The two eigenvalues of `diag(-2, 2)` are `-2` and `2`, in some order. -/
lemma checkDiag_eigenvalues :
    (checkDiag_isHermitian.eigenvalues 0 = -2 ∧ checkDiag_isHermitian.eigenvalues 1 = 2) ∨
    (checkDiag_isHermitian.eigenvalues 0 = 2 ∧ checkDiag_isHermitian.eigenvalues 1 = -2) := by
  have hdet := checkDiag_isHermitian.det_eq_prod_eigenvalues
  have htr := checkDiag_isHermitian.trace_eq_sum_eigenvalues
  have hd : checkDiag.det = -4 := by
    rw [checkDiag, Matrix.det_fin_two_of]
    norm_num
  have ht : checkDiag.trace = 0 := by
    rw [checkDiag, Matrix.trace_fin_two_of]
    norm_num
  rw [hd, Fin.prod_univ_two] at hdet
  rw [ht, Fin.sum_univ_two] at htr
  simp only [RCLike.ofReal_real_eq_id, id] at hdet htr
  set x := checkDiag_isHermitian.eigenvalues 0
  set y := checkDiag_isHermitian.eigenvalues 1
  have hxy : y = -x := by linarith
  rw [hxy] at hdet
  have hx : (x - 2) * (x + 2) = 0 := by nlinarith
  rcases mul_eq_zero.1 hx with h | h
  · right
    constructor <;> linarith
  · left
    constructor <;> linarith

private lemma nsc_nonneg (E : ℝ) : 0 ≤ nsc E := by
  rcases le_or_gt E (-2) with h | h
  · rw [nsc_eq_zero h]
  · rw [← nsc_eq_zero (le_refl (-2 : ℝ))]
    exact monotone_nsc h.le

private lemma nsc_le_one (E : ℝ) : nsc E ≤ 1 := by
  rcases le_or_gt 2 E with h | h
  · rw [nsc_eq_one h]
  · rw [← nsc_eq_one (le_refl (2 : ℝ))]
    exact monotone_nsc h.le

/-- The counting function of `diag(-2, 2)` is `0`, `1/2`, `1` on `(-∞, -2)`, `[-2, 2)`,
`[2, ∞)`. -/
lemma countFn_checkDiag (E : ℝ) :
    countFn checkDiag_isHermitian E =
      ((if -2 ≤ E then 1 else 0) + (if 2 ≤ E then 1 else 0) : ℝ) / 2 := by
  unfold countFn
  rw [Finset.card_filter, Fin.sum_univ_two]
  rcases checkDiag_eigenvalues with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h1]
    push_cast
    norm_num
  · rw [h0, h1]
    push_cast
    norm_num
    ring

example : ∃ C > 0, ∀ j : Fin 2,
    |eigAsc checkDiag_isHermitian j - gammaLoc 2 (j.val + 1)| ≤
      C * (1 : ℝ) ^ 2 * (min (j.val + 1 : ℝ) ((2 : ℕ) - j.val)) ^ (-(1 : ℝ) / 3) *
        ((2 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) := by
  obtain ⟨C, hC, h⟩ := abs_eigAsc_sub_gammaLoc_le
  refine ⟨C, hC, h 2 (by norm_num) checkDiag checkDiag_isHermitian 1 le_rfl ?_ ?_⟩
  · intro E
    rw [countFn_checkDiag]
    have h0 := nsc_nonneg E
    have h1 := nsc_le_one E
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
  · intro α
    have : |checkDiag_isHermitian.eigenvalues α| = 2 := by
      fin_cases α
      · rcases checkDiag_eigenvalues with ⟨h0, -⟩ | ⟨h0, -⟩ <;> simp [h0]
      · rcases checkDiag_eigenvalues with ⟨-, h1⟩ | ⟨-, h1⟩ <;> simp [h1]
    rw [this]
    have : (0 : ℝ) < ((2 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) := by positivity
    linarith

#print axioms abs_eigAsc_sub_gammaLoc_le

end WEdgeNS
