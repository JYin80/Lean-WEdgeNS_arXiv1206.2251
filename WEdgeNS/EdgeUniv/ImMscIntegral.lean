import WEdgeNS.EdgeUniv.PoissonKernel
import WEdgeNS.Semicircle.Bounds
import WEdgeNS.Semicircle.Stieltjes

/-!
# Integrals of `Im m_sc` and of `Im m` against the Poisson kernel
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- `∫ g_ℓ = π/ℓ` ([26] (6.14), (6.18)). -/
theorem integral_univ_inv_sq_add_sq {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫ y : ℝ, 1 / (y ^ 2 + ℓ ^ 2) = Real.pi / ℓ := by
  have h := integral_thetaEta hℓ
  have e : ∀ y : ℝ, thetaEta ℓ y = (ℓ / Real.pi) * (1 / (y ^ 2 + ℓ ^ 2)) := by
    intro y; unfold thetaEta; field_simp
  simp_rw [e, integral_const_mul] at h
  field_simp at h ⊢
  linarith

/-- The window integral `∫_{-ℓ}^{ℓ} g_ℓ = π/(2ℓ)`. -/
theorem integral_window_inv_sq_add_sq {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫ y in (-ℓ)..ℓ, 1 / (y ^ 2 + ℓ ^ 2) = Real.pi / (2 * ℓ) := by
  have e : ∀ y : ℝ, 1 / (y ^ 2 + ℓ ^ 2) = (ℓ ^ 2 + y ^ 2)⁻¹ := fun y => by rw [one_div, add_comm]
  simp_rw [e]
  rw [integral_inv_sq_add_sq hℓ.ne', div_self hℓ.ne', neg_div, div_self hℓ.ne', Real.arctan_neg,
    Real.arctan_one]
  field_simp
  ring

/-- `√(a + b) ≤ √a + √b`. -/
private lemma sqrt_add_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- The elementary estimate before (6.17): `Im m_sc(x + iℓ) ≤ C √(ℓ + ||x| - 2|)` for `|x| ≤ 5`,
`0 < ℓ ≤ 10`. -/
theorem imMsc_le : ∃ C ≥ (1 : ℝ), ∀ x ℓ : ℝ, |x| ≤ 5 → 0 < ℓ → ℓ ≤ 10 →
    (msc ⟨x, ℓ⟩).im ≤ C * Real.sqrt (ℓ + kappa x) := by
  obtain ⟨C, hC, h⟩ := msc_bounds
  refine ⟨C, hC, fun x ℓ hx hℓ hℓ10 => ?_⟩
  obtain ⟨-, -, hedge, hbulk⟩ := h ⟨x, ℓ⟩ hx hℓ hℓ10
  simp only at hedge hbulk
  have hk : 0 ≤ kappa x := abs_nonneg _
  by_cases hcase : kappa x ≤ ℓ ∨ |x| ≤ 2
  · have := (hbulk hcase).2
    rwa [add_comm (kappa x) ℓ] at this
  · push Not at hcase
    obtain ⟨h1, h2⟩ := hcase
    have := (hedge h1.le h2.le).2
    have hs : 0 < Real.sqrt (kappa x + ℓ) := Real.sqrt_pos.2 (by linarith)
    have h3 : ℓ / Real.sqrt (kappa x + ℓ) ≤ Real.sqrt (kappa x + ℓ) := by
      rw [div_le_iff₀ hs, ← sq, Real.sq_sqrt (by linarith)]
      linarith
    rw [add_comm ℓ (kappa x)]
    calc (msc ⟨x, ℓ⟩).im ≤ C * (ℓ / Real.sqrt (kappa x + ℓ)) := this
      _ ≤ C * Real.sqrt (kappa x + ℓ) := by gcongr

/-- `κ(x) = ||x| - 2| ≤ |x - 2|`. -/
private lemma kappa_le_abs_sub (x : ℝ) : kappa x ≤ |x - 2| := by
  unfold kappa
  have := abs_abs_sub_abs_le_abs_sub x 2
  simpa using this

/-- The majorant used on the regions `A` and `Aᶜ` of [26] after (6.18): for `|E - y| ≤ 5`,
`Im m_sc(E - y + iℓ) ≤ C (√ℓ + √|y| + √|E - 2|)`. -/
theorem imMsc_le_majorant : ∃ C ≥ (1 : ℝ), ∀ E y ℓ : ℝ, |E - y| ≤ 5 → 0 < ℓ → ℓ ≤ 10 →
    (msc ⟨E - y, ℓ⟩).im ≤ C * (Real.sqrt ℓ + Real.sqrt |y| + Real.sqrt |E - 2|) := by
  obtain ⟨C, hC, h⟩ := imMsc_le
  refine ⟨C, hC, fun E y ℓ hx hℓ hℓ10 => ?_⟩
  have h1 := h (E - y) ℓ hx hℓ hℓ10
  have hk : kappa (E - y) ≤ |y| + |E - 2| := by
    refine (kappa_le_abs_sub _).trans ?_
    have : E - y - 2 = (E - 2) + (-y) := by ring
    rw [this]
    calc |(E - 2) + (-y)| ≤ |E - 2| + |-y| := abs_add_le _ _
      _ = |y| + |E - 2| := by rw [abs_neg]; ring
  have h2 : Real.sqrt (ℓ + kappa (E - y)) ≤ Real.sqrt ℓ + Real.sqrt |y| + Real.sqrt |E - 2| := by
    calc Real.sqrt (ℓ + kappa (E - y)) ≤ Real.sqrt (ℓ + (|y| + |E - 2|)) :=
          Real.sqrt_le_sqrt (by linarith)
      _ ≤ Real.sqrt ℓ + Real.sqrt (|y| + |E - 2|) := sqrt_add_le_add hℓ.le (by positivity)
      _ ≤ Real.sqrt ℓ + (Real.sqrt |y| + Real.sqrt |E - 2|) := by
          gcongr; exact sqrt_add_le_add (abs_nonneg _) (abs_nonneg _)
      _ = _ := by ring
  calc _ ≤ C * Real.sqrt (ℓ + kappa (E - y)) := h1
    _ ≤ _ := by gcongr

/-- The window form of the majorant: for `|y| ≤ ℓ` and `|E - y| ≤ 5`,
`Im m_sc(E - y + iℓ) ≤ C (√(2ℓ) + √|E - 2|)`. -/
theorem imMsc_le_window : ∃ C ≥ (1 : ℝ), ∀ E y ℓ : ℝ, |y| ≤ ℓ → |E - y| ≤ 5 → 0 < ℓ → ℓ ≤ 10 →
    (msc ⟨E - y, ℓ⟩).im ≤ C * (Real.sqrt (2 * ℓ) + Real.sqrt |E - 2|) := by
  obtain ⟨C, hC, h⟩ := imMsc_le
  refine ⟨C, hC, fun E y ℓ hy hx hℓ hℓ10 => ?_⟩
  have h1 := h (E - y) ℓ hx hℓ hℓ10
  have hk : kappa (E - y) ≤ ℓ + |E - 2| := by
    refine (kappa_le_abs_sub _).trans ?_
    have : E - y - 2 = (E - 2) + (-y) := by ring
    rw [this]
    calc |(E - 2) + (-y)| ≤ |E - 2| + |-y| := abs_add_le _ _
      _ ≤ ℓ + |E - 2| := by rw [abs_neg]; linarith
  have h2 : Real.sqrt (ℓ + kappa (E - y)) ≤ Real.sqrt (2 * ℓ) + Real.sqrt |E - 2| := by
    calc Real.sqrt (ℓ + kappa (E - y)) ≤ Real.sqrt (2 * ℓ + |E - 2|) :=
          Real.sqrt_le_sqrt (by linarith)
      _ ≤ _ := sqrt_add_le_add (by positivity) (abs_nonneg _)
  calc _ ≤ C * Real.sqrt (ℓ + kappa (E - y)) := h1
    _ ≤ _ := by gcongr

/-- The region `|x| ≥ 5` on `‖H‖ ≤ 3`: `Im m(x + iℓ) ≤ ℓ/4` ([26] (6.17), the region
`|E - y| > 5`). -/
theorem imStieltjesM_le_quarter {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    (hspec : ∀ α, |hH.eigenvalues α| ≤ 3) {x ℓ : ℝ} (hx : 5 ≤ |x|) (hℓ : 0 < ℓ) :
    (stieltjesM H ⟨x, ℓ⟩).im ≤ ℓ / 4 := by
  rw [im_stieltjesM_eq hH (z := ⟨x, ℓ⟩) hℓ]
  simp only
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp; positivity
  · have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hterm : ∀ α, ℓ / ((hH.eigenvalues α - x) ^ 2 + ℓ ^ 2) ≤ ℓ / 4 := by
      intro α
      have h1 : 2 ≤ |hH.eigenvalues α - x| := by
        have := abs_sub_abs_le_abs_sub x (hH.eigenvalues α)
        rw [abs_sub_comm] at this
        linarith [hspec α]
      have h2 : 4 ≤ (hH.eigenvalues α - x) ^ 2 := by
        have := sq_le_sq' (by linarith [abs_nonneg (hH.eigenvalues α - x)]) h1
        rw [sq_abs] at this
        linarith
      exact div_le_div_of_nonneg_left hℓ.le (by norm_num) (by nlinarith [sq_nonneg ℓ])
    calc (N : ℝ)⁻¹ * ∑ α, ℓ / ((hH.eigenvalues α - x) ^ 2 + ℓ ^ 2)
        ≤ (N : ℝ)⁻¹ * ∑ _α : Fin N, ℓ / 4 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun α _ => hterm α) (by positivity)
      _ = ℓ / 4 := by simp; field_simp

private lemma integrable_inv_sq_add_sq {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Integrable fun y : ℝ => 1 / (y ^ 2 + ℓ ^ 2) := by
  have h := (integrable_thetaEta hℓ).const_mul (Real.pi / ℓ)
  refine h.congr (Eventually.of_forall fun y => ?_)
  unfold thetaEta
  have : y ^ 2 + ℓ ^ 2 ≠ 0 := by positivity
  have := Real.pi_pos
  field_simp

private lemma continuous_imStieltjesM {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    (E : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) : Continuous fun y : ℝ => (stieltjesM H ⟨E - y, ℓ⟩).im := by
  have : (fun y : ℝ => (stieltjesM H ⟨E - y, ℓ⟩).im) = fun y =>
      (N : ℝ)⁻¹ * ∑ α, ℓ / ((hH.eigenvalues α - (E - y)) ^ 2 + ℓ ^ 2) := by
    funext y; exact im_stieltjesM_eq hH (z := ⟨E - y, ℓ⟩) hℓ
  rw [this]
  refine continuous_const.mul (continuous_finsetSum _ fun α _ => ?_)
  exact Continuous.div continuous_const (by fun_prop) (fun y => by positivity)

private lemma imStieltjesM_nonneg {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    (x : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) : 0 ≤ (stieltjesM H ⟨x, ℓ⟩).im := by
  rw [im_stieltjesM_eq hH (z := ⟨x, ℓ⟩) hℓ]
  positivity

/-- The contribution of the region `|E - y| > 5` to (6.17) on `‖H‖ ≤ 3`:
`∫_{|E-y|>5} g_ℓ(y) Im m(E - y + iℓ) dy ≤ π/4`. -/
theorem integral_imStieltjesM_far_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (hspec : ∀ α, |hH.eigenvalues α| ≤ 3) (E : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫ y in {y : ℝ | 5 < |E - y|}, (stieltjesM H ⟨E - y, ℓ⟩).im / (y ^ 2 + ℓ ^ 2) ≤
      Real.pi / 4 := by
  have hs : MeasurableSet {y : ℝ | 5 < |E - y|} := measurableSet_lt measurable_const (by fun_prop)
  have hg : Integrable fun y : ℝ => ℓ / 4 * (1 / (y ^ 2 + ℓ ^ 2)) :=
    (integrable_inv_sq_add_sq hℓ).const_mul _
  have hden : ∀ y : ℝ, y ^ 2 + ℓ ^ 2 ≠ 0 := fun y => by positivity
  have hfc : Continuous fun y : ℝ => (stieltjesM H ⟨E - y, ℓ⟩).im / (y ^ 2 + ℓ ^ 2) :=
    Continuous.div (continuous_imStieltjesM hH E hℓ) (by fun_prop) hden
  have hbound : ∀ y ∈ {y : ℝ | 5 < |E - y|},
      (stieltjesM H ⟨E - y, ℓ⟩).im / (y ^ 2 + ℓ ^ 2) ≤ ℓ / 4 * (1 / (y ^ 2 + ℓ ^ 2)) := by
    intro y hy
    have h1 := imStieltjesM_le_quarter hH hspec (x := E - y) (ℓ := ℓ) (le_of_lt hy) hℓ
    have hpos : 0 < y ^ 2 + ℓ ^ 2 := by positivity
    rw [div_le_iff₀ hpos]
    have : ℓ / 4 * (1 / (y ^ 2 + ℓ ^ 2)) * (y ^ 2 + ℓ ^ 2) = ℓ / 4 := by field_simp
    rw [this]
    exact h1
  have hfint : IntegrableOn (fun y : ℝ => (stieltjesM H ⟨E - y, ℓ⟩).im / (y ^ 2 + ℓ ^ 2))
      {y : ℝ | 5 < |E - y|} := by
    refine Integrable.mono' hg.integrableOn hfc.aestronglyMeasurable.restrict
      (ae_restrict_of_forall_mem hs fun y hy => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (imStieltjesM_nonneg hH _ hℓ)
      (by positivity))]
    exact hbound y hy
  calc ∫ y in {y : ℝ | 5 < |E - y|}, (stieltjesM H ⟨E - y, ℓ⟩).im / (y ^ 2 + ℓ ^ 2)
      ≤ ∫ y in {y : ℝ | 5 < |E - y|}, ℓ / 4 * (1 / (y ^ 2 + ℓ ^ 2)) :=
        setIntegral_mono_on hfint hg.integrableOn hs hbound
    _ ≤ ∫ y : ℝ, ℓ / 4 * (1 / (y ^ 2 + ℓ ^ 2)) :=
        setIntegral_le_integral hg (Eventually.of_forall fun y => by positivity)
    _ = Real.pi / 4 := by
        rw [integral_const_mul, integral_univ_inv_sq_add_sq hℓ]
        field_simp

section MaxPow

open Set

private lemma integrableOn_maxPow {ℓ : ℝ} (hℓ : 0 < ℓ) :
    IntegrableOn (fun t : ℝ => (max t ℓ) ^ (-(3 : ℝ) / 2)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi hℓ.le]
  refine IntegrableOn.union ?_ ?_
  · have : IntegrableOn (fun _ : ℝ => ℓ ^ (-(3 : ℝ) / 2)) (Ioc 0 ℓ) :=
      integrableOn_const (by simp)
    exact this.congr_fun (fun t ht => by simp [max_eq_right ht.2]) measurableSet_Ioc
  · exact (integrableOn_Ioi_rpow_of_lt (a := -(3 : ℝ) / 2) (by norm_num) hℓ).congr_fun
      (fun t ht => by simp [max_eq_left (Set.mem_Ioi.1 ht).le]) measurableSet_Ioi

private lemma integral_maxPow_Ioi {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫ t in Ioi 0, (max t ℓ) ^ (-(3 : ℝ) / 2) = 3 * ℓ ^ (-(1 : ℝ) / 2) := by
  have hint := integrableOn_maxPow hℓ
  rw [← Ioc_union_Ioi_eq_Ioi hℓ.le] at hint ⊢
  rw [setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi (hint.mono_set subset_union_left)
    (hint.mono_set subset_union_right)]
  have h1 : ∫ t in Ioc 0 ℓ, (max t ℓ) ^ (-(3 : ℝ) / 2) = ℓ ^ (-(1 : ℝ) / 2) := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => ℓ ^ (-(3 : ℝ) / 2))
      (fun t ht => by simp [max_eq_right ht.2])]
    simp only [setIntegral_const, Real.volume_real_Ioc, smul_eq_mul]
    rw [max_eq_left (by linarith), sub_zero, ← Real.rpow_one_add' hℓ.le (by norm_num)]
    norm_num
  have h2 : ∫ t in Ioi ℓ, (max t ℓ) ^ (-(3 : ℝ) / 2) = 2 * ℓ ^ (-(1 : ℝ) / 2) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t => t ^ (-(3 : ℝ) / 2))
      (fun t ht => by simp [max_eq_left (Set.mem_Ioi.1 ht).le])]
    rw [integral_Ioi_rpow_of_lt (a := -(3 : ℝ) / 2) (by norm_num) hℓ]
    norm_num
    ring
  rw [h1, h2]; ring

private lemma integrable_maxPow_abs {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Integrable fun y : ℝ => (max |y| ℓ) ^ (-(3 : ℝ) / 2) := by
  have hf : IntegrableOn (fun x : ℝ => (max |x| ℓ) ^ (-(3 : ℝ) / 2)) (Ioi 0) :=
    (integrableOn_maxPow hℓ).congr_fun (fun x hx => by simp [abs_of_pos (Set.mem_Ioi.1 hx)])
      measurableSet_Ioi
  have int_Iic : IntegrableOn (fun x : ℝ => (max |x| ℓ) ^ (-(3 : ℝ) / 2)) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact int_Iic.union hf

private lemma integral_maxPow_abs {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫ y : ℝ, (max |y| ℓ) ^ (-(3 : ℝ) / 2) = 6 * ℓ ^ (-(1 : ℝ) / 2) := by
  rw [integral_comp_abs (f := fun t : ℝ => (max t ℓ) ^ (-(3 : ℝ) / 2)), integral_maxPow_Ioi hℓ]
  ring

private lemma rpow_neg_three_halves {t : ℝ} (ht : 0 < t) :
    t ^ (-(3 : ℝ) / 2) = Real.sqrt t / t ^ 2 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_two, ← Real.rpow_sub ht]
  norm_num

private lemma sqrt_abs_mul_le {ℓ : ℝ} (hℓ : 0 < ℓ) (y : ℝ) :
    Real.sqrt |y| * (1 / (y ^ 2 + ℓ ^ 2)) ≤ (max |y| ℓ) ^ (-(3 : ℝ) / 2) := by
  have hpos : 0 < y ^ 2 + ℓ ^ 2 := by positivity
  rw [mul_one_div]
  rcases le_total |y| ℓ with h | h
  · rw [max_eq_right h, rpow_neg_three_halves hℓ]
    have : Real.sqrt |y| ≤ Real.sqrt ℓ := Real.sqrt_le_sqrt h
    exact div_le_div₀ (Real.sqrt_nonneg _) this (by positivity) (by nlinarith [sq_nonneg y])
  · rw [max_eq_left h]
    have hy : 0 < |y| := lt_of_lt_of_le hℓ h
    rw [rpow_neg_three_halves hy]
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
      (by rw [sq_abs]; nlinarith [sq_nonneg ℓ])

private lemma continuous_imMsc (E : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Continuous fun y : ℝ => (msc ⟨E - y, ℓ⟩).im := by
  have h : DifferentiableOn ℂ msc {z : ℂ | 0 < z.im} := by
    have := isProbabilityMeasure_semicircle
    have h := (analyticOn_resolventTransform (μ := semicircle)).differentiableOn
    have hsub : {z : ℂ | 0 < z.im} ⊆ (algebraMap ℝ ℂ '' semicircle.support)ᶜ := by
      intro z hz
      rintro ⟨x, -, rfl⟩
      simp at hz
    exact (h.mono hsub).congr fun z hz => msc_eq_resolventTransform hz
  have hc : Continuous (fun y : ℝ => (⟨E - y, ℓ⟩ : ℂ)) := by
    have : (fun y : ℝ => (⟨E - y, ℓ⟩ : ℂ)) = fun y => ((E - y : ℝ) : ℂ) + (ℓ : ℂ) * Complex.I := by
      funext y; apply Complex.ext <;> simp
    rw [this]; fun_prop
  exact Complex.continuous_im.comp (h.continuousOn.comp_continuous hc fun y => by simpa using hℓ)

/-- The integral bound of [26] after (6.18), over `{|E - y| ≤ 5} = [E - 5, E + 5]` (both `A` and
`Aᶜ`): `∫ g_ℓ(y) Im m_sc(E - y + iℓ) dy ≤ C (ℓ^{-1/2} + |E - 2|^{1/2} ℓ^{-1})`. -/
theorem integral_imMsc_le : ∃ C ≥ (1 : ℝ), ∀ E ℓ : ℝ, 0 < ℓ → ℓ ≤ 10 →
    ∫ y in (E - 5)..(E + 5), (msc ⟨E - y, ℓ⟩).im / (y ^ 2 + ℓ ^ 2) ≤
      C * ((Real.sqrt ℓ)⁻¹ + Real.sqrt |E - 2| / ℓ) := by
  obtain ⟨Cm, hCm, hm⟩ := imMsc_le_majorant
  refine ⟨10 * Cm, by linarith, fun E ℓ hℓ hℓ10 => ?_⟩
  have hab : E - 5 ≤ E + 5 := by linarith
  have hsℓ : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓ
  set a₀ := Real.sqrt ℓ + Real.sqrt |E - 2| with ha₀
  have ha₀0 : 0 ≤ a₀ := by positivity
  have hg := integrable_inv_sq_add_sq hℓ
  have hH := integrable_maxPow_abs hℓ
  have hden : ∀ y : ℝ, y ^ 2 + ℓ ^ 2 ≠ 0 := fun y => by positivity
  have hcont : Continuous fun y : ℝ => (msc ⟨E - y, ℓ⟩).im / (y ^ 2 + ℓ ^ 2) :=
    Continuous.div (continuous_imMsc E hℓ) (by fun_prop) hden
  have hpt : ∀ y ∈ Icc (E - 5) (E + 5), (msc ⟨E - y, ℓ⟩).im / (y ^ 2 + ℓ ^ 2) ≤
      Cm * (a₀ * (1 / (y ^ 2 + ℓ ^ 2)) + (max |y| ℓ) ^ (-(3 : ℝ) / 2)) := by
    intro y hy
    have hxy : |E - y| ≤ 5 := abs_le.2 ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have h1 := hm E y ℓ hxy hℓ hℓ10
    have hgpos : 0 < 1 / (y ^ 2 + ℓ ^ 2) := by positivity
    have h2 := sqrt_abs_mul_le hℓ y
    rw [div_eq_mul_one_div]
    calc (msc ⟨E - y, ℓ⟩).im * (1 / (y ^ 2 + ℓ ^ 2))
        ≤ Cm * (Real.sqrt ℓ + Real.sqrt |y| + Real.sqrt |E - 2|) * (1 / (y ^ 2 + ℓ ^ 2)) :=
          mul_le_mul_of_nonneg_right h1 hgpos.le
      _ = Cm * (a₀ * (1 / (y ^ 2 + ℓ ^ 2)) + Real.sqrt |y| * (1 / (y ^ 2 + ℓ ^ 2))) := by
          rw [ha₀]; ring
      _ ≤ _ := by gcongr
  have hrhs : Integrable fun y : ℝ =>
      Cm * (a₀ * (1 / (y ^ 2 + ℓ ^ 2)) + (max |y| ℓ) ^ (-(3 : ℝ) / 2)) :=
    ((hg.const_mul a₀).add hH).const_mul Cm
  calc ∫ y in (E - 5)..(E + 5), (msc ⟨E - y, ℓ⟩).im / (y ^ 2 + ℓ ^ 2)
      ≤ ∫ y in (E - 5)..(E + 5), Cm * (a₀ * (1 / (y ^ 2 + ℓ ^ 2)) + (max |y| ℓ) ^ (-(3 : ℝ) / 2)) :=
        intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable _ _)
          (hrhs.intervalIntegrable) hpt
    _ ≤ ∫ y : ℝ, Cm * (a₀ * (1 / (y ^ 2 + ℓ ^ 2)) + (max |y| ℓ) ^ (-(3 : ℝ) / 2)) := by
        rw [intervalIntegral.integral_of_le hab]
        refine setIntegral_le_integral hrhs (Eventually.of_forall fun y => ?_)
        have : 0 ≤ (max |y| ℓ) ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
        have : 0 ≤ 1 / (y ^ 2 + ℓ ^ 2) := by positivity
        show 0 ≤ Cm * (a₀ * (1 / (y ^ 2 + ℓ ^ 2)) + (max |y| ℓ) ^ (-(3 : ℝ) / 2))
        positivity
    _ = Cm * (a₀ * (Real.pi / ℓ) + 6 * ℓ ^ (-(1 : ℝ) / 2)) := by
        rw [integral_const_mul, integral_add (hg.const_mul a₀) hH, integral_const_mul,
          integral_univ_inv_sq_add_sq hℓ, integral_maxPow_abs hℓ]
    _ ≤ _ := by
        have e1 : ℓ ^ (-(1 : ℝ) / 2) = (Real.sqrt ℓ)⁻¹ := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hℓ.le]; ring_nf
        have e2 : Real.sqrt ℓ / ℓ = (Real.sqrt ℓ)⁻¹ := by
          have : ℓ = Real.sqrt ℓ * Real.sqrt ℓ := (Real.mul_self_sqrt hℓ.le).symm
          field_simp
          nlinarith [Real.sq_sqrt hℓ.le]
        rw [e1, ha₀]
        have hpi := Real.pi_lt_d2
        have h3 : 0 ≤ (Real.sqrt ℓ)⁻¹ := by positivity
        have h4 : 0 ≤ Real.sqrt |E - 2| / ℓ := by positivity
        have : (Real.sqrt ℓ + Real.sqrt |E - 2|) * (Real.pi / ℓ) =
            Real.pi * (Real.sqrt ℓ)⁻¹ + Real.pi * (Real.sqrt |E - 2| / ℓ) := by
          rw [← e2]; ring
        rw [this]
        have : Real.pi * (Real.sqrt ℓ)⁻¹ + Real.pi * (Real.sqrt |E - 2| / ℓ) +
            6 * (Real.sqrt ℓ)⁻¹ ≤ 10 * ((Real.sqrt ℓ)⁻¹ + Real.sqrt |E - 2| / ℓ) := by
          nlinarith
        nlinarith

end MaxPow

/-! ## Nondegenerate instances -/

/-- `imStieltjesM_le_quarter` at `N = 2`, `H = 0` (`‖H‖ = 0 ≤ 3`), `x = 5`, `ℓ = 1`. -/
example : (stieltjesM (0 : Matrix (Fin 2) (Fin 2) ℝ) ⟨5, 1⟩).im ≤ 1 / 4 := by
  have hH : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian := Matrix.isHermitian_zero
  have h0 : hH.eigenvalues = 0 := (hH.eigenvalues_eq_zero_iff).2 rfl
  have := imStieltjesM_le_quarter hH (fun α => by simp [h0]) (x := 5) (ℓ := 1)
    (by norm_num [abs_of_pos]) one_pos
  simpa using this

/-- `integral_imStieltjesM_far_le` at `N = 2`, `H = 0`, `E = 2`, `ℓ = 1`. -/
example : ∫ y in {y : ℝ | 5 < |2 - y|},
      (stieltjesM (0 : Matrix (Fin 2) (Fin 2) ℝ) ⟨2 - y, 1⟩).im / (y ^ 2 + 1 ^ 2) ≤ Real.pi / 4 := by
  have hH : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian := Matrix.isHermitian_zero
  have h0 : hH.eigenvalues = 0 := (hH.eigenvalues_eq_zero_iff).2 rfl
  exact integral_imStieltjesM_far_le hH (fun α => by simp [h0]) 2 one_pos

#print axioms integral_univ_inv_sq_add_sq
#print axioms integral_window_inv_sq_add_sq
#print axioms imMsc_le
#print axioms imMsc_le_majorant
#print axioms imMsc_le_window
#print axioms integral_imMsc_le
#print axioms imStieltjesM_le_quarter
#print axioms integral_imStieltjesM_far_le

end WEdgeNS
