import WEdgeNS.EdgeUniv.Smoothing

/-!
# The Poisson kernel `θ_η` and the counting bounds of Lemma 6.1 of [26]
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

private lemma thetaEta_eq_cauchy {η : ℝ} (hη : 0 < η) :
    thetaEta η = cauchyPDFReal 0 η.toNNReal := by
  funext x
  have : (x ^ 2 + η ^ 2) ≠ 0 := by positivity
  rw [cauchyPDFReal_def, Real.coe_toNNReal _ hη.le]
  simp only [thetaEta, sub_zero]
  field_simp

/-- `θ_η` is integrable. -/
theorem integrable_thetaEta {η : ℝ} (hη : 0 < η) : Integrable (thetaEta η) := by
  rw [thetaEta_eq_cauchy hη]
  exact integrable_cauchyPDFReal 0

/-- `∫ θ_η = 1` ([26] (6.6)). -/
theorem integral_thetaEta {η : ℝ} (hη : 0 < η) : ∫ x, thetaEta η x = 1 := by
  rw [thetaEta_eq_cauchy hη]
  exact integral_cauchyPDFReal_eq_one 0 (by simpa using hη)

private lemma arctan_tail_le {s : ℝ} (hs : 0 ≤ s) :
    Real.pi / 2 - Real.arctan s ≤ Real.pi / (s + 1) := by
  have hpi := Real.pi_gt_three
  have hpi0 := Real.pi_pos
  by_cases hs1 : s ≤ 1
  · have h0 : 0 ≤ Real.arctan s := Real.arctan_nonneg.2 hs
    have : Real.pi / 2 ≤ Real.pi / (s + 1) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    linarith
  · have hs1 : 1 < s := not_le.1 hs1
    have hs0 : 0 < s := by linarith
    have h1 : Real.arctan s⁻¹ = Real.pi / 2 - Real.arctan s := Real.arctan_inv_of_pos hs0
    have h2 : Real.arctan s⁻¹ ≤ s⁻¹ := Real.arctan_le_self (by positivity)
    have h3 : s⁻¹ ≤ Real.pi / (s + 1) := by
      rw [inv_eq_one_div, div_le_div_iff₀ hs0 (by linarith)]
      nlinarith
    linarith

private lemma arctan_sub_le {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    Real.arctan v - Real.arctan u ≤ 2 * (1 / (u + 1) - 1 / (v + 1)) := by
  let h : ℝ → ℝ := fun t => 2 * (1 / (u + 1) - 1 / (t + 1)) - (Real.arctan t - Real.arctan u)
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt h (2 / (t + 1) ^ 2 - 1 / (1 + t ^ 2)) t := by
    intro t ht
    have ht1 : t + 1 ≠ 0 := by linarith
    have h1 : HasDerivAt (fun t : ℝ => (t + 1)⁻¹) (-1 / (t + 1) ^ 2) t := by
      have := (hasDerivAt_inv ht1).comp t ((hasDerivAt_id t).add_const (1 : ℝ))
      convert this using 1
      · rfl
      · ring
    have h2 : HasDerivAt (fun t : ℝ => Real.arctan t) (1 / (1 + t ^ 2)) t :=
      Real.hasDerivAt_arctan t
    have h3 := ((h1.const_sub (1 / (u + 1))).const_mul 2).sub (h2.sub_const (Real.arctan u))
    convert h3 using 1
    · funext s; simp only [h, Pi.sub_apply, one_div]
    · field_simp
  have hmono : MonotoneOn h (Set.Ici u) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici u) ?_ ?_ ?_
    · intro t ht
      exact (hd t (hu.trans ht)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hd t (hu.trans (le_of_lt ht))).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : 0 ≤ t := hu.trans (le_of_lt ht)
      rw [(hd t ht0).deriv]
      have : 1 / (1 + t ^ 2) ≤ 2 / (t + 1) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg (t - 1)]
      linarith
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 huv) huv
  simp only [h, sub_self, mul_zero] at this
  linarith

private lemma arctan_outer {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    (Real.arctan v - Real.arctan u) / Real.pi ≤ 4 * ((v - u) / ((u + 1) * (v + 1))) := by
  have hpi := Real.pi_gt_three
  have hpi0 := Real.pi_pos
  have h := arctan_sub_le hu huv
  have hv : 0 ≤ v := hu.trans huv
  have hu1 : u + 1 ≠ 0 := by linarith
  have hv1 : v + 1 ≠ 0 := by linarith
  have e : 2 * (1 / (u + 1) - 1 / (v + 1)) = 2 * ((v - u) / ((u + 1) * (v + 1))) := by
    field_simp; ring
  rw [e] at h
  have hnn : 0 ≤ (v - u) / ((u + 1) * (v + 1)) := by
    apply div_nonneg (by linarith) (by positivity)
  rw [div_le_iff₀ hpi0]
  nlinarith

private lemma arctan_dimless (α β : ℝ) (h : 0 ≤ α + β) :
    |(if 0 ≤ α ∧ 0 ≤ β then (1 : ℝ) else 0) - (Real.arctan α + Real.arctan β) / Real.pi| ≤
      4 * ((α + β) / ((|α| + 1) * (|β| + 1)) +
        (if 0 ≤ α ∧ 0 ≤ β then (1 : ℝ) else 0) / (|α| + |β| + 2)) := by
  have hpi := Real.pi_gt_three
  have hpi0 := Real.pi_pos
  have hlt : ∀ x : ℝ, Real.arctan x < Real.pi / 2 := Real.arctan_lt_pi_div_two
  by_cases hα : 0 ≤ α
  · by_cases hβ : 0 ≤ β
    · -- both nonnegative
      have hc : (0 ≤ α ∧ 0 ≤ β) := ⟨hα, hβ⟩
      simp only [hc, and_self, ↓reduceIte, abs_of_nonneg hα, abs_of_nonneg hβ]
      have e : (1 : ℝ) - (Real.arctan α + Real.arctan β) / Real.pi =
          ((Real.pi / 2 - Real.arctan α) + (Real.pi / 2 - Real.arctan β)) / Real.pi := by
        field_simp; ring
      rw [e, abs_of_nonneg (by
        apply div_nonneg _ hpi0.le
        linarith [hlt α, hlt β])]
      have h1 := arctan_tail_le hα
      have h2 := arctan_tail_le hβ
      have hP : 0 < (α + 1) * (β + 1) := by positivity
      have hS : 0 < α + β + 2 := by linarith
      have key : 1 / (α + 1) + 1 / (β + 1) ≤
          4 * ((α + β) / ((α + 1) * (β + 1)) + 1 / (α + β + 2)) := by
        rw [div_add_div _ _ (by positivity) (by positivity), div_add_div _ _ hP.ne' hS.ne',
          mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg hα hβ, mul_nonneg (mul_nonneg hα hβ) hα, mul_nonneg (mul_nonneg hα hβ) hβ,
          mul_pos hP hS, sq_nonneg (α - β)]
      calc _ ≤ (Real.pi / (α + 1) + Real.pi / (β + 1)) / Real.pi := by
            apply div_le_div_of_nonneg_right _ hpi0.le
            linarith
        _ = 1 / (α + 1) + 1 / (β + 1) := by field_simp
        _ ≤ _ := key
    · -- β < 0, so α ≥ -β > 0
      have hβ' : β < 0 := not_le.1 hβ
      have hnc : ¬ (0 ≤ α ∧ 0 ≤ β) := fun h => hβ h.2
      simp only [hnc, ↓reduceIte, zero_div, add_zero, zero_sub, abs_neg]
      have hv : 0 ≤ -β := by linarith
      have hle : -β ≤ α := by linarith
      have h1 := arctan_outer hv hle
      have e1 : Real.arctan α + Real.arctan β = Real.arctan α - Real.arctan (-β) := by
        rw [Real.arctan_neg]; ring
      have hnn : 0 ≤ (Real.arctan α - Real.arctan (-β)) / Real.pi := by
        apply div_nonneg _ Real.pi_pos.le
        have := Real.arctan_strictMono.monotone hle
        linarith
      rw [e1, abs_of_nonneg hnn, abs_of_nonneg hα, abs_of_neg hβ']
      have e2 : (α - -β) / ((-β + 1) * (α + 1)) = (α + β) / ((α + 1) * (-β + 1)) := by
        rw [sub_neg_eq_add, add_comm α β, mul_comm]
      rw [e2] at h1
      exact h1
  · -- α < 0, so β ≥ -α > 0
    have hα' : α < 0 := not_le.1 hα
    have hnc : ¬ (0 ≤ α ∧ 0 ≤ β) := fun h => hα h.1
    simp only [hnc, ↓reduceIte, zero_div, add_zero, zero_sub, abs_neg]
    have hu : 0 ≤ -α := by linarith
    have hle : -α ≤ β := by linarith
    have h1 := arctan_outer hu hle
    have e1 : Real.arctan α + Real.arctan β = Real.arctan β - Real.arctan (-α) := by
      rw [Real.arctan_neg]; ring
    have hnn : 0 ≤ (Real.arctan β - Real.arctan (-α)) / Real.pi := by
      apply div_nonneg _ Real.pi_pos.le
      have := Real.arctan_strictMono.monotone hle
      linarith
    have hβ0 : 0 ≤ β := by linarith
    rw [e1, abs_of_nonneg hnn, abs_of_neg hα', abs_of_nonneg hβ0]
    have e2 : (β - -α) / ((-α + 1) * (β + 1)) = (α + β) / ((-α + 1) * (β + 1)) := by
      rw [sub_neg_eq_add, add_comm β α]
    rw [e2] at h1
    exact h1

private lemma integral_thetaEta_interval {η : ℝ} (hη : 0 < η) (a b : ℝ) :
    ∫ u in a..b, thetaEta η u = (Real.arctan (b / η) - Real.arctan (a / η)) / Real.pi := by
  have e : ∀ u : ℝ, thetaEta η u = Real.pi⁻¹ * (η / (η ^ 2 + u ^ 2)) := by
    intro u; unfold thetaEta; rw [add_comm (u ^ 2)]; field_simp
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, integral_div_sq_add_sq]
  field_simp

/-- [26] (6.10), with the constant `4`: for `E ≤ E_L`, `d = |λ - E| + η`, `d_L = |λ - E_L| + η`,
`|1_{[E,E_L]}(λ) - ∫_E^{E_L} θ_η(λ - y) dy| ≤ 4η [ (E_L - E)/(d_L d) + 1_{[E,E_L]}(λ)/(d_L + d) ]`. -/
theorem abs_indicator_sub_integral_thetaEta_le {η E EL : ℝ} (hη : 0 < η) (hEL : E ≤ EL)
    (lam : ℝ) :
    |(if E ≤ lam ∧ lam ≤ EL then (1 : ℝ) else 0) - ∫ y in E..EL, thetaEta η (lam - y)| ≤
      4 * η * ((EL - E) / ((|lam - EL| + η) * (|lam - E| + η)) +
        (if E ≤ lam ∧ lam ≤ EL then (1 : ℝ) else 0) /
          ((|lam - EL| + η) + (|lam - E| + η))) := by
  set α := (lam - E) / η with hα
  set β := (EL - lam) / η with hβ
  have hα' : lam - E = η * α := by rw [hα]; field_simp
  have hβ' : EL - lam = η * β := by rw [hβ]; field_simp
  have hab : 0 ≤ α + β := by
    have : 0 ≤ (EL - E) / η := div_nonneg (by linarith) hη.le
    have e : (EL - E) / η = α + β := by rw [hα, hβ]; field_simp; ring
    linarith
  have hI : ∫ y in E..EL, thetaEta η (lam - y) =
      (Real.arctan α + Real.arctan β) / Real.pi := by
    rw [intervalIntegral.integral_comp_sub_left (fun u => thetaEta η u) lam,
      integral_thetaEta_interval hη]
    have e1 : (lam - E) / η = α := rfl
    have e2 : (lam - EL) / η = -β := by rw [hβ]; field_simp; ring
    rw [e1, e2, Real.arctan_neg]
    ring
  have hcond : (E ≤ lam ∧ lam ≤ EL) ↔ (0 ≤ α ∧ 0 ≤ β) := by
    rw [hα, hβ, le_div_iff₀ hη, le_div_iff₀ hη]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have h1 : |lam - EL| = η * |β| := by
    rw [abs_sub_comm, hβ', abs_mul, abs_of_pos hη]
  have h2 : |lam - E| = η * |α| := by
    rw [hα', abs_mul, abs_of_pos hη]
  have h3 : EL - E = η * (α + β) := by linarith
  have key := arctan_dimless α β hab
  rw [hI]
  simp only [hcond] at *
  rw [h1, h2, h3]
  have e : 4 * η * (η * (α + β) / ((η * |β| + η) * (η * |α| + η)) +
      (if 0 ≤ α ∧ 0 ≤ β then (1 : ℝ) else 0) / (η * |β| + η + (η * |α| + η))) =
      4 * ((α + β) / ((|α| + 1) * (|β| + 1)) +
        (if 0 ≤ α ∧ 0 ≤ β then (1 : ℝ) else 0) / (|α| + |β| + 2)) := by
    have hα0 : 0 < |α| + 1 := by positivity
    have hβ0 : 0 < |β| + 1 := by positivity
    have hs0 : 0 < |α| + |β| + 2 := by positivity
    have hηne := hη.ne'
    field_simp
    ring
  rw [e]
  exact key

private lemma hasDerivAt_arctan_div {η : ℝ} (hη : 0 < η) (x : ℝ) :
    HasDerivAt (fun x : ℝ => Real.arctan (x / η) / Real.pi) (thetaEta η x) x := by
  have h1 : HasDerivAt (fun x : ℝ => x / η) (1 / η) x := (hasDerivAt_id x).div_const η
  have h2 := h1.arctan.div_const Real.pi
  convert h2 using 1
  unfold thetaEta
  have : (x ^ 2 + η ^ 2) ≠ 0 := by positivity
  field_simp
  ring

/-- The one-sided tail of `θ_η`, exactly. -/
private lemma integral_Ioi_thetaEta {η : ℝ} (hη : 0 < η) (α : ℝ) :
    ∫ x in Set.Ioi α, thetaEta η x = 1 / 2 - Real.arctan (α / η) / Real.pi := by
  have hlim : Tendsto (fun x : ℝ => Real.arctan (x / η) / Real.pi) atTop (𝓝 (1 / 2)) := by
    have h1 : Tendsto (fun x : ℝ => x / η) atTop atTop := tendsto_id.atTop_div_const hη
    have h2 := (tendsto_nhds_of_tendsto_nhdsWithin (Real.tendsto_arctan_atTop.comp h1)).div_const
      Real.pi
    have e : (Real.pi / 2) / Real.pi = 1 / 2 := by field_simp
    simpa [e] using h2
  have := integral_Ioi_of_hasDerivAt_of_tendsto' (a := α) (f := fun x : ℝ => Real.arctan (x / η) / Real.pi)
    (f' := thetaEta η) (m := 1 / 2) (fun x _ => hasDerivAt_arctan_div hη x)
    (integrable_thetaEta hη).integrableOn hlim
  simpa using this

/-- The one-sided tail of `θ_η`: `∫_{x>α} θ_η ≤ η/(α+η)` for `α ≥ 0` ([26] proof of Lemma 6.1,
display before (6.10)). -/
theorem integral_Ioi_thetaEta_le {η α : ℝ} (hη : 0 < η) (hα : 0 ≤ α) :
    ∫ x in Set.Ioi α, thetaEta η x ≤ η / (α + η) := by
  rw [integral_Ioi_thetaEta hη]
  have hs : 0 ≤ α / η := div_nonneg hα hη.le
  have h := arctan_tail_le hs
  have hpi := Real.pi_pos
  have e : η / (α + η) = 1 / (α / η + 1) := by
    have : α + η ≠ 0 := by positivity
    field_simp
  have e2 : 1 / 2 - Real.arctan (α / η) / Real.pi = (Real.pi / 2 - Real.arctan (α / η)) / Real.pi := by
    field_simp
  rw [e, e2, div_le_iff₀ hpi]
  have : 1 / (α / η + 1) * Real.pi = Real.pi / (α / η + 1) := by ring
  linarith

/-- The two-sided tail: `∫_{|x|≥α} θ_η ≤ 2η/(α+η)` for `α ≥ 0`. -/
theorem integral_abs_ge_thetaEta_le {η α : ℝ} (hη : 0 < η) (hα : 0 ≤ α) :
    ∫ x in {x : ℝ | α ≤ |x|}, thetaEta η x ≤ 2 * η / (α + η) := by
  have hset : {x : ℝ | α ≤ |x|} = (Set.Ioo (-α) α)ᶜ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt]
    constructor
    · intro h
      rcases le_abs'.1 h with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr h
    · rintro (h | h)
      · exact le_trans (by linarith) (neg_le_abs x)
      · exact le_trans h (le_abs_self x)
  rw [hset, setIntegral_compl measurableSet_Ioo (integrable_thetaEta hη), integral_thetaEta hη,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
    integral_thetaEta_interval hη]
  have hs : 0 ≤ α / η := div_nonneg hα hη.le
  have h := arctan_tail_le hs
  have hpi := Real.pi_pos
  have e1 : -α / η = -(α / η) := by ring
  rw [e1, Real.arctan_neg]
  have e : 2 * η / (α + η) = 2 / (α / η + 1) := by
    have : α + η ≠ 0 := by positivity
    field_simp
  have e2 : 1 - (Real.arctan (α / η) - -Real.arctan (α / η)) / Real.pi =
      2 * ((Real.pi / 2 - Real.arctan (α / η)) / Real.pi) := by field_simp; ring
  rw [e, e2]
  have h' : (Real.pi / 2 - Real.arctan (α / η)) / Real.pi ≤ 1 / (α / η + 1) := by
    rw [div_le_iff₀ hpi]
    have : 1 / (α / η + 1) * Real.pi = Real.pi / (α / η + 1) := by ring
    linarith
  calc 2 * ((Real.pi / 2 - Real.arctan (α / η)) / Real.pi) ≤ 2 * (1 / (α / η + 1)) := by linarith
    _ = 2 / (α / η + 1) := by ring

/-- `η m/(x y) ≤ c (η/y)` when `0 ≤ m ≤ c x`. -/
private lemma bridge_aux {η m x y c : ℝ} (hη : 0 < η) (hx : 0 < x) (hy : 0 < y) (hm : 0 ≤ m)
    (hmx : m ≤ c * x) : η * m / (x * y) ≤ c * (η / y) := by
  have hc : 0 ≤ c := by
    by_contra h
    push Not at h
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  have : c * (η / y) * (x * y) = c * η * x := by field_simp
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left hmx hη.le]

/-- `η m/(x y) ≤ η/x + η/y` when `m ≤ x + y`. -/
private lemma bridge_aux3 {η m x y : ℝ} (hη : 0 < η) (hx : 0 < x) (hy : 0 < y)
    (hm : m ≤ x + y) : η * m / (x * y) ≤ η / x + η / y := by
  rw [div_le_iff₀ (by positivity)]
  have : (η / x + η / y) * (x * y) = η * (x + y) := by field_simp; ring
  rw [this]
  nlinarith

/-- [26] (6.11), pointwise (for `η ≤ ℓ₁ ≤ (E_L - E)/2`): the right side of (6.10) is at most
`4 f(λ) + 12 (η/ℓ₁) 1_{[E,E_L]}(λ) + 10 · 1_{[E-ℓ₁,E+ℓ₁]}(λ) + 10 · 1_{[E_L-ℓ₁,∞)}(λ)`, with
`f(x) = η (E_L - E)/(d_L(x) d(x)) · 1(x ≤ E - ℓ₁)` of (6.12). -/
theorem poisson_bridge_pointwise {η ℓ₁ E EL : ℝ} (hη : 0 < η) (hηℓ : η ≤ ℓ₁)
    (hℓE : 2 * ℓ₁ ≤ EL - E) (lam : ℝ) :
    4 * η * ((EL - E) / ((|lam - EL| + η) * (|lam - E| + η)) +
        (if E ≤ lam ∧ lam ≤ EL then (1 : ℝ) else 0) /
          ((|lam - EL| + η) + (|lam - E| + η))) ≤
      4 * (η * (EL - E) / ((|lam - EL| + η) * (|lam - E| + η)) *
          (if lam ≤ E - ℓ₁ then (1 : ℝ) else 0)) +
        12 * (η / ℓ₁) * (if E ≤ lam ∧ lam ≤ EL then (1 : ℝ) else 0) +
        10 * (if E - ℓ₁ ≤ lam ∧ lam ≤ E + ℓ₁ then (1 : ℝ) else 0) +
        10 * (if EL - ℓ₁ ≤ lam then (1 : ℝ) else 0) := by
  have hℓ : 0 < ℓ₁ := lt_of_lt_of_le hη hηℓ
  have hm0 : 0 < EL - E := by linarith
  have hr : 0 ≤ η / ℓ₁ := by positivity
  have hdpos : 0 < |lam - E| + η := by positivity
  have hdLpos : 0 < |lam - EL| + η := by positivity
  have hdη : η ≤ |lam - E| + η := by linarith [abs_nonneg (lam - E)]
  have hdLη : η ≤ |lam - EL| + η := by linarith [abs_nonneg (lam - EL)]
  have hL : 4 * η * ((EL - E) / ((|lam - EL| + η) * (|lam - E| + η)) +
        (if E ≤ lam ∧ lam ≤ EL then (1 : ℝ) else 0) / ((|lam - EL| + η) + (|lam - E| + η))) =
      4 * (η * (EL - E) / ((|lam - EL| + η) * (|lam - E| + η))) +
        4 * η * ((if E ≤ lam ∧ lam ≤ EL then (1 : ℝ) else 0) /
          ((|lam - EL| + η) + (|lam - E| + η))) := by
    field_simp
  rw [hL]
  have e4 : 4 * η * (1 / ((|lam - EL| + η) + (|lam - E| + η))) =
      4 * (η / ((|lam - EL| + η) + (|lam - E| + η))) := by ring
  have hN1 : 0 ≤ (if E - ℓ₁ ≤ lam ∧ lam ≤ E + ℓ₁ then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have hN2 : 0 ≤ (if EL - ℓ₁ ≤ lam then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  by_cases h1 : lam ≤ E - ℓ₁
  · -- region 1: equality with 4 f
    have hc : ¬ (E ≤ lam ∧ lam ≤ EL) := fun h => by linarith [h.1]
    simp only [hc, h1, ↓reduceIte, zero_div, mul_zero, add_zero, mul_one]
    have hB : 0 ≤ 10 * (if E - ℓ₁ ≤ lam ∧ lam ≤ E + ℓ₁ then (1 : ℝ) else 0) := by linarith
    have hC : 0 ≤ 10 * (if EL - ℓ₁ ≤ lam then (1 : ℝ) else 0) := by linarith
    linarith
  · have h1' : E - ℓ₁ < lam := not_le.1 h1
    simp only [h1, ↓reduceIte, mul_zero]
    by_cases h2 : lam < E
    · -- region 2: E - ℓ₁ < lam < E
      have hc : ¬ (E ≤ lam ∧ lam ≤ EL) := fun h => by linarith [h.1]
      have hB : (E - ℓ₁ ≤ lam ∧ lam ≤ E + ℓ₁) := ⟨h1'.le, by linarith⟩
      simp only [hc, hB, and_self, ↓reduceIte, zero_div, mul_zero, add_zero]
      have e1 : |lam - EL| + η = EL - lam + η := by rw [abs_of_nonpos (by linarith)]; ring
      have key := bridge_aux (η := η) (m := EL - E) (x := |lam - EL| + η) (y := |lam - E| + η)
        (c := 1) hη hdLpos hdpos hm0.le (by rw [e1]; linarith)
      have h3 : η / (|lam - E| + η) ≤ 1 := by rw [div_le_one hdpos]; exact hdη
      linarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hN2]
    · have h2' : E ≤ lam := not_lt.1 h2
      by_cases h3 : lam ≤ EL
      · -- region 3: E ≤ lam ≤ EL
        have hc : (E ≤ lam ∧ lam ≤ EL) := ⟨h2', h3⟩
        simp only [hc, and_self, ↓reduceIte, mul_one]
        have e1 : |lam - EL| + η = EL - lam + η := by rw [abs_of_nonpos (by linarith)]; ring
        have e2 : |lam - E| + η = lam - E + η := by rw [abs_of_nonneg (by linarith)]
        by_cases h4 : lam ≤ E + ℓ₁
        · -- 3a: near E
          have hB : (E - ℓ₁ ≤ lam ∧ lam ≤ E + ℓ₁) := ⟨h1'.le, h4⟩
          simp only [hB, and_self, ↓reduceIte, mul_one]
          have key := bridge_aux (η := η) (m := EL - E) (x := |lam - EL| + η)
            (y := |lam - E| + η) (c := 2) hη hdLpos hdpos hm0.le (by rw [e1]; linarith)
          have h5 : η / (|lam - E| + η) ≤ 1 := by rw [div_le_one hdpos]; exact hdη
          have h6 : η / ((|lam - EL| + η) + (|lam - E| + η)) ≤ 1 / 2 := by
            rw [div_le_iff₀ (by positivity)]; linarith
          have h7 : 0 ≤ 12 * (η / ℓ₁) := by positivity
          rw [e4]
          linarith
        · have h4' : E + ℓ₁ < lam := not_le.1 h4
          by_cases h5 : EL - ℓ₁ ≤ lam
          · -- 3b: near EL
            have hB : ¬ (E - ℓ₁ ≤ lam ∧ lam ≤ E + ℓ₁) := fun h => by linarith [h.2]
            simp only [hB, h5, ↓reduceIte, mul_zero, zero_add, add_zero]
            have key := bridge_aux (η := η) (m := EL - E) (x := |lam - E| + η)
              (y := |lam - EL| + η) (c := 2) hη hdpos hdLpos hm0.le (by rw [e2]; linarith)
            have h5' : η / (|lam - EL| + η) ≤ 1 := by rw [div_le_one hdLpos]; exact hdLη
            have h6 : η / ((|lam - EL| + η) + (|lam - E| + η)) ≤ 1 / 2 := by
              rw [div_le_iff₀ (by positivity)]; linarith
            have h7 : 0 ≤ 12 * (η / ℓ₁) := by positivity
            have e3 : η * (EL - E) / ((|lam - EL| + η) * (|lam - E| + η)) =
                η * (EL - E) / ((|lam - E| + η) * (|lam - EL| + η)) := by rw [mul_comm (|lam - EL| + η) (|lam - E| + η)]
            rw [e3, e4]
            linarith
          · -- 3c: the middle
            have h5' : lam < EL - ℓ₁ := not_le.1 h5
            have hB : ¬ (E - ℓ₁ ≤ lam ∧ lam ≤ E + ℓ₁) := fun h => by linarith [h.2]
            simp only [hB, h5, ↓reduceIte, mul_zero, zero_add, add_zero]
            have hd1 : ℓ₁ < |lam - E| + η := by rw [e2]; linarith
            have hdL1 : ℓ₁ < |lam - EL| + η := by rw [e1]; linarith
            have key := bridge_aux3 (η := η) (m := EL - E) (x := |lam - EL| + η)
              (y := |lam - E| + η) hη hdLpos hdpos (by rw [e1, e2]; linarith)
            have a1 : η / (|lam - EL| + η) ≤ η / ℓ₁ :=
              div_le_div_of_nonneg_left hη.le hℓ hdL1.le
            have a2 : η / (|lam - E| + η) ≤ η / ℓ₁ :=
              div_le_div_of_nonneg_left hη.le hℓ hd1.le
            have a3 : η / ((|lam - EL| + η) + (|lam - E| + η)) ≤ η / (2 * ℓ₁) :=
              div_le_div_of_nonneg_left hη.le (by positivity) (by linarith)
            have a4 : η / (2 * ℓ₁) = (η / ℓ₁) / 2 := by field_simp
            rw [e4]
            linarith
      · -- region 4: lam > EL
        have h3' : EL < lam := not_le.1 h3
        have hc : ¬ (E ≤ lam ∧ lam ≤ EL) := fun h => h3 h.2
        have hC : EL - ℓ₁ ≤ lam := by linarith
        simp only [hc, hC, ↓reduceIte, zero_div, mul_zero, add_zero]
        have e2 : |lam - E| + η = lam - E + η := by rw [abs_of_nonneg (by linarith)]
        have key := bridge_aux (η := η) (m := EL - E) (x := |lam - E| + η)
          (y := |lam - EL| + η) (c := 1) hη hdpos hdLpos hm0.le (by rw [e2]; linarith)
        have e3 : η * (EL - E) / ((|lam - EL| + η) * (|lam - E| + η)) =
            η * (EL - E) / ((|lam - E| + η) * (|lam - EL| + η)) := by rw [mul_comm (|lam - EL| + η) (|lam - E| + η)]
        rw [e3]
        have h5 : η / (|lam - EL| + η) ≤ 1 := by rw [div_le_one hdLpos]; exact hdLη
        have hB : 0 ≤ 10 * (if E - ℓ₁ ≤ lam ∧ lam ≤ E + ℓ₁ then (1 : ℝ) else 0) := by linarith
        linarith

private lemma continuous_kernel_conv (ℓ a : ℝ) (hℓ : 0 < ℓ) :
    Continuous fun y : ℝ => 1 / (y ^ 2 + ℓ ^ 2) * thetaEta ℓ (a - y) := by
  unfold thetaEta
  refine Continuous.mul (Continuous.div continuous_const (by fun_prop) fun y => by positivity)
    (Continuous.div continuous_const (by fun_prop) fun y => by positivity)

/-- [26] (6.15), window form: `1/a² ≤ 5π ∫_{-ℓ}^{ℓ} g_ℓ(y) θ_ℓ(a - y) dy` for `|a| ≥ ℓ`, with
`g_ℓ(y) = 1/(y² + ℓ²)` of (6.14). -/
theorem inv_sq_le_window_conv {ℓ a : ℝ} (hℓ : 0 < ℓ) (ha : ℓ ≤ |a|) :
    1 / a ^ 2 ≤ 5 * Real.pi * ∫ y in (-ℓ)..ℓ, 1 / (y ^ 2 + ℓ ^ 2) * thetaEta ℓ (a - y) := by
  have hpi := Real.pi_pos
  have ha0 : 0 < |a| := lt_of_lt_of_le hℓ ha
  have ha' : a ≠ 0 := abs_pos.1 ha0
  have ha2 : 0 < a ^ 2 := by positivity
  have hℓa : ℓ ^ 2 ≤ a ^ 2 := by
    have := sq_le_sq' (by linarith [abs_nonneg a]) ha
    simpa [sq_abs] using this
  have hlow : ∀ y ∈ Set.Icc (-ℓ) ℓ,
      1 / (10 * Real.pi * ℓ * a ^ 2) ≤ 1 / (y ^ 2 + ℓ ^ 2) * thetaEta ℓ (a - y) := by
    intro y hy
    have hy2 : y ^ 2 ≤ ℓ ^ 2 := by nlinarith [hy.1, hy.2]
    have hay : |a - y| ≤ 2 * |a| := by
      have := abs_sub a y
      have hyl : |y| ≤ ℓ := abs_le.2 hy
      linarith
    have hay2 : (a - y) ^ 2 ≤ 4 * a ^ 2 := by
      calc (a - y) ^ 2 = |a - y| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * |a|) ^ 2 := by gcongr
        _ = 4 * a ^ 2 := by rw [mul_pow, sq_abs]; norm_num
    have h1 : 1 / (2 * ℓ ^ 2) ≤ 1 / (y ^ 2 + ℓ ^ 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have h2 : ℓ / (Real.pi * (5 * a ^ 2)) ≤ thetaEta ℓ (a - y) := by
      unfold thetaEta
      apply div_le_div_of_nonneg_left hℓ.le (by positivity)
      have : 0 < Real.pi := hpi
      nlinarith
    calc 1 / (10 * Real.pi * ℓ * a ^ 2)
        = 1 / (2 * ℓ ^ 2) * (ℓ / (Real.pi * (5 * a ^ 2))) := by field_simp; ring
      _ ≤ 1 / (y ^ 2 + ℓ ^ 2) * thetaEta ℓ (a - y) := by
          apply mul_le_mul h1 h2 (by positivity) (by positivity)
  have hint := intervalIntegral.integral_mono_on (μ := volume) (by linarith)
    (continuous_const.intervalIntegrable (μ := volume) _ _)
    ((continuous_kernel_conv ℓ a hℓ).intervalIntegrable (μ := volume) _ _) hlow
  rw [intervalIntegral.integral_const] at hint
  simp only [smul_eq_mul] at hint
  have e : (ℓ - -ℓ) * (1 / (10 * Real.pi * ℓ * a ^ 2)) = 1 / (5 * Real.pi * a ^ 2) := by
    field_simp; ring
  rw [e] at hint
  calc 1 / a ^ 2 = 5 * Real.pi * (1 / (5 * Real.pi * a ^ 2)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hint (by positivity)

private lemma integrable_kernel_conv {ℓ : ℝ} (hℓ : 0 < ℓ) (a : ℝ) :
    Integrable fun y : ℝ => 1 / (y ^ 2 + ℓ ^ 2) * thetaEta ℓ (a - y) := by
  have hb : Integrable fun y : ℝ => (ℓ ^ 2)⁻¹ * thetaEta ℓ (a - y) :=
    ((integrable_thetaEta hℓ).comp_sub_left a).const_mul _
  refine hb.mono' (continuous_kernel_conv ℓ a hℓ).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have hth : 0 ≤ thetaEta ℓ (a - y) := by unfold thetaEta; positivity
  have hg : 1 / (y ^ 2 + ℓ ^ 2) ≤ (ℓ ^ 2)⁻¹ := by
    rw [one_div]
    exact inv_anti₀ (by positivity) (by nlinarith [sq_nonneg y])
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right hg hth

/-- [26] (6.15), full-line form: `1/a² ≤ 5π (g_ℓ ∗ θ_ℓ)(a)` for `|a| ≥ ℓ`. -/
theorem inv_sq_le_conv {ℓ a : ℝ} (hℓ : 0 < ℓ) (ha : ℓ ≤ |a|) :
    1 / a ^ 2 ≤ 5 * Real.pi * ∫ y, 1 / (y ^ 2 + ℓ ^ 2) * thetaEta ℓ (a - y) := by
  refine (inv_sq_le_window_conv hℓ ha).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [intervalIntegral.integral_of_le (by linarith)]
  refine setIntegral_le_integral (integrable_kernel_conv hℓ a) (Eventually.of_forall fun y => ?_)
  have hth : 0 ≤ thetaEta ℓ (a - y) := by unfold thetaEta; positivity
  show 0 ≤ 1 / (y ^ 2 + ℓ ^ 2) * thetaEta ℓ (a - y)
  positivity

/-! ## Nondegenerate instances -/

/-- `integrable_thetaEta` and `integral_thetaEta` at `η = 1/10`. -/
example : Integrable (thetaEta (1 / 10)) ∧ ∫ x, thetaEta (1 / 10) x = 1 :=
  ⟨integrable_thetaEta (by norm_num), integral_thetaEta (by norm_num)⟩

/-- `integral_Ioi_thetaEta_le` and `integral_abs_ge_thetaEta_le` at `η = 1/10`, `α = 1/10`. -/
example : ∫ x in Set.Ioi (1 / 10 : ℝ), thetaEta (1 / 10) x ≤ (1 / 10) / (1 / 10 + 1 / 10) ∧
    ∫ x in {x : ℝ | (1 / 10 : ℝ) ≤ |x|}, thetaEta (1 / 10) x ≤ 2 * (1 / 10) / (1 / 10 + 1 / 10) :=
  ⟨integral_Ioi_thetaEta_le (by norm_num) (by norm_num),
    integral_abs_ge_thetaEta_le (by norm_num) (by norm_num)⟩

/-- `integral_Ioi_thetaEta_le` and `integral_abs_ge_thetaEta_le` at `η = 1/10`, `α = 0`. -/
example : ∫ x in Set.Ioi (0 : ℝ), thetaEta (1 / 10) x ≤ (1 / 10) / (0 + 1 / 10) ∧
    ∫ x in {x : ℝ | (0 : ℝ) ≤ |x|}, thetaEta (1 / 10) x ≤ 2 * (1 / 10) / (0 + 1 / 10) :=
  ⟨integral_Ioi_thetaEta_le (by norm_num) le_rfl, integral_abs_ge_thetaEta_le (by norm_num) le_rfl⟩

/-- `abs_indicator_sub_integral_thetaEta_le` at `η = 1/10`, `E = 0`, `E_L = 1`, `λ = 1/2`. -/
example : |(if (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1 then (1 : ℝ) else 0) -
      ∫ y in (0 : ℝ)..1, thetaEta (1 / 10) (1 / 2 - y)| ≤
    4 * (1 / 10) * ((1 - 0) / ((|1 / 2 - 1| + 1 / 10) * (|1 / 2 - 0| + 1 / 10)) +
      (if (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1 then (1 : ℝ) else 0) /
        ((|1 / 2 - 1| + 1 / 10) + (|1 / 2 - 0| + 1 / 10))) :=
  abs_indicator_sub_integral_thetaEta_le (by norm_num) (by norm_num) (1 / 2)

/-- `inv_sq_le_window_conv` and `inv_sq_le_conv` at `ℓ = 1/10`, `a = 1/5`. -/
example : 1 / (1 / 5 : ℝ) ^ 2 ≤ 5 * Real.pi * ∫ y in (-(1 / 10 : ℝ))..(1 / 10),
      1 / (y ^ 2 + (1 / 10 : ℝ) ^ 2) * thetaEta (1 / 10) (1 / 5 - y) ∧
    1 / (1 / 5 : ℝ) ^ 2 ≤ 5 * Real.pi * ∫ y, 1 / (y ^ 2 + (1 / 10 : ℝ) ^ 2) *
      thetaEta (1 / 10) (1 / 5 - y) :=
  ⟨inv_sq_le_window_conv (by norm_num) (by rw [abs_of_pos (by norm_num)]; norm_num),
    inv_sq_le_conv (by norm_num) (by rw [abs_of_pos (by norm_num)]; norm_num)⟩

/-- `poisson_bridge_pointwise` at `η = 1/100`, `ℓ₁ = 1/10`, `E = 0`, `E_L = 1`, `λ = 1/2`. -/
example : 4 * (1 / 100 : ℝ) * ((1 - 0) / ((|1 / 2 - 1| + 1 / 100) * (|1 / 2 - 0| + 1 / 100)) +
        (if (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1 then (1 : ℝ) else 0) /
          ((|1 / 2 - 1| + 1 / 100) + (|1 / 2 - 0| + 1 / 100))) ≤
      4 * ((1 / 100 : ℝ) * (1 - 0) / ((|1 / 2 - 1| + 1 / 100) * (|1 / 2 - 0| + 1 / 100)) *
          (if (1 / 2 : ℝ) ≤ 0 - 1 / 10 then (1 : ℝ) else 0)) +
        12 * ((1 / 100) / (1 / 10)) * (if (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1 then (1 : ℝ) else 0) +
        10 * (if (0 : ℝ) - 1 / 10 ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 0 + 1 / 10 then (1 : ℝ) else 0) +
        10 * (if (1 : ℝ) - 1 / 10 ≤ 1 / 2 then (1 : ℝ) else 0) :=
  poisson_bridge_pointwise (by norm_num) (by norm_num) (by norm_num) (1 / 2)


#print axioms integrable_thetaEta
#print axioms integral_thetaEta
#print axioms abs_indicator_sub_integral_thetaEta_le
#print axioms integral_Ioi_thetaEta_le
#print axioms integral_abs_ge_thetaEta_le
#print axioms poisson_bridge_pointwise
#print axioms inv_sq_le_window_conv
#print axioms inv_sq_le_conv

end WEdgeNS
