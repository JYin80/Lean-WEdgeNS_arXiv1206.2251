import WEdgeNS.LocalLaw.SelfConsistent
import WEdgeNS.LocalLaw.LargeEta
import WEdgeNS.LocalLaw.Dichotomy
import WEdgeNS.LocalLaw.Lattice

/-!
# The weak local semicircle law
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

-- Parameter arithmetic, elementary bounds on the control parameters and the Rademacher instance
-- of the self-consistent equation module.
open private sc_one_le_phi sc_phi_pos sc_rpow_sq sc_rpow_mono sc_specDomain_mono sc_specDomain
  sc_msc_ne_zero sc_lamO_nonneg sc_lamD_nonneg sc_avg_le sc_lamAvg_le_lamD sc_rad_instance
  from WEdgeNS.LocalLaw.SelfConsistent

/-! ### Lipschitz continuity in `z` -/

/-- `m_sc(z) (z + m_sc(z)) = -1` for `Im z > 0`. -/
private lemma weak_msc_mul_add {z : ℂ} (hz : 0 < z.im) : msc z * (z + msc z) = -1 := by
  have h := msc_add_inv_eq_zero hz
  have hm := sc_msc_ne_zero hz
  have hzm : z + msc z ≠ 0 := fun h0 => by
    rw [h0, _root_.inv_zero, add_zero] at h
    exact hm h
  field_simp at h
  linear_combination h

/-- `Im m_sc (1 - |m_sc|²) = η |m_sc|²`. -/
private lemma weak_im_msc_mul {z : ℂ} (hz : 0 < z.im) :
    (msc z).im * (1 - ‖msc z‖ ^ 2) = z.im * ‖msc z‖ ^ 2 := by
  have h := weak_msc_mul_add hz
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re,
    Complex.neg_im, Complex.one_re, Complex.one_im] at hre him
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  linear_combination (msc z).im * hre - (msc z).re * him

/-- Lipschitz continuity of `m_sc`: `|m_sc(z) - m_sc(w)| ≤ |z - w| / (Im z Im w)`. -/
private lemma weak_norm_msc_sub_le {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    ‖msc z - msc w‖ ≤ ‖z - w‖ / (z.im * w.im) := by
  have e1 := weak_msc_mul_add hz
  have e2 := weak_msc_mul_add hw
  have hid : (msc z - msc w) * (1 - msc z * msc w) = msc z * msc w * (z - w) := by
    linear_combination (-msc w) * e1 + msc z * e2
  have hn := congrArg norm hid
  rw [norm_mul, norm_mul, norm_mul] at hn
  set a := ‖msc z‖ with ha
  set b := ‖msc w‖ with hb
  have ha0 : 0 < a := norm_pos_iff.mpr (sc_msc_ne_zero hz)
  have hb0 : 0 < b := norm_pos_iff.mpr (sc_msc_ne_zero hw)
  have ha1 : a < 1 := (norm_msc_eq_inv_and_lt_one hz).2
  have hb1 : b < 1 := (norm_msc_eq_inv_and_lt_one hw).2
  have hya : (msc z).im ≤ a := Complex.im_le_norm _
  have hyb : (msc w).im ≤ b := Complex.im_le_norm _
  have hy0 := im_msc_pos hz
  have hyw := im_msc_pos hw
  have i1 := weak_im_msc_mul hz
  have i2 := weak_im_msc_mul hw
  rw [← ha] at i1
  rw [← hb] at i2
  have h1 : z.im * a ≤ 1 - a ^ 2 := by
    have : z.im * a ^ 2 ≤ a * (1 - a ^ 2) := by
      rw [← i1]
      exact mul_le_mul_of_nonneg_right hya (by nlinarith)
    nlinarith
  have h2 : w.im * b ≤ 1 - b ^ 2 := by
    have : w.im * b ^ 2 ≤ b * (1 - b ^ 2) := by
      rw [← i2]
      exact mul_le_mul_of_nonneg_right hyb (by nlinarith)
    nlinarith
  have h3 : (z.im * a) * (w.im * b) ≤ 1 - a * b := by
    have hp : (z.im * a) * (w.im * b) ≤ (1 - a ^ 2) * (1 - b ^ 2) :=
      mul_le_mul h1 h2 (by positivity) (by nlinarith)
    have hab : 0 ≤ a * b := by positivity
    have hab1 : a * b ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (a - b)]
  have h4 : 1 - a * b ≤ ‖1 - msc z * msc w‖ := by
    have := norm_sub_norm_le (1 : ℂ) (msc z * msc w)
    rw [norm_one, norm_mul] at this
    linarith
  set D := ‖msc z - msc w‖
  have hD : 0 ≤ D := norm_nonneg _
  have h5 : D * (a * b * (z.im * w.im)) ≤ a * b * ‖z - w‖ := by
    calc D * (a * b * (z.im * w.im)) = D * ((z.im * a) * (w.im * b)) := by ring
      _ ≤ D * ‖1 - msc z * msc w‖ := mul_le_mul_of_nonneg_left (h3.trans h4) hD
      _ = a * b * ‖z - w‖ := hn
  have hab : 0 < a * b := by positivity
  rw [le_div_iff₀ (by positivity)]
  have : a * b * (D * (z.im * w.im)) ≤ a * b * ‖z - w‖ := by linarith
  exact le_of_mul_le_mul_left this hab

section Lipschitz

variable {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}

/-- Lipschitz continuity of `Λ_o` in `z`. -/
private lemma weak_lamO_le_add (hH : H.IsHermitian) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    lamO H z ≤ lamO H w + ‖z - w‖ / (z.im * w.im) := by
  have hL : 0 ≤ ‖z - w‖ / (z.im * w.im) := by positivity
  have h0 := sc_lamO_nonneg H w
  refine Real.iSup_le (fun i => Real.iSup_le (fun j => ?_) (by positivity)) (by positivity)
  split_ifs with hij
  · positivity
  · have h1 := norm_resolventC_apply_sub_le hH hz hw i j
    have h2 := norm_resolventC_off_le_lamO (H := H) (z := w) hij
    have h3 := norm_sub_norm_le (resolventC H z i j) (resolventC H w i j)
    linarith

/-- Lipschitz continuity of `Λ_d` in `z`. -/
private lemma weak_lamD_le_add (hH : H.IsHermitian) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    lamD H z ≤ lamD H w + 2 * (‖z - w‖ / (z.im * w.im)) := by
  have hL : 0 ≤ ‖z - w‖ / (z.im * w.im) := by positivity
  have h0 := sc_lamD_nonneg H w
  refine Real.iSup_le (fun i => ?_) (by positivity)
  have h1 := norm_resolventC_apply_sub_le hH hz hw i i
  have h2 := norm_resolventC_sub_msc_le_lamD (H := H) (z := w) i
  have h3 := weak_norm_msc_sub_le hz hw
  have e : resolventC H z i i - msc z = (resolventC H w i i - msc w) +
      (resolventC H z i i - resolventC H w i i) - (msc z - msc w) := by ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have := norm_add_le (resolventC H w i i - msc w) (resolventC H z i i - resolventC H w i i)
  linarith

/-- Lipschitz continuity of `m` in `z`. -/
private lemma weak_norm_stieltjesM_sub_le (hN : 0 < N) (hH : H.IsHermitian) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    ‖stieltjesM H z - stieltjesM H w‖ ≤ ‖z - w‖ / (z.im * w.im) := by
  have e : stieltjesM H z - stieltjesM H w =
      (N : ℂ)⁻¹ * ∑ i, (resolventC H z i i - resolventC H w i i) := by
    unfold stieltjesM
    rw [Finset.sum_sub_distrib, Matrix.trace, Matrix.trace]
    simp only [Matrix.diag]
    ring
  rw [e]
  exact sc_avg_le hN _ fun i => norm_resolventC_apply_sub_le hH hz hw i i

/-- Lipschitz continuity of `Λ` in `z`. -/
private lemma weak_lamAvg_le_add (hN : 0 < N) (hH : H.IsHermitian) {z w : ℂ} (hz : 0 < z.im)
    (hw : 0 < w.im) : lamAvg H z ≤ lamAvg H w + 2 * (‖z - w‖ / (z.im * w.im)) := by
  have h1 := weak_norm_stieltjesM_sub_le hN hH hz hw
  have h3 := weak_norm_msc_sub_le hz hw
  unfold lamAvg
  have e : stieltjesM H z - msc z = (stieltjesM H w - msc w) +
      (stieltjesM H z - stieltjesM H w) - (msc z - msc w) := by ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have := norm_add_le (stieltjesM H w - msc w) (stieltjesM H z - stieltjesM H w)
  linarith

/-- `Λ_d ≤ max_i |G_ii - m| + Λ`. -/
private lemma weak_lamD_le (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    lamD H z ≤ (⨆ i, ‖resolventC H z i i - stieltjesM H z‖) + lamAvg H z := by
  have h0 : 0 ≤ ⨆ i, ‖resolventC H z i i - stieltjesM H z‖ :=
    Real.iSup_nonneg fun _ => norm_nonneg _
  have h1 : 0 ≤ lamAvg H z := norm_nonneg _
  refine Real.iSup_le (fun i => ?_) (by positivity)
  have h2 : ‖resolventC H z i i - stieltjesM H z‖ ≤ ⨆ i, ‖resolventC H z i i - stieltjesM H z‖ :=
    le_ciSup (f := fun i => ‖resolventC H z i i - stieltjesM H z‖) (Set.finite_range _).bddAbove i
  have e : resolventC H z i i - msc z = (resolventC H z i i - stieltjesM H z) +
      (stieltjesM H z - msc z) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  unfold lamAvg
  linarith

end Lipschitz

/-! ### The input of the dichotomy -/

/-- `s² √((Λ + I)/n) ≤ β (β + Λ + I)/2` once `s⁴/n ≤ β³` (the bound of `Ψ` behind (3.46)). -/
private lemma weak_psi_le {s n Λ I β : ℝ} (hn : 0 < n) (hΛI : 0 ≤ Λ + I) (hβ : 0 ≤ β)
    (hβn : s ^ 2 * s ^ 2 / n ≤ β ^ 3) :
    s ^ 2 * Real.sqrt ((Λ + I) / n) ≤ β * (β + Λ + I) / 2 := by
  have hX : 0 ≤ (Λ + I) / n := div_nonneg hΛI hn.le
  have e : s ^ 2 * Real.sqrt ((Λ + I) / n) = Real.sqrt ((s ^ 2) ^ 2 * ((Λ + I) / n)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [e, Real.sqrt_le_left (div_nonneg (mul_nonneg hβ (by linarith)) two_pos.le)]
  have h1 : (s ^ 2) ^ 2 * ((Λ + I) / n) = (s ^ 2 * s ^ 2 / n) * (Λ + I) := by
    field_simp
  rw [h1]
  calc (s ^ 2 * s ^ 2 / n) * (Λ + I) ≤ β ^ 3 * (Λ + I) := mul_le_mul_of_nonneg_right hβn hΛI
    _ ≤ (β * (β + Λ + I) / 2) ^ 2 := by
        nlinarith [mul_nonneg (sq_nonneg β) (sq_nonneg (β - (Λ + I)))]

/-- `|w| ∼ √(κ + η)` for `w = (1 - m_sc²)/m_sc³`, with constant `C_m⁴`. -/
private lemma weak_w_bounds {Cm t : ℝ} {M : ℂ} (hCm : 1 ≤ Cm) (hM1 : Cm⁻¹ ≤ ‖M‖)
    (hM2 : ‖M‖ ≤ Cm) (ht1 : Cm⁻¹ * t ≤ ‖1 - M ^ 2‖) (ht2 : ‖1 - M ^ 2‖ ≤ Cm * t) :
    (Cm ^ 4)⁻¹ * t ≤ ‖(1 - M ^ 2) / M ^ 3‖ ∧ ‖(1 - M ^ 2) / M ^ 3‖ ≤ Cm ^ 4 * t := by
  have hCm0 : 0 < Cm := by linarith
  have hMpos : 0 < ‖M‖ := lt_of_lt_of_le (inv_pos.mpr hCm0) hM1
  have hM3 : 0 < ‖M‖ ^ 3 := by positivity
  have hMinv : ‖M‖⁻¹ ≤ Cm := by
    rw [inv_le_comm₀ hMpos hCm0]
    exact hM1
  have hMinv3 : (‖M‖ ^ 3)⁻¹ ≤ Cm ^ 3 := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (by positivity) hMinv 3
  have hM3le : ‖M‖ ^ 3 ≤ Cm ^ 3 := pow_le_pow_left₀ hMpos.le hM2 3
  have hw : ‖(1 - M ^ 2) / M ^ 3‖ = ‖1 - M ^ 2‖ / ‖M‖ ^ 3 := by
    rw [norm_div, norm_pow]
  have ht0 : 0 ≤ t := by
    by_contra h
    push Not at h
    have : Cm * t < 0 := mul_neg_of_pos_of_neg hCm0 h
    linarith [norm_nonneg (1 - M ^ 2)]
  constructor
  · rw [hw, le_div_iff₀ hM3]
    calc (Cm ^ 4)⁻¹ * t * ‖M‖ ^ 3 ≤ (Cm ^ 4)⁻¹ * t * Cm ^ 3 :=
          mul_le_mul_of_nonneg_left hM3le (by positivity)
      _ = Cm⁻¹ * t := by field_simp
      _ ≤ ‖1 - M ^ 2‖ := ht1
  · rw [hw, div_eq_mul_inv]
    calc ‖1 - M ^ 2‖ * (‖M‖ ^ 3)⁻¹ ≤ (Cm * t) * Cm ^ 3 :=
          mul_le_mul ht2 hMinv3 (by positivity) (by positivity)
      _ = Cm ^ 4 * t := by ring

/-- (3.42) divided by `m_sc³` is the hypothesis of the dichotomy (Lemma 3.17 of [15]), with
`w = (1 - m_sc²)/m_sc³`, `K = C_m⁴`, `δ = C_m³ C/log N` and `Cs = C C_m³ (2 + C_m⁵)`. -/
private lemma weak_dich_input {Cc Cm s q n I lg β t : ℝ} {M v : ℂ}
    (hCm : 1 ≤ Cm) (hM1 : Cm⁻¹ ≤ ‖M‖) (hM2 : ‖M‖ ≤ Cm)
    (ht1 : Cm⁻¹ * t ≤ ‖1 - M ^ 2‖) (ht2 : ‖1 - M ^ 2‖ ≤ Cm * t)
    (hI0 : 0 ≤ I) (hI : I ≤ Cm * t) (hn : 0 < n) (hlg : 0 < lg) (hCc : 0 < Cc)
    (hβ : 0 ≤ β) (hβq : s / q ≤ β ^ 2) (hβn : s ^ 2 * s ^ 2 / n ≤ β ^ 3)
    (hSC : ‖(1 - M ^ 2) * v - M ^ 3 * v ^ 2‖ ≤
      Cc * (‖v‖ ^ 2 / lg + s / q + s ^ 2 * Real.sqrt ((‖v‖ + I) / n))) :
    ‖(1 - M ^ 2) / M ^ 3 * v - v ^ 2‖ ≤ Cm ^ 3 * Cc / lg * ‖v‖ ^ 2 +
        Cc * Cm ^ 3 * (2 + Cm ^ 5) * (β * ‖v‖ + ‖(1 - M ^ 2) / M ^ 3‖ * β + β ^ 2) ∧
      (Cm ^ 4)⁻¹ * t ≤ ‖(1 - M ^ 2) / M ^ 3‖ ∧ ‖(1 - M ^ 2) / M ^ 3‖ ≤ Cm ^ 4 * t := by
  have hCm0 : 0 < Cm := by linarith
  have hMpos : 0 < ‖M‖ := lt_of_lt_of_le (inv_pos.mpr hCm0) hM1
  have hM0 : M ≠ 0 := norm_pos_iff.mp hMpos
  have hMinv : ‖M‖⁻¹ ≤ Cm := by
    rw [inv_le_comm₀ hMpos hCm0]
    exact hM1
  have hMinv3 : (‖M‖ ^ 3)⁻¹ ≤ Cm ^ 3 := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (by positivity) hMinv 3
  obtain ⟨hwlo, hwhi⟩ := weak_w_bounds hCm hM1 hM2 ht1 ht2
  refine ⟨?_, hwlo, hwhi⟩
  set W := ‖(1 - M ^ 2) / M ^ 3‖ with hW
  set Λ := ‖v‖ with hΛ
  have hΛ0 : 0 ≤ Λ := norm_nonneg v
  have hIW : I ≤ Cm ^ 5 * W := by
    have h1 : t ≤ Cm ^ 4 * W := by
      have := mul_le_mul_of_nonneg_left hwlo (by positivity : (0 : ℝ) ≤ Cm ^ 4)
      rwa [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at this
    calc I ≤ Cm * t := hI
      _ ≤ Cm * (Cm ^ 4 * W) := mul_le_mul_of_nonneg_left h1 hCm0.le
      _ = Cm ^ 5 * W := by ring
  have hpsi := weak_psi_le hn (add_nonneg hΛ0 hI0) hβ hβn
  have e : (1 - M ^ 2) / M ^ 3 * v - v ^ 2 = ((1 - M ^ 2) * v - M ^ 3 * v ^ 2) / M ^ 3 := by
    field_simp
  rw [e, norm_div, norm_pow, div_eq_mul_inv]
  have hW0 : 0 ≤ W := norm_nonneg _
  have hR0 : 0 ≤ Cc * (Λ ^ 2 / lg + s / q + s ^ 2 * Real.sqrt ((Λ + I) / n)) :=
    (norm_nonneg _).trans hSC
  have hinner : 3 / 2 * β ^ 2 + β * Λ / 2 + β * I / 2 ≤
      (2 + Cm ^ 5) * (β * Λ + W * β + β ^ 2) := by
    have a1 : β * I ≤ β * (Cm ^ 5 * W) := mul_le_mul_of_nonneg_left hIW hβ
    have a2 : 0 ≤ Cm ^ 5 * (β * Λ) := by positivity
    have a3 : 0 ≤ Cm ^ 5 * β ^ 2 := by positivity
    have a4 : 0 ≤ W * β := mul_nonneg hW0 hβ
    have a5 : 0 ≤ β * Λ := mul_nonneg hβ hΛ0
    have a6 : 0 ≤ β ^ 2 := sq_nonneg β
    nlinarith
  have hP : 0 < Cc * Cm ^ 3 := by positivity
  calc ‖(1 - M ^ 2) * v - M ^ 3 * v ^ 2‖ * (‖M‖ ^ 3)⁻¹
      ≤ Cc * (Λ ^ 2 / lg + s / q + s ^ 2 * Real.sqrt ((Λ + I) / n)) * Cm ^ 3 :=
        mul_le_mul hSC hMinv3 (by positivity) hR0
    _ ≤ Cc * (Λ ^ 2 / lg + β ^ 2 + β * (β + Λ + I) / 2) * Cm ^ 3 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ hCc.le
        linarith
    _ = Cm ^ 3 * Cc / lg * Λ ^ 2 + Cc * Cm ^ 3 * (3 / 2 * β ^ 2 + β * Λ / 2 + β * I / 2) := by
        field_simp
        ring
    _ ≤ Cm ^ 3 * Cc / lg * Λ ^ 2 + Cc * Cm ^ 3 * ((2 + Cm ^ 5) * (β * Λ + W * β + β ^ 2)) := by
        have := mul_le_mul_of_nonneg_left hinner hP.le
        linarith
    _ = _ := by ring

/-- `Im m_sc ≤ C √(κ + η)` from the two regimes of Lemma 2.6. -/
private lemma weak_im_msc_le {z : ℂ} {Cm : ℝ} (hz : 0 < z.im) (hCm : 0 ≤ Cm)
    (h3 : z.im ≤ kappa z.re → 2 ≤ |z.re| →
      Cm⁻¹ * (z.im / Real.sqrt (kappa z.re + z.im)) ≤ (msc z).im ∧
      (msc z).im ≤ Cm * (z.im / Real.sqrt (kappa z.re + z.im)))
    (h4 : kappa z.re ≤ z.im ∨ |z.re| ≤ 2 →
      Cm⁻¹ * Real.sqrt (kappa z.re + z.im) ≤ (msc z).im ∧
      (msc z).im ≤ Cm * Real.sqrt (kappa z.re + z.im)) :
    (msc z).im ≤ Cm * Real.sqrt (kappa z.re + z.im) := by
  by_cases hk : kappa z.re ≤ z.im
  · exact (h4 (Or.inl hk)).2
  by_cases he : |z.re| ≤ 2
  · exact (h4 (Or.inr he)).2
  push Not at hk he
  refine (h3 hk.le he.le).2.trans (mul_le_mul_of_nonneg_left ?_ hCm)
  have hκ : 0 ≤ kappa z.re := abs_nonneg _
  have ht : 0 < Real.sqrt (kappa z.re + z.im) := Real.sqrt_pos.mpr (by linarith)
  rw [div_le_iff₀ ht, Real.mul_self_sqrt (by linarith)]
  linarith

/-! ### Parameter arithmetic -/

/-- `β` of (3.46) of [15] with `(log N)^ξ = φ^ζ`. -/
private def weakBeta (N : ℕ) (ζ q : ℝ) (z : ℂ) : ℝ :=
  phi N ^ ζ / Real.sqrt q + phi N ^ (4 * ζ / 3) / (N * z.im) ^ ((1 : ℝ) / 3)

private lemma weak_rpow_le {x y a K : ℝ} (hx : 1 ≤ x) (haK : a ≤ K) (hy : x ^ K ≤ y) :
    x ^ a ≤ y :=
  (Real.rpow_le_rpow_of_exponent_le hx haK).trans hy

private lemma weak_cbrt_cube {n : ℝ} (hn : 0 ≤ n) : (n ^ ((1 : ℝ) / 3)) ^ 3 = n := by
  rw [show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.rpow_inv_natCast_pow hn (by norm_num)

/-- The exponent bookkeeping of the bootstrap for `φ^K ≤ q`, `φ^K ≤ n = Nη`, `K ≥ 8ζ + 3`. -/
private lemma weak_rpow_facts {x ζ K q n : ℝ} (hx : 1 ≤ x) (hζ : 0 < ζ) (hK : 8 * ζ + 3 ≤ K)
    (hq : x ^ K ≤ q) (hn : x ^ K ≤ n) :
    x ^ ζ * (x ^ ζ / q) ≤ 1 / x ∧
    x ^ ζ * ((x ^ ζ) ^ 2 / Real.sqrt n) ≤ 1 / x ∧
    x ^ ζ * (x ^ ζ / Real.sqrt q + x ^ (4 * ζ / 3) / n ^ ((1 : ℝ) / 3)) ≤ 2 / x ∧
    (x ^ ζ) ^ 2 * (x ^ ζ) ^ 2 / n ≤
      (x ^ ζ / Real.sqrt q + x ^ (4 * ζ / 3) / n ^ ((1 : ℝ) / 3)) ^ 3 ∧
    x ^ ζ / q ≤ (x ^ ζ / Real.sqrt q + x ^ (4 * ζ / 3) / n ^ ((1 : ℝ) / 3)) ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hxK : 0 < x ^ K := Real.rpow_pos_of_pos hx0 K
  have hq0 : 0 < q := hxK.trans_le hq
  have hn0 : 0 < n := hxK.trans_le hn
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hcn : 0 < n ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hn0 _
  have hs1 : 1 ≤ x ^ ζ := Real.one_le_rpow hx hζ.le
  have hs0 : 0 < x ^ ζ := by linarith
  have pw : ∀ a b : ℝ, x ^ a * x ^ b = x ^ (a + b) := fun a b => (Real.rpow_add hx0 a b).symm
  have pw1 : ∀ a : ℝ, x ^ a * x = x ^ (a + 1) := fun a => (Real.rpow_add_one hx0.ne' a).symm
  have sq2 : ∀ a : ℝ, (x ^ a) ^ 2 = x ^ (2 * a) := fun a => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    ring_nf
  -- `s² x ≤ q`
  have hA : x ^ ζ * x ^ ζ * x ≤ q := by
    rw [pw, pw1]
    exact weak_rpow_le hx (by linarith) hq
  -- `s³ x ≤ √n`
  have hB : (x ^ ζ) ^ 2 * x ^ ζ * x ≤ Real.sqrt n := by
    rw [Real.le_sqrt (by positivity) hn0.le]
    have e : ((x ^ ζ) ^ 2 * x ^ ζ * x) ^ 2 = x ^ (6 * ζ + 2) := by
      rw [sq2, pw, pw1, sq2]
      ring_nf
    rw [e]
    exact weak_rpow_le hx (by linarith) hn
  -- `s² x ≤ √q`
  have hC : x ^ ζ * x ^ ζ * x ≤ Real.sqrt q := by
    rw [Real.le_sqrt (by positivity) hq0.le]
    have e : (x ^ ζ * x ^ ζ * x) ^ 2 = x ^ (4 * ζ + 2) := by
      rw [pw, pw1, sq2]
      ring_nf
    rw [e]
    exact weak_rpow_le hx (by linarith) hq
  -- `s x^{4ζ/3} x ≤ n^{1/3}`
  have hD : x ^ ζ * x ^ (4 * ζ / 3) * x ≤ n ^ ((1 : ℝ) / 3) := by
    have e : x ^ ζ * x ^ (4 * ζ / 3) * x = (x ^ (7 * ζ + 3)) ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_mul hx0.le, pw, pw1]
      ring_nf
    rw [e]
    exact Real.rpow_le_rpow (by positivity) (weak_rpow_le hx (by linarith) hn) (by norm_num)
  set β := x ^ ζ / Real.sqrt q + x ^ (4 * ζ / 3) / n ^ ((1 : ℝ) / 3) with hβ
  have hb1 : 0 ≤ x ^ ζ / Real.sqrt q := by positivity
  have hb2 : 0 ≤ x ^ (4 * ζ / 3) / n ^ ((1 : ℝ) / 3) := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← mul_div_assoc, div_le_div_iff₀ hq0 hx0]
    linarith
  · rw [← mul_div_assoc, div_le_div_iff₀ hsn hx0]
    nlinarith
  · have e1 : x ^ ζ * (x ^ ζ / Real.sqrt q) ≤ 1 / x := by
      rw [← mul_div_assoc, div_le_div_iff₀ hsq hx0]
      linarith
    have e2 : x ^ ζ * (x ^ (4 * ζ / 3) / n ^ ((1 : ℝ) / 3)) ≤ 1 / x := by
      rw [← mul_div_assoc, div_le_div_iff₀ hcn hx0]
      linarith
    rw [mul_add]
    have : 2 / x = 1 / x + 1 / x := by ring
    linarith
  · have hy3 : (x ^ ζ) ^ 2 * (x ^ ζ) ^ 2 / n = (x ^ (4 * ζ / 3) / n ^ ((1 : ℝ) / 3)) ^ 3 := by
      have e3 : (x ^ (4 * ζ / 3)) ^ 3 = x ^ (4 * ζ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
        ring_nf
      rw [div_pow, weak_cbrt_cube hn0.le, e3, sq2, pw]
      ring_nf
    rw [hy3]
    exact pow_le_pow_left₀ hb2 (by linarith) 3
  · have h1 : x ^ ζ / q ≤ (x ^ ζ / Real.sqrt q) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hq0.le]
      exact div_le_div_of_nonneg_right (by nlinarith) hq0.le
    exact h1.trans (pow_le_pow_left₀ hb1 (by linarith) 2)

/-- `Ψ ≤ √2 / √(Nη)` once `Λ ≤ 1`. -/
private lemma weak_psiCtrl_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ} (hz : 0 < z.im)
    (hn : 0 < (N : ℝ) * z.im) (hΛ : lamAvg H z ≤ 1) :
    psiCtrl H z ≤ Real.sqrt 2 / Real.sqrt (N * z.im) := by
  have hI : (msc z).im ≤ 1 :=
    (Complex.im_le_norm _).trans (norm_msc_eq_inv_and_lt_one hz).2.le
  unfold psiCtrl
  rw [← Real.sqrt_div' 2 hn.le]
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) hn.le)

/-- `β` decreases in `η`. -/
private lemma weak_beta_anti {N : ℕ} {ζ q : ℝ} {z z' : ℂ} (hN : 0 < N) (hz : 0 < z.im)
    (hzz : z.im ≤ z'.im) : weakBeta N ζ q z' ≤ weakBeta N ζ q z := by
  unfold weakBeta
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hn : 0 < (N : ℝ) * z.im := by positivity
  have hφ : 0 ≤ phi N ^ (4 * ζ / 3) := by
    unfold phi
    exact Real.rpow_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg N) _) _
  have h1 : ((N : ℝ) * z.im) ^ ((1 : ℝ) / 3) ≤ ((N : ℝ) * z'.im) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow hn.le (mul_le_mul_of_nonneg_left hzz hNr.le) (by norm_num)
  have h2 := div_le_div_of_nonneg_left hφ (Real.rpow_pos_of_pos hn _) h1
  linarith

/-- `β ≥ 4/N` on `S(K)` for `N ≥ 40`. -/
private lemma weak_beta_ge {N : ℕ} {ζ q K : ℝ} {z : ℂ} (hN : 40 ≤ N) (hζ : 0 < ζ) (hq : 0 < q)
    (hz : z ∈ specDomain N K) : 4 / N ≤ weakBeta N ζ q z := by
  obtain ⟨-, hz0, hz10, -⟩ := sc_specDomain (by omega : 3 ≤ N) hz
  have hNr : (40 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : 0 < (N : ℝ) * z.im := by positivity
  have hφ : 1 ≤ phi N ^ (4 * ζ / 3) :=
    Real.one_le_rpow (sc_one_le_phi (by omega)) (by positivity)
  have hc : ((N : ℝ) * z.im) ^ ((1 : ℝ) / 3) ≤ N / 4 := by
    have h1 : (N : ℝ) * z.im ≤ (N / 4) ^ 3 := by
      have e1 : (N : ℝ) * z.im ≤ N * 10 := mul_le_mul_of_nonneg_left hz10 (by positivity)
      have hN2 : (640 : ℝ) ≤ N * N := by nlinarith
      have e2 := mul_le_mul_of_nonneg_left hN2 (by positivity : (0 : ℝ) ≤ N)
      nlinarith
    calc ((N : ℝ) * z.im) ^ ((1 : ℝ) / 3) ≤ ((N / 4) ^ 3) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow hn.le h1 (by norm_num)
      _ = N / 4 := by
          rw [show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
          exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
  have hcp : 0 < ((N : ℝ) * z.im) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hn _
  have h2 : 4 / (N : ℝ) ≤ phi N ^ (4 * ζ / 3) / ((N : ℝ) * z.im) ^ ((1 : ℝ) / 3) := by
    rw [div_le_div_iff₀ (by positivity) hcp]
    nlinarith
  have h3 : 0 ≤ phi N ^ ζ / Real.sqrt q := by
    have := sc_phi_pos (by omega : 3 ≤ N)
    positivity
  unfold weakBeta
  linarith

/-! ### One point of the continuity argument -/

/-- The bounds of Lemma 2.6 with constant `Cm`. -/
private def WeakMscBd (Cm : ℝ) : Prop :=
  ∀ z : ℂ, |z.re| ≤ 5 → 0 < z.im → z.im ≤ 10 →
    (Cm⁻¹ ≤ ‖msc z‖ ∧ ‖msc z‖ ≤ Cm) ∧
    (Cm⁻¹ * Real.sqrt (kappa z.re + z.im) ≤ ‖1 - msc z ^ 2‖ ∧
      ‖1 - msc z ^ 2‖ ≤ Cm * Real.sqrt (kappa z.re + z.im)) ∧
    (z.im ≤ kappa z.re → 2 ≤ |z.re| →
      Cm⁻¹ * (z.im / Real.sqrt (kappa z.re + z.im)) ≤ (msc z).im ∧
      (msc z).im ≤ Cm * (z.im / Real.sqrt (kappa z.re + z.im))) ∧
    (kappa z.re ≤ z.im ∨ |z.re| ≤ 2 →
      Cm⁻¹ * Real.sqrt (kappa z.re + z.im) ≤ (msc z).im ∧
      (msc z).im ≤ Cm * Real.sqrt (kappa z.re + z.im))

/-- The conclusion of the dichotomy (Lemma 3.17 of [15]) for fixed `Cs`, `K`, `U`, `C1`. -/
private def WeakDich (Cs Km U C1 : ℝ) : Prop :=
  ∀ (w v : ℂ) (t β δ : ℝ), 0 < t → 0 < β → 0 ≤ δ →
    δ ≤ 1 / 2 → Km⁻¹ * t ≤ ‖w‖ → ‖w‖ ≤ Km * t →
    ‖w * v - v ^ 2‖ ≤ δ * ‖v‖ ^ 2 + Cs * (β * ‖v‖ + ‖w‖ * β + β ^ 2) →
    (2 * U ^ 2 * Km * β ≤ t → ‖v‖ ≤ U * β ∨ ‖w‖ / U ≤ ‖v‖) ∧
    (t < 2 * U ^ 2 * Km * β → ‖v‖ ≤ C1 * β)

/-- The estimates that hold at one point `z` outside the exceptional events: (3.42), (3.32) and
(3.36) of [15] on `Ω(z)`, and the initial estimate (Lemma 3.16 of [15]) for `η ≥ 2`. -/
private def WeakGood (N : ℕ) (ζ q Cc Co Cd Ci : ℝ) (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    Prop :=
  (lamD H z + lamO H z ≤ (phi N ^ ζ)⁻¹ →
    ‖(1 - msc z ^ 2) * (stieltjesM H z - msc z) - msc z ^ 3 * (stieltjesM H z - msc z) ^ 2‖ ≤
      Cc * (lamAvg H z ^ 2 / Real.log N + phi N ^ ζ / q + (phi N ^ ζ) ^ 2 * psiCtrl H z) ∧
    lamO H z ≤ Co * (1 / q + phi N ^ (2 * ζ) * psiCtrl H z) ∧
    (⨆ i, ‖resolventC H z i i - stieltjesM H z‖) ≤
      Cd * (phi N ^ ζ / q + (phi N ^ ζ) ^ 2 * psiCtrl H z)) ∧
  (2 ≤ z.im → lamD H z + lamO H z ≤ Ci * (phi N ^ ζ / q + phi N ^ (2 * ζ) / Real.sqrt N))

/-- The induction hypothesis of Lemma 3.18 of [15] at `z`: `Λ_d + Λ_o ≤ φ^{-ζ}/2`, `Λ ≤ C β`, and
`Λ ≤ U β` when `η ≥ η̃`. -/
private def WeakInv (N : ℕ) (ζ q Cm U C1 : ℝ) (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : Prop :=
  lamD H z + lamO H z ≤ (phi N ^ ζ)⁻¹ / 2 ∧ lamAvg H z ≤ (U + C1) * weakBeta N ζ q z ∧
  (2 * U ^ 2 * Cm ^ 4 * weakBeta N ζ q z ≤ Real.sqrt (kappa z.re + z.im) →
    lamAvg H z ≤ U * weakBeta N ζ q z)

private lemma weak_beta_pos {N : ℕ} {ζ q K : ℝ} {z : ℂ} (hN : 3 ≤ N) (hq : 0 < q)
    (hz : z ∈ specDomain N K) : 0 < weakBeta N ζ q z := by
  obtain ⟨-, hz0, -, -⟩ := sc_specDomain hN hz
  have hφ := sc_phi_pos hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h1 : 0 < phi N ^ ζ / Real.sqrt q := by
    have := Real.sqrt_pos.mpr hq
    positivity
  have h2 : 0 ≤ phi N ^ (4 * ζ / 3) / ((N : ℝ) * z.im) ^ ((1 : ℝ) / 3) := by positivity
  unfold weakBeta
  linarith

/-- The dichotomy at one point on `Ω(z)` (Lemma 3.17 of [15] applied to (3.42)). -/
private lemma weak_point_dich {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ}
    {ζ q K Cc Cm U C1 : ℝ} (hN : 3 ≤ N) (hζ : 0 < ζ) (hK : 8 * ζ + 3 ≤ K)
    (hqK : phi N ^ K ≤ q) (hz : z ∈ specDomain N K) (hCc : 0 < Cc) (hCm : 1 ≤ Cm)
    (hmsc : WeakMscBd Cm) (hU : 0 ≤ U) (hC1 : 0 ≤ C1)
    (hlog : 2 * (Cm ^ 3 * Cc) ≤ Real.log N)
    (hdich : WeakDich (Cc * Cm ^ 3 * (2 + Cm ^ 5)) (Cm ^ 4) U C1)
    (hSC : ‖(1 - msc z ^ 2) * (stieltjesM H z - msc z) -
        msc z ^ 3 * (stieltjesM H z - msc z) ^ 2‖ ≤
      Cc * (lamAvg H z ^ 2 / Real.log N + phi N ^ ζ / q + (phi N ^ ζ) ^ 2 * psiCtrl H z))
    (hexcl : 2 * U ^ 2 * Cm ^ 4 * weakBeta N ζ q z ≤ Real.sqrt (kappa z.re + z.im) →
      lamAvg H z < ‖(1 - msc z ^ 2) / msc z ^ 3‖ / U) :
    lamAvg H z ≤ (U + C1) * weakBeta N ζ q z ∧
    (2 * U ^ 2 * Cm ^ 4 * weakBeta N ζ q z ≤ Real.sqrt (kappa z.re + z.im) →
      lamAvg H z ≤ U * weakBeta N ζ q z) := by
  obtain ⟨hre, hz0, hz10, hnK⟩ := sc_specDomain hN hz
  have hφ1 := sc_one_le_phi hN
  have hq : 0 < q := lt_of_lt_of_le (Real.rpow_pos_of_pos (sc_phi_pos hN) K) hqK
  obtain ⟨-, -, -, hfd, hfe⟩ := weak_rpow_facts hφ1 hζ hK hqK hnK.le
  obtain ⟨⟨hm1, hm2⟩, ⟨ht1, ht2⟩, h3, h4⟩ := hmsc z hre hz0 hz10
  have hI := weak_im_msc_le hz0 (by linarith) h3 h4
  have hI0 := (im_msc_pos hz0).le
  have hn : 0 < (N : ℝ) * z.im := lt_of_le_of_lt (Real.rpow_nonneg (sc_phi_pos hN).le K) hnK
  have hP : 0 < Cm ^ 3 * Cc := by positivity
  have hlg : 0 < Real.log N := by linarith
  have hβ0 := weak_beta_pos (ζ := ζ) hN hq hz
  unfold lamAvg psiCtrl at hSC
  obtain ⟨hin, hwlo, hwhi⟩ := weak_dich_input (β := weakBeta N ζ q z)
    (v := stieltjesM H z - msc z) hCm hm1 hm2 ht1 ht2 hI0 hI hn hlg hCc hβ0.le hfe hfd hSC
  have hκ : 0 ≤ kappa z.re := abs_nonneg _
  have ht : 0 < Real.sqrt (kappa z.re + z.im) := Real.sqrt_pos.mpr (by linarith)
  have hδ0 : 0 ≤ Cm ^ 3 * Cc / Real.log N := by positivity
  have hδ1 : Cm ^ 3 * Cc / Real.log N ≤ 1 / 2 := by
    rw [div_le_iff₀ hlg]
    linarith
  obtain ⟨d1, d2⟩ := hdich _ _ _ _ _ ht hβ0 hδ0 hδ1 hwlo hwhi hin
  have hcase1 : 2 * U ^ 2 * Cm ^ 4 * weakBeta N ζ q z ≤ Real.sqrt (kappa z.re + z.im) →
      lamAvg H z ≤ U * weakBeta N ζ q z := by
    intro hc
    rcases d1 hc with h | h
    · exact h
    · exact absurd h (not_le.mpr (hexcl hc))
  refine ⟨?_, hcase1⟩
  by_cases hc : 2 * U ^ 2 * Cm ^ 4 * weakBeta N ζ q z ≤ Real.sqrt (kappa z.re + z.im)
  · have := hcase1 hc
    nlinarith
  · have := d2 (not_le.mp hc)
    unfold lamAvg
    nlinarith

/-- On `Ω(z)` with `Λ ≤ C' β`, the bounds (3.32), (3.36) give `Λ_d + Λ_o ≤ φ^{-ζ}/2`
(the first step in the proof of Lemma 3.18 of [15]). -/
private lemma weak_point_half {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ}
    {ζ q K Co Cd C' : ℝ} (hN : 3 ≤ N) (hζ : 0 < ζ) (hK : 8 * ζ + 3 ≤ K)
    (hqK : phi N ^ K ≤ q) (hz : z ∈ specDomain N K) (hCo : 0 ≤ Co) (hCd : 0 ≤ Cd)
    (hC' : 0 ≤ C') (hA : 2 * (3 * (Co + Cd) + 2 * C') ≤ phi N)
    (hΩ : lamD H z + lamO H z ≤ (phi N ^ ζ)⁻¹)
    (hO : lamO H z ≤ Co * (1 / q + phi N ^ (2 * ζ) * psiCtrl H z))
    (hD : (⨆ i, ‖resolventC H z i i - stieltjesM H z‖) ≤
      Cd * (phi N ^ ζ / q + (phi N ^ ζ) ^ 2 * psiCtrl H z))
    (hΛ : lamAvg H z ≤ C' * weakBeta N ζ q z) :
    lamD H z + lamO H z ≤ (phi N ^ ζ)⁻¹ / 2 := by
  obtain ⟨-, hz0, -, hnK⟩ := sc_specDomain hN hz
  have hφ1 := sc_one_le_phi hN
  have hφ0 : 0 < phi N := by linarith
  have hq : 0 < q := lt_of_lt_of_le (Real.rpow_pos_of_pos hφ0 K) hqK
  have hn : 0 < (N : ℝ) * z.im := lt_of_le_of_lt (Real.rpow_nonneg hφ0.le K) hnK
  obtain ⟨fa, fb, fc, -, -⟩ := weak_rpow_facts hφ1 hζ hK hqK hnK.le
  set s := phi N ^ ζ with hs
  have hs1 : 1 ≤ s := Real.one_le_rpow hφ1 hζ.le
  have hs0 : 0 < s := by linarith
  have hNpos : 0 < N := by omega
  have hO0 := sc_lamO_nonneg H z
  have hΛd : lamAvg H z ≤ lamD H z := sc_lamAvg_le_lamD hNpos H z
  have hsi : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs1
  have hΛ1 : lamAvg H z ≤ 1 := by linarith
  have hψ := weak_psiCtrl_le hz0 hn hΛ1
  have hψ0 : 0 ≤ psiCtrl H z := Real.sqrt_nonneg _
  have e2 : phi N ^ (2 * ζ) = s ^ 2 := (sc_rpow_sq hφ0 ζ).symm
  rw [e2] at hO
  set P := s / q + s ^ 2 * psiCtrl H z with hP
  have hqs : 1 / q ≤ s / q := div_le_div_of_nonneg_right hs1 hq.le
  have hO' : lamO H z ≤ Co * P := by
    refine hO.trans (mul_le_mul_of_nonneg_left ?_ hCo)
    linarith
  have hLd := weak_lamD_le H z
  have hX : lamD H z + lamO H z ≤ (Co + Cd) * P + C' * weakBeta N ζ q z := by
    nlinarith
  have hsn : 0 < Real.sqrt ((N : ℝ) * z.im) := Real.sqrt_pos.mpr hn
  have hsP : s * P ≤ 3 / phi N := by
    have h1 : s * (s ^ 2 * psiCtrl H z) ≤ Real.sqrt 2 * (s * (s ^ 2 / Real.sqrt (N * z.im))) := by
      have : s ^ 2 * psiCtrl H z ≤ s ^ 2 * (Real.sqrt 2 / Real.sqrt (N * z.im)) :=
        mul_le_mul_of_nonneg_left hψ (by positivity)
      calc s * (s ^ 2 * psiCtrl H z) ≤ s * (s ^ 2 * (Real.sqrt 2 / Real.sqrt (N * z.im))) :=
            mul_le_mul_of_nonneg_left this hs0.le
        _ = _ := by ring
    have h2 : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have h3 : 0 ≤ s * (s ^ 2 / Real.sqrt (N * z.im)) := by positivity
    have h4 : Real.sqrt 2 * (s * (s ^ 2 / Real.sqrt (N * z.im))) ≤ 2 * (1 / phi N) := by
      have := mul_le_mul h2 fb h3 (by norm_num)
      linarith
    have : s * P = s * (s / q) + s * (s ^ 2 * psiCtrl H z) := by rw [hP]; ring
    rw [this]
    have e3 : 3 / phi N = 1 / phi N + 2 * (1 / phi N) := by ring
    linarith
  have hsβ := fc
  have hsX : s * (lamD H z + lamO H z) ≤ 1 / 2 := by
    have h1 : s * (lamD H z + lamO H z) ≤ (Co + Cd) * (s * P) + C' * (s * weakBeta N ζ q z) := by
      have := mul_le_mul_of_nonneg_left hX hs0.le
      linarith
    have h2 : (Co + Cd) * (s * P) ≤ (Co + Cd) * (3 / phi N) :=
      mul_le_mul_of_nonneg_left hsP (by linarith)
    have h3 : C' * (s * weakBeta N ζ q z) ≤ C' * (2 / phi N) :=
      mul_le_mul_of_nonneg_left hsβ hC'
    have h4 : (Co + Cd) * (3 / phi N) + C' * (2 / phi N) ≤ 1 / 2 := by
      rw [show (Co + Cd) * (3 / phi N) + C' * (2 / phi N) = (3 * (Co + Cd) + 2 * C') / phi N by
        ring, div_le_iff₀ hφ0]
      linarith
    linarith
  calc lamD H z + lamO H z = s⁻¹ * (s * (lamD H z + lamO H z)) := by field_simp
    _ ≤ s⁻¹ * (1 / 2) := mul_le_mul_of_nonneg_left hsX (by positivity)
    _ = s⁻¹ / 2 := by ring

/-- `1/N ≤ η` on `S(K)` for `K ≥ 0`. -/
private lemma weak_im_ge {N : ℕ} {K : ℝ} {z : ℂ} (hN : 3 ≤ N) (hK : 0 ≤ K)
    (hz : z ∈ specDomain N K) : 1 / (N : ℝ) ≤ z.im := by
  obtain ⟨-, -, -, hnK⟩ := sc_specDomain hN hz
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h1 : 1 ≤ phi N ^ K := Real.one_le_rpow (sc_one_le_phi hN) hK
  rw [div_le_iff₀ hNr]
  linarith

/-- The start of the continuity argument at `η ≥ 2` (Lemma 3.16 of [15]): `Ω(z)` holds, and `Λ` is
far below `|w|/U`. -/
private lemma weak_point_start {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ}
    {ζ q K Ci Cm U : ℝ} (hN : 3 ≤ N) (hζ : 0 < ζ) (hK : 8 * ζ + 3 ≤ K)
    (hqK : phi N ^ K ≤ q) (hz : z ∈ specDomain N K) (h2 : 2 ≤ z.im) (hCm : 1 ≤ Cm)
    (hmsc : WeakMscBd Cm) (hU : 0 < U) (hCi0 : 0 ≤ Ci) (hCi : 2 * Ci ≤ phi N)
    (hKmU : Cm ^ 4 * U < phi N ^ ζ) (hNsq : phi N ^ (3 * ζ + 1) ≤ Real.sqrt N)
    (hI : lamD H z + lamO H z ≤ Ci * (phi N ^ ζ / q + phi N ^ (2 * ζ) / Real.sqrt N)) :
    lamD H z + lamO H z ≤ (phi N ^ ζ)⁻¹ ∧
      lamAvg H z < ‖(1 - msc z ^ 2) / msc z ^ 3‖ / U := by
  obtain ⟨hre, hz0, hz10, hnK⟩ := sc_specDomain hN hz
  have hφ1 := sc_one_le_phi hN
  have hφ0 : 0 < phi N := by linarith
  have hq : 0 < q := lt_of_lt_of_le (Real.rpow_pos_of_pos hφ0 K) hqK
  obtain ⟨fa, -, -, -, -⟩ := weak_rpow_facts hφ1 hζ hK hqK hnK.le
  have e2 : phi N ^ (2 * ζ) = (phi N ^ ζ) ^ 2 := (sc_rpow_sq hφ0 ζ).symm
  have e3 : phi N ^ ζ * (phi N ^ ζ) ^ 2 * phi N = phi N ^ (3 * ζ + 1) := by
    rw [sc_rpow_sq hφ0 ζ, ← Real.rpow_add hφ0, Real.rpow_add_one hφ0.ne']
    ring_nf
  rw [e2] at hI
  set s := phi N ^ ζ with hs
  have hs1 : 1 ≤ s := Real.one_le_rpow hφ1 hζ.le
  have hs0 : 0 < s := by linarith
  have hNpos : 0 < N := by omega
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hNpos)
  have fb : s * (s ^ 2 / Real.sqrt N) ≤ 1 / phi N := by
    rw [← mul_div_assoc, div_le_div_iff₀ hsqN hφ0, e3]
    linarith
  have hsX : s * (lamD H z + lamO H z) ≤ 1 := by
    have h1 : s * (lamD H z + lamO H z) ≤ Ci * (s * (s / q) + s * (s ^ 2 / Real.sqrt N)) := by
      have := mul_le_mul_of_nonneg_left hI hs0.le
      linarith
    have h2 : Ci * (s * (s / q) + s * (s ^ 2 / Real.sqrt N)) ≤ Ci * (2 / phi N) := by
      apply mul_le_mul_of_nonneg_left _ hCi0
      have : 2 / phi N = 1 / phi N + 1 / phi N := by ring
      linarith
    have h3 : Ci * (2 / phi N) ≤ 1 := by
      rw [← mul_div_assoc, div_le_one hφ0]
      linarith
    linarith
  have hΩ : lamD H z + lamO H z ≤ s⁻¹ := by
    calc lamD H z + lamO H z = s⁻¹ * (s * (lamD H z + lamO H z)) := by field_simp
      _ ≤ s⁻¹ * 1 := mul_le_mul_of_nonneg_left hsX (by positivity)
      _ = s⁻¹ := mul_one _
  refine ⟨hΩ, ?_⟩
  have hΛ : lamAvg H z ≤ s⁻¹ := by
    have := sc_lamAvg_le_lamD hNpos H z
    have := sc_lamO_nonneg H z
    linarith
  obtain ⟨⟨hm1, hm2⟩, ⟨ht1, ht2⟩, -, -⟩ := hmsc z hre hz0 hz10
  obtain ⟨hwlo, -⟩ := weak_w_bounds hCm hm1 hm2 ht1 ht2
  have hκ : 0 ≤ kappa z.re := abs_nonneg _
  have ht : 1 ≤ Real.sqrt (kappa z.re + z.im) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hKm : 0 < Cm ^ 4 * U := by positivity
  have h1 : s⁻¹ < (Cm ^ 4 * U)⁻¹ := inv_strictAnti₀ hKm hKmU
  have h2 : (Cm ^ 4 * U)⁻¹ ≤ ‖(1 - msc z ^ 2) / msc z ^ 3‖ / U := by
    rw [le_div_iff₀ hU, mul_inv, mul_assoc, inv_mul_cancel₀ hU.ne', mul_one]
    calc (Cm ^ 4)⁻¹ = (Cm ^ 4)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (Cm ^ 4)⁻¹ * Real.sqrt (kappa z.re + z.im) :=
          mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ _ := hwlo
  linarith

/-- One step of the continuity argument (Lemma 3.18 of [15]): from `z' = z + i N⁻⁸` to `z`. -/
private lemma weak_point_step {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z z' : ℂ} {ζ q K Cm U C1 : ℝ} (hN : 40 ≤ N) (hζ : 0 < ζ) (hK : 0 ≤ K) (hq : 0 < q)
    (hz : z ∈ specDomain N K) (hz' : z' ∈ specDomain N K) (hre : z'.re = z.re)
    (him : z'.im = z.im + 1 / (N : ℝ) ^ 8) (hCm : 1 ≤ Cm) (hmsc : WeakMscBd Cm) (hU : 9 ≤ U)
    (hN6 : 6 * phi N ^ ζ ≤ (N : ℝ) ^ 6) (hinv : WeakInv N ζ q Cm U C1 H z') :
    lamD H z + lamO H z ≤ (phi N ^ ζ)⁻¹ ∧
      (2 * U ^ 2 * Cm ^ 4 * weakBeta N ζ q z ≤ Real.sqrt (kappa z.re + z.im) →
        lamAvg H z < ‖(1 - msc z ^ 2) / msc z ^ 3‖ / U) := by
  have hN3 : 3 ≤ N := by omega
  obtain ⟨hre0, hz0, hz10, -⟩ := sc_specDomain hN3 hz
  obtain ⟨-, hz0', -, -⟩ := sc_specDomain hN3 hz'
  obtain ⟨hinv1, hinv2, hinv3⟩ := hinv
  have hNr : (40 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hη := weak_im_ge hN3 hK hz
  have hη' := weak_im_ge hN3 hK hz'
  have hd : ‖z - z'‖ ≤ 1 / (N : ℝ) ^ 8 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im, hre, him]
    have : 0 ≤ 1 / (N : ℝ) ^ 8 := by positivity
    simp
  have hL : ‖z - z'‖ / (z.im * z'.im) ≤ 1 / (N : ℝ) ^ 6 := by
    rw [div_le_iff₀ (by positivity)]
    calc ‖z - z'‖ ≤ 1 / (N : ℝ) ^ 8 := hd
      _ = 1 / (N : ℝ) ^ 6 * (1 / N * (1 / N)) := by field_simp
      _ ≤ 1 / (N : ℝ) ^ 6 * (z.im * z'.im) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hη hη' (by positivity) (by linarith)
  set s := phi N ^ ζ with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos (sc_phi_pos hN3) ζ
  have hLs : 3 * (1 / (N : ℝ) ^ 6) ≤ s⁻¹ / 2 := by
    have h6 : 6 * s * (1 / (N : ℝ) ^ 6) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]
      exact hN6
    calc 3 * (1 / (N : ℝ) ^ 6) = s⁻¹ / 2 * (6 * s * (1 / (N : ℝ) ^ 6)) := by
          field_simp
          norm_num
      _ ≤ s⁻¹ / 2 * 1 := mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = s⁻¹ / 2 := mul_one _
  have hO := weak_lamO_le_add hH hz0 hz0' (H := H)
  have hD := weak_lamD_le_add hH hz0 hz0' (H := H)
  refine ⟨by linarith, fun hc => ?_⟩
  have hNpos : 0 < N := by omega
  have hA := weak_lamAvg_le_add hNpos hH hz0 hz0'
  have hβ := weak_beta_anti (ζ := ζ) (q := q) hNpos hz0 (by
    rw [him]
    have : 0 ≤ 1 / (N : ℝ) ^ 8 := by positivity
    linarith)
  have hβ0 := weak_beta_pos (ζ := ζ) hN3 hq hz
  have hβ4 := weak_beta_ge (ζ := ζ) hN hζ hq hz
  have ht : Real.sqrt (kappa z.re + z.im) ≤ Real.sqrt (kappa z'.re + z'.im) := by
    apply Real.sqrt_le_sqrt
    rw [hre, him]
    have : 0 ≤ 1 / (N : ℝ) ^ 8 := by positivity
    linarith
  have hc' : 2 * U ^ 2 * Cm ^ 4 * weakBeta N ζ q z' ≤ Real.sqrt (kappa z'.re + z'.im) := by
    have : 2 * U ^ 2 * Cm ^ 4 * weakBeta N ζ q z' ≤ 2 * U ^ 2 * Cm ^ 4 * weakBeta N ζ q z :=
      mul_le_mul_of_nonneg_left hβ (by positivity)
    linarith
  have hΛ' := hinv3 hc'
  have hU0 : 0 < U := by linarith
  have hΛ : lamAvg H z ≤ U * weakBeta N ζ q z + 2 * (1 / (N : ℝ) ^ 6) := by
    have := mul_le_mul_of_nonneg_left hβ hU0.le
    linarith
  have hsmall : 2 * (1 / (N : ℝ) ^ 6) < U * weakBeta N ζ q z := by
    have h1 : 1 / (N : ℝ) ^ 6 ≤ 1 / N := by
      apply one_div_le_one_div_of_le hN0
      calc (N : ℝ) = N ^ 1 := (pow_one _).symm
        _ ≤ N ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h2 : 9 * (4 / (N : ℝ)) ≤ U * weakBeta N ζ q z :=
      mul_le_mul hU hβ4 (by positivity) hU0.le
    have h3 : 0 < 1 / (N : ℝ) := by positivity
    have h4 : 9 * (4 / (N : ℝ)) = 36 * (1 / N) := by ring
    linarith
  obtain ⟨⟨hm1, hm2⟩, ⟨ht1, ht2⟩, -, -⟩ := hmsc z hre0 hz0 hz10
  obtain ⟨hwlo, -⟩ := weak_w_bounds hCm hm1 hm2 ht1 ht2
  have hCm4 : 0 < Cm ^ 4 := by positivity
  have hw : 2 * U ^ 2 * weakBeta N ζ q z ≤ ‖(1 - msc z ^ 2) / msc z ^ 3‖ := by
    refine le_trans ?_ hwlo
    have := mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hCm4.le)
    calc 2 * U ^ 2 * weakBeta N ζ q z = (Cm ^ 4)⁻¹ * (2 * U ^ 2 * Cm ^ 4 * weakBeta N ζ q z) := by
          field_simp
      _ ≤ _ := this
  rw [lt_div_iff₀ hU0]
  nlinarith

/-- From a point `w` of the grid to a nearby `z ∈ S(K)` (Corollary 3.19 of [15]). -/
private lemma weak_point_final {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z w : ℂ} {ζ q K Co Cm U C1 : ℝ} (hN : 40 ≤ N) (hζ : 0 < ζ) (hK : 0 ≤ K) (hq : 0 < q)
    (hz : z ∈ specDomain N K) (hw : w ∈ specDomain N K) (hzw : z.im ≤ w.im)
    (hd : ‖z - w‖ ≤ 2 / (N : ℝ) ^ 3) (hCo : 0 ≤ Co) (hU : 0 ≤ U) (hC1 : 0 ≤ C1)
    (hinv : WeakInv N ζ q Cm U C1 H w)
    (hO : lamO H w ≤ Co * (1 / q + phi N ^ (2 * ζ) * psiCtrl H w)) :
    lamO H z ≤ (2 * Co + U + C1 + 1) * (1 / q + phi N ^ (2 * ζ) / Real.sqrt (N * z.im)) ∧
      lamAvg H z ≤ (2 * Co + U + C1 + 1) * weakBeta N ζ q z := by
  have hN3 : 3 ≤ N := by omega
  obtain ⟨-, hz0, hz10, -⟩ := sc_specDomain hN3 hz
  obtain ⟨-, hw0, -, -⟩ := sc_specDomain hN3 hw
  obtain ⟨hinv1, hinv2, -⟩ := hinv
  have hNr : (40 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNpos : 0 < N := by omega
  have hη := weak_im_ge hN3 hK hz
  have hηw := weak_im_ge hN3 hK hw
  have hL : ‖z - w‖ / (z.im * w.im) ≤ 2 / N := by
    rw [div_le_iff₀ (by positivity)]
    calc ‖z - w‖ ≤ 2 / (N : ℝ) ^ 3 := hd
      _ = 2 / N * (1 / N * (1 / N)) := by field_simp
      _ ≤ 2 / N * (z.im * w.im) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hη hηw (by positivity) (by linarith)
  have hφ1 := sc_one_le_phi hN3
  have hs1 : 1 ≤ phi N ^ ζ := Real.one_le_rpow hφ1 hζ.le
  have hs0 : 0 < phi N ^ ζ := by linarith
  have hφ2 : 1 ≤ phi N ^ (2 * ζ) := Real.one_le_rpow hφ1 (by linarith)
  have hn : 0 < (N : ℝ) * z.im := by positivity
  have hnw : 0 < (N : ℝ) * w.im := by positivity
  have hsn : 0 < Real.sqrt ((N : ℝ) * z.im) := Real.sqrt_pos.mpr hn
  have hsnw : Real.sqrt ((N : ℝ) * z.im) ≤ Real.sqrt ((N : ℝ) * w.im) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hzw hN0.le)
  -- `Λ(w) ≤ 1`, so `Ψ(w) ≤ √2/√(Nη_w) ≤ √2/√(Nη_z)`
  have hΛw : lamAvg H w ≤ 1 := by
    have h1 := sc_lamAvg_le_lamD hNpos H w
    have h2 := sc_lamO_nonneg H w
    have h3 : (phi N ^ ζ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs1
    linarith
  have hψ : psiCtrl H w ≤ Real.sqrt 2 / Real.sqrt (N * z.im) :=
    (weak_psiCtrl_le hw0 hnw hΛw).trans (div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hsn hsnw)
  have h2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  set T := 1 / q + phi N ^ (2 * ζ) / Real.sqrt (N * z.im) with hT
  have hT1 : 0 ≤ 1 / q := by positivity
  have hT2 : 0 ≤ phi N ^ (2 * ζ) / Real.sqrt (N * z.im) := by positivity
  have hOw : lamO H w ≤ 2 * Co * T := by
    refine hO.trans ?_
    rw [mul_comm 2 Co, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hCo
    have : phi N ^ (2 * ζ) * psiCtrl H w ≤ 2 * (phi N ^ (2 * ζ) / Real.sqrt (N * z.im)) := by
      calc phi N ^ (2 * ζ) * psiCtrl H w
          ≤ phi N ^ (2 * ζ) * (Real.sqrt 2 / Real.sqrt (N * z.im)) :=
            mul_le_mul_of_nonneg_left hψ (by linarith)
        _ = Real.sqrt 2 * (phi N ^ (2 * ζ) / Real.sqrt (N * z.im)) := by ring
        _ ≤ 2 * (phi N ^ (2 * ζ) / Real.sqrt (N * z.im)) := mul_le_mul_of_nonneg_right h2 hT2
    linarith
  -- `2/N ≤ φ^{2ζ}/√(Nη) ≤ T`
  have hsq : Real.sqrt ((N : ℝ) * z.im) ≤ N / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have h2N : 2 / (N : ℝ) ≤ T := by
    have : 2 / (N : ℝ) ≤ 1 / Real.sqrt (N * z.im) := by
      rw [div_le_div_iff₀ hN0 hsn]
      linarith
    have h' : 1 / Real.sqrt (N * z.im) ≤ phi N ^ (2 * ζ) / Real.sqrt (N * z.im) :=
      div_le_div_of_nonneg_right hφ2 hsn.le
    linarith
  have hlo := weak_lamO_le_add hH hz0 hw0 (H := H)
  have hla := weak_lamAvg_le_add hNpos hH hz0 hw0 (H := H)
  have hβ := weak_beta_anti (ζ := ζ) (q := q) hNpos hz0 hzw
  have hβ4 := weak_beta_ge (ζ := ζ) hN hζ hq hz
  have hT0 : 0 ≤ T := by positivity
  constructor
  · have : (2 * Co + 1) * T ≤ (2 * Co + U + C1 + 1) * T :=
      mul_le_mul_of_nonneg_right (by linarith) hT0
    nlinarith
  · have : (U + C1) * weakBeta N ζ q w ≤ (U + C1) * weakBeta N ζ q z :=
      mul_le_mul_of_nonneg_left hβ (by linarith)
    have hβ0 : 0 ≤ weakBeta N ζ q z := by linarith [show (0 : ℝ) < 4 / N by positivity]
    have e : (2 * Co + U + C1 + 1) * weakBeta N ζ q z =
        2 * Co * weakBeta N ζ q z + (U + C1) * weakBeta N ζ q z + weakBeta N ζ q z := by ring
    have h0 : 0 ≤ 2 * Co * weakBeta N ζ q z := by positivity
    have e4 : 2 * (2 / (N : ℝ)) = 4 / N := by ring
    linarith

/-- On `Ω(z)` with `Λ` far below `|w|/U` when `η ≥ η̃`, the estimates at `z` give the induction
hypothesis at `z`. -/
private lemma weak_point_inv {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ}
    {ζ q K Cc Co Cd Ci Cm U C1 : ℝ} (hN : 3 ≤ N) (hζ : 0 < ζ) (hK : 8 * ζ + 3 ≤ K)
    (hqK : phi N ^ K ≤ q) (hz : z ∈ specDomain N K) (hCc : 0 < Cc) (hCo : 0 ≤ Co)
    (hCd : 0 ≤ Cd) (hCm : 1 ≤ Cm) (hmsc : WeakMscBd Cm) (hU : 0 ≤ U) (hC1 : 0 ≤ C1)
    (hdich : WeakDich (Cc * Cm ^ 3 * (2 + Cm ^ 5)) (Cm ^ 4) U C1)
    (hA : 2 * (3 * (Co + Cd) + 2 * (U + C1)) ≤ phi N)
    (hlog : 2 * (Cm ^ 3 * Cc) ≤ Real.log N) (hgood : WeakGood N ζ q Cc Co Cd Ci H z)
    (hΩ : lamD H z + lamO H z ≤ (phi N ^ ζ)⁻¹)
    (hexcl : 2 * U ^ 2 * Cm ^ 4 * weakBeta N ζ q z ≤ Real.sqrt (kappa z.re + z.im) →
      lamAvg H z < ‖(1 - msc z ^ 2) / msc z ^ 3‖ / U) :
    WeakInv N ζ q Cm U C1 H z := by
  obtain ⟨hSC, hO, hD⟩ := hgood.1 hΩ
  obtain ⟨d1, d2⟩ := weak_point_dich hN hζ hK hqK hz hCc hCm hmsc hU hC1 hlog hdich hSC hexcl
  exact ⟨weak_point_half hN hζ hK hqK hz hCo hCd (by linarith) hA hΩ hO hD d1, d1, d2⟩

/-! ### The grid and the deterministic continuity argument -/

/-- The grid point `a N⁻³ + i (10 - b N⁻⁸)`. -/
private def weakPt (N : ℕ) (a : ℤ) (b : ℕ) : ℂ :=
  ⟨(a : ℝ) / (N : ℝ) ^ 3, 10 - (b : ℝ) / (N : ℝ) ^ 8⟩

/-- The continuity argument of Lemma 3.18 and Corollary 3.19 of [15] for one matrix `H`: if the
estimates of `WeakGood` hold at every grid point of `S(K)`, then `Λ_o` and `Λ` obey the bounds of
(3.3) and (3.58) at every `z ∈ S(K)`. -/
private lemma weak_det {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {ζ q K Cc Co Cd Ci Cm U C1 : ℝ} (hN : 40 ≤ N) (hζ : 0 < ζ) (hK : 8 * ζ + 3 ≤ K)
    (hqK : phi N ^ K ≤ q) (hCc : 0 < Cc) (hCo : 0 ≤ Co) (hCd : 0 ≤ Cd) (hCi : 0 ≤ Ci)
    (hCm : 1 ≤ Cm) (hmsc : WeakMscBd Cm) (hU : 9 ≤ U) (hC1 : 0 ≤ C1)
    (hdich : WeakDich (Cc * Cm ^ 3 * (2 + Cm ^ 5)) (Cm ^ 4) U C1)
    (hA : 2 * (3 * (Co + Cd) + 2 * (U + C1)) ≤ phi N) (hAi : 2 * Ci ≤ phi N)
    (hlog : 2 * (Cm ^ 3 * Cc) ≤ Real.log N) (hKmU : Cm ^ 4 * U < phi N ^ ζ)
    (hN6 : 6 * phi N ^ ζ ≤ (N : ℝ) ^ 6) (hNsq : phi N ^ (3 * ζ + 1) ≤ Real.sqrt N)
    (hgood : ∀ a : ℤ, ∀ b : ℕ, -(5 * (N : ℤ) ^ 3) ≤ a → a ≤ 5 * (N : ℤ) ^ 3 → b < 10 * N ^ 8 →
      weakPt N a b ∈ specDomain N K → WeakGood N ζ q Cc Co Cd Ci H (weakPt N a b)) :
    ∀ z ∈ specDomain N K,
      lamO H z ≤ (2 * Co + U + C1 + 1) * (1 / q + phi N ^ (2 * ζ) / Real.sqrt (N * z.im)) ∧
      lamAvg H z ≤ (2 * Co + U + C1 + 1) * weakBeta N ζ q z := by
  have hN3 : 3 ≤ N := by omega
  have hNr : (40 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hq : 0 < q := lt_of_lt_of_le (Real.rpow_pos_of_pos (sc_phi_pos hN3) K) hqK
  have hU0 : 0 < U := by linarith
  -- the induction along a vertical line of the grid, downwards from `η = 10`
  have hind : ∀ a : ℤ, -(5 * (N : ℤ) ^ 3) ≤ a → a ≤ 5 * (N : ℤ) ^ 3 → ∀ b : ℕ,
      b < 10 * N ^ 8 → weakPt N a b ∈ specDomain N K →
      WeakInv N ζ q Cm U C1 H (weakPt N a b) := by
    intro a ha1 ha2 b
    induction b with
    | zero =>
      intro hb hzS
      have h2 : 2 ≤ (weakPt N a 0).im := by
        simp only [weakPt, Nat.cast_zero, zero_div, sub_zero]
        norm_num
      have hg := hgood a 0 ha1 ha2 hb hzS
      obtain ⟨hΩ, hlt⟩ := weak_point_start hN3 hζ hK hqK hzS h2 hCm hmsc hU0 hCi hAi hKmU hNsq
        (hg.2 h2)
      exact weak_point_inv hN3 hζ hK hqK hzS hCc hCo hCd hCm hmsc hU0.le hC1 hdich hA hlog hg hΩ
        fun _ => hlt
    | succ b ih =>
      intro hb hzS
      have hg := hgood a (b + 1) ha1 ha2 hb hzS
      by_cases h2 : 2 ≤ (weakPt N a (b + 1)).im
      · obtain ⟨hΩ, hlt⟩ := weak_point_start hN3 hζ hK hqK hzS h2 hCm hmsc hU0 hCi hAi hKmU
          hNsq (hg.2 h2)
        exact weak_point_inv hN3 hζ hK hqK hzS hCc hCo hCd hCm hmsc hU0.le hC1 hdich hA hlog hg
          hΩ fun _ => hlt
      · have hb' : b < 10 * N ^ 8 := by omega
        have him : (weakPt N a b).im = (weakPt N a (b + 1)).im + 1 / (N : ℝ) ^ 8 := by
          simp only [weakPt]
          push_cast
          ring
        have hre : (weakPt N a b).re = (weakPt N a (b + 1)).re := rfl
        have hzS' : weakPt N a b ∈ specDomain N K := by
          obtain ⟨h1, h2', h3⟩ := hzS
          refine ⟨by rw [hre]; exact h1, ?_, ?_⟩
          · rw [him]
            have : 0 ≤ 1 / (N : ℝ) ^ 8 := by positivity
            linarith
          · simp only [weakPt]
            have : 0 ≤ (b : ℝ) / (N : ℝ) ^ 8 := by positivity
            linarith
        have hinv := ih hb' hzS'
        obtain ⟨hΩ, hlt⟩ := weak_point_step hH hN hζ hK0 hq hzS hzS' hre him hCm hmsc hU hN6 hinv
        exact weak_point_inv hN3 hζ hK hqK hzS hCc hCo hCd hCm hmsc hU0.le hC1 hdich hA hlog hg
          hΩ hlt
  -- transfer to an arbitrary `z ∈ S(K)`
  intro z hz
  obtain ⟨hre, hz0, hz10, -⟩ := sc_specDomain hN3 hz
  have hN3p : (0 : ℝ) < (N : ℝ) ^ 3 := by positivity
  have hN8p : (0 : ℝ) < (N : ℝ) ^ 8 := by positivity
  set a : ℤ := ⌊z.re * (N : ℝ) ^ 3⌋ with ha
  set x : ℝ := (10 - z.im) * (N : ℝ) ^ 8 with hx
  have hx0 : 0 ≤ x := mul_nonneg (by linarith) hN8p.le
  set b : ℕ := ⌊x⌋₊ with hb
  have hre' := abs_le.mp hre
  have ha1 : -(5 * (N : ℤ) ^ 3) ≤ a := by
    rw [ha, Int.le_floor]
    push_cast
    nlinarith
  have ha2 : a ≤ 5 * (N : ℤ) ^ 3 := by
    have h1 : ((a : ℤ) : ℝ) ≤ z.re * (N : ℝ) ^ 3 := Int.floor_le _
    have h2 : z.re * (N : ℝ) ^ 3 ≤ 5 * (N : ℝ) ^ 3 := by nlinarith
    have h3 : ((a : ℤ) : ℝ) ≤ ((5 * (N : ℤ) ^ 3 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast h3
  have hbx : (b : ℝ) ≤ x := Nat.floor_le hx0
  have hxb : x < b + 1 := Nat.lt_floor_add_one x
  have hb10 : b < 10 * N ^ 8 := by
    have h1 : x < 10 * (N : ℝ) ^ 8 := by
      rw [hx]
      nlinarith
    have h2 : (b : ℝ) < ((10 * N ^ 8 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h2
  set w := weakPt N a b with hw
  have hwim : z.im ≤ w.im := by
    simp only [hw, weakPt]
    rw [le_sub_comm, div_le_iff₀ hN8p]
    linarith
  have hwim' : w.im ≤ z.im + 1 / (N : ℝ) ^ 8 := by
    simp only [hw, weakPt]
    have : x - 1 < (b : ℝ) := by linarith
    have h1 : (x - 1) / (N : ℝ) ^ 8 ≤ (b : ℝ) / (N : ℝ) ^ 8 :=
      div_le_div_of_nonneg_right this.le hN8p.le
    have h2 : (x - 1) / (N : ℝ) ^ 8 = 10 - z.im - 1 / (N : ℝ) ^ 8 := by
      rw [hx]
      field_simp
    linarith
  have hwre : 0 ≤ z.re - w.re ∧ z.re - w.re ≤ 1 / (N : ℝ) ^ 3 := by
    simp only [hw, weakPt]
    have h1 : ((a : ℤ) : ℝ) ≤ z.re * (N : ℝ) ^ 3 := Int.floor_le _
    have h2 : z.re * (N : ℝ) ^ 3 < (a : ℝ) + 1 := Int.lt_floor_add_one _
    constructor
    · rw [sub_nonneg, div_le_iff₀ hN3p]
      exact h1
    · rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hN3p]
      linarith
  have hwS : w ∈ specDomain N K := by
    obtain ⟨-, h2, -⟩ := hz
    refine ⟨?_, lt_of_lt_of_le h2 hwim, ?_⟩
    · simp only [hw, weakPt]
      rw [abs_div, abs_of_pos hN3p, div_le_iff₀ hN3p, abs_le]
      constructor
      · have : ((-(5 * (N : ℤ) ^ 3) : ℤ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
        push_cast at this
        linarith
      · have : (a : ℝ) ≤ ((5 * (N : ℤ) ^ 3 : ℤ) : ℝ) := by exact_mod_cast ha2
        push_cast at this
        linarith
    · simp only [hw, weakPt]
      have : 0 ≤ (b : ℝ) / (N : ℝ) ^ 8 := by positivity
      linarith
  have hd : ‖z - w‖ ≤ 2 / (N : ℝ) ^ 3 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im, abs_of_nonneg hwre.1, abs_sub_comm,
      abs_of_nonneg (by linarith)]
    have h8 : 1 / (N : ℝ) ^ 8 ≤ 1 / (N : ℝ) ^ 3 :=
      one_div_le_one_div_of_le hN3p (pow_le_pow_right₀ (by linarith) (by norm_num))
    have : 2 / (N : ℝ) ^ 3 = 1 / (N : ℝ) ^ 3 + 1 / (N : ℝ) ^ 3 := by ring
    linarith [hwre.2]
  have hinv := hind a ha1 ha2 b hb10 hwS
  have hg := hgood a b ha1 ha2 hb10 hwS
  have hΩw : lamD H w + lamO H w ≤ (phi N ^ ζ)⁻¹ := by
    have := hinv.1
    have h0 : 0 ≤ (phi N ^ ζ)⁻¹ := by
      have := sc_phi_pos hN3
      positivity
    linarith
  exact weak_point_final hH hN hζ hK0 hq hz hwS hwim hd hCo hU0.le hC1 hinv (hg.1 hΩw).2.1

/-! ### The union bound -/

/-- The grid has at most `110 N¹¹` points. -/
private lemma weak_card_le {N : ℕ} (hN : 1 ≤ N) (P : ℤ × ℕ → Prop) [DecidablePred P] :
    ((((Finset.Icc (-(5 * (N : ℤ) ^ 3)) (5 * (N : ℤ) ^ 3)) ×ˢ Finset.range (10 * N ^ 8)).filter
      P).card : ℝ) ≤ 110 * (N : ℝ) ^ 11 := by
  have h1 := Finset.card_filter_le
    ((Finset.Icc (-(5 * (N : ℤ) ^ 3)) (5 * (N : ℤ) ^ 3)) ×ˢ Finset.range (10 * N ^ 8)) P
  rw [Finset.card_product, Int.card_Icc, Finset.card_range] at h1
  have hn : (0 : ℤ) ≤ 5 * (N : ℤ) ^ 3 + 1 - -(5 * (N : ℤ) ^ 3) := by
    have : (0 : ℤ) ≤ (N : ℤ) ^ 3 := by positivity
    linarith
  have e : (((5 * (N : ℤ) ^ 3 + 1 - -(5 * (N : ℤ) ^ 3)).toNat : ℕ) : ℝ) = 10 * (N : ℝ) ^ 3 + 1 := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hn]
    push_cast
    ring
  have h2 : (((((Finset.Icc (-(5 * (N : ℤ) ^ 3)) (5 * (N : ℤ) ^ 3)) ×ˢ
      Finset.range (10 * N ^ 8)).filter P).card : ℕ) : ℝ) ≤
      (((5 * (N : ℤ) ^ 3 + 1 - -(5 * (N : ℤ) ^ 3)).toNat : ℕ) : ℝ) * ((10 * N ^ 8 : ℕ) : ℝ) := by
    exact_mod_cast h1
  rw [e] at h2
  push_cast at h2
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h3 : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ hN1
  have h8 : (0 : ℝ) ≤ (N : ℝ) ^ 8 := by positivity
  calc _ ≤ (10 * (N : ℝ) ^ 3 + 1) * (10 * (N : ℝ) ^ 8) := h2
    _ ≤ (11 * (N : ℝ) ^ 3) * (10 * (N : ℝ) ^ 8) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
    _ = 110 * (N : ℝ) ^ 11 := by ring

/-- `110 N¹¹ · 4 e^{-c s} ≤ e^{-c s/2}` once `2 (11 + log 440)/c · (log N + 1) ≤ s`. -/
private lemma weak_union_exp {N : ℕ} {c s : ℝ} (hN : 1 ≤ N) (hc : 0 < c)
    (hs : 2 * (11 + Real.log 440) / c * (Real.log N + 1) ≤ s) :
    110 * (N : ℝ) ^ 11 * (4 * Real.exp (-c * s)) ≤ Real.exp (-(c / 2) * s) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hl440 : 0 ≤ Real.log 440 := Real.log_nonneg (by norm_num)
  have e1 : 110 * (N : ℝ) ^ 11 * 4 = Real.exp (Real.log 440 + 11 * Real.log N) := by
    rw [Real.exp_add, show (11 : ℝ) = ((11 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul,
      Real.exp_log hN0, Real.exp_log (by norm_num)]
    ring
  have h2 : Real.log 440 + 11 * Real.log N ≤ c / 2 * s := by
    have h3 : (11 + Real.log 440) * (Real.log N + 1) ≤ c / 2 * s := by
      have := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ c / 2)
      calc (11 + Real.log 440) * (Real.log N + 1)
          = c / 2 * (2 * (11 + Real.log 440) / c * (Real.log N + 1)) := by field_simp
        _ ≤ c / 2 * s := this
    nlinarith
  calc 110 * (N : ℝ) ^ 11 * (4 * Real.exp (-c * s))
      = Real.exp (Real.log 440 + 11 * Real.log N) * Real.exp (-c * s) := by rw [← e1]; ring
    _ = Real.exp (Real.log 440 + 11 * Real.log N + -c * s) := by rw [Real.exp_add (_ + _)]
    _ ≤ Real.exp (-(c / 2) * s) := Real.exp_le_exp.mpr (by linarith)

/-- The eventual inequalities on `N` used by the continuity argument and the union bound. -/
private lemma weak_eventually {ζ : ℝ} (hζ : 0 < ζ) (A X Y B : ℝ) : ∀ᶠ N : ℕ in atTop,
    40 ≤ N ∧ A ≤ phi N ∧ X ≤ Real.log N ∧ Y < phi N ^ ζ ∧ 6 * phi N ^ ζ ≤ (N : ℝ) ^ 6 ∧
      phi N ^ (3 * ζ + 1) ≤ Real.sqrt N ∧ B * (Real.log N + 1) ≤ phi N ^ ζ := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 40, eventually_mul_log_add_one_le_phi_rpow one_pos (|A|),
    hlog.eventually_ge_atTop X, eventually_mul_log_add_one_le_phi_rpow hζ (|Y| + 1),
    phi_rpow_le_rpow ζ one_pos,
    phi_rpow_le_rpow (3 * ζ + 1) (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_mul_log_add_one_le_phi_rpow hζ B]
    with N h40 hA hX hY h6 hsq hB
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  refine ⟨h40, ?_, hX, ?_, ?_, ?_, hB.2⟩
  · rw [Real.rpow_one] at hA
    have : |A| ≤ |A| * (Real.log N + 1) := by nlinarith [abs_nonneg A]
    linarith [le_abs_self A, hA.2]
  · have : |Y| + 1 ≤ (|Y| + 1) * (Real.log N + 1) := by nlinarith [abs_nonneg Y]
    linarith [le_abs_self Y, hY.2]
  · rw [Real.rpow_one] at h6
    have hN : (40 : ℝ) ≤ N := by exact_mod_cast h40
    have : (N : ℝ) ^ 1 ≤ (N : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    nlinarith
  · rw [Real.sqrt_eq_rpow]
    exact hsq

/-- `μ (A ∪ B ∪ C ∪ D) ≤ μ A + μ B + μ C + μ D`. -/
private lemma weak_law_le {N : ℕ} {L : EntryLaws N} (A B C D : Set (Entries N)) :
    L.law (A ∪ B ∪ C ∪ D) ≤ L.law A + L.law B + L.law C + L.law D :=
  (measure_union_le _ _).trans <| add_le_add
    ((measure_union_le _ _).trans <| add_le_add (measure_union_le _ _) le_rfl) le_rfl

/-- The exceptional events at one point `z`: the complements of (3.42), (3.32), (3.36) of [15] on
`Ω(z)`, and of the initial estimate (Lemma 3.16 of [15]) for `η ≥ 2`. -/
private def weakBad (N : ℕ) (ζ q Cc Co Cd Ci : ℝ) (z : ℂ) : Set (Entries N) :=
  {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ (phi N ^ ζ)⁻¹ ∧
      Cc * (lamAvg (symOfEntries ω) z ^ 2 / Real.log N + phi N ^ ζ / q +
        (phi N ^ ζ) ^ 2 * psiCtrl (symOfEntries ω) z) <
      ‖(1 - msc z ^ 2) * (stieltjesM (symOfEntries ω) z - msc z) -
        msc z ^ 3 * (stieltjesM (symOfEntries ω) z - msc z) ^ 2‖} ∪
  {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ (phi N ^ ζ)⁻¹ ∧
      Co * (1 / q + phi N ^ (2 * ζ) * psiCtrl (symOfEntries ω) z) < lamO (symOfEntries ω) z} ∪
  {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ (phi N ^ ζ)⁻¹ ∧
      Cd * (phi N ^ ζ / q + (phi N ^ ζ) ^ 2 * psiCtrl (symOfEntries ω) z) <
        ⨆ i, ‖resolventC (symOfEntries ω) z i i - stieltjesM (symOfEntries ω) z‖} ∪
  {ω | 2 ≤ z.im ∧ Ci * (phi N ^ ζ / q + phi N ^ (2 * ζ) / Real.sqrt N) <
      lamD (symOfEntries ω) z + lamO (symOfEntries ω) z}

private lemma weak_good_of_not_mem {N : ℕ} {ζ q Cc Co Cd Ci : ℝ} {z : ℂ} {ω : Entries N}
    (h : ω ∉ weakBad N ζ q Cc Co Cd Ci z) : WeakGood N ζ q Cc Co Cd Ci (symOfEntries ω) z := by
  simp only [weakBad, Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_lt] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨fun hΩ => ⟨h1 hΩ, h2 hΩ, h3 hΩ⟩, h4⟩

/-! ### The weak local semicircle law -/

/-- Weak local semicircle law (Theorem 3.1 of [15]) on `S(K)`, uniform in `z`. -/
theorem weakLocalLaw {ζ C0 : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) :
    ∃ K > 0, ∃ C > 0, ∃ c > 0, ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (L : EntryLaws N) (q : ℝ),
      L.IsGenWigner C0 → L.BoundedSupportAS q → phi N ^ K ≤ q →
      L.law {ω | ∃ z ∈ specDomain N K,
        C * (1 / q + phi N ^ (2 * ζ) / Real.sqrt (N * z.im)) < lamO (symOfEntries ω) z ∨
        C * (phi N ^ ζ / Real.sqrt q + phi N ^ (4 * ζ / 3) / (N * z.im) ^ ((1 : ℝ) / 3)) <
          lamAvg (symOfEntries ω) z} ≤ ENNReal.ofReal (Real.exp (-c * phi N ^ ζ)) := by
  classical
  obtain ⟨Kc, -, Cc, hCc, cc, hcc, Nc, hSC⟩ := selfConsistent_weak_on_omega hζ hC0
  obtain ⟨Ko, -, Co, hCo, co, hco, No, hO⟩ := lamO_le_on_omega hζ hC0
  obtain ⟨Kd, -, Cd, hCd, cd, hcd, Nd, hD⟩ := norm_resolventC_diag_sub_le_on_omega hζ hC0
  obtain ⟨Ki, -, Ci, hCi, ci, hci, Ni, hI⟩ := initial_large_eta hζ hC0
  obtain ⟨Cm, hCm, hmsc⟩ := msc_bounds
  have hCm0 : (0 : ℝ) < Cm := by linarith
  have hCs : 0 < Cc * Cm ^ 3 * (2 + Cm ^ 5) := by positivity
  obtain ⟨C1, hC1, hdich⟩ := dichotomy _ _ hCs (one_le_pow₀ hCm : (1 : ℝ) ≤ Cm ^ 4)
    (9 * (Cc * Cm ^ 3 * (2 + Cm ^ 5) + 1)) le_rfl
  set U : ℝ := 9 * (Cc * Cm ^ 3 * (2 + Cm ^ 5) + 1) with hU
  have hU9 : 9 ≤ U := by
    rw [hU]
    linarith
  set c0 : ℝ := min (min cc co) (min cd ci) with hc0
  have hc00 : 0 < c0 := lt_min (lt_min hcc hco) (lt_min hcd hci)
  set K : ℝ := max (max Kc Ko) (max Kd (max (Ki : ℝ) (8 * ζ + 3))) with hK
  have hKc : Kc ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hKo : Ko ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have hKd : Kd ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKi : (Ki : ℝ) ≤ K :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hK8 : 8 * ζ + 3 ≤ K :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (weak_eventually hζ
    (2 * (3 * (Co + Cd) + 2 * (U + C1)) + 2 * Ci) (2 * (Cm ^ 3 * Cc)) (Cm ^ 4 * U)
    (2 * (11 + Real.log 440) / c0))
  refine ⟨K, lt_of_lt_of_le (by linarith) hK8, 2 * Co + U + C1 + 1, by positivity, c0 / 2,
    by positivity, max N1 (max Nc (max No (max Nd Ni))), ?_⟩
  intro N hN L q hL hq hqK
  obtain ⟨h40, hA, hX, hY, h6, hsq, hB⟩ := hN1 N (le_trans (le_max_left _ _) hN)
  have hNc : Nc ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNo : No ≤ N :=
    le_trans (le_trans (le_max_left _ _) ((le_max_right _ _).trans (le_max_right _ _))) hN
  have hNd : Nd ≤ N := le_trans (le_trans (le_max_left _ _)
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))) hN
  have hNi : Ni ≤ N := le_trans (le_trans (le_max_right _ _)
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))) hN
  have hN3 : 3 ≤ N := by omega
  have hφ0 := sc_phi_pos hN3
  have hs0 : 0 ≤ phi N ^ ζ := (Real.rpow_pos_of_pos hφ0 ζ).le
  have hsle : phi N ^ ζ ≤ phi N ^ (ζ + 3) := sc_rpow_mono hN3 (by linarith)
  have hCi2 : 2 * Ci ≤ phi N := by
    have : 0 ≤ 2 * (3 * (Co + Cd) + 2 * (U + C1)) := by positivity
    linarith
  have hA1 : 2 * (3 * (Co + Cd) + 2 * (U + C1)) ≤ phi N := by
    have : 0 ≤ 2 * Ci := by positivity
    linarith
  set I : Finset (ℤ × ℕ) :=
    ((Finset.Icc (-(5 * (N : ℤ) ^ 3)) (5 * (N : ℤ) ^ 3)) ×ˢ Finset.range (10 * N ^ 8)).filter
      (fun p => weakPt N p.1 p.2 ∈ specDomain N K) with hIdef
  -- the event lies in the union of the exceptional events over the grid
  have hsub : {ω | ∃ z ∈ specDomain N K,
      (2 * Co + U + C1 + 1) * (1 / q + phi N ^ (2 * ζ) / Real.sqrt (N * z.im)) <
        lamO (symOfEntries ω) z ∨
      (2 * Co + U + C1 + 1) * (phi N ^ ζ / Real.sqrt q +
        phi N ^ (4 * ζ / 3) / (N * z.im) ^ ((1 : ℝ) / 3)) < lamAvg (symOfEntries ω) z} ⊆
      ⋃ p ∈ I, weakBad N ζ q Cc Co Cd Ci (weakPt N p.1 p.2) := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_iUnion, not_exists] at hnot
    obtain ⟨z, hz, hbad⟩ := hω
    have key := weak_det (symOfEntries_isHermitian ω) h40 hζ hK8 hqK hCc hCo.le hCd.le hCi.le
      hCm hmsc hU9 hC1.le hdich hA1 hCi2 hX hY h6 hsq (fun a b ha1 ha2 hb hS =>
        weak_good_of_not_mem (hnot (a, b) (by
          simp only [hIdef, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
            Finset.mem_range]
          exact ⟨⟨⟨ha1, ha2⟩, hb⟩, hS⟩))) z hz
    rcases hbad with h | h
    · exact absurd key.1 (not_le.mpr h)
    · exact absurd key.2 (not_le.mpr h)
  -- each exceptional event is exponentially small
  have hbad : ∀ p ∈ I, L.law (weakBad N ζ q Cc Co Cd Ci (weakPt N p.1 p.2)) ≤
      ENNReal.ofReal (4 * Real.exp (-c0 * phi N ^ ζ)) := by
    intro p hp
    have hzS : weakPt N p.1 p.2 ∈ specDomain N K := (Finset.mem_filter.mp hp).2
    set z := weakPt N p.1 p.2 with hz
    obtain ⟨hre, hz0, hz10, -⟩ := sc_specDomain hN3 hzS
    have hexp : ∀ c' : ℝ, c0 ≤ c' → ENNReal.ofReal (Real.exp (-c' * phi N ^ ζ)) ≤
        ENNReal.ofReal (Real.exp (-c0 * phi N ^ ζ)) := fun c' hc' =>
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith))
    have a1 := (hSC N hNc L q (phi N ^ ζ) z hL hq ((sc_rpow_mono hN3 hKc).trans hqK)
      (sc_specDomain_mono hN3 hKc hzS) le_rfl hsle).trans
      (hexp cc ((min_le_left _ _).trans (min_le_left _ _)))
    have a2 := (hO N hNo L q z hL hq ((sc_rpow_mono hN3 hKo).trans hqK)
      (sc_specDomain_mono hN3 hKo hzS)).trans
      (hexp co ((min_le_left _ _).trans (min_le_right _ _)))
    have a3 := (hD N hNd L q (phi N ^ ζ) z hL hq ((sc_rpow_mono hN3 hKd).trans hqK)
      (sc_specDomain_mono hN3 hKd hzS) le_rfl hsle).trans
      (hexp cd ((min_le_right _ _).trans (min_le_left _ _)))
    have a4 : L.law {ω | 2 ≤ z.im ∧ Ci * (phi N ^ ζ / q + phi N ^ (2 * ζ) / Real.sqrt N) <
        lamD (symOfEntries ω) z + lamO (symOfEntries ω) z} ≤
        ENNReal.ofReal (Real.exp (-c0 * phi N ^ ζ)) := by
      by_cases h2 : 2 ≤ z.im
      · have hqKi : phi N ^ Ki ≤ q := by
          have := sc_rpow_mono hN3 hKi
          rw [Real.rpow_natCast] at this
          exact this.trans hqK
        refine le_trans (measure_mono ?_) ((hI N hNi L q z hL hq hqKi hre h2 hz10).trans
          (hexp ci ((min_le_right _ _).trans (min_le_right _ _))))
        intro ω hω
        exact hω.2
      · have : {ω : Entries N | 2 ≤ z.im ∧ Ci * (phi N ^ ζ / q + phi N ^ (2 * ζ) / Real.sqrt N) <
            lamD (symOfEntries ω) z + lamO (symOfEntries ω) z} = ∅ := by
          ext ω
          simp [h2]
        rw [this, measure_empty]
        exact bot_le
    have he : 0 ≤ Real.exp (-c0 * phi N ^ ζ) := (Real.exp_pos _).le
    calc L.law (weakBad N ζ q Cc Co Cd Ci z) ≤ _ := weak_law_le _ _ _ _
      _ ≤ ENNReal.ofReal (Real.exp (-c0 * phi N ^ ζ)) +
          ENNReal.ofReal (Real.exp (-c0 * phi N ^ ζ)) +
          ENNReal.ofReal (Real.exp (-c0 * phi N ^ ζ)) +
          ENNReal.ofReal (Real.exp (-c0 * phi N ^ ζ)) :=
        add_le_add (add_le_add (add_le_add a1 a2) a3) a4
      _ = ENNReal.ofReal (4 * Real.exp (-c0 * phi N ^ ζ)) := by
        rw [← ENNReal.ofReal_add he he, ← ENNReal.ofReal_add (by positivity) he,
          ← ENNReal.ofReal_add (by positivity) he]
        ring_nf
  have hcard := weak_card_le (by omega : 1 ≤ N) (fun p => weakPt N p.1 p.2 ∈ specDomain N K)
  have hu := weak_union_exp (by omega : 1 ≤ N) hc00 hB
  calc _ ≤ L.law (⋃ p ∈ I, weakBad N ζ q Cc Co Cd Ci (weakPt N p.1 p.2)) := measure_mono hsub
    _ ≤ ∑ p ∈ I, L.law (weakBad N ζ q Cc Co Cd Ci (weakPt N p.1 p.2)) :=
        measure_biUnion_finset_le I _
    _ ≤ ∑ _p ∈ I, ENNReal.ofReal (4 * Real.exp (-c0 * phi N ^ ζ)) := Finset.sum_le_sum hbad
    _ = ENNReal.ofReal (I.card • (4 * Real.exp (-c0 * phi N ^ ζ))) := by
        rw [Finset.sum_const, ENNReal.ofReal_nsmul]
    _ ≤ ENNReal.ofReal (Real.exp (-(c0 / 2) * phi N ^ ζ)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [nsmul_eq_mul]
        refine le_trans ?_ hu
        exact mul_le_mul_of_nonneg_right hcard (by positivity)

/-! ### The event `Ω(z)` at every point of `S(K)` -/

/-- A grid point of `S(K)` above a given `z ∈ S(K)`, at distance at most `2 N⁻³`
(Corollary 3.19 of [15]). -/
private lemma weak_grid_above {N : ℕ} {K : ℝ} (hN : 3 ≤ N) {z : ℂ} (hz : z ∈ specDomain N K) :
    ∃ (a : ℤ) (b : ℕ), -(5 * (N : ℤ) ^ 3) ≤ a ∧ a ≤ 5 * (N : ℤ) ^ 3 ∧ b < 10 * N ^ 8 ∧
      weakPt N a b ∈ specDomain N K ∧ z.im ≤ (weakPt N a b).im ∧
      ‖z - weakPt N a b‖ ≤ 2 / (N : ℝ) ^ 3 := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨hre, hz0, hz10, -⟩ := sc_specDomain hN hz
  have hN3p : (0 : ℝ) < (N : ℝ) ^ 3 := by positivity
  have hN8p : (0 : ℝ) < (N : ℝ) ^ 8 := by positivity
  set a : ℤ := ⌊z.re * (N : ℝ) ^ 3⌋ with ha
  set x : ℝ := (10 - z.im) * (N : ℝ) ^ 8 with hx
  have hx0 : 0 ≤ x := mul_nonneg (by linarith) hN8p.le
  set b : ℕ := ⌊x⌋₊ with hb
  have hre' := abs_le.mp hre
  have ha1 : -(5 * (N : ℤ) ^ 3) ≤ a := by
    rw [ha, Int.le_floor]
    push_cast
    nlinarith
  have ha2 : a ≤ 5 * (N : ℤ) ^ 3 := by
    have h1 : ((a : ℤ) : ℝ) ≤ z.re * (N : ℝ) ^ 3 := Int.floor_le _
    have h2 : z.re * (N : ℝ) ^ 3 ≤ 5 * (N : ℝ) ^ 3 := by nlinarith
    have h3 : ((a : ℤ) : ℝ) ≤ ((5 * (N : ℤ) ^ 3 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast h3
  have hbx : (b : ℝ) ≤ x := Nat.floor_le hx0
  have hxb : x < b + 1 := Nat.lt_floor_add_one x
  have hb10 : b < 10 * N ^ 8 := by
    have h1 : x < 10 * (N : ℝ) ^ 8 := by
      rw [hx]
      nlinarith
    have h2 : (b : ℝ) < ((10 * N ^ 8 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h2
  set w := weakPt N a b with hw
  have hwim : z.im ≤ w.im := by
    simp only [hw, weakPt]
    rw [le_sub_comm, div_le_iff₀ hN8p]
    linarith
  have hwim' : w.im ≤ z.im + 1 / (N : ℝ) ^ 8 := by
    simp only [hw, weakPt]
    have : x - 1 < (b : ℝ) := by linarith
    have h1 : (x - 1) / (N : ℝ) ^ 8 ≤ (b : ℝ) / (N : ℝ) ^ 8 :=
      div_le_div_of_nonneg_right this.le hN8p.le
    have h2 : (x - 1) / (N : ℝ) ^ 8 = 10 - z.im - 1 / (N : ℝ) ^ 8 := by
      rw [hx]
      field_simp
    linarith
  have hwre : 0 ≤ z.re - w.re ∧ z.re - w.re ≤ 1 / (N : ℝ) ^ 3 := by
    simp only [hw, weakPt]
    have h1 : ((a : ℤ) : ℝ) ≤ z.re * (N : ℝ) ^ 3 := Int.floor_le _
    have h2 : z.re * (N : ℝ) ^ 3 < (a : ℝ) + 1 := Int.lt_floor_add_one _
    constructor
    · rw [sub_nonneg, div_le_iff₀ hN3p]
      exact h1
    · rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hN3p]
      linarith
  have hwS : w ∈ specDomain N K := by
    obtain ⟨-, h2, -⟩ := hz
    refine ⟨?_, lt_of_lt_of_le h2 hwim, ?_⟩
    · simp only [hw, weakPt]
      rw [abs_div, abs_of_pos hN3p, div_le_iff₀ hN3p, abs_le]
      constructor
      · have : ((-(5 * (N : ℤ) ^ 3) : ℤ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
        push_cast at this
        linarith
      · have : (a : ℝ) ≤ ((5 * (N : ℤ) ^ 3 : ℤ) : ℝ) := by exact_mod_cast ha2
        push_cast at this
        linarith
    · simp only [hw, weakPt]
      have : 0 ≤ (b : ℝ) / (N : ℝ) ^ 8 := by positivity
      linarith
  have hd : ‖z - w‖ ≤ 2 / (N : ℝ) ^ 3 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im, abs_of_nonneg hwre.1, abs_sub_comm,
      abs_of_nonneg (by linarith)]
    have h8 : 1 / (N : ℝ) ^ 8 ≤ 1 / (N : ℝ) ^ 3 :=
      one_div_le_one_div_of_le hN3p (pow_le_pow_right₀ (by linarith) (by norm_num))
    have : 2 / (N : ℝ) ^ 3 = 1 / (N : ℝ) ^ 3 + 1 / (N : ℝ) ^ 3 := by ring
    linarith [hwre.2]
  exact ⟨a, b, ha1, ha2, hb10, hwS, hwim, hd⟩

/-- The induction hypothesis of Lemma 3.18 of [15] at every grid point of `S(K)`, when the
estimates of `WeakGood` hold at every grid point of `S(K)`. -/
private lemma weak_grid_inv {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {ζ q K Cc Co Cd Ci Cm U C1 : ℝ} (hN : 40 ≤ N) (hζ : 0 < ζ) (hK : 8 * ζ + 3 ≤ K)
    (hqK : phi N ^ K ≤ q) (hCc : 0 < Cc) (hCo : 0 ≤ Co) (hCd : 0 ≤ Cd) (hCi : 0 ≤ Ci)
    (hCm : 1 ≤ Cm) (hmsc : WeakMscBd Cm) (hU : 9 ≤ U) (hC1 : 0 ≤ C1)
    (hdich : WeakDich (Cc * Cm ^ 3 * (2 + Cm ^ 5)) (Cm ^ 4) U C1)
    (hA : 2 * (3 * (Co + Cd) + 2 * (U + C1)) ≤ phi N) (hAi : 2 * Ci ≤ phi N)
    (hlog : 2 * (Cm ^ 3 * Cc) ≤ Real.log N) (hKmU : Cm ^ 4 * U < phi N ^ ζ)
    (hN6 : 6 * phi N ^ ζ ≤ (N : ℝ) ^ 6) (hNsq : phi N ^ (3 * ζ + 1) ≤ Real.sqrt N)
    (hgood : ∀ a : ℤ, ∀ b : ℕ, -(5 * (N : ℤ) ^ 3) ≤ a → a ≤ 5 * (N : ℤ) ^ 3 → b < 10 * N ^ 8 →
      weakPt N a b ∈ specDomain N K → WeakGood N ζ q Cc Co Cd Ci H (weakPt N a b)) :
    ∀ a : ℤ, -(5 * (N : ℤ) ^ 3) ≤ a → a ≤ 5 * (N : ℤ) ^ 3 → ∀ b : ℕ,
      b < 10 * N ^ 8 → weakPt N a b ∈ specDomain N K →
      WeakInv N ζ q Cm U C1 H (weakPt N a b) := by
  have hN3 : 3 ≤ N := by omega
  have hNr : (40 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hq : 0 < q := lt_of_lt_of_le (Real.rpow_pos_of_pos (sc_phi_pos hN3) K) hqK
  have hU0 : 0 < U := by linarith
  intro a ha1 ha2 b
  induction b with
  | zero =>
    intro hb hzS
    have h2 : 2 ≤ (weakPt N a 0).im := by
      simp only [weakPt, Nat.cast_zero, zero_div, sub_zero]
      norm_num
    have hg := hgood a 0 ha1 ha2 hb hzS
    obtain ⟨hΩ, hlt⟩ := weak_point_start hN3 hζ hK hqK hzS h2 hCm hmsc hU0 hCi hAi hKmU hNsq
      (hg.2 h2)
    exact weak_point_inv hN3 hζ hK hqK hzS hCc hCo hCd hCm hmsc hU0.le hC1 hdich hA hlog hg hΩ
      fun _ => hlt
  | succ b ih =>
    intro hb hzS
    have hg := hgood a (b + 1) ha1 ha2 hb hzS
    by_cases h2 : 2 ≤ (weakPt N a (b + 1)).im
    · obtain ⟨hΩ, hlt⟩ := weak_point_start hN3 hζ hK hqK hzS h2 hCm hmsc hU0 hCi hAi hKmU
        hNsq (hg.2 h2)
      exact weak_point_inv hN3 hζ hK hqK hzS hCc hCo hCd hCm hmsc hU0.le hC1 hdich hA hlog hg
        hΩ fun _ => hlt
    · have hb' : b < 10 * N ^ 8 := by omega
      have him : (weakPt N a b).im = (weakPt N a (b + 1)).im + 1 / (N : ℝ) ^ 8 := by
        simp only [weakPt]
        push_cast
        ring
      have hre : (weakPt N a b).re = (weakPt N a (b + 1)).re := rfl
      have hzS' : weakPt N a b ∈ specDomain N K := by
        obtain ⟨h1, h2', h3⟩ := hzS
        refine ⟨by rw [hre]; exact h1, ?_, ?_⟩
        · rw [him]
          have : 0 ≤ 1 / (N : ℝ) ^ 8 := by positivity
          linarith
        · simp only [weakPt]
          have : 0 ≤ (b : ℝ) / (N : ℝ) ^ 8 := by positivity
          linarith
      have hinv := ih hb' hzS'
      obtain ⟨hΩ, hlt⟩ := weak_point_step hH hN hζ hK0 hq hzS hzS' hre him hCm hmsc hU hN6 hinv
      exact weak_point_inv hN3 hζ hK hqK hzS hCc hCo hCd hCm hmsc hU0.le hC1 hdich hA hlog hg
        hΩ hlt

/-- The continuity argument for one matrix `H`: if the estimates of `WeakGood` hold at every grid
point of `S(K)`, and `12 φ^ζ ≤ N`, then `Λ_d + Λ_o ≤ φ^{-ζ}` at every `z ∈ S(K)`, that is, `Ω(z)`
of (3.25) of [15] holds simultaneously for all `z ∈ S(K)`. -/
private lemma weak_det_omega {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {ζ q K Cc Co Cd Ci Cm U C1 : ℝ} (hN : 40 ≤ N) (hζ : 0 < ζ) (hK : 8 * ζ + 3 ≤ K)
    (hqK : phi N ^ K ≤ q) (hCc : 0 < Cc) (hCo : 0 ≤ Co) (hCd : 0 ≤ Cd) (hCi : 0 ≤ Ci)
    (hCm : 1 ≤ Cm) (hmsc : WeakMscBd Cm) (hU : 9 ≤ U) (hC1 : 0 ≤ C1)
    (hdich : WeakDich (Cc * Cm ^ 3 * (2 + Cm ^ 5)) (Cm ^ 4) U C1)
    (hA : 2 * (3 * (Co + Cd) + 2 * (U + C1)) ≤ phi N) (hAi : 2 * Ci ≤ phi N)
    (hlog : 2 * (Cm ^ 3 * Cc) ≤ Real.log N) (hKmU : Cm ^ 4 * U < phi N ^ ζ)
    (hN6 : 6 * phi N ^ ζ ≤ (N : ℝ) ^ 6) (hNsq : phi N ^ (3 * ζ + 1) ≤ Real.sqrt N)
    (hNΩ : 12 * phi N ^ ζ ≤ N)
    (hgood : ∀ a : ℤ, ∀ b : ℕ, -(5 * (N : ℤ) ^ 3) ≤ a → a ≤ 5 * (N : ℤ) ^ 3 → b < 10 * N ^ 8 →
      weakPt N a b ∈ specDomain N K → WeakGood N ζ q Cc Co Cd Ci H (weakPt N a b)) :
    ∀ z ∈ specDomain N K, lamD H z + lamO H z ≤ (phi N ^ ζ)⁻¹ := by
  have hN3 : 3 ≤ N := by omega
  have hNr : (40 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hind := weak_grid_inv hH hN hζ hK hqK hCc hCo hCd hCi hCm hmsc hU hC1 hdich hA hAi hlog
    hKmU hN6 hNsq hgood
  intro z hz
  obtain ⟨a, b, ha1, ha2, hb, hwS, hwim, hd⟩ := weak_grid_above hN3 hz
  have hinv := hind a ha1 ha2 b hb hwS
  set w := weakPt N a b with hw
  obtain ⟨-, hz0, -, -⟩ := sc_specDomain hN3 hz
  obtain ⟨-, hw0, -, -⟩ := sc_specDomain hN3 hwS
  have hη := weak_im_ge hN3 hK0 hz
  have hηw := weak_im_ge hN3 hK0 hwS
  have hL : ‖z - w‖ / (z.im * w.im) ≤ 2 / N := by
    rw [div_le_iff₀ (by positivity)]
    calc ‖z - w‖ ≤ 2 / (N : ℝ) ^ 3 := hd
      _ = 2 / N * (1 / N * (1 / N)) := by field_simp
      _ ≤ 2 / N * (z.im * w.im) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hη hηw (by positivity) (by linarith)
  have hs0 : 0 < phi N ^ ζ := Real.rpow_pos_of_pos (sc_phi_pos hN3) ζ
  have h6 : 6 / (N : ℝ) ≤ (phi N ^ ζ)⁻¹ / 2 := by
    rw [div_le_iff₀ hN0]
    have e : (phi N ^ ζ)⁻¹ / 2 * N = N / (2 * phi N ^ ζ) := by field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  have hO := weak_lamO_le_add hH hz0 hw0 (H := H)
  have hD := weak_lamD_le_add hH hz0 hw0 (H := H)
  have e6 : 3 * (2 / (N : ℝ)) = 6 / N := by ring
  have h1 := hinv.1
  have h2 : 0 ≤ ‖z - w‖ / (z.im * w.im) := by positivity
  linarith

/-- `Ω(z)` of (3.25) of [15], `Λ_d + Λ_o ≤ φ^{-ζ}`, holds at all `z ∈ S(K)` simultaneously with
probability at least `1 - e^{-c φ^ζ}` (the first term of (3.58) of [15]). -/
theorem weakLocalLaw_omega {ζ C0 : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) :
    ∃ K > (0 : ℝ), ∃ c > (0 : ℝ), ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (L : EntryLaws N) (q : ℝ),
      L.IsGenWigner C0 → L.BoundedSupportAS q → phi N ^ K ≤ q →
      L.law {ω | ∃ z ∈ specDomain N K,
        (phi N ^ ζ)⁻¹ < lamD (symOfEntries ω) z + lamO (symOfEntries ω) z} ≤
        ENNReal.ofReal (Real.exp (-c * phi N ^ ζ)) := by
  classical
  obtain ⟨Kc, -, Cc, hCc, cc, hcc, Nc, hSC⟩ := selfConsistent_weak_on_omega hζ hC0
  obtain ⟨Ko, -, Co, hCo, co, hco, No, hO⟩ := lamO_le_on_omega hζ hC0
  obtain ⟨Kd, -, Cd, hCd, cd, hcd, Nd, hD⟩ := norm_resolventC_diag_sub_le_on_omega hζ hC0
  obtain ⟨Ki, -, Ci, hCi, ci, hci, Ni, hI⟩ := initial_large_eta hζ hC0
  obtain ⟨Cm, hCm, hmsc⟩ := msc_bounds
  have hCm0 : (0 : ℝ) < Cm := by linarith
  have hCs : 0 < Cc * Cm ^ 3 * (2 + Cm ^ 5) := by positivity
  obtain ⟨C1, hC1, hdich⟩ := dichotomy _ _ hCs (one_le_pow₀ hCm : (1 : ℝ) ≤ Cm ^ 4)
    (9 * (Cc * Cm ^ 3 * (2 + Cm ^ 5) + 1)) le_rfl
  set U : ℝ := 9 * (Cc * Cm ^ 3 * (2 + Cm ^ 5) + 1) with hU
  have hU9 : 9 ≤ U := by
    rw [hU]
    linarith
  set c0 : ℝ := min (min cc co) (min cd ci) with hc0
  have hc00 : 0 < c0 := lt_min (lt_min hcc hco) (lt_min hcd hci)
  set K : ℝ := max (max Kc Ko) (max Kd (max (Ki : ℝ) (8 * ζ + 3))) with hK
  have hKc : Kc ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hKo : Ko ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have hKd : Kd ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKi : (Ki : ℝ) ≤ K :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hK8 : 8 * ζ + 3 ≤ K :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (weak_eventually hζ
    (2 * (3 * (Co + Cd) + 2 * (U + C1)) + 2 * Ci) (2 * (Cm ^ 3 * Cc)) (Cm ^ 4 * U)
    (2 * (11 + Real.log 440) / c0))
  refine ⟨K, lt_of_lt_of_le (by linarith) hK8, c0 / 2, by positivity,
    max 144 (max N1 (max Nc (max No (max Nd Ni)))), ?_⟩
  intro N hN L q hL hq hqK
  have h144 : 144 ≤ N := le_trans (le_max_left _ _) hN
  have hNm : max N1 (max Nc (max No (max Nd Ni))) ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨h40, hA, hX, hY, h6, hsq, hB⟩ := hN1 N (le_trans (le_max_left _ _) hNm)
  have hNc : Nc ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hNm
  have hNo : No ≤ N :=
    le_trans (le_trans (le_max_left _ _) ((le_max_right _ _).trans (le_max_right _ _))) hNm
  have hNd : Nd ≤ N := le_trans (le_trans (le_max_left _ _)
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))) hNm
  have hNi : Ni ≤ N := le_trans (le_trans (le_max_right _ _)
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))) hNm
  have hN3 : 3 ≤ N := by omega
  have hφ0 := sc_phi_pos hN3
  have hs0 : 0 ≤ phi N ^ ζ := (Real.rpow_pos_of_pos hφ0 ζ).le
  have hsle : phi N ^ ζ ≤ phi N ^ (ζ + 3) := sc_rpow_mono hN3 (by linarith)
  have hCi2 : 2 * Ci ≤ phi N := by
    have : 0 ≤ 2 * (3 * (Co + Cd) + 2 * (U + C1)) := by positivity
    linarith
  have hA1 : 2 * (3 * (Co + Cd) + 2 * (U + C1)) ≤ phi N := by
    have : 0 ≤ 2 * Ci := by positivity
    linarith
  -- `12 φ^ζ ≤ φ^{3ζ+1} · 12 ≤ 12 √N ≤ N` for `N ≥ 144`
  have hNΩ : 12 * phi N ^ ζ ≤ N := by
    have h1 : phi N ^ ζ ≤ phi N ^ (3 * ζ + 1) := sc_rpow_mono hN3 (by linarith)
    have h144r : (144 : ℝ) ≤ N := by exact_mod_cast h144
    have h12 : (12 : ℝ) ≤ Real.sqrt N := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]
      linarith
    have h2 : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by linarith)
    nlinarith
  set I : Finset (ℤ × ℕ) :=
    ((Finset.Icc (-(5 * (N : ℤ) ^ 3)) (5 * (N : ℤ) ^ 3)) ×ˢ Finset.range (10 * N ^ 8)).filter
      (fun p => weakPt N p.1 p.2 ∈ specDomain N K) with hIdef
  -- the event lies in the union of the exceptional events over the grid
  have hsub : {ω | ∃ z ∈ specDomain N K,
      (phi N ^ ζ)⁻¹ < lamD (symOfEntries ω) z + lamO (symOfEntries ω) z} ⊆
      ⋃ p ∈ I, weakBad N ζ q Cc Co Cd Ci (weakPt N p.1 p.2) := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_iUnion, not_exists] at hnot
    obtain ⟨z, hz, hbad⟩ := hω
    have key := weak_det_omega (symOfEntries_isHermitian ω) h40 hζ hK8 hqK hCc hCo.le hCd.le
      hCi.le hCm hmsc hU9 hC1.le hdich hA1 hCi2 hX hY h6 hsq hNΩ (fun a b ha1 ha2 hb hS =>
        weak_good_of_not_mem (hnot (a, b) (by
          simp only [hIdef, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
            Finset.mem_range]
          exact ⟨⟨⟨ha1, ha2⟩, hb⟩, hS⟩))) z hz
    exact absurd key (not_le.mpr hbad)
  -- each exceptional event is exponentially small
  have hbad : ∀ p ∈ I, L.law (weakBad N ζ q Cc Co Cd Ci (weakPt N p.1 p.2)) ≤
      ENNReal.ofReal (4 * Real.exp (-c0 * phi N ^ ζ)) := by
    intro p hp
    have hzS : weakPt N p.1 p.2 ∈ specDomain N K := (Finset.mem_filter.mp hp).2
    set z := weakPt N p.1 p.2 with hz
    obtain ⟨hre, hz0, hz10, -⟩ := sc_specDomain hN3 hzS
    have hexp : ∀ c' : ℝ, c0 ≤ c' → ENNReal.ofReal (Real.exp (-c' * phi N ^ ζ)) ≤
        ENNReal.ofReal (Real.exp (-c0 * phi N ^ ζ)) := fun c' hc' =>
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith))
    have a1 := (hSC N hNc L q (phi N ^ ζ) z hL hq ((sc_rpow_mono hN3 hKc).trans hqK)
      (sc_specDomain_mono hN3 hKc hzS) le_rfl hsle).trans
      (hexp cc ((min_le_left _ _).trans (min_le_left _ _)))
    have a2 := (hO N hNo L q z hL hq ((sc_rpow_mono hN3 hKo).trans hqK)
      (sc_specDomain_mono hN3 hKo hzS)).trans
      (hexp co ((min_le_left _ _).trans (min_le_right _ _)))
    have a3 := (hD N hNd L q (phi N ^ ζ) z hL hq ((sc_rpow_mono hN3 hKd).trans hqK)
      (sc_specDomain_mono hN3 hKd hzS) le_rfl hsle).trans
      (hexp cd ((min_le_right _ _).trans (min_le_left _ _)))
    have a4 : L.law {ω | 2 ≤ z.im ∧ Ci * (phi N ^ ζ / q + phi N ^ (2 * ζ) / Real.sqrt N) <
        lamD (symOfEntries ω) z + lamO (symOfEntries ω) z} ≤
        ENNReal.ofReal (Real.exp (-c0 * phi N ^ ζ)) := by
      by_cases h2 : 2 ≤ z.im
      · have hqKi : phi N ^ Ki ≤ q := by
          have := sc_rpow_mono hN3 hKi
          rw [Real.rpow_natCast] at this
          exact this.trans hqK
        refine le_trans (measure_mono ?_) ((hI N hNi L q z hL hq hqKi hre h2 hz10).trans
          (hexp ci ((min_le_right _ _).trans (min_le_right _ _))))
        intro ω hω
        exact hω.2
      · have : {ω : Entries N | 2 ≤ z.im ∧ Ci * (phi N ^ ζ / q + phi N ^ (2 * ζ) / Real.sqrt N) <
            lamD (symOfEntries ω) z + lamO (symOfEntries ω) z} = ∅ := by
          ext ω
          simp [h2]
        rw [this, measure_empty]
        exact bot_le
    have he : 0 ≤ Real.exp (-c0 * phi N ^ ζ) := (Real.exp_pos _).le
    calc L.law (weakBad N ζ q Cc Co Cd Ci z) ≤ _ := weak_law_le _ _ _ _
      _ ≤ ENNReal.ofReal (Real.exp (-c0 * phi N ^ ζ)) +
          ENNReal.ofReal (Real.exp (-c0 * phi N ^ ζ)) +
          ENNReal.ofReal (Real.exp (-c0 * phi N ^ ζ)) +
          ENNReal.ofReal (Real.exp (-c0 * phi N ^ ζ)) :=
        add_le_add (add_le_add (add_le_add a1 a2) a3) a4
      _ = ENNReal.ofReal (4 * Real.exp (-c0 * phi N ^ ζ)) := by
        rw [← ENNReal.ofReal_add he he, ← ENNReal.ofReal_add (by positivity) he,
          ← ENNReal.ofReal_add (by positivity) he]
        ring_nf
  have hcard := weak_card_le (by omega : 1 ≤ N) (fun p => weakPt N p.1 p.2 ∈ specDomain N K)
  have hu := weak_union_exp (by omega : 1 ≤ N) hc00 hB
  calc _ ≤ L.law (⋃ p ∈ I, weakBad N ζ q Cc Co Cd Ci (weakPt N p.1 p.2)) := measure_mono hsub
    _ ≤ ∑ p ∈ I, L.law (weakBad N ζ q Cc Co Cd Ci (weakPt N p.1 p.2)) :=
        measure_biUnion_finset_le I _
    _ ≤ ∑ _p ∈ I, ENNReal.ofReal (4 * Real.exp (-c0 * phi N ^ ζ)) := Finset.sum_le_sum hbad
    _ = ENNReal.ofReal (I.card • (4 * Real.exp (-c0 * phi N ^ ζ))) := by
        rw [Finset.sum_const, ENNReal.ofReal_nsmul]
    _ ≤ ENNReal.ofReal (Real.exp (-(c0 / 2) * phi N ^ ζ)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [nsmul_eq_mul]
        refine le_trans ?_ hu
        exact mul_le_mul_of_nonneg_right hcard (by positivity)

/-! ### Compiled checks -/

/-- The weak local law for the Rademacher laws with `q = N^{2/5}`, `ζ = 1`, `C0 = 1`: for all
large `N` the hypotheses hold, `i ∈ S(K)`, and the bound applies. -/
example : ∃ K > (0 : ℝ), ∃ C > 0, ∃ c > 0, ∀ᶠ N : ℕ in atTop,
    (⟨0, 1⟩ : ℂ) ∈ specDomain N K ∧
    (radLaws N).law {ω | ∃ z ∈ specDomain N K,
      C * (1 / (N : ℝ) ^ (2 / 5 : ℝ) + phi N ^ (2 * 1 : ℝ) / Real.sqrt (N * z.im)) <
        lamO (symOfEntries ω) z ∨
      C * (phi N ^ (1 : ℝ) / Real.sqrt ((N : ℝ) ^ (2 / 5 : ℝ)) +
        phi N ^ (4 * 1 / 3 : ℝ) / (N * z.im) ^ ((1 : ℝ) / 3)) < lamAvg (symOfEntries ω) z} ≤
      ENNReal.ofReal (Real.exp (-c * phi N ^ (1 : ℝ))) := by
  obtain ⟨K, hK, C, hC, c, hc, N0, h⟩ := weakLocalLaw (ζ := 1) one_pos zero_le_one
  refine ⟨K, hK, C, hC, c, hc, ?_⟩
  filter_upwards [sc_rad_instance K 1, eventually_ge_atTop N0] with N hi hN
  exact ⟨hi.2.2.2.1, h N hN (radLaws N) _ hi.1 hi.2.1 hi.2.2.1⟩

#print axioms weakLocalLaw

/-- The event `Ω(z)` for the Rademacher laws with `q = N^{2/5}`, `ζ = 1`, `C0 = 1`: for all large
`N` the hypotheses hold, `i ∈ S(K)`, and the bound applies. -/
example : ∃ K > (0 : ℝ), ∃ c > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
    (⟨0, 1⟩ : ℂ) ∈ specDomain N K ∧
    (radLaws N).law {ω | ∃ z ∈ specDomain N K,
      (phi N ^ (1 : ℝ))⁻¹ < lamD (symOfEntries ω) z + lamO (symOfEntries ω) z} ≤
      ENNReal.ofReal (Real.exp (-c * phi N ^ (1 : ℝ))) := by
  obtain ⟨K, hK, c, hc, N0, h⟩ := weakLocalLaw_omega (ζ := 1) one_pos zero_le_one
  refine ⟨K, hK, c, hc, ?_⟩
  filter_upwards [sc_rad_instance K 1, eventually_ge_atTop N0] with N hi hN
  exact ⟨hi.2.2.2.1, h N hN (radLaws N) _ hi.1 hi.2.1 hi.2.2.1⟩

#print axioms weakLocalLaw_omega

end WEdgeNS
