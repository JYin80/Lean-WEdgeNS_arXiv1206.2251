import Mathlib

/-!
# The Stieltjes transform m_sc of the semicircle law ((2.7), (2.8), (2.10))
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open Complex in
/-- The branch `√(z-2)·√(z+2)` of `√(z² - 4)` in (2.8): cut `[-2, 2]`, `∼ z` at infinity. -/
def sqrtZ4 (z : ℂ) : ℂ := (z - 2) ^ (1 / 2 : ℂ) * (z + 2) ^ (1 / 2 : ℂ)

/-- `m_sc(z) = (-z + √(z² - 4))/2` of (2.8). -/
def msc (z : ℂ) : ℂ := (-z + sqrtZ4 z) / 2

/-- The principal square root squares back to its argument. -/
private lemma msc_cpow_half_sq (x : ℂ) : (x ^ (1 / 2 : ℂ)) ^ 2 = x := by
  simp [one_div]

/-- The principal square root of a point of the upper half-plane lies in the open first
quadrant. -/
private lemma msc_cpow_half_pos {x : ℂ} (hx : 0 < x.im) :
    0 < (x ^ (1 / 2 : ℂ)).re ∧ 0 < (x ^ (1 / 2 : ℂ)).im := by
  set a : ℂ := x ^ (1 / 2 : ℂ) with ha
  have hsq : a ^ 2 = x := msc_cpow_half_sq x
  have hx0 : x ≠ 0 := by
    intro h
    rw [h] at hx
    simp at hx
  have hre : 0 ≤ a.re := by
    rw [ha, Complex.cpow_def_of_ne_zero hx0, Complex.exp_re]
    refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc ?_)
    have h1 := Complex.neg_pi_lt_arg x
    have h2 := Complex.arg_le_pi x
    have hi : (Complex.log x * (1 / 2 : ℂ)).im = x.arg / 2 := by
      simp [Complex.log_im]
      ring
    rw [hi]
    constructor <;> linarith
  have him : (a ^ 2).im = 2 * a.re * a.im := by
    rw [pow_two, Complex.mul_im]
    ring
  rw [hsq] at him
  have hprod : 0 < a.re * a.im := by linarith
  have hre' : 0 < a.re := by
    rcases hre.lt_or_eq with h | h
    · exact h
    · rw [← h] at hprod
      simp at hprod
  exact ⟨hre', pos_of_mul_pos_right hprod hre'.le⟩

/-- The branch `sqrtZ4` has positive imaginary part on the upper half-plane. -/
private lemma msc_im_sqrtZ4_pos {z : ℂ} (hz : 0 < z.im) : 0 < (sqrtZ4 z).im := by
  have ha := msc_cpow_half_pos (x := z - 2) (by simpa using hz)
  have hb := msc_cpow_half_pos (x := z + 2) (by simpa using hz)
  have h1 := mul_pos ha.1 hb.2
  have h2 := mul_pos ha.2 hb.1
  unfold sqrtZ4
  rw [Complex.mul_im]
  linarith

theorem sqrtZ4_sq (z : ℂ) : sqrtZ4 z ^ 2 = z ^ 2 - 4 := by
  unfold sqrtZ4
  rw [mul_pow, msc_cpow_half_sq, msc_cpow_half_sq]
  ring

/-- The product identity `m (z + m) = -1`, valid for every `z`. -/
private lemma msc_mul_add (z : ℂ) : msc z * (z + msc z) = -1 := by
  have h := sqrtZ4_sq z
  unfold msc
  linear_combination (1 / 4 : ℂ) * h

/-- `z + m` never vanishes. -/
private lemma msc_add_ne_zero (z : ℂ) : z + msc z ≠ 0 := by
  intro h
  have := msc_mul_add z
  rw [h, mul_zero] at this
  norm_num at this

/-- Imaginary part of `m` against the squared modulus of `z + m`. -/
private lemma msc_im_mul_normSq (z : ℂ) :
    (msc z).im * Complex.normSq (z + msc z) = (z + msc z).im := by
  have hu := msc_add_ne_zero z
  have hm : msc z = -(z + msc z)⁻¹ := by
    have := msc_mul_add z
    field_simp
    linear_combination this
  have hn : Complex.normSq (z + msc z) ≠ 0 := (Complex.normSq_pos.2 hu).ne'
  have him : (msc z).im = (z + msc z).im / Complex.normSq (z + msc z) := by
    conv_lhs => rw [hm]
    rw [Complex.neg_im, Complex.inv_im]
    ring
  rw [him]
  field_simp

theorem msc_add_inv_eq_zero {z : ℂ} (hz : 0 < z.im) : msc z + (z + msc z)⁻¹ = 0 := by
  have hu := msc_add_ne_zero z
  have := msc_mul_add z
  field_simp
  linear_combination this

theorem im_msc_pos {z : ℂ} (hz : 0 < z.im) : 0 < (msc z).im := by
  have hs := msc_im_sqrtZ4_pos hz
  have hu : 0 < (z + msc z).im := by
    have : (msc z).im = ((sqrtZ4 z).im - z.im) / 2 := by
      simp [msc, Complex.div_ofNat_im]
      ring
    rw [Complex.add_im, this]
    linarith
  have hn : 0 < Complex.normSq (z + msc z) := Complex.normSq_pos.2 (msc_add_ne_zero z)
  have h := msc_im_mul_normSq z
  by_contra hneg
  rw [not_lt] at hneg
  nlinarith [mul_nonneg (neg_nonneg.2 hneg) hn.le]

theorem eq_msc_of_add_inv {z w : ℂ} (hz : 0 < z.im) (hw : w + (z + w)⁻¹ = 0) (hwi : 0 < w.im) :
    w = msc z := by
  have hzw : z + w ≠ 0 := by
    intro h
    rw [h, _root_.inv_zero, add_zero] at hw
    rw [hw] at hwi
    simp at hwi
  have h1 : w * (z + w) = -1 := by
    field_simp at hw
    linear_combination hw
  have hsq := sqrtZ4_sq z
  have h2 : (2 * w + z - sqrtZ4 z) * (2 * w + z + sqrtZ4 z) = 0 := by
    linear_combination 4 * h1 - hsq
  rcases mul_eq_zero.1 h2 with h | h
  · unfold msc
    linear_combination h / 2
  · exfalso
    have hs := msc_im_sqrtZ4_pos hz
    have := congrArg Complex.im h
    simp at this
    linarith

/-- (2.10). -/
theorem norm_msc_eq_inv_and_lt_one {z : ℂ} (hz : 0 < z.im) :
    ‖msc z‖ = ‖msc z + z‖⁻¹ ∧ ‖msc z‖ < 1 := by
  have hm := msc_mul_add z
  have hmi := im_msc_pos hz
  have hnorm : ‖msc z‖ * ‖z + msc z‖ = 1 := by
    rw [← norm_mul, hm]
    simp
  have hupos : 0 < ‖z + msc z‖ := norm_pos_iff.2 (msc_add_ne_zero z)
  refine ⟨?_, ?_⟩
  · rw [add_comm (msc z) z]
    exact eq_inv_of_mul_eq_one_left hnorm
  · have h := msc_im_mul_normSq z
    rw [Complex.normSq_eq_norm_sq, Complex.add_im] at h
    have hu1 : 1 < ‖z + msc z‖ := by
      by_contra hle
      rw [not_lt] at hle
      nlinarith [mul_nonneg hmi.le (sub_nonneg.2 hle), mul_nonneg hupos.le (sub_nonneg.2 hle)]
    have hm0 : 0 ≤ ‖msc z‖ := norm_nonneg _
    by_contra hge
    rw [not_lt] at hge
    nlinarith

/-- `m_sc(z) ∼ -1/z` at infinity, uniformly in the upper half-plane. -/
theorem tendsto_mul_msc :
    Tendsto (fun z => z * msc z) (Bornology.cobounded ℂ ⊓ 𝓟 {z | 0 < z.im}) (𝓝 (-1)) := by
  set F : Filter ℂ := Bornology.cobounded ℂ ⊓ 𝓟 {z | 0 < z.im} with hF
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) F atTop :=
    tendsto_norm_cobounded_atTop.mono_left inf_le_left
  have hbound : ∀ᶠ z in F, ‖msc z‖ ≤ (‖z‖ - 1)⁻¹ := by
    have hpos : ∀ᶠ z in F, 0 < z.im :=
      eventually_of_mem (mem_inf_of_right (mem_principal_self _)) (fun z hz => hz)
    filter_upwards [hpos, hnorm.eventually_gt_atTop 1] with z hz hz1
    obtain ⟨h1, h2⟩ := norm_msc_eq_inv_and_lt_one hz
    have hu : ‖z‖ - 1 ≤ ‖msc z + z‖ := by
      have := norm_sub_norm_le z (-msc z)
      rw [norm_neg, sub_neg_eq_add, add_comm] at this
      linarith
    rw [h1]
    exact inv_anti₀ (by linarith) hu
  have hzero : Tendsto (fun z : ℂ => (‖z‖ - 1)⁻¹) F (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ (-1) hnorm)
  have hm : Tendsto msc F (𝓝 0) := squeeze_zero_norm' hbound hzero
  have hlim : Tendsto (fun z => -1 - msc z ^ 2) F (𝓝 (-1)) := by
    have := (tendsto_const_nhds (x := (-1 : ℂ))).sub (hm.pow 2)
    simpa using this
  refine hlim.congr' ?_
  filter_upwards with z
  have := msc_mul_add z
  linear_combination -this

/-- `κ = ||E| - 2|`. -/
def kappa (E : ℝ) : ℝ := |(|E| - 2)|

/-- At `z = i` the hypotheses of `eq_msc_of_add_inv` hold for `w = ((√5 - 1)/2) i`, a root of
`w² + z w + 1 = 0` with positive imaginary part, and the conclusion identifies `m_sc(i)`. -/
example : ∃ w : ℂ, 0 < Complex.I.im ∧ w + (Complex.I + w)⁻¹ = 0 ∧ 0 < w.im ∧
    w = msc Complex.I ∧ w = (((Real.sqrt 5 - 1) / 2 : ℝ) : ℂ) * Complex.I := by
  set r : ℝ := (Real.sqrt 5 - 1) / 2 with hr
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : 2 < Real.sqrt 5 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hrpos : 0 < r := by rw [hr]; linarith
  have hrr : r * (1 + r) = 1 := by rw [hr]; nlinarith
  have hwim : (((r : ℝ) : ℂ) * Complex.I).im = r := by simp
  have hinv : (Complex.I + (r : ℂ) * Complex.I)⁻¹ = -((r : ℂ) * Complex.I) := by
    apply inv_eq_of_mul_eq_one_right
    have : (r : ℂ) * (1 + r) = 1 := by exact_mod_cast hrr
    linear_combination this - (r : ℂ) * (1 + r) * Complex.I_sq
  have hw : (r : ℂ) * Complex.I + (Complex.I + (r : ℂ) * Complex.I)⁻¹ = 0 := by
    rw [hinv]; ring
  refine ⟨(r : ℂ) * Complex.I, by simp, hw, by rw [hwim]; exact hrpos, ?_, rfl⟩
  exact eq_msc_of_add_inv (by simp) hw (by rw [hwim]; exact hrpos)

/-- A point with `Re z < 0`, where the principal root of `z² - 4` is the wrong branch: the
imaginary part of `m_sc` is still positive and `‖m_sc‖ < 1`. -/
example : 0 < (msc (-3 + ((1 / 1000 : ℝ) : ℂ) * Complex.I)).im ∧
    ‖msc (-3 + ((1 / 1000 : ℝ) : ℂ) * Complex.I)‖ < 1 :=
  ⟨im_msc_pos (by simp), (norm_msc_eq_inv_and_lt_one (by simp)).2⟩

#print axioms sqrtZ4_sq
#print axioms msc_add_inv_eq_zero
#print axioms im_msc_pos
#print axioms eq_msc_of_add_inv
#print axioms norm_msc_eq_inv_and_lt_one
#print axioms tendsto_mul_msc
#print axioms sqrtZ4
#print axioms msc
#print axioms kappa

end WEdgeNS
