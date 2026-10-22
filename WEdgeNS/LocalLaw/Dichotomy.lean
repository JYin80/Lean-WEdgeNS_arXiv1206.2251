import Mathlib

/-!
# The dichotomy for the self-consistent equation
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- Lemma 3.17 of [15]: `w = (1 - m_sc²)/m_sc³`, `v = [v]`, `t = √(κ+η)`, `K` of (3.47);
the case condition `2U²Kβ ≤ t` is equivalent to `η ≥ η̃(U, E)`. -/
theorem dichotomy (Cs K : ℝ) (hCs : 0 < Cs) (hK : 1 ≤ K) :
    ∀ U ≥ 9 * (Cs + 1), ∃ C1 > 0, ∀ (w v : ℂ) (t β δ : ℝ), 0 < t → 0 < β → 0 ≤ δ →
      δ ≤ 1 / 2 → K⁻¹ * t ≤ ‖w‖ → ‖w‖ ≤ K * t →
      ‖w * v - v ^ 2‖ ≤ δ * ‖v‖ ^ 2 + Cs * (β * ‖v‖ + ‖w‖ * β + β ^ 2) →
      (2 * U ^ 2 * K * β ≤ t → ‖v‖ ≤ U * β ∨ ‖w‖ / U ≤ ‖v‖) ∧
      (t < 2 * U ^ 2 * K * β → ‖v‖ ≤ C1 * β) := by
  intro U hU
  have hU9 : 9 ≤ U := by linarith
  have hU0 : 0 < U := by linarith
  set A : ℝ := 2 * U ^ 2 * K ^ 2 with hA
  have hA0 : 0 < A := by positivity
  refine ⟨2 * (A + Cs) + 2 * Cs * (A + 1) + 1, by positivity, ?_⟩
  intro w v t β δ ht hβ hδ0 hδ1 hlow hup hmain
  have habs : |‖w * v‖ - ‖v ^ 2‖| ≤ ‖w * v - v ^ 2‖ := abs_norm_sub_norm_le _ _
  rw [norm_mul, norm_pow] at habs
  have hboth := (abs_le.mp habs)
  have hnorm : ‖w‖ * ‖v‖ - ‖v‖ ^ 2 ≤ δ * ‖v‖ ^ 2 + Cs * (β * ‖v‖ + ‖w‖ * β + β ^ 2) :=
    hboth.2.trans hmain
  have hnorm2 : ‖v‖ ^ 2 - ‖w‖ * ‖v‖ ≤ δ * ‖v‖ ^ 2 + Cs * (β * ‖v‖ + ‖w‖ * β + β ^ 2) := by
    have := hboth.1
    linarith
  have hKpos : 0 < K := by linarith
  have ha : 0 < ‖w‖ := by
    have : 0 < K⁻¹ * t := by positivity
    linarith
  have hx : 0 ≤ ‖v‖ := norm_nonneg v
  generalize ‖w‖ = a at *
  generalize ‖v‖ = x at *
  refine ⟨fun _ => ?_, fun hcase => ?_⟩
  · by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have h2' : U * x < a := by
      have := (lt_div_iff₀ hU0).mp h2
      linarith
    have hUβ : 0 < U * β := by positivity
    have hxpos : 0 < x := by linarith
    have e1 : U * x ^ 2 ≤ a * x := by
      have := mul_le_mul_of_nonneg_right h2'.le hx
      linarith
    have e2 : U * β * x ≤ x ^ 2 := by
      have := mul_le_mul_of_nonneg_right h1.le hx
      linarith
    have e3 : U * β * a ≤ a * x := by
      have := mul_le_mul_of_nonneg_right h1.le ha.le
      linarith
    have e4 : U * U * β ^ 2 ≤ x ^ 2 := by
      have := mul_self_le_mul_self hUβ.le h1.le
      linarith
    have hUx2 : 0 ≤ U * x ^ 2 := by positivity
    have e5 : δ * (U * x ^ 2) ≤ a * x / 2 := by
      have := mul_le_mul_of_nonneg_right hδ1 hUx2
      linarith
    have f2 : 9 * x ^ 2 ≤ a * x := by
      have := mul_le_mul_of_nonneg_right hU9 (sq_nonneg x)
      linarith
    have hUβ2 : 0 ≤ U * β ^ 2 := by positivity
    have f4 : 9 * (U * β ^ 2) ≤ x ^ 2 := by
      have := mul_le_mul_of_nonneg_right hU9 hUβ2
      linarith
    have hax : 0 < a * x := by positivity
    have key : U * (a * x - x ^ 2) ≤
        U * (δ * x ^ 2 + Cs * (β * x + a * β + β ^ 2)) :=
      mul_le_mul_of_nonneg_left hnorm hU0.le
    have g1 : Cs * (U * β * x) ≤ Cs * (a * x / 9) :=
      mul_le_mul_of_nonneg_left (by linarith) hCs.le
    have g2 : Cs * (U * β * a) ≤ Cs * (a * x) := mul_le_mul_of_nonneg_left e3 hCs.le
    have g3 : Cs * (U * β ^ 2) ≤ Cs * (a * x / 81) :=
      mul_le_mul_of_nonneg_left (by linarith) hCs.le
    have hfac : 0 < (U - 3 / 2 - 2 * Cs) * (a * x) := mul_pos (by linarith) hax
    nlinarith [hfac]
  · have hax : a < A * β := by
      have : a ≤ K * t := hup
      have h2 : K * t < K * (2 * U ^ 2 * K * β) := by
        exact mul_lt_mul_of_pos_left hcase hKpos
      have : K * (2 * U ^ 2 * K * β) = A * β := by rw [hA]; ring
      linarith
    by_contra hcon
    push Not at hcon
    have hxb : (2 * (A + Cs) + 2 * Cs * (A + 1) + 1) * β < x := hcon
    have hc0 : 0 ≤ 2 * (A + Cs) + 2 * Cs * (A + 1) := by positivity
    have hxβ : β < x := by
      have : 0 ≤ (2 * (A + Cs) + 2 * Cs * (A + 1)) * β := mul_nonneg hc0 hβ.le
      linarith
    have hxpos : 0 < x := by linarith
    have h0 : δ * x ^ 2 ≤ x ^ 2 / 2 := by
      have := mul_le_mul_of_nonneg_right hδ1 (sq_nonneg x)
      linarith
    have h1 : a * x ≤ A * β * x := mul_le_mul_of_nonneg_right hax.le hx
    have h2 : Cs * (a * β) ≤ Cs * (A * β * β) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hax.le hβ.le) hCs.le
    have h3 : x ^ 2 ≤ 2 * (A + Cs) * β * x + 2 * Cs * (A + 1) * β ^ 2 := by
      linarith
    have h4 : β ^ 2 ≤ β * x := by
      have := mul_le_mul_of_nonneg_left hxβ.le hβ.le
      linarith
    have h5 : x ^ 2 ≤ (2 * (A + Cs) + 2 * Cs * (A + 1)) * β * x := by
      have : 2 * Cs * (A + 1) * β ^ 2 ≤ 2 * Cs * (A + 1) * (β * x) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      linarith
    have h6 : x ≤ (2 * (A + Cs) + 2 * Cs * (A + 1)) * β := by
      by_contra h
      push Not at h
      have := mul_lt_mul_of_pos_right h hxpos
      linarith
    linarith

#print axioms dichotomy

/-- Nondegenerate instances of `dichotomy` at `Cs = K = 1`, `U = 18`: the hypotheses hold at
`w = 1/2`, `t = 1/2`, `δ = 1/2`, with `β = 1/2000` and `v = 1/2500` or `v = 49/100` (first
conjunct, case `2U²Kβ ≤ t`), and with `β = v = 1/100` (second conjunct, case `t < 2U²Kβ`). -/
example : ∃ C1 > (0 : ℝ),
    (‖((4 / 10000 : ℝ) : ℂ)‖ ≤ 18 * (1 / 2000 : ℝ) ∨
      ‖((1 / 2 : ℝ) : ℂ)‖ / 18 ≤ ‖((4 / 10000 : ℝ) : ℂ)‖) ∧
    (‖((49 / 100 : ℝ) : ℂ)‖ ≤ 18 * (1 / 2000 : ℝ) ∨
      ‖((1 / 2 : ℝ) : ℂ)‖ / 18 ≤ ‖((49 / 100 : ℝ) : ℂ)‖) ∧
    ‖((1 / 100 : ℝ) : ℂ)‖ ≤ C1 * (1 / 100) := by
  obtain ⟨C1, hC1, h⟩ := dichotomy 1 1 one_pos le_rfl 18 (by norm_num)
  refine ⟨C1, hC1, ?_, ?_, ?_⟩
  · exact (h ((1 / 2 : ℝ) : ℂ) ((4 / 10000 : ℝ) : ℂ) (1 / 2) (1 / 2000) (1 / 2)
      (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by
        simp only [Complex.norm_real, Real.norm_eq_abs]
        norm_num [abs_of_nonneg]) (by
        simp only [Complex.norm_real, Real.norm_eq_abs]
        norm_num [abs_of_nonneg]) (by
        simp only [← Complex.ofReal_mul, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
        norm_num [abs_of_nonneg])).1 (by norm_num)
  · exact (h ((1 / 2 : ℝ) : ℂ) ((49 / 100 : ℝ) : ℂ) (1 / 2) (1 / 2000) (1 / 2)
      (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by
        simp only [Complex.norm_real, Real.norm_eq_abs]
        norm_num [abs_of_nonneg]) (by
        simp only [Complex.norm_real, Real.norm_eq_abs]
        norm_num [abs_of_nonneg]) (by
        simp only [← Complex.ofReal_mul, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
        norm_num [abs_of_nonneg])).1 (by norm_num)
  · exact (h ((1 / 2 : ℝ) : ℂ) ((1 / 100 : ℝ) : ℂ) (1 / 2) (1 / 100) (1 / 2)
      (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by
        simp only [Complex.norm_real, Real.norm_eq_abs]
        norm_num [abs_of_nonneg]) (by
        simp only [Complex.norm_real, Real.norm_eq_abs]
        norm_num [abs_of_nonneg]) (by
        simp only [← Complex.ofReal_mul, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
        norm_num [abs_of_nonneg])).2 (by norm_num)

end WEdgeNS
