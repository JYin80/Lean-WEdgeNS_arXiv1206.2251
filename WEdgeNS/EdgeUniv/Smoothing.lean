import WEdgeNS.Resolvent.Basic
import WEdgeNS.Model.HighProb

/-!
# The Poisson kernel, smoothed counting functions and the edge cutoff
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- `θ_η(x) = η / (π (x² + η²))`, [26] (6.6), [16] (6.23). -/
def thetaEta (η x : ℝ) : ℝ := η / (Real.pi * (x ^ 2 + η ^ 2))

/-- `Tr (χ_{[E₁,E₂]} * θ_η)(H) = Σ_α ∫_{E₁}^{E₂} θ_η(λ_α - y) dy` ([26] §6). -/
def smoothCount {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) (η E₁ E₂ : ℝ) : ℝ :=
  ∑ α, ∫ y in E₁..E₂, thetaEta η (hH.eigenvalues α - y)

/-- `Tr (χ_{[E₁,E₂]} * θ_η)(H) = (N/π) ∫_{E₁}^{E₂} Im m(y + iη) dy`
([26], proof of Lemma 6.1; [16], after (6.19), where the factor π is missing). -/
theorem smoothCount_eq {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) {η : ℝ}
    (hη : 0 < η) (E₁ E₂ : ℝ) :
    smoothCount hH η E₁ E₂ = N / Real.pi * ∫ y in E₁..E₂, (stieltjesM H ⟨y, η⟩).im := by
  have hcont : ∀ α, Continuous fun y : ℝ => η / ((hH.eigenvalues α - y) ^ 2 + η ^ 2) :=
    fun α => Continuous.div continuous_const (by fun_prop) (fun y => by positivity)
  have him : ∀ y : ℝ, (stieltjesM H ⟨y, η⟩).im =
      (N : ℝ)⁻¹ * ∑ α, η / ((hH.eigenvalues α - y) ^ 2 + η ^ 2) :=
    fun y => im_stieltjesM_eq hH (z := ⟨y, η⟩) hη
  have hth : ∀ α (y : ℝ), thetaEta η (hH.eigenvalues α - y) =
      Real.pi⁻¹ * (η / ((hH.eigenvalues α - y) ^ 2 + η ^ 2)) := by
    intro α y; unfold thetaEta; rw [div_mul_eq_div_div_swap, inv_mul_eq_div]
  simp only [smoothCount, hth, him, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum (fun α _ => (hcont α).intervalIntegrable _ _),
    ← Finset.mul_sum]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have : (N : ℝ) ≠ 0 := by positivity
    field_simp

/-- `N(E₁, E₂) = #{α : E₁ ≤ λ_α ≤ E₂}`. -/
def countIcc {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) (E₁ E₂ : ℝ) : ℕ :=
  (Finset.univ.filter fun α => E₁ ≤ hH.eigenvalues α ∧ hH.eigenvalues α ≤ E₂).card

/-- `N(E, ∞) = #{α : E ≤ λ_α}`. -/
def countIci {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) (E : ℝ) : ℕ :=
  (Finset.univ.filter fun α => E ≤ hH.eigenvalues α).card

/-- `E_L = 2 + 2 φ^C N^{-2/3}` ([26] (6.5), [16] (6.19)). -/
def edgeEL (N : ℕ) (C : ℝ) : ℝ := 2 + 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)

/-- The bump behind the cutoff `K`. -/
def edgeBump : ContDiffBump (0 : ℝ) := ⟨1 / 9, 2 / 9, by norm_num, by norm_num⟩

/-- The smooth cutoff `K` of [16] (6.18) (`q` of [26] §6): `K = 1` on `[-1/9, 1/9]`, `K = 0`
outside `(-2/9, 2/9)`, `0 ≤ K ≤ 1`. -/
def edgeCutoff (x : ℝ) : ℝ := edgeBump x

/-- The properties of `K` used in [26] Corollary 6.2. -/
theorem edgeCutoff_props :
    (∀ n : ℕ, ContDiff ℝ n edgeCutoff) ∧ (∀ x, 0 ≤ edgeCutoff x ∧ edgeCutoff x ≤ 1) ∧
      (∀ x : ℝ, |x| ≤ 1 / 9 → edgeCutoff x = 1) ∧ (∀ x : ℝ, 2 / 9 ≤ |x| → edgeCutoff x = 0) := by
  refine ⟨fun n => edgeBump.contDiff, fun x => ⟨edgeBump.nonneg, edgeBump.le_one⟩,
    fun x hx => edgeBump.one_of_mem_closedBall ?_, fun x hx => ?_⟩
  · simpa [Metric.mem_closedBall, Real.dist_eq, edgeBump] using hx
  · have h : x ∉ Function.support edgeBump := by
      rw [edgeBump.support_eq]
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero, not_lt]
      simpa [edgeBump] using hx
    simpa [edgeCutoff] using h

/-- `F = K(·/π)` satisfies (3.16) and (5.12): derivatives of orders `1–4` are bounded
by `CF (1 + |x|)^CF`. -/
theorem edgeCutoff_deriv_le : ∃ CF > 0, ∀ n ∈ Finset.Icc 1 4, ∀ x : ℝ,
    |iteratedDeriv n (fun x => edgeCutoff (x / Real.pi)) x| ≤ CF * (1 + |x|) ^ CF := by
  set f : ℝ → ℝ := fun x => edgeCutoff (x / Real.pi) with hfdef
  have hsm : ContDiff ℝ 4 f := (edgeBump.contDiff (n := 4)).comp (contDiff_id.div_const _)
  have hcs : HasCompactSupport f := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun x hx => ?_
    apply edgeCutoff_props.2.2.2
    have hx' : 1 < |x| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h
    rw [abs_div, abs_of_pos Real.pi_pos, le_div_iff₀ Real.pi_pos]
    linarith [Real.pi_lt_d2]
  have hcsn : ∀ n, HasCompactSupport (iteratedDeriv n f) := by
    intro n
    induction n with
    | zero => simpa using hcs
    | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv
  have hbd : ∀ m : ℕ, m ≤ 4 → ∃ B : ℝ, ∀ x, |iteratedDeriv m f x| ≤ B := by
    intro m hm
    have hc : Continuous (iteratedDeriv m f) :=
      hsm.continuous_iteratedDeriv m (by exact_mod_cast hm)
    obtain ⟨x₀, hx₀⟩ := hc.norm.exists_forall_ge_of_hasCompactSupport (hcsn m).norm
    exact ⟨‖iteratedDeriv m f x₀‖, fun x => by simpa [Real.norm_eq_abs] using hx₀ x⟩
  obtain ⟨B1, h1⟩ := hbd 1 (by norm_num)
  obtain ⟨B2, h2⟩ := hbd 2 (by norm_num)
  obtain ⟨B3, h3⟩ := hbd 3 (by norm_num)
  obtain ⟨B4, h4⟩ := hbd 4 (by norm_num)
  set CF := 1 + |B1| + |B2| + |B3| + |B4| with hCF
  have hCF0 : 0 < CF := by positivity
  refine ⟨CF, hCF0, fun n hn x => ?_⟩
  have hge : CF ≤ CF * (1 + |x|) ^ CF :=
    le_mul_of_one_le_right hCF0.le (Real.one_le_rpow (by linarith [abs_nonneg x]) hCF0.le)
  have a1 := le_abs_self B1
  have a2 := le_abs_self B2
  have a3 := le_abs_self B3
  have a4 := le_abs_self B4
  have b1 := abs_nonneg B1
  have b2 := abs_nonneg B2
  have b3 := abs_nonneg B3
  have b4 := abs_nonneg B4
  simp only [Finset.mem_Icc] at hn
  obtain ⟨hn1, hn4⟩ := hn
  interval_cases n
  · exact (h1 x).trans (by linarith)
  · exact (h2 x).trans (by linarith)
  · exact (h3 x).trans (by linarith)
  · exact (h4 x).trans (by linarith)


/-- The symmetric matrix `[[0, 1], [1, 0]]` with eigenvalues `±1`. -/
private def smoothingCheckMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

private lemma smoothingCheckMatrix_isHermitian : smoothingCheckMatrix.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [smoothingCheckMatrix]

/-- `smoothCount_eq` at `N = 2`, `H = [[0, 1], [1, 0]]`, `η = 1`, `E₁ = 0 < 1 = E₂`. -/
example : smoothCount smoothingCheckMatrix_isHermitian 1 0 1 =
    (2 : ℕ) / Real.pi * ∫ y in (0 : ℝ)..1, (stieltjesM smoothingCheckMatrix ⟨y, 1⟩).im :=
  smoothCount_eq smoothingCheckMatrix_isHermitian one_pos 0 1

#print axioms smoothCount_eq
#print axioms edgeCutoff_props
#print axioms edgeCutoff_deriv_le

end WEdgeNS
