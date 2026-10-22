import WEdgeNS.Resolvent.Basic

/-!
# Spectral consequences of the resolvent: Stieltjes form, free intervals, monotonicity, counting
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- The eigenvector `u_α` has unit norm: `Σ_i u_α(i)² = 1`. -/
lemma eigenvectorBasis_sum_mul_self {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (α : Fin N) :
    ∑ i, hH.eigenvectorBasis α i * hH.eigenvectorBasis α i = 1 := by
  have h := (hH.eigenvectorBasis).norm_eq_one α
  have h2 := EuclideanSpace.real_norm_sq_eq (hH.eigenvectorBasis α)
  rw [h] at h2
  simp only [one_pow] at h2
  rw [h2]
  exact Finset.sum_congr rfl fun i _ => (sq _).symm

/-- For `Im z > 0` no eigenvalue of `H` equals `z`: `λ_α - z ≠ 0`. -/
lemma eigenvalue_sub_ne_zero_of_im_pos {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (α : Fin N) :
    (hH.eigenvalues α : ℂ) - z ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

/-- `m(z) = N⁻¹ Σ_α (λ_α - z)⁻¹`. -/
lemma stieltjesM_eq_sum {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    stieltjesM H z = (N : ℂ)⁻¹ * ∑ α, ((hH.eigenvalues α : ℂ) - z)⁻¹ := by
  have hz' : ∀ α, (hH.eigenvalues α : ℂ) ≠ z :=
    fun α h => eigenvalue_sub_ne_zero_of_im_pos hH hz α (sub_eq_zero.mpr h)
  unfold stieltjesM
  congr 1
  unfold Matrix.trace
  simp only [Matrix.diag_apply, resolventC_apply_eq_sum hH hz']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.sum_div]
  have : ∑ i, (((hH.eigenvectorBasis α i * hH.eigenvectorBasis α i : ℝ)) : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, eigenvectorBasis_sum_mul_self hH α]; simp
  rw [this, one_div]

/-- `Im m(x + iy) = N⁻¹ Σ_α y / ((λ_α - x)² + y²)`. -/
private lemma im_stieltjesM_eq_real {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (stieltjesM H (x + y * Complex.I)).im =
      (N : ℝ)⁻¹ * ∑ α, y / ((hH.eigenvalues α - x) ^ 2 + y ^ 2) := by
  have hz : 0 < (x + y * Complex.I).im := by simpa using hy
  have := im_stieltjesM_eq hH hz
  simpa using this

theorem stieltjesM_eq_resolventTransform {N : ℕ} [NeZero N] {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    stieltjesM H z = resolventTransform (empiricalLaw hH) z := by
  rw [stieltjesM_eq_sum hH hz, resolventTransform_apply, empiricalLaw, integral_smul_measure,
    integral_finsetSum_measure]
  · have hN : ((N : ENNReal)⁻¹).toReal = (N : ℝ)⁻¹ := by
      rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rw [hN]
    simp only [integral_dirac' _ _ (measurable_resolvent (𝕜 := ℝ) (a := z)).stronglyMeasurable]
    rw [Complex.real_smul]
    push_cast
    simp [resolvent, Ring.inverse_eq_inv']
  · intro α _
    exact integrable_dirac enorm_lt_top

/-- Eigenvalue-free interval criterion (proof of (5.17)):
`Im m(E + iη) < (2Nη)⁻¹` forces `[E - η, E + η]` to contain no eigenvalue. -/
theorem lt_abs_eigenvalues_sub_of_im_stieltjesM_lt {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {E η : ℝ} (hη : 0 < η)
    (h : (stieltjesM H (E + η * Complex.I)).im < 1 / (2 * N * η)) (α : Fin N) :
    η < |hH.eigenvalues α - E| := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos α
  rw [im_stieltjesM_eq_real hH E hη] at h
  by_contra hcon
  rw [not_lt, abs_le] at hcon
  have hterm : 1 / (2 * η) ≤ η / ((hH.eigenvalues α - E) ^ 2 + η ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hcon.1, hcon.2, mul_nonneg (sub_nonneg.mpr hcon.2) (neg_le_iff_add_nonneg.mp hcon.1)]
  have hsum : η / ((hH.eigenvalues α - E) ^ 2 + η ^ 2) ≤
      ∑ β, η / ((hH.eigenvalues β - E) ^ 2 + η ^ 2) :=
    Finset.single_le_sum (f := fun β => η / ((hH.eigenvalues β - E) ^ 2 + η ^ 2))
      (fun β _ => by positivity) (Finset.mem_univ α)
  have h2 : (N : ℝ)⁻¹ * (1 / (2 * η)) ≤ (N : ℝ)⁻¹ *
      ∑ β, η / ((hH.eigenvalues β - E) ^ 2 + η ^ 2) :=
    mul_le_mul_of_nonneg_left (hterm.trans hsum) (by positivity)
  have h3 : (N : ℝ)⁻¹ * (1 / (2 * η)) = 1 / (2 * N * η) := by
    field_simp
  linarith

/-- `y ↦ y Im m(x + iy)` is increasing ((5.7)). -/
theorem monotoneOn_mul_im_stieltjesM {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (x : ℝ) :
    MonotoneOn (fun y : ℝ => y * (stieltjesM H (x + y * Complex.I)).im) (Set.Ioi 0) := by
  intro y₁ hy₁ y₂ hy₂ hle
  have hy₁' : 0 < y₁ := hy₁
  have hy₂' : 0 < y₂ := hy₂
  have key : ∀ y : ℝ, 0 < y → y * (stieltjesM H (x + y * Complex.I)).im =
      (N : ℝ)⁻¹ * ∑ α, y * y / ((hH.eigenvalues α - x) ^ 2 + y ^ 2) := by
    intro y hy
    rw [im_stieltjesM_eq_real hH x hy]
    rw [mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [mul_div_assoc]
  simp only
  rw [key y₁ hy₁', key y₂ hy₂']
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun α _ => ?_) (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have ha := sq_nonneg (hH.eigenvalues α - x)
  nlinarith [mul_nonneg ha (sub_nonneg.mpr (mul_self_le_mul_self hy₁'.le hle))]

/-- `|∂_η m(x + iη)| ≤ η⁻¹ Im m(x + iη)` ((5.5)–(5.6)). -/
theorem norm_deriv_stieltjesM_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖deriv (fun t : ℝ => stieltjesM H (x + t * Complex.I)) y‖ ≤
      (stieltjesM H (x + y * Complex.I)).im / y := by
  have hne : ∀ t : ℝ, 0 < t → ∀ α, (hH.eigenvalues α : ℂ) - (x + t * Complex.I) ≠ 0 :=
    fun t ht α =>
      eigenvalue_sub_ne_zero_of_im_pos hH (z := x + t * Complex.I) (by simpa using ht) α
  have hterm : ∀ α : Fin N, HasDerivAt
      (fun t : ℝ => ((hH.eigenvalues α : ℂ) - (x + t * Complex.I))⁻¹)
      ((-Complex.I) • (-(((hH.eigenvalues α : ℂ) - (x + y * Complex.I)) ^ 2)⁻¹)) y := by
    intro α
    have hc : HasDerivAt (fun t : ℝ => (hH.eigenvalues α : ℂ) - (x + t * Complex.I))
        (-Complex.I) y := by
      have := (((hasDerivAt_id y).ofReal_comp.mul_const Complex.I).const_add (x : ℂ)).const_sub
        (hH.eigenvalues α : ℂ)
      simpa using this
    exact (hasDerivAt_inv (hne y hy α)).scomp y hc
  have hf : HasDerivAt (fun t : ℝ => (N : ℂ)⁻¹ * ∑ α, ((hH.eigenvalues α : ℂ) -
        (x + t * Complex.I))⁻¹)
      ((N : ℂ)⁻¹ * ∑ α, ((-Complex.I) •
        (-(((hH.eigenvalues α : ℂ) - (x + y * Complex.I)) ^ 2)⁻¹))) y :=
    (HasDerivAt.fun_sum (fun α _ => hterm α)).const_mul _
  have hev : (fun t : ℝ => stieltjesM H (x + t * Complex.I)) =ᶠ[𝓝 y]
      (fun t : ℝ => (N : ℂ)⁻¹ * ∑ α, ((hH.eigenvalues α : ℂ) - (x + t * Complex.I))⁻¹) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact stieltjesM_eq_sum hH (by simpa using (ht : 0 < t))
  rw [(hf.congr_of_eventuallyEq hev).deriv]
  rw [im_stieltjesM_eq_real hH x hy]
  rw [norm_mul, norm_inv, Complex.norm_natCast, mul_div_assoc, Finset.sum_div]
  gcongr
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun α _ => ?_
  have hu : ‖(hH.eigenvalues α : ℂ) - (x + y * Complex.I)‖ ^ 2 =
      (hH.eigenvalues α - x) ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [smul_eq_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, norm_neg, norm_inv, norm_pow,
    hu, div_div_cancel_left' hy.ne']

/-- Counting bound (5.10): `n(x + η) - n(x - η) ≤ 2η Im m(x + iη)`. -/
theorem countFn_sub_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    (x : ℝ) {η : ℝ} (hη : 0 < η) :
    countFn hH (x + η) - countFn hH (x - η) ≤
      2 * η * (stieltjesM H (x + η * Complex.I)).im := by
  rw [im_stieltjesM_eq_real hH x hη]
  unfold countFn
  rw [← sub_div, div_eq_inv_mul, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  set A := Finset.univ.filter (fun α => hH.eigenvalues α ≤ x + η)
  set B := Finset.univ.filter (fun α => hH.eigenvalues α ≤ x - η)
  have hBA : B ⊆ A := by
    intro α hα
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hα ⊢
    linarith
  have hcard : (A.card : ℝ) - B.card = ((A \ B).card : ℝ) := by
    rw [Finset.card_sdiff_of_subset hBA, Nat.cast_sub (Finset.card_le_card hBA)]
  rw [hcard]
  have h1 : ∀ α ∈ A \ B, 1 / (2 * η) ≤ η / ((hH.eigenvalues α - x) ^ 2 + η ^ 2) := by
    intro α hα
    simp only [A, B, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      not_le] at hα
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : hH.eigenvalues α - x ≤ η := by linarith [hα.1]
    have h2 : -η ≤ hH.eigenvalues α - x := by linarith [hα.2]
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (neg_le_iff_add_nonneg.mp h2)]
  have h2 : ((A \ B).card : ℝ) * (1 / (2 * η)) ≤
      ∑ α ∈ A \ B, η / ((hH.eigenvalues α - x) ^ 2 + η ^ 2) := by
    have := Finset.card_nsmul_le_sum (A \ B) _ _ h1
    simpa [nsmul_eq_mul] using this
  have h3 : ∑ α ∈ A \ B, η / ((hH.eigenvalues α - x) ^ 2 + η ^ 2) ≤
      ∑ α, η / ((hH.eigenvalues α - x) ^ 2 + η ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
  have h4 := h2.trans h3
  rw [mul_one_div, div_le_iff₀ (by positivity)] at h4
  linarith

/-! ### Compiled checks at a concrete nondegenerate point

`N = 2`, `H = [[0, 1], [1, 0]]` (symmetric, eigenvalues `-1` and `1`). -/

private def spectralCheckMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

private lemma spectralCheckMatrix_isHermitian : spectralCheckMatrix.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spectralCheckMatrix]

/-- `G(w) = (w² - 1)⁻¹ [[-w, -1], [-1, -w]]` for `H = [[0, 1], [1, 0]]`. -/
private lemma resolventC_spectralCheckMatrix {w : ℂ} (hw : w ^ 2 - 1 ≠ 0) :
    resolventC spectralCheckMatrix w =
      !![-w / (w ^ 2 - 1), -1 / (w ^ 2 - 1); -1 / (w ^ 2 - 1), -w / (w ^ 2 - 1)] := by
  unfold resolventC
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spectralCheckMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    field_simp <;> ring

private lemma stieltjesM_spectralCheckMatrix_five :
    stieltjesM spectralCheckMatrix (5 + 1 * Complex.I) = (-125 + 27 * Complex.I) / 629 := by
  have hw : (5 + 1 * Complex.I) ^ 2 - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [pow_two] at this
  unfold stieltjesM
  rw [resolventC_spectralCheckMatrix hw]
  simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply]
  simp
  have h23 : (23 + 10 * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have : ((5 : ℂ) + Complex.I) ^ 2 - 1 = 23 + 10 * Complex.I := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [this]
  field_simp
  rw [div_eq_iff (by simpa [mul_comm] using h23)]
  linear_combination (-540) * Complex.I_sq

/-- Eigenvalue-free interval at `E = 5`, `η = 1`: `Im m = 27/629 < 1/4`. -/
example : ∀ α : Fin 2, 1 < |spectralCheckMatrix_isHermitian.eigenvalues α - 5| := by
  refine lt_abs_eigenvalues_sub_of_im_stieltjesM_lt spectralCheckMatrix_isHermitian
    (E := 5) (η := 1) one_pos ?_
  have h := stieltjesM_spectralCheckMatrix_five
  simp only [Complex.ofReal_ofNat, Complex.ofReal_one]
  rw [h]
  have : ((-125 + 27 * Complex.I) / 629 : ℂ) = ((-125 / 629 : ℝ) : ℂ) +
      ((27 / 629 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this]
  simp
  norm_num

example : stieltjesM spectralCheckMatrix Complex.I =
    resolventTransform (empiricalLaw spectralCheckMatrix_isHermitian) Complex.I :=
  stieltjesM_eq_resolventTransform spectralCheckMatrix_isHermitian (by simp)

example : MonotoneOn (fun y : ℝ => y * (stieltjesM spectralCheckMatrix (0 + y * Complex.I)).im)
    (Set.Ioi 0) :=
  monotoneOn_mul_im_stieltjesM spectralCheckMatrix_isHermitian 0

example : ‖deriv (fun t : ℝ => stieltjesM spectralCheckMatrix (0 + t * Complex.I)) 2‖ ≤
    (stieltjesM spectralCheckMatrix (0 + 2 * Complex.I)).im / 2 :=
  norm_deriv_stieltjesM_le spectralCheckMatrix_isHermitian 0 (by norm_num)

example : countFn spectralCheckMatrix_isHermitian (0 + 1) -
      countFn spectralCheckMatrix_isHermitian (0 - 1) ≤
    2 * 1 * (stieltjesM spectralCheckMatrix (0 + 1 * Complex.I)).im :=
  countFn_sub_le spectralCheckMatrix_isHermitian 0 one_pos

#print axioms stieltjesM_eq_resolventTransform
#print axioms lt_abs_eigenvalues_sub_of_im_stieltjesM_lt
#print axioms monotoneOn_mul_im_stieltjesM
#print axioms norm_deriv_stieltjesM_le
#print axioms countFn_sub_le

end WEdgeNS
