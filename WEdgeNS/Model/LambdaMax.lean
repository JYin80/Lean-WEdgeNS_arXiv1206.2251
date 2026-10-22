import WEdgeNS.Model.Wigner

/-!
# The largest eigenvalue of a real symmetric matrix

Facts about `lambdaMax` used in the proof of Theorem 1.2: identification with the largest
eigenvalue, the Rayleigh bound, an entrywise perturbation bound, the two-entry bound (4.3)–(4.4),
and measurability of `N^{2/3}(λ_N - 2)`.
-/

open Matrix MeasureTheory

namespace WEdgeNS

/-- For a real symmetric matrix of positive size, `lambdaMax` is the largest eigenvalue. -/
theorem lambdaMax_isGreatest {N : ℕ} [NeZero N] {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) : IsGreatest (Set.range hA.eigenvalues) (lambdaMax A) := by
  have hspec : spectrum ℝ A = Set.range hA.eigenvalues := hA.spectrum_real_eq_range_eigenvalues
  unfold lambdaMax
  rw [hspec]
  exact (Set.range_nonempty _).isGreatest_csSup (Set.finite_range _)

/-- A real symmetric matrix is `U D Uᵀ` with `U` orthogonal and `D` the diagonal matrix of its
eigenvalues. -/
private lemma lambdaMax_spectral_decomp {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) :
    ∃ U : Matrix (Fin N) (Fin N) ℝ, U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧
      A = U * diagonal hA.eigenvalues * Uᵀ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ), ?_, ?_, ?_⟩
  · have := Unitary.coe_mul_star_self hA.eigenvectorUnitary
    rwa [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] at this
  · have := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  · have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this

/-- The Rayleigh bound `⟨u, A u⟩ ≤ λ_N ⟨u, u⟩` for a real symmetric matrix `A`. -/
theorem dotProduct_mulVec_le_lambdaMax {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (u : Fin N → ℝ) : u ⬝ᵥ (A *ᵥ u) ≤ lambdaMax A * (u ⬝ᵥ u) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [dotProduct]
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨U, hUU, hUU', hspec⟩ := lambdaMax_spectral_decomp hA
  have hmax := (lambdaMax_isGreatest hA).2
  have h1 : u ⬝ᵥ (A *ᵥ u) = (Uᵀ *ᵥ u) ⬝ᵥ (diagonal hA.eigenvalues *ᵥ (Uᵀ *ᵥ u)) := by
    conv_lhs => rw [hspec]
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  have h2 : u ⬝ᵥ u = (Uᵀ *ᵥ u) ⬝ᵥ (Uᵀ *ᵥ u) := by
    conv_rhs => rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, hUU, one_mulVec]
  rw [h1, h2, dotProduct, dotProduct, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [mulVec_diagonal]
  have := hmax ⟨k, rfl⟩
  nlinarith [sq_nonneg ((Uᵀ *ᵥ u) k)]

/-- The quadratic form of a matrix with all entries of modulus at most `δ` is at most
`N δ ⟨u, u⟩`. -/
private lemma dotProduct_mulVec_le_of_abs_le {N : ℕ} {D : Matrix (Fin N) (Fin N) ℝ} {δ : ℝ}
    (hD : ∀ i j, |D i j| ≤ δ) (hδ : 0 ≤ δ) (u : Fin N → ℝ) :
    u ⬝ᵥ (D *ᵥ u) ≤ N * δ * (u ⬝ᵥ u) := by
  calc u ⬝ᵥ (D *ᵥ u) = ∑ i, ∑ j, u i * D i j * u j := by
        simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
    _ ≤ ∑ i, ∑ j, |u i| * δ * |u j| := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        calc u i * D i j * u j ≤ |u i * D i j * u j| := le_abs_self _
          _ = |u i| * |D i j| * |u j| := by rw [abs_mul, abs_mul]
          _ ≤ |u i| * δ * |u j| := by gcongr; exact hD i j
    _ = δ * (∑ i, |u i|) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ δ * (N * ∑ i, |u i| ^ 2) := by
        gcongr
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |u i|)
    _ = N * δ * (u ⬝ᵥ u) := by
        simp only [sq_abs, dotProduct, ← sq]
        ring

private lemma lambdaMax_sub_le {N : ℕ} [NeZero N] {A B : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {δ : ℝ} (hAB : ∀ i j, |A i j - B i j| ≤ δ) :
    lambdaMax A - lambdaMax B ≤ N * δ := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hAB 0 0)
  obtain ⟨k, hk⟩ := (lambdaMax_isGreatest hA).1
  have hAu : A *ᵥ ⇑(hA.eigenvectorBasis k) = lambdaMax A • ⇑(hA.eigenvectorBasis k) := by
    rw [← hk]; exact hA.mulVec_eigenvectorBasis k
  have huu : (⇑(hA.eigenvectorBasis k)) ⬝ᵥ (⇑(hA.eigenvectorBasis k)) = 1 := by
    have h := orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal k k
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simpa using h
  set u : Fin N → ℝ := ⇑(hA.eigenvectorBasis k) with hu
  have hR := dotProduct_mulVec_le_lambdaMax hB u
  have hD := dotProduct_mulVec_le_of_abs_le (D := A - B) (fun i j => hAB i j) hδ u
  have hsplit : u ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ (B *ᵥ u) + u ⬝ᵥ ((A - B) *ᵥ u) := by
    rw [sub_mulVec, dotProduct_sub]; ring
  rw [hAu, dotProduct_smul, huu] at hsplit
  rw [huu] at hR hD
  simp only [smul_eq_mul, mul_one] at hsplit hR hD
  linarith

/-- Entrywise perturbation bound: `|λ_N(A) - λ_N(B)| ≤ N max_ij |A_ij - B_ij|`. -/
theorem abs_lambdaMax_sub_le {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {δ : ℝ} (hAB : ∀ i j, |A i j - B i j| ≤ δ) :
    |lambdaMax A - lambdaMax B| ≤ N * δ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Subsingleton.elim A B]; simp
  have : NeZero N := ⟨hN.ne'⟩
  have h1 := lambdaMax_sub_le hA hB hAB
  have h2 := lambdaMax_sub_le hB hA fun i j => by rw [abs_sub_comm]; exact hAB i j
  rw [abs_le]
  constructor <;> linarith

/-- (4.3)–(4.4): one off-diagonal entry of size at least `4` and two diagonal entries of size at
most `1` in the same rows force `λ_N ≥ 3`. -/
theorem three_le_lambdaMax {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    {i j : Fin N} (hij : i ≠ j) (h4 : 4 ≤ |A i j|) (hi : |A i i| ≤ 1) (hj : |A j j| ≤ 1) :
    3 ≤ lambdaMax A := by
  obtain ⟨s, hs, hsA⟩ : ∃ s : ℝ, s * s = 1 ∧ s * A i j = |A i j| := by
    rcases le_total 0 (A i j) with h | h
    · exact ⟨1, by norm_num, by rw [abs_of_nonneg h]; ring⟩
    · exact ⟨-1, by norm_num, by rw [abs_of_nonpos h]; ring⟩
  have hji : A j i = A i j := by
    have := congrFun (congrFun hA.eq i) j
    simpa [conjTranspose_apply] using this
  set v : Fin N → ℝ := Pi.single i 1 + s • Pi.single j 1 with hv
  have hvv : v ⬝ᵥ v = 2 := by
    simp [hv, dotProduct_add, hij, hij.symm]
    linarith
  have hvAv : v ⬝ᵥ (A *ᵥ v) = A i i + A j j + 2 * |A i j| := by
    simp only [hv, mulVec_add, mulVec_single, MulOpposite.op_one, one_smul, mulVec_smul,
      dotProduct_add, add_dotProduct, single_dotProduct, col_apply, one_mul, smul_dotProduct,
      smul_eq_mul, dotProduct_smul]
    rw [hji]
    linear_combination 2 * hsA + A j j * hs
  have h := dotProduct_mulVec_le_lambdaMax hA v
  rw [hvv, hvAv] at h
  have h1 := abs_le.mp hi
  have h2 := abs_le.mp hj
  linarith

/-- Entries of `H_N` depend on the entry vector in a `(√N)⁻¹`-Lipschitz way. -/
private lemma abs_wignerMatrix_sub_le (N : ℕ) (ω ω' : Entries N) (i j : Fin N) :
    |wignerMatrix N ω i j - wignerMatrix N ω' i j| ≤ (Real.sqrt N)⁻¹ * dist ω ω' := by
  have hinv : 0 ≤ (Real.sqrt N)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  unfold wignerMatrix
  rw [← mul_sub, abs_mul, abs_of_nonneg hinv]
  refine mul_le_mul_of_nonneg_left ?_ hinv
  rw [Prod.dist_eq]
  split_ifs
  · rw [← Real.dist_eq]
    exact (dist_le_pi_dist ω.1 ω'.1 i).trans (le_max_left _ _)
  · rw [← Real.dist_eq]
    exact (dist_le_pi_dist ω.2 ω'.2 _).trans (le_max_right _ _)
  · rw [← Real.dist_eq]
    exact (dist_le_pi_dist ω.2 ω'.2 _).trans (le_max_right _ _)

/-- `λ_N(H_N)` is a continuous function of the entries. -/
theorem continuous_lambdaMax_wignerMatrix (N : ℕ) :
    Continuous fun ω : Entries N => lambdaMax (wignerMatrix N ω) := by
  have hlip : LipschitzWith (Real.sqrt N).toNNReal
      (fun ω : Entries N => lambdaMax (wignerMatrix N ω)) := by
    refine LipschitzWith.of_dist_le_mul fun ω ω' => ?_
    rw [Real.dist_eq, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
    refine (abs_lambdaMax_sub_le (wignerMatrix_isHermitian N ω) (wignerMatrix_isHermitian N ω')
      (abs_wignerMatrix_sub_le N ω ω')).trans (le_of_eq ?_)
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
      have key : (N : ℝ) * (Real.sqrt N)⁻¹ = Real.sqrt N := by
        field_simp
        exact (Real.sq_sqrt (Nat.cast_nonneg _)).symm
      rw [← mul_assoc, key]
  exact hlip.continuous

/-- `N^{2/3}(λ_N - 2)` is a measurable function of the entries. -/
theorem measurable_edgeScaled (N : ℕ) : Measurable (edgeScaled N) := by
  have h : Continuous (edgeScaled N) :=
    continuous_const.mul ((continuous_lambdaMax_wignerMatrix N).sub continuous_const)
  exact h.measurable

/-- A nondegenerate instance of `three_le_lambdaMax`: the symmetric matrix with off-diagonal entry
`5` and diagonal entries `1/2` and `-1`. -/
example : 3 ≤ lambdaMax !![(1 / 2 : ℝ), 5; 5, -1] := by
  have hA : (!![(1 / 2 : ℝ), 5; 5, -1]).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  exact three_le_lambdaMax hA (i := 0) (j := 1) (by decide) (by norm_num [abs_of_nonneg])
    (by norm_num [abs_of_nonneg]) (by norm_num)

#print axioms lambdaMax_isGreatest
#print axioms dotProduct_mulVec_le_lambdaMax
#print axioms abs_lambdaMax_sub_le
#print axioms three_le_lambdaMax
#print axioms continuous_lambdaMax_wignerMatrix
#print axioms measurable_edgeScaled

end WEdgeNS
