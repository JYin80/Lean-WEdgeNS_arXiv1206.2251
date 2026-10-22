import WEdgeNS.Model.LambdaMax

/-!
# Finite-rank perturbation: the determinant criterion (4.32) and a one-sided barrier
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- A real number lies in the spectrum of a real square matrix `M` iff `det (M - μ) = 0`. -/
lemma mem_spectrum_iff_det_eq_zero {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} {μ : ℝ} :
    μ ∈ spectrum ℝ M ↔ (M - μ • (1 : Matrix (Fin N) (Fin N) ℝ)).det = 0 := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, ← neg_sub, IsUnit.neg_iff,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]

/-- If `μ` is not in the spectrum of `H`, then `det (H - μ)` is a unit. -/
private lemma isUnit_det_sub_smul_one_of_not_mem_spectrum {N : ℕ}
    {H : Matrix (Fin N) (Fin N) ℝ} {μ : ℝ} (hμ : μ ∉ spectrum ℝ H) :
    IsUnit (H - μ • (1 : Matrix (Fin N) (Fin N) ℝ)).det := by
  rw [isUnit_iff_ne_zero]
  exact fun h => hμ (mem_spectrum_iff_det_eq_zero.mpr h)

/-- (4.32)–(4.33): `det(H + γVDVᵀ - μ) = det(H - μ) det(γD) det((γD)⁻¹ + Vᵀ(H - μ)⁻¹V)`. -/
theorem det_add_smul_lowRank {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix (Fin N) (Fin N) ℝ) (V : Matrix (Fin N) ι ℝ) (D : Matrix ι ι ℝ) {γ μ : ℝ}
    (hD : IsUnit D.det) (hγ : γ ≠ 0) (hμ : μ ∉ spectrum ℝ H) :
    (H + γ • (V * D * Vᵀ) - μ • (1 : Matrix (Fin N) (Fin N) ℝ)).det =
      (H - μ • (1 : Matrix (Fin N) (Fin N) ℝ)).det * (γ • D).det *
        ((γ • D)⁻¹ + Vᵀ * (H - μ • (1 : Matrix (Fin N) (Fin N) ℝ))⁻¹ * V).det := by
  have hA := isUnit_det_sub_smul_one_of_not_mem_spectrum hμ
  have hγD : IsUnit (γ • D).det := by
    rw [Matrix.det_smul]
    exact (hγ.isUnit.pow _).mul hD
  have h1 : H + γ • (V * D * Vᵀ) - μ • (1 : Matrix (Fin N) (Fin N) ℝ) =
      (H - μ • (1 : Matrix (Fin N) (Fin N) ℝ)) + V * ((γ • D) * Vᵀ) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
    abel
  have h2 : (1 : Matrix ι ι ℝ) + ((γ • D) * Vᵀ) * (H - μ • (1 : Matrix (Fin N) (Fin N) ℝ))⁻¹ * V =
      (γ • D) * ((γ • D)⁻¹ + Vᵀ * (H - μ • (1 : Matrix (Fin N) (Fin N) ℝ))⁻¹ * V) := by
    have hinv : (γ • D) * (γ • D)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ hγD
    rw [Matrix.mul_add, hinv]
    simp only [Matrix.mul_assoc]
  rw [h1, Matrix.det_add_mul V _ hA, h2, Matrix.det_mul]
  ring

/-- (4.32)–(4.33): for `μ ∉ spec(H)`, `μ ∈ spec(H + γVDVᵀ)` iff `det F^γ(μ) = 0`. -/
theorem mem_spectrum_add_smul_lowRank_iff {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix (Fin N) (Fin N) ℝ) (V : Matrix (Fin N) ι ℝ) (D : Matrix ι ι ℝ) {γ μ : ℝ}
    (hD : IsUnit D.det) (hγ : γ ≠ 0) (hμ : μ ∉ spectrum ℝ H) :
    μ ∈ spectrum ℝ (H + γ • (V * D * Vᵀ)) ↔
      ((γ • D)⁻¹ + Vᵀ * (H - μ • (1 : Matrix (Fin N) (Fin N) ℝ))⁻¹ * V).det = 0 := by
  have hA := (isUnit_det_sub_smul_one_of_not_mem_spectrum hμ).ne_zero
  have hγD : (γ • D).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hγ) hD.ne_zero
  rw [mem_spectrum_iff_det_eq_zero, det_add_smul_lowRank H V D hD hγ hμ]
  rw [mul_eq_zero, mul_eq_zero]
  tauto

/-- A real symmetric matrix is `U D Uᵀ` with `UᵀU = 1` and `D` the diagonal matrix of its
eigenvalues. -/
private lemma spectral_decomp_aux {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) :
    ∃ U : Matrix (Fin N) (Fin N) ℝ, Uᵀ * U = 1 ∧ A = U * diagonal hA.eigenvalues * Uᵀ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ), ?_, ?_⟩
  · have := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  · have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this

/-- Every real symmetric `E` is `V D Vᵀ` with `D` diagonal invertible and `Vᵀ V = 1`,
the number of columns being `rank E` ((4.27)). -/
theorem exists_lowRank_decomp {N : ℕ} {E : Matrix (Fin N) (Fin N) ℝ} (hE : E.IsHermitian) :
    ∃ (V : Matrix (Fin N) (Fin E.rank) ℝ) (d : Fin E.rank → ℝ),
      (∀ k, d k ≠ 0) ∧ Vᵀ * V = 1 ∧ E = V * diagonal d * Vᵀ := by
  obtain ⟨U, hUU, hspec⟩ := spectral_decomp_aux hE
  have hcard : Fintype.card (Fin E.rank) = Fintype.card { i // hE.eigenvalues i ≠ 0 } := by
    rw [Fintype.card_fin]; exact hE.rank_eq_card_non_zero_eigs
  let e : Fin E.rank ≃ { i // hE.eigenvalues i ≠ 0 } := Fintype.equivOfCardEq hcard
  refine ⟨U.submatrix id (fun k => (e k).1), fun k => hE.eigenvalues (e k).1,
    fun k => (e k).2, ?_, ?_⟩
  · ext k l
    have h := congrFun (congrFun hUU (e k).1) (e l).1
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Matrix.submatrix_apply,
      id] at h ⊢
    rw [h]
    simp only [Subtype.val_inj, e.apply_eq_iff_eq]
  · have key : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (W : Matrix (Fin N) κ ℝ) (f : κ → ℝ)
        (i j : Fin N), (W * diagonal f * Wᵀ) i j = ∑ m, W i m * f m * W j m := by
      intro κ _ _ W f i j
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
    ext i j
    have h1 : E i j = ∑ m, U i m * hE.eigenvalues m * U j m := by
      have := key U hE.eigenvalues i j
      rwa [← hspec] at this
    rw [key, h1]
    simp only [Matrix.submatrix_apply, id]
    rw [Equiv.sum_comp e (fun s : { i // hE.eigenvalues i ≠ 0 } =>
      U i s.1 * hE.eigenvalues s.1 * U j s.1)]
    rw [← Finset.sum_subtype (Finset.univ.filter fun m => hE.eigenvalues m ≠ 0)
      (fun m => by simp) (fun m => U i m * hE.eigenvalues m * U j m)]
    symm
    refine Finset.sum_filter_of_ne fun m _ hm h => hm ?_
    rw [h]
    ring

/-- `H + γ E` is symmetric for symmetric `H`, `E` and real `γ`. -/
private lemma isHermitian_add_smul {N : ℕ} {H E : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (hE : E.IsHermitian) (γ : ℝ) : (H + γ • E).IsHermitian :=
  hH.add (hE.smul (IsSelfAdjoint.all γ))

theorem continuous_lambdaMax_add_smul {N : ℕ} {H E : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (hE : E.IsHermitian) :
    Continuous fun γ : ℝ => lambdaMax (H + γ • E) := by
  set S : ℝ := ∑ i, ∑ j, |E i j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hEij : ∀ i j, |E i j| ≤ S := fun i j =>
    (Finset.single_le_sum (f := fun j => |E i j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, |E i j|)
        (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i))
  have hK : (0 : ℝ) ≤ N * S := mul_nonneg (Nat.cast_nonneg N) hS0
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (N * S)) fun γ γ' => ?_).continuous
  rw [Real.coe_toNNReal _ hK, Real.dist_eq, Real.dist_eq]
  refine (abs_lambdaMax_sub_le (isHermitian_add_smul hH hE γ) (isHermitian_add_smul hH hE γ')
    (δ := |γ - γ'| * S) fun i j => ?_).trans ?_
  · have : (H + γ • E) i j - (H + γ' • E) i j = (γ - γ') * E i j := by
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
    rw [this, abs_mul]
    exact mul_le_mul_of_nonneg_left (hEij i j) (abs_nonneg _)
  · exact le_of_eq (by ring)

/-- Rayleigh lower bound: `λ_N(H) + ⟨u, Eu⟩ ≤ λ_N(H + E)` for a unit top eigenvector `u`. -/
theorem lambdaMax_add_dotProduct_le {N : ℕ} {H E : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (hE : E.IsHermitian) {u : Fin N → ℝ} (hu : u ⬝ᵥ u = 1)
    (huH : H *ᵥ u = lambdaMax H • u) : lambdaMax H + u ⬝ᵥ (E *ᵥ u) ≤ lambdaMax (H + E) := by
  have h := dotProduct_mulVec_le_lambdaMax (hH.add hE) u
  rw [add_mulVec, dotProduct_add, huH, dotProduct_smul, hu, smul_eq_mul, mul_one, mul_one] at h
  exact h

/-- `⟨u, Eu⟩ ≥ -M · #supp(E) · max_i u_i²`. -/
theorem neg_le_dotProduct_mulVec {N : ℕ} {E : Matrix (Fin N) (Fin N) ℝ} {M b : ℝ}
    (hM : ∀ i j, |E i j| ≤ M) {u : Fin N → ℝ} (hb : ∀ i, u i ^ 2 ≤ b) :
    -(M * (Finset.univ.filter (fun p : Fin N × Fin N => E p.1 p.2 ≠ 0)).card * b) ≤
      u ⬝ᵥ (E *ᵥ u) := by
  set s := Finset.univ.filter (fun p : Fin N × Fin N => E p.1 p.2 ≠ 0) with hs
  have hdot : u ⬝ᵥ (E *ᵥ u) = ∑ p : Fin N × Fin N, u p.1 * E p.1 p.2 * u p.2 := by
    rw [Fintype.sum_prod_type]
    simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have hsupp : ∑ p : Fin N × Fin N, u p.1 * E p.1 p.2 * u p.2 =
      ∑ p ∈ s, u p.1 * E p.1 p.2 * u p.2 := by
    symm
    refine Finset.sum_filter_of_ne fun p _ hp h => hp ?_
    rw [h]; ring
  have hterm : ∀ p ∈ s, -(M * b) ≤ u p.1 * E p.1 p.2 * u p.2 := by
    intro p _
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM p.1 p.2)
    have hu1 : |u p.1 * u p.2| ≤ b := by
      rw [abs_mul]
      nlinarith [hb p.1, hb p.2, sq_abs (u p.1), sq_abs (u p.2), sq_nonneg (|u p.1| - |u p.2|)]
    have h1 : |u p.1 * E p.1 p.2 * u p.2| ≤ M * b := by
      calc |u p.1 * E p.1 p.2 * u p.2| = |E p.1 p.2| * |u p.1 * u p.2| := by
            rw [show u p.1 * E p.1 p.2 * u p.2 = E p.1 p.2 * (u p.1 * u p.2) by ring, abs_mul]
        _ ≤ M * b := mul_le_mul (hM p.1 p.2) hu1 (abs_nonneg _) hM0
    exact neg_le_of_abs_le h1
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  rw [hdot, hsupp]
  calc -(M * (s.card : ℝ) * b) = (s.card : ℝ) * -(M * b) := by ring
    _ ≤ _ := hsum

/-- One-sided barrier for (4.26): if `μ > λ_N(H)` is not an
eigenvalue of `H + γE` for any `γ ∈ (0, 1]`, then `λ_N(H + E) < μ`. -/
theorem lambdaMax_add_lt_of_barrier {N : ℕ} [NeZero N] {H E : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (hE : E.IsHermitian) {μ : ℝ} (hμ : lambdaMax H < μ)
    (hnot : ∀ γ ∈ Set.Ioc (0 : ℝ) 1, μ ∉ spectrum ℝ (H + γ • E)) : lambdaMax (H + E) < μ := by
  by_contra hcon
  replace hcon : μ ≤ lambdaMax (H + E) := not_lt.mp hcon
  have hf := continuous_lambdaMax_add_smul hH hE
  have h0 : lambdaMax (H + (0 : ℝ) • E) = lambdaMax H := by simp
  have h1 : lambdaMax (H + (1 : ℝ) • E) = lambdaMax (H + E) := by simp
  have hmem : μ ∈ Set.Icc (lambdaMax (H + (0 : ℝ) • E)) (lambdaMax (H + (1 : ℝ) • E)) :=
    ⟨by rw [h0]; exact hμ.le, by rw [h1]; exact hcon⟩
  obtain ⟨γ, hγ, hγμ'⟩ := intermediate_value_Icc (zero_le_one' ℝ) hf.continuousOn hmem
  have hγμ : lambdaMax (H + γ • E) = μ := hγμ'
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [h0] at hγμ
    exact hμ.ne hγμ
  refine hnot γ ⟨lt_of_le_of_ne hγ.1 (Ne.symm hγ0), hγ.2⟩ ?_
  have hHerm := isHermitian_add_smul hH hE γ
  rw [← hγμ]
  rw [hHerm.spectrum_real_eq_range_eigenvalues]
  exact (lambdaMax_isGreatest hHerm).1

/-- (4.32) instance: `H = diag(1, -1)`, `V` the two vectors `(e₁ ± e₂)/√2`, `D = diag(1, -1)`,
`γ = 1`, `μ = 0 ∉ spec(H)`. -/
example : IsUnit (diagonal ![(1 : ℝ), -1]).det ∧ (1 : ℝ) ≠ 0 := by
  refine ⟨?_, one_ne_zero⟩
  simp [Matrix.det_diagonal, Fin.prod_univ_two]

/-- The matrix `diag(1, -1)` of the compiled instances below. -/
private def exH : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![1, -1]

/-- The matrix `[[0, 1], [1, 0]]` of the compiled instances below. -/
private def exE : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- The columns `(1, 1)` and `(1, -1)`, with `exV * exD * exVᵀ = exE`. -/
private def exV : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, -1]

/-- The diagonal matrix `diag(1/2, -1/2)`. -/
private def exD : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![1 / 2, -1 / 2]

private lemma exH_isHermitian : exH.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exH, Matrix.conjTranspose_apply]

private lemma exE_isHermitian : exE.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exE, Matrix.conjTranspose_apply]

private lemma exV_mul_exD_mul_transpose : exV * exD * exVᵀ = exE := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exV, exD, exE, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul_diagonal] <;>
    norm_num

private lemma exH_sub_smul_det (μ : ℝ) : (exH - μ • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det =
    (1 - μ) * (-1 - μ) := by
  simp [exH, Matrix.det_fin_two]

private lemma lambdaMax_exH : lambdaMax exH = 1 := by
  have hspec : spectrum ℝ exH = Set.range ![(1 : ℝ), -1] := spectrum_diagonal _
  unfold lambdaMax
  rw [hspec]
  refine le_antisymm (csSup_le (Set.range_nonempty _) ?_)
    (le_csSup (Set.finite_range _).bddAbove ⟨0, rfl⟩)
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> norm_num

/-- (4.32) instance: `H = diag(1, -1)`, `V = [[1, 1], [1, -1]]`, `D = diag(1/2, -1/2)`
(so `V D Vᵀ = [[0, 1], [1, 0]]`), `γ = 1`, `μ = 0 ∉ spec(H)`; both sides equal `-2`. -/
example :
    (exH + (1 : ℝ) • (exV * exD * exVᵀ) - (0 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = -2 ∧
    (exH + (1 : ℝ) • (exV * exD * exVᵀ) - (0 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det =
      (exH - (0 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det * ((1 : ℝ) • exD).det *
        (((1 : ℝ) • exD)⁻¹ +
          exVᵀ * (exH - (0 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ * exV).det := by
  have hμ : (0 : ℝ) ∉ spectrum ℝ exH := fun h => by
    have := mem_spectrum_iff_det_eq_zero.mp h
    rw [exH_sub_smul_det] at this
    norm_num at this
  have hD : IsUnit exD.det := by
    simp [exD]
  refine ⟨?_, det_add_smul_lowRank exH exV exD hD one_ne_zero hμ⟩
  rw [exV_mul_exD_mul_transpose]
  simp [exH, exE, Matrix.det_fin_two]
  norm_num

private lemma exD_isUnit_det : IsUnit exD.det := by
  simp [exD]

private lemma det_exH_add_exE_sub (μ : ℝ) :
    (exH + (1 : ℝ) • (exV * exD * exVᵀ) - μ • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det =
      μ ^ 2 - 2 := by
  rw [exV_mul_exD_mul_transpose]
  simp [exH, exE, Matrix.det_fin_two]
  ring

/-- (4.32)–(4.33) instance, same data: `√2 ∈ spec(H + V D Vᵀ)` and `det F(√2) = 0`. -/
example : Real.sqrt 2 ∈ spectrum ℝ (exH + (1 : ℝ) • (exV * exD * exVᵀ)) ∧
    (((1 : ℝ) • exD)⁻¹ + exVᵀ * (exH - Real.sqrt 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ * exV).det =
      0 := by
  have hμ : Real.sqrt 2 ∉ spectrum ℝ exH := fun h => by
    have := mem_spectrum_iff_det_eq_zero.mp h
    rw [exH_sub_smul_det] at this
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hmem : Real.sqrt 2 ∈ spectrum ℝ (exH + (1 : ℝ) • (exV * exD * exVᵀ)) := by
    rw [mem_spectrum_iff_det_eq_zero, det_exH_add_exE_sub]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  exact ⟨hmem,
    (mem_spectrum_add_smul_lowRank_iff exH exV exD exD_isUnit_det one_ne_zero hμ).mp hmem⟩

/-- (4.32)–(4.33) instance, same data: `0 ∉ spec(H + V D Vᵀ)` and `det F(0) ≠ 0`. -/
example : (0 : ℝ) ∉ spectrum ℝ (exH + (1 : ℝ) • (exV * exD * exVᵀ)) ∧
    (((1 : ℝ) • exD)⁻¹ + exVᵀ * (exH - (0 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ * exV).det ≠
      0 := by
  have hμ : (0 : ℝ) ∉ spectrum ℝ exH := fun h => by
    have := mem_spectrum_iff_det_eq_zero.mp h
    rw [exH_sub_smul_det] at this
    norm_num at this
  have hnot : (0 : ℝ) ∉ spectrum ℝ (exH + (1 : ℝ) • (exV * exD * exVᵀ)) := fun h => by
    have := mem_spectrum_iff_det_eq_zero.mp h
    rw [det_exH_add_exE_sub] at this
    norm_num at this
  exact ⟨hnot, fun h => hnot
    ((mem_spectrum_add_smul_lowRank_iff exH exV exD exD_isUnit_det one_ne_zero hμ).mpr h)⟩

/-- (4.27) instance: `E = [[0, 1], [1, 0]]` has rank `2`, so the decomposition has two columns. -/
example : exE.rank = 2 ∧ ∃ (V : Matrix (Fin 2) (Fin exE.rank) ℝ) (d : Fin exE.rank → ℝ),
    (∀ k, d k ≠ 0) ∧ Vᵀ * V = 1 ∧ exE = V * diagonal d * Vᵀ := by
  refine ⟨?_, exists_lowRank_decomp exE_isHermitian⟩
  rw [Matrix.rank_of_isUnit]
  · simp
  · rw [Matrix.isUnit_iff_isUnit_det]
    simp [exE, Matrix.det_fin_two]

/-- Continuity instance: `γ ↦ λ_N(diag(1, -1) + γ [[0, 1], [1, 0]])` is continuous, and equals
`1` at `γ = 0`. -/
example : Continuous (fun γ : ℝ => lambdaMax (exH + γ • exE)) ∧
    lambdaMax (exH + (0 : ℝ) • exE) = 1 := by
  refine ⟨continuous_lambdaMax_add_smul exH_isHermitian exE_isHermitian, ?_⟩
  rw [zero_smul, add_zero, lambdaMax_exH]

/-- Rayleigh-bound instance: `H = diag(1, -1)`, `u = e₁`, `E = [[-1/2, 1], [1, 0]]` give
`1/2 ≤ λ_N(H + E)`. -/
example : (1 : ℝ) / 2 ≤ lambdaMax (exH + !![-1 / 2, 1; 1, 0]) := by
  have hE : (!![-1 / 2, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  have hu : (![1, 0] : Fin 2 → ℝ) ⬝ᵥ ![1, 0] = 1 := by
    simp [dotProduct, Fin.sum_univ_two]
  have huH : exH *ᵥ (![1, 0] : Fin 2 → ℝ) = lambdaMax exH • ![1, 0] := by
    rw [lambdaMax_exH]
    ext i
    fin_cases i <;> simp [exH, Matrix.mulVec_diagonal]
  have h := lambdaMax_add_dotProduct_le exH_isHermitian hE hu huH
  have hq : (![1, 0] : Fin 2 → ℝ) ⬝ᵥ ((!![-1 / 2, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![1, 0]) =
      -1 / 2 := by
    simp [dotProduct, Fin.sum_univ_two, Matrix.mulVec]
  rw [lambdaMax_exH, hq] at h
  linarith

/-- Instance of the lower bound on the quadratic form: `E = (3/4) [[0, 1], [1, 0]]` with two
nonzero entries, `u = (1, -1)`, `M = 3/4`, `b = 1`; the bound `-3/2` is attained. -/
example :
    (Finset.univ.filter (fun p : Fin 2 × Fin 2 =>
      ((3 / 4 : ℝ) • exE) p.1 p.2 ≠ 0)).card = 2 ∧
    ![(1 : ℝ), -1] ⬝ᵥ (((3 / 4 : ℝ) • exE) *ᵥ ![1, -1]) = -3 / 2 ∧
    -((3 / 4 : ℝ) * 2 * 1) ≤ ![(1 : ℝ), -1] ⬝ᵥ (((3 / 4 : ℝ) • exE) *ᵥ ![1, -1]) := by
  have hcard : (Finset.univ.filter (fun p : Fin 2 × Fin 2 =>
      ((3 / 4 : ℝ) • exE) p.1 p.2 ≠ 0)).card = 2 := by
    have : (Finset.univ.filter (fun p : Fin 2 × Fin 2 =>
        ((3 / 4 : ℝ) • exE) p.1 p.2 ≠ 0)) = {(0, 1), (1, 0)} := by
      ext ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> simp [exE]
    rw [this]
    decide
  have hM : ∀ i j, |((3 / 4 : ℝ) • exE) i j| ≤ 3 / 4 := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [exE, abs_of_pos]
  have hb : ∀ i, (![(1 : ℝ), -1] : Fin 2 → ℝ) i ^ 2 ≤ 1 := by
    intro i
    fin_cases i <;> simp
  have h := neg_le_dotProduct_mulVec hM hb
  rw [hcard] at h
  refine ⟨hcard, ?_, by simpa using h⟩
  simp [dotProduct, Fin.sum_univ_two, Matrix.mulVec, exE]
  norm_num

/-- One-sided barrier instance: `H = diag(1, -1)`, `E = [[0, 1], [1, 0]]`, `μ = 2`; here
`λ_N(H) = 1 < 2`, and `det (H + γE - 2) = 3 - γ² > 0` on `(0, 1]`, so `λ_N(H + E) < 2`. -/
example : lambdaMax (exH + exE) < 2 := by
  refine lambdaMax_add_lt_of_barrier exH_isHermitian exE_isHermitian ?_ ?_
  · rw [lambdaMax_exH]; norm_num
  · intro γ hγ h
    have := mem_spectrum_iff_det_eq_zero.mp h
    simp [exH, exE, Matrix.det_fin_two] at this
    nlinarith [hγ.1, hγ.2]

#print axioms det_add_smul_lowRank
#print axioms mem_spectrum_add_smul_lowRank_iff
#print axioms exists_lowRank_decomp
#print axioms continuous_lambdaMax_add_smul
#print axioms lambdaMax_add_dotProduct_le
#print axioms neg_le_dotProduct_mulVec
#print axioms lambdaMax_add_lt_of_barrier

end WEdgeNS
