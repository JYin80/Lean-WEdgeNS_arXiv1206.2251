import WEdgeNS.Model.LambdaMax

/-!
# Resolvent, Stieltjes transform of H, ordered eigenvalues, counting function
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- `G(z) = (H - z)⁻¹` of (2.5), as a complex matrix. -/
def resolventC {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (H.map (fun x : ℝ => (x : ℂ)) - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹

/-- `m(z) = N⁻¹ Tr G(z)` of (2.6). -/
def stieltjesM {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : ℂ :=
  (N : ℂ)⁻¹ * (resolventC H z).trace

/-- Eigenvalues in increasing order: `eigAsc hH j` is `λ_{j+1}` of the paper. -/
def eigAsc {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) (j : Fin N) : ℝ :=
  hH.eigenvalues₀ (Fin.cast (Fintype.card_fin N).symm (Fin.rev j))

/-- `n(E) = N⁻¹ #{j : λ_j ≤ E}` (before Theorem 3.6). -/
def countFn {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) (E : ℝ) : ℝ :=
  ((Finset.univ.filter (fun α => hH.eigenvalues α ≤ E)).card : ℝ) / N

/-- Empirical eigenvalue law `N⁻¹ Σ_α δ_{λ_α}`. -/
def empiricalLaw {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) : Measure ℝ :=
  (N : ENNReal)⁻¹ • ∑ α, Measure.dirac (hH.eigenvalues α)

/-- The real orthogonal eigenvector matrix of a real symmetric matrix: column `α` is the
eigenvector `u_α`, so `eigU hH i α = u_α(i)`. -/
private def eigU {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) :
    Matrix (Fin N) (Fin N) ℝ :=
  (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ)

private lemma eigU_apply {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    (i α : Fin N) : eigU hH i α = hH.eigenvectorBasis α i := by
  simp [eigU, Matrix.IsHermitian.eigenvectorUnitary_apply]

private lemma eigU_mul_transpose {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) :
    eigU hH * (eigU hH)ᵀ = 1 := by
  have := Unitary.coe_mul_star_self hH.eigenvectorUnitary
  rwa [Unitary.coe_star, Matrix.star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial] at this

private lemma eigU_transpose_mul {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) :
    (eigU hH)ᵀ * eigU hH = 1 := by
  have := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  rwa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this

private lemma eigU_spectral {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) :
    H = eigU hH * diagonal hH.eigenvalues * (eigU hH)ᵀ := by
  have := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at this
  simpa [eigU, Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this

/-- The row `i` of the eigenvector matrix has unit norm: `Σ_α u_α(i)² = 1`. -/
private lemma sum_sq_eigenvectorBasis {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (i : Fin N) :
    ∑ α, hH.eigenvectorBasis α i * hH.eigenvectorBasis α i = 1 := by
  have := congrFun (congrFun (eigU_mul_transpose hH) i) i
  simpa [Matrix.mul_apply, eigU_apply] using this

/-- The eigenvector `u_α` has unit norm: `Σ_i u_α(i)² = 1`. -/
private lemma sum_sq_eigenvectorBasis' {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (α : Fin N) :
    ∑ i, hH.eigenvectorBasis α i * hH.eigenvectorBasis α i = 1 := by
  have := congrFun (congrFun (eigU_transpose_mul hH) α) α
  simpa [Matrix.mul_apply, eigU_apply] using this

/-- The complexification of `eigU`. -/
private def eigUc {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) :
    Matrix (Fin N) (Fin N) ℂ :=
  (eigU hH).map (fun x : ℝ => (x : ℂ))

private lemma eigUc_eq {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) :
    eigUc hH = (eigU hH).map Complex.ofRealHom := rfl

private lemma eigUc_mul_transpose {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) :
    eigUc hH * (eigUc hH)ᵀ = 1 := by
  have h : eigUc hH * (eigUc hH)ᵀ = (eigU hH * (eigU hH)ᵀ).map Complex.ofRealHom := by
    rw [eigUc_eq, Matrix.map_mul, Matrix.transpose_map]
  rw [h, eigU_mul_transpose]
  exact Matrix.map_one _ (map_zero _) (map_one _)

private lemma eigUc_transpose_mul {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) :
    (eigUc hH)ᵀ * eigUc hH = 1 := by
  have h : (eigUc hH)ᵀ * eigUc hH = ((eigU hH)ᵀ * eigU hH).map Complex.ofRealHom := by
    rw [eigUc_eq, Matrix.map_mul, Matrix.transpose_map]
  rw [h, eigU_transpose_mul]
  exact Matrix.map_one _ (map_zero _) (map_one _)

private lemma map_eq_eigUc {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) :
    H.map (fun x : ℝ => (x : ℂ)) =
      eigUc hH * diagonal (fun α => (hH.eigenvalues α : ℂ)) * (eigUc hH)ᵀ := by
  have h : H.map Complex.ofRealHom =
      (eigU hH * diagonal hH.eigenvalues * (eigU hH)ᵀ).map Complex.ofRealHom := by
    rw [← eigU_spectral hH]
  have h2 : (eigU hH * diagonal hH.eigenvalues * (eigU hH)ᵀ).map Complex.ofRealHom =
      eigUc hH * diagonal (fun α => (hH.eigenvalues α : ℂ)) * (eigUc hH)ᵀ := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.diagonal_map (map_zero _)]
    rfl
  exact h.trans h2

private lemma sub_smul_one_eq {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    (z : ℂ) : H.map (fun x : ℝ => (x : ℂ)) - z • (1 : Matrix (Fin N) (Fin N) ℂ) =
      eigUc hH * diagonal (fun α => (hH.eigenvalues α : ℂ) - z) * (eigUc hH)ᵀ := by
  have h1 : z • (1 : Matrix (Fin N) (Fin N) ℂ) =
      eigUc hH * diagonal (fun _ : Fin N => z) * (eigUc hH)ᵀ := by
    rw [Matrix.mul_assoc]
    have : diagonal (fun _ : Fin N => z) * (eigUc hH)ᵀ = z • (eigUc hH)ᵀ := by
      rw [← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
    rw [this, Matrix.mul_smul, eigUc_mul_transpose]
  rw [map_eq_eigUc hH, h1, ← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.diagonal_sub]

/-- Conjugating a diagonal matrix by the complexified eigenvector matrix and multiplying
two such conjugates multiplies the diagonals. -/
private lemma conj_diagonal_mul {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    (a b : Fin N → ℂ) :
    eigUc hH * diagonal a * (eigUc hH)ᵀ * (eigUc hH * diagonal b * (eigUc hH)ᵀ) =
      eigUc hH * diagonal (fun α => a α * b α) * (eigUc hH)ᵀ := by
  calc eigUc hH * diagonal a * (eigUc hH)ᵀ * (eigUc hH * diagonal b * (eigUc hH)ᵀ)
      = eigUc hH * (diagonal a * ((eigUc hH)ᵀ * eigUc hH) * diagonal b) * (eigUc hH)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = eigUc hH * diagonal (fun α => a α * b α) * (eigUc hH)ᵀ := by
        rw [eigUc_transpose_mul, Matrix.mul_one, Matrix.diagonal_mul_diagonal]

private lemma resolventC_eq_spectral {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {z : ℂ} (hz : ∀ α, (hH.eigenvalues α : ℂ) ≠ z) :
    resolventC H z =
      eigUc hH * diagonal (fun α => ((hH.eigenvalues α : ℂ) - z)⁻¹) * (eigUc hH)ᵀ := by
  unfold resolventC
  apply Matrix.inv_eq_right_inv
  rw [sub_smul_one_eq hH z, conj_diagonal_mul]
  have : (fun α => ((hH.eigenvalues α : ℂ) - z) * ((hH.eigenvalues α : ℂ) - z)⁻¹) =
      fun _ => (1 : ℂ) := by
    funext α
    exact mul_inv_cancel₀ (sub_ne_zero.mpr (hz α))
  rw [this, Matrix.diagonal_one, Matrix.mul_one, eigUc_mul_transpose]

/-- For `0 < Im z` no real number equals `z`. -/
private lemma eigenvalues_ne_of_im_pos {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (α : Fin N) :
    (hH.eigenvalues α : ℂ) ≠ z := by
  intro h
  have := congrArg Complex.im h
  rw [Complex.ofReal_im] at this
  linarith

/-- Entries of `U D Uᵀ` for a diagonal `D` and the complexified eigenvector matrix `U`. -/
private lemma eigUc_diagonal_apply {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (a : Fin N → ℂ) (i j : Fin N) :
    (eigUc hH * diagonal a * (eigUc hH)ᵀ) i j =
      ∑ α, ((hH.eigenvectorBasis α i * hH.eigenvectorBasis α j : ℝ) : ℂ) * a α := by
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply, eigUc,
    Matrix.map_apply, eigU_apply]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp
  ring

private lemma resolventC_apply_spectral {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {z : ℂ} (hz : ∀ α, (hH.eigenvalues α : ℂ) ≠ z) (i j : Fin N) :
    resolventC H z i j =
      ∑ α, ((hH.eigenvectorBasis α i * hH.eigenvectorBasis α j : ℝ) : ℂ) *
        ((hH.eigenvalues α : ℂ) - z)⁻¹ := by
  rw [resolventC_eq_spectral hH hz, eigUc_diagonal_apply]

theorem monotone_eigAsc {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) :
    Monotone (eigAsc hH) := by
  intro j k hjk
  unfold eigAsc
  apply hH.eigenvalues₀_antitone
  rw [Fin.le_def]
  simp only [Fin.val_cast, Fin.val_rev]
  have := Fin.le_def.mp hjk
  omega

theorem lambdaMax_eq_eigAsc_last {N : ℕ} [NeZero N] {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) : lambdaMax H = eigAsc hH ⟨N - 1, Nat.sub_lt (Nat.pos_of_neZero N) one_pos⟩ := by
  refine (lambdaMax_isGreatest hH).unique ⟨?_, ?_⟩
  · refine ⟨(Fintype.equivOfCardEq (Fintype.card_fin _))
      (Fin.cast (Fintype.card_fin N).symm
        (Fin.rev ⟨N - 1, Nat.sub_lt (Nat.pos_of_neZero N) one_pos⟩)), ?_⟩
    simp [Matrix.IsHermitian.eigenvalues, eigAsc]
  · rintro _ ⟨α, rfl⟩
    refine hH.eigenvalues₀_antitone ?_
    rw [Fin.le_def]
    simp only [Fin.val_cast, Fin.val_rev]
    omega

theorem resolventC_mul_eq_one {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : ∀ α, (hH.eigenvalues α : ℂ) ≠ z) :
    (H.map (fun x : ℝ => (x : ℂ)) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) * resolventC H z = 1 := by
  rw [resolventC_eq_spectral hH hz, sub_smul_one_eq hH z, conj_diagonal_mul]
  have : (fun α => ((hH.eigenvalues α : ℂ) - z) * ((hH.eigenvalues α : ℂ) - z)⁻¹) =
      fun _ => (1 : ℂ) := by
    funext α
    exact mul_inv_cancel₀ (sub_ne_zero.mpr (hz α))
  rw [this, Matrix.diagonal_one, Matrix.mul_one, eigUc_mul_transpose]

/-- Spectral decomposition of `G` (the identity behind (4.44)). -/
theorem resolventC_apply_eq_sum {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : ∀ α, (hH.eigenvalues α : ℂ) ≠ z) (i j : Fin N) :
    resolventC H z i j = ∑ α, ((hH.eigenvectorBasis α i * hH.eigenvectorBasis α j : ℝ) : ℂ) /
      ((hH.eigenvalues α : ℂ) - z) := by
  rw [resolventC_apply_spectral hH hz]
  exact Finset.sum_congr rfl fun α _ => (div_eq_mul_inv _ _).symm

/-- (4.44), exact form. -/
theorem resolventC_sub_apply_eq_sum {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {z w : ℂ} (hz : ∀ α, (hH.eigenvalues α : ℂ) ≠ z)
    (hw : ∀ α, (hH.eigenvalues α : ℂ) ≠ w) (i j : Fin N) :
    resolventC H z i j - resolventC H w i j =
      ∑ α, ((hH.eigenvectorBasis α i * hH.eigenvectorBasis α j : ℝ) : ℂ) * (z - w) /
        (((hH.eigenvalues α : ℂ) - z) * ((hH.eigenvalues α : ℂ) - w)) := by
  rw [resolventC_apply_eq_sum hH hz, resolventC_apply_eq_sum hH hw, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  have h1 : (hH.eigenvalues α : ℂ) - z ≠ 0 := sub_ne_zero.mpr (hz α)
  have h2 : (hH.eigenvalues α : ℂ) - w ≠ 0 := sub_ne_zero.mpr (hw α)
  field_simp
  ring

theorem norm_resolventC_apply_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (i j : Fin N) : ‖resolventC H z i j‖ ≤ 1 / z.im := by
  rw [resolventC_apply_spectral hH (eigenvalues_ne_of_im_pos hH hz) i j]
  have hterm : ∀ α : Fin N,
      ‖((hH.eigenvectorBasis α i * hH.eigenvectorBasis α j : ℝ) : ℂ) *
        ((hH.eigenvalues α : ℂ) - z)⁻¹‖ ≤
      (|hH.eigenvectorBasis α i| * |hH.eigenvectorBasis α j|) / z.im := by
    intro α
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_mul, ← div_eq_mul_inv]
    have him : z.im ≤ ‖(hH.eigenvalues α : ℂ) - z‖ := by
      have := Complex.abs_im_le_norm ((hH.eigenvalues α : ℂ) - z)
      rw [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg, abs_of_pos hz] at this
      exact this
    exact div_le_div_of_nonneg_left (by positivity) hz him
  calc ‖∑ α, ((hH.eigenvectorBasis α i * hH.eigenvectorBasis α j : ℝ) : ℂ) *
        ((hH.eigenvalues α : ℂ) - z)⁻¹‖
      ≤ ∑ α, ‖((hH.eigenvectorBasis α i * hH.eigenvectorBasis α j : ℝ) : ℂ) *
        ((hH.eigenvalues α : ℂ) - z)⁻¹‖ := norm_sum_le _ _
    _ ≤ ∑ α, (|hH.eigenvectorBasis α i| * |hH.eigenvectorBasis α j|) / z.im :=
        Finset.sum_le_sum fun α _ => hterm α
    _ = (∑ α, |hH.eigenvectorBasis α i| * |hH.eigenvectorBasis α j|) / z.im := by
        rw [Finset.sum_div]
    _ ≤ 1 / z.im := by
        gcongr
        calc ∑ α, |hH.eigenvectorBasis α i| * |hH.eigenvectorBasis α j|
            ≤ ∑ α, ((hH.eigenvectorBasis α i * hH.eigenvectorBasis α i +
                hH.eigenvectorBasis α j * hH.eigenvectorBasis α j) / 2) := by
              refine Finset.sum_le_sum fun α _ => ?_
              nlinarith [sq_nonneg (|hH.eigenvectorBasis α i| - |hH.eigenvectorBasis α j|),
                sq_abs (hH.eigenvectorBasis α i), sq_abs (hH.eigenvectorBasis α j)]
          _ = 1 := by
              rw [← Finset.sum_div, Finset.sum_add_distrib, sum_sq_eigenvectorBasis,
                sum_sq_eigenvectorBasis]
              norm_num

theorem im_stieltjesM_eq {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) :
    (stieltjesM H z).im =
      (N : ℝ)⁻¹ * ∑ α, z.im / ((hH.eigenvalues α - z.re) ^ 2 + z.im ^ 2) := by
  have hz' := eigenvalues_ne_of_im_pos hH hz
  have htr : (resolventC H z).trace = ∑ α, ((hH.eigenvalues α : ℂ) - z)⁻¹ := by
    rw [resolventC_eq_spectral hH hz', Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      eigUc_transpose_mul, Matrix.one_mul, Matrix.trace_diagonal]
  have hN : (N : ℂ)⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  unfold stieltjesM
  rw [htr, hN, Complex.im_ofReal_mul, Complex.im_sum]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, zero_sub,
    neg_neg]
  congr 1
  ring

/-- Ward identity: `Σ_j |G_ij|² = η⁻¹ Im G_ii`. -/
theorem sum_norm_sq_resolventC {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (i : Fin N) :
    ∑ j, ‖resolventC H z i j‖ ^ 2 = (resolventC H z i i).im / z.im := by
  have hz' := eigenvalues_ne_of_im_pos hH hz
  have hGH : (resolventC H z)ᴴ =
      eigUc hH * diagonal (fun α => star (((hH.eigenvalues α : ℂ) - z)⁻¹)) *
        (eigUc hH)ᵀ := by
    ext a b
    rw [Matrix.conjTranspose_apply, resolventC_apply_spectral hH hz', eigUc_diagonal_apply,
      star_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [star_mul', Complex.star_def, Complex.conj_ofReal, mul_comm (hH.eigenvectorBasis α b)]
  have hprod : resolventC H z * (resolventC H z)ᴴ =
      eigUc hH * diagonal (fun α => ((hH.eigenvalues α : ℂ) - z)⁻¹ *
        star (((hH.eigenvalues α : ℂ) - z)⁻¹)) * (eigUc hH)ᵀ := by
    rw [hGH, resolventC_eq_spectral hH hz', conj_diagonal_mul]
  have hL : ((∑ j, ‖resolventC H z i j‖ ^ 2 : ℝ) : ℂ) =
      ∑ α, ((hH.eigenvectorBasis α i * hH.eigenvectorBasis α i *
        Complex.normSq (((hH.eigenvalues α : ℂ) - z)⁻¹) : ℝ) : ℂ) := by
    have h := congrFun (congrFun hprod i) i
    rw [eigUc_diagonal_apply] at h
    push_cast
    calc ∑ j, (‖resolventC H z i j‖ : ℂ) ^ 2
        = ∑ j, resolventC H z i j * star (resolventC H z i j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
          push_cast
          rfl
      _ = (resolventC H z * (resolventC H z)ᴴ) i i := by
          simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
      _ = _ := by
          rw [h]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [Complex.star_def, Complex.mul_conj]
          push_cast
          ring
  have hL' : ∑ j, ‖resolventC H z i j‖ ^ 2 =
      ∑ α, hH.eigenvectorBasis α i * hH.eigenvectorBasis α i *
        Complex.normSq (((hH.eigenvalues α : ℂ) - z)⁻¹) := by
    exact_mod_cast hL
  have hR : (resolventC H z i i).im =
      ∑ α, hH.eigenvectorBasis α i * hH.eigenvectorBasis α i *
        (((hH.eigenvalues α : ℂ) - z)⁻¹).im := by
    rw [resolventC_apply_spectral hH hz', Complex.im_sum]
    exact Finset.sum_congr rfl fun α _ => Complex.im_ofReal_mul _ _
  rw [hL', hR, eq_div_iff hz.ne', Finset.sum_mul]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Complex.inv_im, Complex.normSq_inv, Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
  ring

/-! ### Compiled checks at a concrete nondegenerate point

`N = 2`, `H = [[0, 1], [1, 0]]` (symmetric, off-diagonal, eigenvalues `-1` and `1`),
`z = i`, `w = 2i`. -/

private def checkMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

private lemma checkMatrix_isHermitian : checkMatrix.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [checkMatrix]

/-- `G(i) = [[i/2, 1/2], [1/2, i/2]]` for `H = [[0, 1], [1, 0]]`. -/
private lemma resolventC_checkMatrix :
    resolventC checkMatrix Complex.I = !![Complex.I / 2, 1 / 2; 1 / 2, Complex.I / 2] := by
  unfold resolventC
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [checkMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> norm_num

example : stieltjesM checkMatrix Complex.I = Complex.I / 2 := by
  unfold stieltjesM
  rw [resolventC_checkMatrix]
  simp [Matrix.trace, Fin.sum_univ_two]
  ring

example : Monotone (eigAsc checkMatrix_isHermitian) :=
  monotone_eigAsc checkMatrix_isHermitian

example : lambdaMax checkMatrix =
    eigAsc checkMatrix_isHermitian ⟨1, by norm_num⟩ :=
  lambdaMax_eq_eigAsc_last (N := 2) checkMatrix_isHermitian

example : (checkMatrix.map (fun x : ℝ => (x : ℂ)) -
      Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * resolventC checkMatrix Complex.I = 1 :=
  resolventC_mul_eq_one checkMatrix_isHermitian
    (fun α h => by simpa using congrArg Complex.im h)

example (i j : Fin 2) : resolventC checkMatrix Complex.I i j =
    ∑ α, ((checkMatrix_isHermitian.eigenvectorBasis α i *
        checkMatrix_isHermitian.eigenvectorBasis α j : ℝ) : ℂ) /
      ((checkMatrix_isHermitian.eigenvalues α : ℂ) - Complex.I) :=
  resolventC_apply_eq_sum checkMatrix_isHermitian
    (fun α h => by simpa using congrArg Complex.im h) i j

example (i j : Fin 2) : resolventC checkMatrix Complex.I i j -
      resolventC checkMatrix (2 * Complex.I) i j =
    ∑ α, ((checkMatrix_isHermitian.eigenvectorBasis α i *
        checkMatrix_isHermitian.eigenvectorBasis α j : ℝ) : ℂ) * (Complex.I - 2 * Complex.I) /
      (((checkMatrix_isHermitian.eigenvalues α : ℂ) - Complex.I) *
        ((checkMatrix_isHermitian.eigenvalues α : ℂ) - 2 * Complex.I)) :=
  resolventC_sub_apply_eq_sum checkMatrix_isHermitian
    (fun α h => by simpa using congrArg Complex.im h)
    (fun α h => by simpa using congrArg Complex.im h) i j

example : ‖resolventC checkMatrix Complex.I 0 1‖ ≤ 1 / Complex.I.im :=
  norm_resolventC_apply_le checkMatrix_isHermitian (by simp) 0 1

example : (stieltjesM checkMatrix Complex.I).im =
    ((2 : ℕ) : ℝ)⁻¹ * ∑ α, Complex.I.im /
      ((checkMatrix_isHermitian.eigenvalues α - Complex.I.re) ^ 2 + Complex.I.im ^ 2) :=
  im_stieltjesM_eq checkMatrix_isHermitian (by simp)

example : ∑ j, ‖resolventC checkMatrix Complex.I 0 j‖ ^ 2 =
    (resolventC checkMatrix Complex.I 0 0).im / Complex.I.im :=
  sum_norm_sq_resolventC checkMatrix_isHermitian (by simp) 0

#print axioms resolventC
#print axioms stieltjesM
#print axioms eigAsc
#print axioms countFn
#print axioms empiricalLaw
#print axioms monotone_eigAsc
#print axioms lambdaMax_eq_eigAsc_last
#print axioms resolventC_mul_eq_one
#print axioms resolventC_apply_eq_sum
#print axioms resolventC_sub_apply_eq_sum
#print axioms norm_resolventC_apply_le
#print axioms im_stieltjesM_eq
#print axioms sum_norm_sq_resolventC

end WEdgeNS
