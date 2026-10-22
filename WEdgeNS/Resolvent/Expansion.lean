import WEdgeNS.Resolvent.Basic

/-!
# Finite resolvent expansions and the rank bound for traces ((3.28), (3.30), (6.47), (6.81))
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- Finite resolvent expansion: `A⁻¹ = Σ_{k<n} (B⁻¹(B - A))^k B⁻¹ + (B⁻¹(B - A))^n A⁻¹`. -/
theorem inv_eq_sum_add {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [Field 𝕜]
    {A B : Matrix ι ι 𝕜} (hA : IsUnit A.det) (hB : IsUnit B.det) (n : ℕ) :
    A⁻¹ = ∑ k ∈ Finset.range n, (B⁻¹ * (B - A)) ^ k * B⁻¹ + (B⁻¹ * (B - A)) ^ n * A⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have key : A⁻¹ = B⁻¹ + B⁻¹ * (B - A) * A⁻¹ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.nonsing_inv_mul _ hB, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]
      abel
    rw [Finset.sum_range_succ, add_assoc, pow_succ, Matrix.mul_assoc _ (B⁻¹ * (B - A)) A⁻¹,
      ← Matrix.mul_add, ← key]
    exact ih

/-- For `0 < Im z` no real number equals `z`. -/
private lemma eigenvalues_ne_of_im_pos' {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (α : Fin N) : (hH.eigenvalues α : ℂ) ≠ z := by
  intro h
  have := congrArg Complex.im h
  rw [Complex.ofReal_im] at this
  linarith

/-- `H - z` is invertible for a real symmetric `H` and `0 < Im z`. -/
private lemma isUnit_det_sub_smul_one {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    IsUnit (H.map (fun x : ℝ => (x : ℂ)) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det :=
  Matrix.isUnit_det_of_right_inverse
    (resolventC_mul_eq_one hH (eigenvalues_ne_of_im_pos' hH hz))

/-- `(Q + V) - z = (Q - z) + V` for the entrywise complex cast. -/
private lemma add_sub_smul_one {N : ℕ} (Q V : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    (Q + V).map (fun x : ℝ => (x : ℂ)) - z • (1 : Matrix (Fin N) (Fin N) ℂ) =
      (Q.map (fun x : ℝ => (x : ℂ)) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) +
        V.map (fun x : ℝ => (x : ℂ)) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.map_apply, Complex.ofReal_add]
  ring

/-- `((Q + V) - z) - (Q - z) = V` for the entrywise complex cast. -/
private lemma sub_sub_smul_one {N : ℕ} (Q V : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    ((Q + V).map (fun x : ℝ => (x : ℂ)) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) -
      (Q.map (fun x : ℝ => (x : ℂ)) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) =
        V.map (fun x : ℝ => (x : ℂ)) := by
  rw [add_sub_smul_one]
  abel

/-- `(Q - z) - ((Q + V) - z) = -V` for the entrywise complex cast. -/
private lemma sub_sub_smul_one_neg {N : ℕ} (Q V : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    (Q.map (fun x : ℝ => (x : ℂ)) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) -
      ((Q + V).map (fun x : ℝ => (x : ℂ)) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) =
        -V.map (fun x : ℝ => (x : ℂ)) := by
  rw [← neg_sub, sub_sub_smul_one]

/-- (3.28): `R = Σ_{k<5} (SV)^k S + (SV)^5 R` with `R = (Q - z)⁻¹`, `S = (Q + V - z)⁻¹`. -/
theorem resolventC_expansion_left {N : ℕ} {Q V : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Q.IsHermitian) (hV : V.IsHermitian) {z : ℂ} (hz : 0 < z.im) (n : ℕ) :
    resolventC Q z = ∑ k ∈ Finset.range n,
        (resolventC (Q + V) z * V.map (fun x : ℝ => (x : ℂ))) ^ k * resolventC (Q + V) z +
      (resolventC (Q + V) z * V.map (fun x : ℝ => (x : ℂ))) ^ n * resolventC Q z := by
  have h := inv_eq_sum_add (isUnit_det_sub_smul_one hQ hz)
    (isUnit_det_sub_smul_one (hQ.add hV) hz) n
  rw [sub_sub_smul_one] at h
  exact h

/-- (3.30), (6.47): `S = Σ_{k ≤ n} (-RV)^k R + (-RV)^{n+1} S`. -/
theorem resolventC_expansion_right {N : ℕ} {Q V : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Q.IsHermitian) (hV : V.IsHermitian) {z : ℂ} (hz : 0 < z.im) (n : ℕ) :
    resolventC (Q + V) z = ∑ k ∈ Finset.range (n + 1),
        (-(resolventC Q z * V.map (fun x : ℝ => (x : ℂ)))) ^ k * resolventC Q z +
      (-(resolventC Q z * V.map (fun x : ℝ => (x : ℂ)))) ^ (n + 1) * resolventC (Q + V) z := by
  have h := inv_eq_sum_add (isUnit_det_sub_smul_one (hQ.add hV) hz)
    (isUnit_det_sub_smul_one hQ hz) (n + 1)
  rw [sub_sub_smul_one_neg, Matrix.mul_neg] at h
  exact h

/-- The entrywise complex cast of a real symmetric matrix is Hermitian. -/
private lemma isHermitian_map_ofReal {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Q.IsHermitian) : (Q.map (fun x : ℝ => (x : ℂ))).IsHermitian := by
  ext i j
  have := hQ.apply i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
  rw [← this]
  simp

/-- A real multiple of `q qᵀ` is Hermitian. -/
private lemma isHermitian_smul_vecMulVec {N : ℕ} (q : Fin N → ℝ) (τ : ℝ) :
    (τ • Matrix.vecMulVec q q).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    star_trivial]
  ring

/-- Rank-one case of (6.81): a real symmetric perturbation `τ q qᵀ` changes the trace of the
resolvent by at most `1/η`. -/
private lemma norm_trace_sub_le_rankOne {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Q.IsHermitian) (q : Fin N → ℝ) (τ : ℝ) {z : ℂ} (hz : 0 < z.im) :
    ‖(resolventC (Q + τ • Matrix.vecMulVec q q) z).trace - (resolventC Q z).trace‖ ≤
      1 / z.im := by
  classical
  set P : Matrix (Fin N) (Fin N) ℝ := τ • Matrix.vecMulVec q q with hP
  set qc : Fin N → ℂ := fun i => (q i : ℂ) with hqc
  set A : Matrix (Fin N) (Fin N) ℂ :=
    Q.map (fun x : ℝ => (x : ℂ)) - z • (1 : Matrix (Fin N) (Fin N) ℂ) with hA
  set R := resolventC Q z with hR
  set S := resolventC (Q + P) z with hS
  have hRA : R = A⁻¹ := rfl
  have hPc : P.map (fun x : ℝ => (x : ℂ)) = (τ : ℂ) • Matrix.vecMulVec qc qc := by
    ext i j
    simp [hP, hqc, Matrix.vecMulVec_apply]
  have hAR : A * R = 1 := resolventC_mul_eq_one hQ (eigenvalues_ne_of_im_pos' hQ hz)
  have hBS : (A + (τ : ℂ) • Matrix.vecMulVec qc qc) * S = 1 := by
    have := resolventC_mul_eq_one (hQ.add (isHermitian_smul_vecMulVec q τ)) (z := z)
      (eigenvalues_ne_of_im_pos' _ hz)
    rwa [add_sub_smul_one, hPc] at this
  have hSB : S * (A + (τ : ℂ) • Matrix.vecMulVec qc qc) = 1 := mul_eq_one_comm.mp hBS
  have hQt : Qᵀ = Q := by
    have := hQ.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hAsymm : Aᵀ = A := by
    have h1 : (Q.map (fun x : ℝ => (x : ℂ)))ᵀ = Q.map (fun x : ℝ => (x : ℂ)) := by
      rw [← Matrix.transpose_map, hQt]
    rw [hA, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, h1]
  have hRsymm : Rᵀ = R := by
    rw [hRA, Matrix.transpose_nonsing_inv, hAsymm]
  set w : Fin N → ℂ := R *ᵥ qc with hw
  have hAw : A *ᵥ w = qc := by
    rw [hw, Matrix.mulVec_mulVec, hAR, Matrix.one_mulVec]
  set g : ℂ := qc ⬝ᵥ w with hg
  set u : ℂ := 1 + (τ : ℂ) * g with hu
  have hBw : (A + (τ : ℂ) • Matrix.vecMulVec qc qc) *ᵥ w = u • qc := by
    have hv : Matrix.vecMulVec qc qc *ᵥ w = g • qc := by
      ext i
      simp [Matrix.vecMulVec_mulVec, hg, mul_comm]
    rw [Matrix.add_mulVec, hAw, Matrix.smul_mulVec, hv, hu, add_smul, one_smul, smul_smul]
  have hu0 : u ≠ 0 := by
    intro h0
    have h1 : w = 0 := by
      have := congrArg (fun v => S *ᵥ v) hBw
      simp only [Matrix.mulVec_mulVec, hSB, Matrix.one_mulVec, h0, zero_smul,
        Matrix.mulVec_zero] at this
      exact this
    have : g = 0 := by rw [hg, h1]; simp
    rw [hu, this] at h0
    simp at h0
  have hSq : S *ᵥ qc = u⁻¹ • w := by
    have := congrArg (fun v => S *ᵥ v) hBw
    simp only [Matrix.mulVec_mulVec, hSB, Matrix.one_mulVec, Matrix.mulVec_smul] at this
    rw [this, smul_smul, inv_mul_cancel₀ hu0, one_smul]
  have hSR : S - R = -((τ : ℂ) • (S * Matrix.vecMulVec qc qc * R)) := by
    have h1 : S - R = S * (A - (A + (τ : ℂ) • Matrix.vecMulVec qc qc)) * R := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hAR, Matrix.mul_one,
        hSB, Matrix.one_mul]
    rw [h1, sub_add_cancel_left, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  have hvec : qc ᵥ* R = w := by
    rw [hw, ← Matrix.vecMul_transpose R qc, hRsymm]
  have htr : S.trace - R.trace = -((τ : ℂ) * (u⁻¹ * (w ⬝ᵥ w))) := by
    rw [← Matrix.trace_sub, hSR, Matrix.trace_neg, Matrix.trace_smul, Matrix.mul_vecMulVec,
      Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, hSq, hvec, smul_dotProduct, smul_eq_mul,
      smul_eq_mul]
  have hQh := isHermitian_map_ofReal hQ
  have hstar_qc : star qc = qc := by
    ext i
    simp [hqc]
  set ρ : ℝ := ∑ i, Complex.normSq (w i) with hρ
  have hρ0 : 0 ≤ ρ := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hρc : star w ⬝ᵥ w = (ρ : ℂ) := by
    rw [hρ, dotProduct]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    rfl
  have hward : g.im = z.im * ρ := by
    have h1 : star w ⬝ᵥ (A *ᵥ w) = star w ⬝ᵥ qc := by rw [hAw]
    have h2 : star w ⬝ᵥ (A *ᵥ w) =
        star w ⬝ᵥ (Q.map (fun x : ℝ => (x : ℂ)) *ᵥ w) - z * (star w ⬝ᵥ w) := by
      rw [hA, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
    have h3 : star w ⬝ᵥ qc = star g := by
      rw [star_dotProduct, hstar_qc]
    have h0 : (star w ⬝ᵥ (Q.map (fun x : ℝ => (x : ℂ)) *ᵥ w)).im = 0 :=
      hQh.im_star_dotProduct_mulVec_self w
    have him := congrArg Complex.im h1
    rw [h2, h3, hρc, Complex.sub_im, h0, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.star_def, Complex.conj_im] at him
    linarith
  have him_u : u.im = τ * g.im := by simp [hu]
  have hub : |τ| * (z.im * ρ) ≤ ‖u‖ := by
    calc |τ| * (z.im * ρ) = |u.im| := by
          rw [him_u, hward, abs_mul, abs_of_nonneg (mul_nonneg hz.le hρ0)]
      _ ≤ ‖u‖ := Complex.abs_im_le_norm u
  have hww : ‖w ⬝ᵥ w‖ ≤ ρ := by
    calc ‖∑ i, w i * w i‖ ≤ ∑ i, ‖w i * w i‖ := norm_sum_le _ _
      _ = ρ := by
          rw [hρ]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_mul, Complex.normSq_eq_norm_sq, sq]
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  rw [htr, norm_neg, norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    le_div_iff₀ hz]
  calc |τ| * (‖u‖⁻¹ * ‖w ⬝ᵥ w‖) * z.im = (|τ| * z.im * ‖w ⬝ᵥ w‖) / ‖u‖ := by
        field_simp
    _ ≤ 1 := by
        rw [div_le_one hupos]
        calc |τ| * z.im * ‖w ⬝ᵥ w‖ ≤ |τ| * z.im * ρ :=
              mul_le_mul_of_nonneg_left hww (by positivity)
          _ = |τ| * (z.im * ρ) := by ring
          _ ≤ ‖u‖ := hub

/-- Entry `(i, j)` of a finite sum of real symmetric rank-one matrices. -/
private lemma sum_smul_vecMulVec_apply {N : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (u : ι → Fin N → ℝ) (i j : Fin N) :
    (∑ a ∈ s, c a • Matrix.vecMulVec (u a) (u a)) i j = ∑ a ∈ s, c a * (u a i * u a j) := by
  simp [Matrix.sum_apply, Matrix.vecMulVec_apply]

/-- A finite sum of real multiples of `u u ᵀ` is Hermitian. -/
private lemma isHermitian_sum_smul_vecMulVec {N : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (u : ι → Fin N → ℝ) : (∑ a ∈ s, c a • Matrix.vecMulVec (u a) (u a)).IsHermitian := by
  ext i j
  rw [Matrix.conjTranspose_apply, star_trivial, sum_smul_vecMulVec_apply,
    sum_smul_vecMulVec_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- (6.81) for a sum of `s.card` real symmetric rank-one matrices. -/
private lemma norm_trace_sub_le_card {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Q.IsHermitian) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → Fin N → ℝ) {z : ℂ}
    (hz : 0 < z.im) :
    ‖(resolventC (Q + ∑ a ∈ s, c a • Matrix.vecMulVec (u a) (u a)) z).trace -
        (resolventC Q z).trace‖ ≤ s.card / z.im := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hQs : (Q + ∑ x ∈ s, c x • Matrix.vecMulVec (u x) (u x)).IsHermitian :=
      hQ.add (isHermitian_sum_smul_vecMulVec s c u)
    have h1 := norm_trace_sub_le_rankOne hQs (u a) (c a) hz
    have e : Q + ∑ x ∈ insert a s, c x • Matrix.vecMulVec (u x) (u x) =
        (Q + ∑ x ∈ s, c x • Matrix.vecMulVec (u x) (u x)) +
          c a • Matrix.vecMulVec (u a) (u a) := by
      rw [Finset.sum_insert ha]
      abel
    rw [e]
    calc ‖(resolventC ((Q + ∑ x ∈ s, c x • Matrix.vecMulVec (u x) (u x)) +
            c a • Matrix.vecMulVec (u a) (u a)) z).trace - (resolventC Q z).trace‖
        = ‖((resolventC ((Q + ∑ x ∈ s, c x • Matrix.vecMulVec (u x) (u x)) +
            c a • Matrix.vecMulVec (u a) (u a)) z).trace -
            (resolventC (Q + ∑ x ∈ s, c x • Matrix.vecMulVec (u x) (u x)) z).trace) +
            ((resolventC (Q + ∑ x ∈ s, c x • Matrix.vecMulVec (u x) (u x)) z).trace -
              (resolventC Q z).trace)‖ := by rw [sub_add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ 1 / z.im + s.card / z.im := add_le_add h1 ih
      _ = (insert a s).card / z.im := by
          rw [Finset.card_insert_of_notMem ha]
          push_cast
          ring

/-- Spectral decomposition of a real symmetric matrix, entrywise:
`H_ij = Σ_α λ_α u_α(i) u_α(j)`. -/
private lemma spectral_apply {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    (i j : Fin N) :
    H i j = ∑ α, hH.eigenvalues α * (hH.eigenvectorBasis α i * hH.eigenvectorBasis α j) := by
  have h := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  have h2 : H = (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) * diagonal hH.eigenvalues *
      (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ)ᵀ := by
    simpa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h
  conv_lhs => rw [h2]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp
  ring

/-- (6.81) for a perturbation of rank `r`: `|Tr S - Tr R| ≤ r/η`. -/
theorem norm_trace_resolventC_sub_le_rank {N : ℕ} {Q V : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Q.IsHermitian) (hV : V.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    ‖(resolventC (Q + V) z).trace - (resolventC Q z).trace‖ ≤ V.rank / z.im := by
  classical
  have hVeq : V = ∑ α ∈ Finset.univ.filter (fun α => hV.eigenvalues α ≠ 0),
      hV.eigenvalues α • Matrix.vecMulVec (hV.eigenvectorBasis α) (hV.eigenvectorBasis α) := by
    ext i j
    rw [sum_smul_vecMulVec_apply, Finset.sum_filter_of_ne, spectral_apply hV i j]
    intro α _ h hne
    exact h (by simp [hne])
  have hrank : V.rank = (Finset.univ.filter (fun α => hV.eigenvalues α ≠ 0)).card := by
    rw [hV.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have h := norm_trace_sub_le_card hQ (Finset.univ.filter (fun α => hV.eigenvalues α ≠ 0))
    (fun α => hV.eigenvalues α) (fun α => ⇑(hV.eigenvectorBasis α)) hz
  rw [← hVeq] at h
  rw [hrank]
  exact h

/-- (6.81): `V` supported on `{(a, b), (b, a)}` gives `|Tr S - Tr R| ≤ 2/η`. -/
theorem norm_trace_resolventC_sub_le_two {N : ℕ} {Q V : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Q.IsHermitian) (hV : V.IsHermitian) (a b : Fin N)
    (hsupp : ∀ k l, V k l ≠ 0 → (k = a ∧ l = b) ∨ (k = b ∧ l = a)) {z : ℂ} (hz : 0 < z.im) :
    ‖(resolventC (Q + V) z).trace - (resolventC Q z).trace‖ ≤ 2 / z.im := by
  classical
  have hrank : V.rank ≤ 2 := by
    let T : Finset (Fin N) := {a, b}
    let M₁ : Matrix (Fin N) T ℝ := Matrix.of fun i k => if i = k then 1 else 0
    let M₂ : Matrix T (Fin N) ℝ := Matrix.of fun k j => V k j
    have hV12 : V = M₁ * M₂ := by
      ext i j
      simp only [M₁, M₂, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_coe_sort T (fun k => if i = k then V k j else 0), Finset.sum_ite_eq]
      by_cases hi : i ∈ T
      · simp only [hi, ↓reduceIte]
      · simp only [hi, ↓reduceIte]
        by_contra hne
        have := hsupp i j hne
        simp only [T, Finset.mem_insert, Finset.mem_singleton] at hi
        tauto
    calc V.rank = (M₁ * M₂).rank := by rw [← hV12]
      _ ≤ M₁.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card T := Matrix.rank_le_card_width _
      _ = T.card := Fintype.card_coe T
      _ ≤ 2 := Finset.card_le_two
  have h := norm_trace_resolventC_sub_le_rank hQ hV hz
  refine h.trans ?_
  gcongr
  exact_mod_cast hrank

/-! ### Compiled checks at a concrete nondegenerate point

`N = 2`, `Q = [[0, 0], [0, 1]]`, `V = [[0, 1], [1, 0]]` (symmetric, rank two, supported on
`{(0, 1), (1, 0)}`), `z = i`. -/

private def checkQ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]

private def checkV : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

private lemma checkQ_isHermitian : checkQ.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [checkQ]

private lemma checkV_isHermitian : checkV.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [checkV]

private lemma checkV_supp : ∀ k l, checkV k l ≠ 0 → (k = 0 ∧ l = 1) ∨ (k = 1 ∧ l = 0) := by
  intro k l h
  fin_cases k <;> fin_cases l <;> simp [checkV] at h ⊢

example : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ =
    ∑ k ∈ Finset.range 3, ((1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *
        (1 - !![2, 1; 1, 2])) ^ k * (1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ +
      ((1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * (1 - !![2, 1; 1, 2])) ^ 3 *
        (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ :=
  inv_eq_sum_add (A := !![2, 1; 1, 2]) (B := 1)
    (by rw [Matrix.det_fin_two_of]; exact isUnit_iff_ne_zero.mpr (by norm_num)) (by simp) 3

example : resolventC checkQ Complex.I =
    ∑ k ∈ Finset.range 5, (resolventC (checkQ + checkV) Complex.I *
        checkV.map (fun x : ℝ => (x : ℂ))) ^ k * resolventC (checkQ + checkV) Complex.I +
      (resolventC (checkQ + checkV) Complex.I * checkV.map (fun x : ℝ => (x : ℂ))) ^ 5 *
        resolventC checkQ Complex.I :=
  resolventC_expansion_left checkQ_isHermitian checkV_isHermitian (by simp) 5

example : resolventC (checkQ + checkV) Complex.I =
    ∑ k ∈ Finset.range 2, (-(resolventC checkQ Complex.I *
        checkV.map (fun x : ℝ => (x : ℂ)))) ^ k * resolventC checkQ Complex.I +
      (-(resolventC checkQ Complex.I * checkV.map (fun x : ℝ => (x : ℂ)))) ^ 2 *
        resolventC (checkQ + checkV) Complex.I :=
  resolventC_expansion_right checkQ_isHermitian checkV_isHermitian (by simp) 1

example : ‖(resolventC (checkQ + checkV) Complex.I).trace -
      (resolventC checkQ Complex.I).trace‖ ≤ checkV.rank / Complex.I.im :=
  norm_trace_resolventC_sub_le_rank checkQ_isHermitian checkV_isHermitian (by simp)

example : ‖(resolventC (checkQ + checkV) Complex.I).trace -
      (resolventC checkQ Complex.I).trace‖ ≤ 2 / Complex.I.im :=
  norm_trace_resolventC_sub_le_two checkQ_isHermitian checkV_isHermitian 0 1 checkV_supp
    (by simp)

#print axioms inv_eq_sum_add
#print axioms resolventC_expansion_left
#print axioms resolventC_expansion_right
#print axioms norm_trace_resolventC_sub_le_rank
#print axioms norm_trace_resolventC_sub_le_two

end WEdgeNS
