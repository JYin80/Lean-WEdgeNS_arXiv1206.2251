import WEdgeNS.Reduction.Coupling
import WEdgeNS.Model.LambdaMax

/-!
# The decomposition of the Wigner matrix along the coupling
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- `H^S = N^{-1/2} x^S`. -/
def smallMat {N : ℕ} (u : CoupleSpace N) : Matrix (Fin N) (Fin N) ℝ :=
  symOfEntries ((Real.sqrt N)⁻¹ • u.1)

/-- `H^L = N^{-1/2} x^L`. -/
def largeMat {N : ℕ} (u : CoupleSpace N) : Matrix (Fin N) (Fin N) ℝ :=
  symOfEntries ((Real.sqrt N)⁻¹ • u.2.1)

/-- The selector matrix `H^C = (c_ij)`. -/
def selMat {N : ℕ} (u : CoupleSpace N) : Matrix (Fin N) (Fin N) ℝ := symOfEntries u.2.2

/-- `M` of (4.16)–(4.17) for the centred decomposition: `N^{-1/2} m` off the diagonal, `N^{-1/2} m̃`
on it. -/
def shiftMat (N : ℕ) (m m' : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (Real.sqrt N)⁻¹ * if i = j then m' else m

/-- (4.16) as an identity: `H = H^S + H̃ ∘ H^C + M` with `H̃ = H^L - H^S`. -/
theorem wignerMatrix_coupleMap (m m' : ℝ) {N : ℕ} (u : CoupleSpace N) :
    wignerMatrix N (coupleMap m m' u) =
      smallMat u + (largeMat u - smallMat u) ⊙ selMat u + shiftMat N m m' := by
  ext i j
  simp only [wignerMatrix, smallMat, largeMat, selMat, shiftMat, symOfEntries, coupleMap,
    Matrix.add_apply, Matrix.sub_apply, Matrix.hadamard_apply]
  by_cases h : i = j
  · simp only [h, dite_true, ite_true, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
    ring
  · by_cases h' : i < j
    · simp only [h, h', dite_true, dite_false, ite_false, Prod.smul_snd, Pi.smul_apply,
        smul_eq_mul]
      ring
    · simp only [h, h', dite_false, ite_false, Prod.smul_snd, Pi.smul_apply,
        smul_eq_mul]
      ring

/-- Adding a scalar matrix shifts the largest eigenvalue by the scalar. -/
private lemma lambdaMax_add_scalar {N : ℕ} [NeZero N] {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (c : ℝ) :
    lambdaMax (A + algebraMap ℝ (Matrix (Fin N) (Fin N) ℝ) c) = lambdaMax A + c := by
  have hG := lambdaMax_isGreatest hA
  rw [← hA.spectrum_real_eq_range_eigenvalues] at hG
  unfold lambdaMax
  refine IsGreatest.csSup_eq ⟨?_, ?_⟩
  · rw [← spectrum.add_singleton_eq]
    exact ⟨_, hG.1, c, rfl, rfl⟩
  · intro x hx
    rw [← spectrum.add_singleton_eq] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have hbc : b = c := hb
    rw [hbc]
    have := hG.2 ha
    change a + c ≤ lambdaMax A + c
    linarith

/-- (4.17) with the split of `M`: the scalar part shifts `λ_N` exactly, the rest costs
`N · N^{-1/2}|m|`. -/
theorem abs_lambdaMax_add_shiftMat_sub_le {N : ℕ} [NeZero N] {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (m m' : ℝ) :
    |lambdaMax (A + shiftMat N m m') - lambdaMax A| ≤
      Real.sqrt N * |m| + |m' - m| / Real.sqrt N := by
  have hN : 0 < Real.sqrt N :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
  set c : ℝ := (Real.sqrt N)⁻¹ * (m' - m) with hc
  set B : Matrix (Fin N) (Fin N) ℝ := A + algebraMap ℝ (Matrix (Fin N) (Fin N) ℝ) c with hB
  have hshift : ∀ i j, |(A + shiftMat N m m') i j - B i j| ≤ (Real.sqrt N)⁻¹ * |m| := by
    intro i j
    have hs : |(Real.sqrt N)⁻¹ * m| = (Real.sqrt N)⁻¹ * |m| := by
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hN.le)]
    rw [← hs]
    simp only [hB, hc, shiftMat, Matrix.add_apply, Matrix.algebraMap_matrix_apply]
    by_cases h : i = j
    · subst h
      simp only [ite_true, Algebra.algebraMap_self, RingHom.id_apply]
      exact le_of_eq (by congr 1; ring)
    · simp only [h, ite_false]
      exact le_of_eq (by congr 1; ring)
  have hsymm : (shiftMat N m m').IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, shiftMat]
    simp only [eq_comm (a := j)]
  have hB' : B.IsHermitian := by
    refine hA.add ?_
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.algebraMap_matrix_apply]
    simp only [eq_comm (a := j)]
  have h1 := abs_lambdaMax_sub_le (hA.add hsymm) hB' hshift
  have h2 : lambdaMax B = lambdaMax A + c := lambdaMax_add_scalar hA c
  have hNs : (N : ℝ) * ((Real.sqrt N)⁻¹ * |m|) = Real.sqrt N * |m| := by
    have hs2 : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg _)
    have : (N : ℝ) * (Real.sqrt N)⁻¹ = Real.sqrt N := by
      calc (N : ℝ) * (Real.sqrt N)⁻¹ = (Real.sqrt N * Real.sqrt N) * (Real.sqrt N)⁻¹ := by
            rw [hs2]
        _ = Real.sqrt N := by rw [mul_assoc, mul_inv_cancel₀ hN.ne', mul_one]
    rw [← mul_assoc, this]
  have hcabs : |c| = |m' - m| / Real.sqrt N := by
    rw [hc, abs_mul, abs_of_nonneg (inv_nonneg.mpr hN.le)]; field_simp
  calc |lambdaMax (A + shiftMat N m m') - lambdaMax A|
      = |(lambdaMax (A + shiftMat N m m') - lambdaMax B) + c| := by rw [h2]; ring_nf
    _ ≤ |lambdaMax (A + shiftMat N m m') - lambdaMax B| + |c| := abs_add_le _ _
    _ ≤ Real.sqrt N * |m| + |m' - m| / Real.sqrt N := by
        rw [hNs] at h1; rw [hcabs] at *; linarith [hcabs]

open scoped Pointwise in
/-- `λ_N(c A) = c λ_N(A)` for `c > 0`. -/
theorem lambdaMax_smul_of_pos {N : ℕ} [NeZero N] {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) {c : ℝ} (hc : 0 < c) : lambdaMax (c • A) = c * lambdaMax A := by
  have _ := hA
  unfold lambdaMax
  have h : c • A = (Units.mk0 c hc.ne') • A := rfl
  rw [h, spectrum.unit_smul_eq_smul]
  have : (Units.mk0 c hc.ne') • spectrum ℝ A = c • spectrum ℝ A := rfl
  rw [this, Real.sSup_smul_of_nonneg hc.le]
  rfl

/-! ### Nondegenerate instances -/

/-- `λ_2(3 · diag(1, 2)) = 3 · λ_2(diag(1, 2))`. -/
example : lambdaMax ((3 : ℝ) • (diagonal ![1, 2] : Matrix (Fin 2) (Fin 2) ℝ)) =
    3 * lambdaMax (diagonal ![1, 2] : Matrix (Fin 2) (Fin 2) ℝ) :=
  lambdaMax_smul_of_pos (isHermitian_diagonal_of_self_adjoint _ (by
    ext i; simp)) (by norm_num)

/-- Equality case of the shift bound: `N = 4`, `A = 0`, `m = 1`, `m' = 3`; `M` has off-diagonal
entries `1/2` and diagonal entries `3/2`, so `λ_4(M) = 3 = √4 · 1 + |3 - 1| / √4`. -/
example : lambdaMax ((0 : Matrix (Fin 4) (Fin 4) ℝ) + shiftMat 4 1 3) = 3 := by
  have hs' : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have hs : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by simpa using hs'
  have h0 : lambdaMax (0 : Matrix (Fin 4) (Fin 4) ℝ) = 0 := by
    unfold lambdaMax; simp
  have hup := abs_lambdaMax_add_shiftMat_sub_le (N := 4) (A := 0) isHermitian_zero 1 3
  rw [h0, hs] at hup
  have hH : ((0 : Matrix (Fin 4) (Fin 4) ℝ) + shiftMat 4 1 3).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, shiftMat, zero_add]
    simp only [eq_comm (a := j)]
  have hlow := dotProduct_mulVec_le_lambdaMax hH (fun _ => (1 : ℝ))
  simp [dotProduct, mulVec, shiftMat, Fin.sum_univ_four] at hlow
  rw [hs'] at hlow
  rw [zero_add] at hup ⊢
  norm_num at hup
  rw [abs_le] at hup
  rw [zero_add] at hH
  linarith [hup.1, hup.2]

#print axioms wignerMatrix_coupleMap
#print axioms abs_lambdaMax_add_shiftMat_sub_le
#print axioms lambdaMax_smul_of_pos

end WEdgeNS
