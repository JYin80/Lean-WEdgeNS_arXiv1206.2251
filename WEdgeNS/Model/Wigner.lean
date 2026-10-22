import Mathlib

/-!
# The real symmetric Wigner model

Definition 1.1 (real symmetric case) of J. O. Lee and J. Yin, *A necessary and sufficient
condition for edge universality of Wigner matrices*: the entry law, the matrix `H_N`, its largest
eigenvalue, condition (1.4), and the GOE.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace WEdgeNS

/-- Strictly upper-triangular index pairs `i < j` of an `N × N` matrix. -/
abbrev OffDiag (N : ℕ) := {p : Fin N × Fin N // p.1 < p.2}

/-- Entry space of Definition 1.1: diagonal entries `x_ii` and upper entries `x_ij`, `i < j`. -/
abbrev Entries (N : ℕ) := (Fin N → ℝ) × (OffDiag N → ℝ)

/-- Joint law of the entries in Definition 1.1: the `x_ii` are i.i.d. with law `ν'`, the `x_ij`
(`i < j`) are i.i.d. with law `ν`, and all of them are independent. -/
noncomputable def entryLaw (ν ν' : Measure ℝ) (N : ℕ) : Measure (Entries N) :=
  (Measure.pi fun _ : Fin N => ν').prod (Measure.pi fun _ : OffDiag N => ν)

/-- The real symmetric Wigner matrix `H_N = N^{-1/2} (x_ij)` of Definition 1.1. -/
noncomputable def wignerMatrix (N : ℕ) (ω : Entries N) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (Real.sqrt N)⁻¹ *
    if h : i = j then ω.1 i
    else if h' : i < j then ω.2 ⟨(i, j), h'⟩
    else ω.2 ⟨(j, i), lt_of_le_of_ne (not_lt.mp h') (fun e => h e.symm)⟩

/-- The largest eigenvalue `λ_N` of a real square matrix, as the supremum of its real spectrum. -/
noncomputable def lambdaMax {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  sSup (spectrum ℝ A)

/-- The hypotheses of Definition 1.1 on the off-diagonal law `ν` and the diagonal law `ν'`. -/
structure WignerLaws (ν ν' : Measure ℝ) : Prop where
  prob : IsProbabilityMeasure ν
  prob' : IsProbabilityMeasure ν'
  sq_int : Integrable (fun x : ℝ => x ^ 2) ν
  sq_int' : Integrable (fun x : ℝ => x ^ 2) ν'
  mean : ∫ x, x ∂ν = 0
  var : ∫ x, x ^ 2 ∂ν = 1
  mean' : ∫ x, x ∂ν' = 0

/-- Condition (1.4): `s^4 P(|x_12| ≥ s) → 0` as `s → ∞`. -/
def TailCond (ν : Measure ℝ) : Prop :=
  Tendsto (fun s : ℝ => s ^ 4 * (ν {x | s ≤ |x|}).toReal) atTop (𝓝 0)

/-- The rescaled largest eigenvalue `N^{2/3}(λ_N - 2)`. -/
noncomputable def edgeScaled (N : ℕ) (ω : Entries N) : ℝ :=
  (N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (wignerMatrix N ω) - 2)

/-- The distribution function `s ↦ P(N^{2/3}(λ_N - 2) ≤ s)`. -/
noncomputable def edgeCdf (ν ν' : Measure ℝ) (N : ℕ) (s : ℝ) : ℝ :=
  (entryLaw ν ν' N {ω | edgeScaled N ω ≤ s}).toReal

/-- The same distribution function for the GOE, defined after Definition 1.1:
`x_ij ~ N(0, 1)` and `x_ii ~ N(0, 2)`. -/
noncomputable def goeCdf (N : ℕ) (s : ℝ) : ℝ :=
  edgeCdf (gaussianReal 0 1) (gaussianReal 0 2) N s

/-- The Rademacher law `(δ_{-1} + δ_1) / 2`. -/
noncomputable def rademacher : Measure ℝ :=
  (2 : ENNReal)⁻¹ • (Measure.dirac (-1) + Measure.dirac 1)

/-- `H_N` is symmetric. -/
theorem wignerMatrix_isSymm (N : ℕ) (ω : Entries N) : (wignerMatrix N ω).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, wignerMatrix]
  congr 1
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.ne, h.ne', not_lt.mpr h.le]
  · simp
  · simp [h, h.ne, h.ne', not_lt.mpr h.le]

/-- `H_N` is Hermitian (real symmetric). -/
theorem wignerMatrix_isHermitian (N : ℕ) (ω : Entries N) : (wignerMatrix N ω).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  exact wignerMatrix_isSymm N ω

instance isProbabilityMeasure_entryLaw (ν ν' : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] (N : ℕ) : IsProbabilityMeasure (entryLaw ν ν' N) := by
  unfold entryLaw
  infer_instance

/-- The GOE laws satisfy Definition 1.1. -/
theorem goe_wignerLaws : WignerLaws (gaussianReal 0 1) (gaussianReal 0 2) := by
  have hsq : ∀ v : NNReal, Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := fun v =>
    (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  have hvar : ∀ v : NNReal, ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := fun v => by
    have h := variance_eq_integral (X := id) (μ := gaussianReal 0 v) aemeasurable_id
    rw [variance_id_gaussianReal] at h
    simpa [integral_id_gaussianReal] using h.symm
  exact ⟨inferInstance, inferInstance, hsq 1, hsq 2, integral_id_gaussianReal,
    by simpa using hvar 1, integral_id_gaussianReal⟩

/-- Rademacher off-diagonal entries with `N(0, 2)` diagonal entries satisfy Definition 1.1. -/
theorem rademacher_wignerLaws : WignerLaws rademacher (gaussianReal 0 2) := by
  have hprob : IsProbabilityMeasure rademacher := by
    refine ⟨?_⟩
    simp only [rademacher, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
    rw [one_add_one_eq_two]
    exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
  have hint : ∀ f : ℝ → ℝ, Integrable f rademacher := fun f => by
    unfold rademacher
    exact ((integrable_dirac (by simp)).add_measure (integrable_dirac (by simp))).smul_measure
      (by simp)
  have hmom : ∀ f : ℝ → ℝ, ∫ x, f x ∂rademacher = (f (-1) + f 1) / 2 := fun f => by
    unfold rademacher
    rw [integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
      (integrable_dirac (by simp)), integral_dirac, integral_dirac]
    simp [ENNReal.toReal_inv]
    ring
  have hgauss := goe_wignerLaws
  refine ⟨hprob, hgauss.prob', hint _, hgauss.sq_int', ?_, ?_, hgauss.mean'⟩
  · rw [hmom]; norm_num
  · rw [hmom]; norm_num

/-- The Rademacher law satisfies (1.4). -/
theorem rademacher_tailCond : TailCond rademacher := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
  have h : rademacher {x : ℝ | s ≤ |x|} = 0 := by
    unfold rademacher
    simp only [Measure.smul_apply, Measure.add_apply, Measure.dirac_apply, smul_eq_mul]
    have h1 : (-1 : ℝ) ∉ {x : ℝ | s ≤ |x|} := by simp [abs_neg]; linarith
    have h2 : (1 : ℝ) ∉ {x : ℝ | s ≤ |x|} := by simp; linarith
    simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  simp [h]

example : WignerLaws rademacher (gaussianReal 0 2) ∧ TailCond rademacher :=
  ⟨rademacher_wignerLaws, rademacher_tailCond⟩
#print axioms goe_wignerLaws
#print axioms rademacher_wignerLaws
#print axioms rademacher_tailCond
#print axioms wignerMatrix_isHermitian

end WEdgeNS
