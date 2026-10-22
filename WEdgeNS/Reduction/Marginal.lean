import WEdgeNS.Reduction.Coupling
import WEdgeNS.Probability.ProductSpace
import WEdgeNS.Model.Transfer

/-!
# The law of the small block
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- The factor `(E|x^S_12|²)^{-1/2}` of `H̃^S` (before (4.20)). -/
def truncNormFactor (ν : Measure ℝ) (ε : ℝ) (N : ℕ) : ℝ :=
  (Real.sqrt (∫ x, x ^ 2 ∂(truncCentered ν ((N : ℝ) ^ (1 / 2 - ε)))))⁻¹

/-- `H̃^S` as a function on the auxiliary space. -/
def normSmall (ν : Measure ℝ) (ε : ℝ) {N : ℕ} (u : CoupleSpace N) : Matrix (Fin N) (Fin N) ℝ :=
  symOfEntries ((truncNormFactor ν ε N * (Real.sqrt N)⁻¹) • u.1)

/-- The small block, rescaled, has the law `truncLawsNorm` of `H̃^S`. -/
theorem map_smallBlock_coupleLaw {ν ν' : Measure ℝ} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] {ε : ℝ} {N : ℕ}
    (hS : ν {x | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)} ≠ 0)
    (hS' : ν' {x | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)} ≠ 0) :
    (coupleLaw ν ν' ε N).map (fun u => (truncNormFactor ν ε N * (Real.sqrt N)⁻¹) • u.1) =
      (truncLawsNorm ν ν' ε N).law := by
  have hP := isProbabilityMeasure_coupleLaw hS hS'
  have hT := isProbabilityMeasure_truncCentered ν hS
  have hT' := isProbabilityMeasure_truncCentered ν' hS'
  set c : ℝ := truncNormFactor ν ε N * (Real.sqrt N)⁻¹ with hc
  set S := entryLaw (truncCentered ν ((N : ℝ) ^ (1 / 2 - ε)))
    (truncCentered ν' ((N : ℝ) ^ (1 / 2 - ε))) N with hSdef
  have hSp : IsProbabilityMeasure S := by
    rw [hSdef]; unfold entryLaw; infer_instance
  have hL := isProbabilityMeasure_truncLargeCentered ν ((N : ℝ) ^ (1 / 2 - ε))
  have hL' := isProbabilityMeasure_truncLargeCentered ν' ((N : ℝ) ^ (1 / 2 - ε))
  have hfst : (coupleLaw ν ν' ε N).map Prod.fst = S := by
    unfold coupleLaw
    rw [← hSdef, Measure.map_fst_prod]
    have : IsProbabilityMeasure
        ((entryLaw (truncLargeCentered ν ((N : ℝ) ^ (1 / 2 - ε)))
            (truncLargeCentered ν' ((N : ℝ) ^ (1 / 2 - ε))) N).prod
          (entryLaw (ν.map (largeInd ((N : ℝ) ^ (1 / 2 - ε))))
            (ν'.map (largeInd ((N : ℝ) ^ (1 / 2 - ε)))) N)) := by
      unfold entryLaw; infer_instance
    rw [measure_univ, one_smul]
  have hf : (fun u : CoupleSpace N => c • u.1) = (fun x : Entries N => c • x) ∘ Prod.fst := rfl
  rw [hf, ← Measure.map_map (measurable_const_smul c) measurable_fst, hfst]
  have hψ : (fun x : Entries N => c • x) =
      Prod.map (fun a : Fin N → ℝ => c • a) (fun b : OffDiag N → ℝ => c • b) := rfl
  have hm1 : Measurable fun a : Fin N → ℝ => c • a := measurable_const_smul c
  have hm2 : Measurable fun b : OffDiag N → ℝ => c • b := measurable_const_smul c
  have hmul : Measurable fun x : ℝ => c * x := measurable_const.mul measurable_id
  have hcomp : ∀ μ : Measure ℝ, (μ.map (fun x => (Real.sqrt N)⁻¹ * x)).map
      (fun x => (Real.sqrt (∫ x, x ^ 2 ∂(truncCentered ν ((N : ℝ) ^ (1 / 2 - ε)))))⁻¹ * x) =
      μ.map (fun x => c * x) := by
    intro μ
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    simp only [Function.comp, hc, truncNormFactor, mul_assoc]
  rw [hψ, hSdef]
  unfold entryLaw
  rw [← Measure.map_prod_map _ _ hm1 hm2]
  have hpi1 : (Measure.pi fun _ : Fin N => truncCentered ν' ((N : ℝ) ^ (1 / 2 - ε))).map
      (fun a : Fin N → ℝ => c • a) =
      Measure.pi fun _ : Fin N => (truncCentered ν' ((N : ℝ) ^ (1 / 2 - ε))).map
        (fun x => c * x) := by
    have : ∀ _ : Fin N, SigmaFinite ((truncCentered ν' ((N : ℝ) ^ (1 / 2 - ε))).map
        (fun x => c * x)) := fun _ => by
      infer_instance
    exact Measure.pi_map_pi (f := fun _ x => c * x) (fun _ => hmul.aemeasurable)
  have hpi2 : (Measure.pi fun _ : OffDiag N => truncCentered ν ((N : ℝ) ^ (1 / 2 - ε))).map
      (fun a : OffDiag N → ℝ => c • a) =
      Measure.pi fun _ : OffDiag N => (truncCentered ν ((N : ℝ) ^ (1 / 2 - ε))).map
        (fun x => c * x) := by
    have : ∀ _ : OffDiag N, SigmaFinite ((truncCentered ν ((N : ℝ) ^ (1 / 2 - ε))).map
        (fun x => c * x)) := fun _ => by
      infer_instance
    exact Measure.pi_map_pi (f := fun _ x => c * x) (fun _ => hmul.aemeasurable)
  rw [hpi1, hpi2]
  unfold EntryLaws.law truncLawsNorm truncLaws EntryLaws.scale ofIID
  simp only [hcomp]

/-- An event of `H̃^S` has at most its `truncLawsNorm` probability on the auxiliary space (outer
measures; no measurability needed). -/
theorem coupleLaw_normSmall_le {ν ν' : Measure ℝ} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] {ε : ℝ} {N : ℕ}
    (hS : ν {x | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)} ≠ 0)
    (hS' : ν' {x | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)} ≠ 0) (A : Set (Entries N)) :
    coupleLaw ν ν' ε N {u | (truncNormFactor ν ε N * (Real.sqrt N)⁻¹) • u.1 ∈ A} ≤
      (truncLawsNorm ν ν' ε N).law A := by
  rw [← map_smallBlock_coupleLaw hS hS']
  exact Measure.le_map_apply
    ((measurable_const_smul _).comp measurable_fst).aemeasurable A

/-- `P_{H̃^S}(N^{2/3}(λ_N - 2) ≤ s)` computed on the auxiliary space. -/
theorem edgeCdfL_truncLawsNorm_eq {ν ν' : Measure ℝ} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] {ε : ℝ} {N : ℕ}
    (hS : ν {x | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)} ≠ 0)
    (hS' : ν' {x | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)} ≠ 0) (s : ℝ) :
    edgeCdfL (truncLawsNorm ν ν' ε N) s = (coupleLaw ν ν' ε N
      {u | (N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (normSmall ν ε u) - 2) ≤ s}).toReal := by
  have hfm : Measurable fun u : CoupleSpace N =>
      (truncNormFactor ν ε N * (Real.sqrt N)⁻¹) • u.1 :=
    (measurable_const_smul _).comp measurable_fst
  rw [edgeCdfL, ← map_smallBlock_coupleLaw hS hS',
    Measure.map_apply hfm
      (measurableSet_le (measurable_edgeScaledSym N) measurable_const)]
  rfl

/-! ### Non-vacuity at Rademacher off-diagonal entries and `N(0, 2)` diagonal entries,
`ε = 1/100`, `N = 1000` -/

private lemma marginal_one_le_T : (1 : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ)) :=
  Real.one_le_rpow (by norm_num) (by norm_num)

/-- The small-mass condition for Rademacher entries. -/
private lemma marginal_hS :
    rademacher {x : ℝ | |x| ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))} ≠ 0 := by
  have h1 : Measure.dirac (1 : ℝ) {x : ℝ | |x| ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))} = 1 :=
    Measure.dirac_apply_of_mem (by simpa using marginal_one_le_T)
  simp only [rademacher, Measure.smul_apply, Measure.add_apply, h1, smul_eq_mul]
  simp

/-- The small-mass condition for `N(0, 2)` diagonal entries. -/
private lemma marginal_hS' :
    gaussianReal 0 2 {x : ℝ | |x| ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))} ≠ 0 := by
  intro h
  have h0 := gaussianReal_absolutelyContinuous' 0 (by norm_num : (2 : NNReal) ≠ 0) h
  have hsub : Set.Icc (-1 : ℝ) 1 ⊆
      {x : ℝ | |x| ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))} := fun x hx =>
    (abs_le.mpr ⟨hx.1, hx.2⟩).trans marginal_one_le_T
  have := measure_mono_null hsub h0
  rw [Real.volume_Icc] at this
  norm_num at this

/-- The small block of the coupled space has the law `truncLawsNorm` at this point. -/
example : (coupleLaw rademacher (gaussianReal 0 2) (1 / 100) 1000).map
    (fun u => (truncNormFactor rademacher (1 / 100) 1000 * (Real.sqrt (1000 : ℕ))⁻¹) • u.1) =
    (truncLawsNorm rademacher (gaussianReal 0 2) (1 / 100) 1000).law := by
  have := rademacher_wignerLaws.prob
  exact map_smallBlock_coupleLaw marginal_hS marginal_hS'

/-- The outer-measure transfer for the event `N^{2/3}(λ_N - 2) ≤ 0` at this point. -/
example : (coupleLaw rademacher (gaussianReal 0 2) (1 / 100) 1000
    {u | (truncNormFactor rademacher (1 / 100) 1000 * (Real.sqrt (1000 : ℕ))⁻¹) • u.1 ∈
      {ω : Entries 1000 | ((1000 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) *
        (lambdaMax (symOfEntries ω) - 2) ≤ 0}}) ≤
    (truncLawsNorm rademacher (gaussianReal 0 2) (1 / 100) 1000).law
      {ω : Entries 1000 | ((1000 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) *
        (lambdaMax (symOfEntries ω) - 2) ≤ 0} := by
  have := rademacher_wignerLaws.prob
  exact coupleLaw_normSmall_le marginal_hS marginal_hS' _

/-- The distribution function of `N^{2/3}(λ_N - 2)` at `s = 0` on the auxiliary space. -/
example : edgeCdfL (truncLawsNorm rademacher (gaussianReal 0 2) (1 / 100) 1000) 0 =
    (coupleLaw rademacher (gaussianReal 0 2) (1 / 100) 1000
      {u | ((1000 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) *
        (lambdaMax (normSmall rademacher (1 / 100) u) - 2) ≤ 0}).toReal := by
  have := rademacher_wignerLaws.prob
  exact edgeCdfL_truncLawsNorm_eq marginal_hS marginal_hS' 0

#print axioms map_smallBlock_coupleLaw
#print axioms coupleLaw_normSmall_le
#print axioms edgeCdfL_truncLawsNorm_eq

end WEdgeNS
