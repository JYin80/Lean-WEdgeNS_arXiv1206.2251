import Mathlib

/-!
# Uniform laws on finite lists of reals

The law `unifList l` puts mass `1 / |l|` on each point of `l`, with multiplicity. Entry laws of this
form are the finitely supported test laws of the nondegenerate instances.
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- Uniform law on the points of `l`, with multiplicity. -/
def unifList (l : List ℝ) : Measure ℝ :=
  ((l.length : ENNReal)⁻¹) • (l.map Measure.dirac).sum

/-- Every real function is integrable against the sum of the Dirac masses at the points of `l`. -/
theorem integrable_listSum (l : List ℝ) (f : ℝ → ℝ) :
    Integrable f ((l.map Measure.dirac).sum) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (integrable_dirac (by simp)).add_measure ih

/-- The integral against the sum of the Dirac masses at the points of `l` is the sum of the values
of the integrand at those points. -/
theorem integral_listSum (l : List ℝ) (f : ℝ → ℝ) :
    ∫ x, f x ∂((l.map Measure.dirac).sum) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add_measure (integrable_dirac (by simp)) (integrable_listSum l f),
      integral_dirac, ih]

/-- The integral against `unifList l` is the average of the integrand over the points of `l`. -/
theorem integral_unifList (l : List ℝ) (f : ℝ → ℝ) :
    ∫ x, f x ∂(unifList l) = (l.map f).sum / l.length := by
  rw [unifList, integral_smul_measure, integral_listSum]
  simp [ENNReal.toReal_inv, div_eq_inv_mul]

/-- Every real function is integrable against `unifList l` when `l` is nonempty. -/
theorem integrable_unifList (l : List ℝ) (h : l ≠ []) (f : ℝ → ℝ) :
    Integrable f (unifList l) :=
  (integrable_listSum l f).smul_measure (by simpa using h)

/-- The mass of a measurable set `s` under the sum of the Dirac masses at the points of `l` is the
number of points of `l` (with multiplicity) in `s`. -/
theorem listSum_apply (l : List ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    (l.map Measure.dirac).sum s = (l.map fun a => s.indicator (1 : ℝ → ENNReal) a).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, Measure.coe_add, Pi.add_apply, ih,
      Measure.dirac_apply' _ hs]

/-- `unifList l` is a probability measure when `l` is nonempty. -/
theorem unifList_prob (l : List ℝ) (h : l ≠ []) : IsProbabilityMeasure (unifList l) := by
  constructor
  rw [unifList, Measure.smul_apply, listSum_apply l MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, List.map_const', List.sum_replicate, nsmul_eq_mul,
    mul_one, smul_eq_mul]
  have h0 : (l.length : ENNReal) ≠ 0 := by simpa using h
  exact ENNReal.inv_mul_cancel h0 (by simp)

/-- If every point `a` of `l` satisfies `|a| ≤ q⁻¹`, then `unifList l` gives no mass to
`{x | q⁻¹ < |x|}`. -/
theorem unifList_tail (l : List ℝ) (q : ℝ) (h : ∀ a ∈ l, |a| ≤ q⁻¹) :
    unifList l {x | q⁻¹ < |x|} = 0 := by
  have hm : MeasurableSet {x : ℝ | q⁻¹ < |x|} := measurableSet_lt measurable_const measurable_abs
  rw [unifList, Measure.smul_apply, listSum_apply l hm]
  have : (l.map fun a => ({x : ℝ | q⁻¹ < |x|}).indicator (1 : ℝ → ENNReal) a) =
      l.map fun _ => 0 := by
    apply List.map_congr_left
    intro a ha
    simp [Set.indicator, not_lt.mpr (h a ha)]
  rw [this]; simp

/-! ### Compiled checks -/

/-- The uniform law on `{1, -1}` is a probability measure with second moment `1`, integrates every
function, and gives no mass to `{|x| > 1}`. -/
example : IsProbabilityMeasure (unifList [1, -1]) ∧ ∫ x, x ^ 2 ∂(unifList [1, -1]) = 1 ∧
    Integrable (fun x : ℝ => x ^ 3) (unifList [1, -1]) ∧
    unifList [1, -1] {x | (1 : ℝ)⁻¹ < |x|} = 0 := by
  refine ⟨unifList_prob _ (by simp), ?_, integrable_unifList _ (by simp) _,
    unifList_tail _ 1 ?_⟩
  · rw [integral_unifList]; norm_num
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> norm_num

/-- The sum of the Dirac masses at `1` and `-1` has total mass `2`, integrates every function, and
the integral of `x ^ 2` against it is `2`. -/
example : (([1, -1] : List ℝ).map Measure.dirac).sum Set.univ = 2 ∧
    Integrable (fun x : ℝ => x) ((([1, -1] : List ℝ).map Measure.dirac).sum) ∧
    ∫ x, x ^ 2 ∂((([1, -1] : List ℝ).map Measure.dirac).sum) = 2 := by
  refine ⟨?_, integrable_listSum _ _, ?_⟩
  · rw [listSum_apply _ MeasurableSet.univ]; simp; norm_num
  · rw [integral_listSum]; norm_num

end WEdgeNS
