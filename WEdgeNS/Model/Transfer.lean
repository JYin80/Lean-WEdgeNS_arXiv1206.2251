import WEdgeNS.Model.General
import WEdgeNS.Resolvent.Basic

/-!
# Transfer from the Wigner model and the GOE to the general model

The matrices of Definition 1.1 (entry law `entryLaw`, scaling `N^{-1/2}`) and the GOE defined after
it are the special cases of the generalized Wigner model of Definition 2.1 in which the entries
are i.i.d. up to the diagonal. This file identifies them: `ofIID` gives the entry laws of
Definition 1.1 as an `EntryLaws`, and `goeLaws` those of the GOE. The distribution functions
`edgeCdf`, `goeCdf` of the rescaled largest eigenvalue agree with `edgeCdfL` of these laws. The
GOE laws satisfy the variance conditions of Definition 2.1, the bounded-support condition of
Definition 2.4 for every exponent `0 < φs < 1/2`, and the moment conditions of Theorem 3.6 with
constant `3` once `N ≥ 3`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

theorem wignerMatrix_eq_symOfEntries (N : ℕ) (ω : Entries N) :
    wignerMatrix N ω = symOfEntries ((Real.sqrt N)⁻¹ • ω) := by
  ext i j
  simp only [wignerMatrix, symOfEntries]
  split_ifs <;> simp

/-- Entry laws of Definition 1.1: `x_ii ∼ ν'`, `x_ij ∼ ν`, rescaled by `N^{-1/2}`. -/
def ofIID (ν ν' : Measure ℝ) (N : ℕ) : EntryLaws N :=
  ⟨fun _ => ν'.map (fun x => (Real.sqrt N)⁻¹ * x), fun _ => ν.map (fun x => (Real.sqrt N)⁻¹ * x)⟩

/-- The GOE entry laws: `h_ij ∼ N(0, 1/N)`, `h_ii ∼ N(0, 2/N)`. -/
def goeLaws (N : ℕ) : EntryLaws N := ofIID (gaussianReal 0 1) (gaussianReal 0 2) N

/-! ### Rescaling lemmas -/

/-- Multiplication by a constant is measurable on `ℝ`. -/
private lemma measurable_mulLeft (c : ℝ) : Measurable fun x : ℝ => c * x :=
  measurable_const.mul measurable_id

/-- `(N^{-1/2})² = N⁻¹`. -/
private lemma invSqrt_sq (N : ℕ) : ((Real.sqrt N)⁻¹) ^ 2 = (N : ℝ)⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]

/-- `(N^{-1/2})³ = N^{-3/2}`. -/
private lemma invSqrt_pow_three (N : ℕ) :
    ((Real.sqrt N)⁻¹) ^ 3 = (N : ℝ) ^ (-(3 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg N), ← Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg N)]
  congr 1
  norm_num

/-- The rescaled largest eigenvalue of `symOfEntries ω` is a measurable function of `ω`. -/
lemma measurable_edgeScaledSym (N : ℕ) :
    Measurable fun ω : Entries N =>
      (N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
    have h : (fun ω : Entries N => (N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2)) =
        edgeScaled N ∘ (fun ω => Real.sqrt N • ω) := by
      funext ω
      simp only [Function.comp, edgeScaled, wignerMatrix_eq_symOfEntries, smul_smul,
        inv_mul_cancel₀ hs, one_smul]
    rw [h]
    exact (measurable_edgeScaled N).comp (measurable_const_smul _)

/-- `symOfEntries` is continuous in the entries. -/
lemma continuous_symOfEntries (N : ℕ) :
    Continuous fun ω : Entries N => symOfEntries ω := by
  refine continuous_matrix fun a b => ?_
  unfold symOfEntries
  by_cases h : a = b
  · simp only [h, dite_true]
    exact (continuous_apply b).comp continuous_fst
  · simp only [h, dite_false]
    by_cases h' : a < b
    · simp only [h', dite_true]
      exact (continuous_apply _).comp continuous_snd
    · simp only [h', dite_false]
      exact (continuous_apply _).comp continuous_snd

/-- The resolvent entries of `symOfEntries ω` at `y + iη` are jointly continuous in `(ω, y)`
for `η > 0`. -/
lemma continuous_resolventC_symOfEntries_prod {N : ℕ} {η : ℝ} (hη : 0 < η) (i j : Fin N) :
    Continuous (fun p : Entries N × ℝ => resolventC (symOfEntries p.1) (⟨p.2, η⟩ : ℂ) i j) := by
  have hz : Continuous fun y : ℝ => (⟨y, η⟩ : ℂ) := by
    have : (fun y : ℝ => (⟨y, η⟩ : ℂ)) = fun y : ℝ => (y : ℂ) + (η : ℂ) * Complex.I := by
      funext y; apply Complex.ext <;> simp
    rw [this]
    exact Complex.continuous_ofReal.add continuous_const
  have hsym : Continuous fun p : Entries N × ℝ => symOfEntries p.1 :=
    (continuous_symOfEntries N).comp continuous_fst
  have hM : Continuous (fun p : Entries N × ℝ => (symOfEntries p.1).map (fun x : ℝ => (x : ℂ)) -
      (⟨p.2, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) :=
    (hsym.matrix_map Complex.continuous_ofReal).sub ((hz.comp continuous_snd).smul continuous_const)
  have hdet : ∀ p : Entries N × ℝ, ((symOfEntries p.1).map (fun x : ℝ => (x : ℂ)) -
      (⟨p.2, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).det ≠ 0 := by
    intro p
    have hH := symOfEntries_isHermitian p.1
    have hne : ∀ α, (hH.eigenvalues α : ℂ) ≠ (⟨p.2, η⟩ : ℂ) := by
      intro α h
      have := congrArg Complex.im h
      simp at this
      linarith
    have h1 := resolventC_mul_eq_one hH hne
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_one] at h2
    exact left_ne_zero_of_mul_eq_one h2
  have hinv : (fun p : Entries N × ℝ => resolventC (symOfEntries p.1) (⟨p.2, η⟩ : ℂ)) = fun p =>
      (((symOfEntries p.1).map (fun x : ℝ => (x : ℂ)) -
        (⟨p.2, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).det)⁻¹ •
      ((symOfEntries p.1).map (fun x : ℝ => (x : ℂ)) -
        (⟨p.2, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).adjugate := by
    funext p
    unfold resolventC
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  have : Continuous (fun p : Entries N × ℝ => resolventC (symOfEntries p.1) (⟨p.2, η⟩ : ℂ)) := by
    rw [hinv]
    exact (hM.matrix_det.inv₀ hdet).smul hM.matrix_adjugate
  exact this.matrix_elem i j

/-- Pushing `N(0, σ)` forward by `x ↦ N^{-1/2} x` gives `N(0, σ / N)`. -/
private lemma gaussianReal_map_invSqrt (N : ℕ) (σ : NNReal) :
    (gaussianReal 0 σ).map (fun x => (Real.sqrt N)⁻¹ * x) =
      gaussianReal 0 ((N : NNReal)⁻¹ * σ) := by
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  ext
  simp

/-- The diagonal GOE laws are `N(0, 2/N)`. -/
private lemma goeLaws_diag (N : ℕ) (i : Fin N) :
    (goeLaws N).diag i = gaussianReal 0 ((N : NNReal)⁻¹ * 2) :=
  gaussianReal_map_invSqrt N 2

/-- The upper GOE laws are `N(0, 1/N)`. -/
private lemma goeLaws_off (N : ℕ) (p : OffDiag N) :
    (goeLaws N).off p = gaussianReal 0 ((N : NNReal)⁻¹ * 1) :=
  gaussianReal_map_invSqrt N 1

/-! ### Identification of the distribution functions -/

theorem map_entryLaw_eq_law_ofIID (ν ν' : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] (N : ℕ) :
    (entryLaw ν ν' N).map (fun ω => (Real.sqrt N)⁻¹ • ω) = (ofIID ν ν' N).law := by
  have hm : Measurable fun x : ℝ => (Real.sqrt N)⁻¹ * x := measurable_mulLeft _
  unfold entryLaw EntryLaws.law ofIID
  simp only
  have e : (fun ω : Entries N => (Real.sqrt N)⁻¹ • ω) =
      Prod.map (fun (x : Fin N → ℝ) i => (fun x : ℝ => (Real.sqrt N)⁻¹ * x) (x i))
        (fun (x : OffDiag N → ℝ) i => (fun x : ℝ => (Real.sqrt N)⁻¹ * x) (x i)) := by
    funext ω
    rfl
  rw [e, ← Measure.map_prod_map, Measure.pi_map_pi (fun _ => hm.aemeasurable),
    Measure.pi_map_pi (fun _ => hm.aemeasurable)]
  · fun_prop
  · fun_prop

theorem edgeCdf_eq_edgeCdfL (ν ν' : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] (N : ℕ) (s : ℝ) : edgeCdf ν ν' N s = edgeCdfL (ofIID ν ν' N) s := by
  have hS : MeasurableSet {ω : Entries N |
      (N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2) ≤ s} :=
    measurableSet_le (measurable_edgeScaledSym N) measurable_const
  unfold edgeCdf edgeCdfL
  rw [← map_entryLaw_eq_law_ofIID, Measure.map_apply (measurable_const_smul _) hS]
  congr 2
  ext ω
  simp [edgeScaled, wignerMatrix_eq_symOfEntries]

theorem goeCdf_eq_edgeCdfL (N : ℕ) (s : ℝ) : goeCdf N s = edgeCdfL (goeLaws N) s := by
  exact edgeCdf_eq_edgeCdfL (gaussianReal 0 1) (gaussianReal 0 2) N s

/-! ### The variance conditions of Definition 2.1 -/

/-- Integrability of `x²` under a pushforward by `x ↦ c x`. -/
private lemma integrable_sq_map {μ : Measure ℝ} (hμ : Integrable (fun x : ℝ => x ^ 2) μ)
    (c : ℝ) : Integrable (fun x : ℝ => x ^ 2) (μ.map (fun x => c * x)) := by
  rw [integrable_map_measure (by fun_prop) (measurable_mulLeft c).aemeasurable]
  refine (hμ.const_mul (c ^ 2)).congr (Eventually.of_forall fun x => ?_)
  simp [mul_pow]

/-- The mean under a pushforward by `x ↦ c x`. -/
private lemma integral_id_map {μ : Measure ℝ} (c : ℝ) :
    ∫ x, x ∂(μ.map (fun x => c * x)) = c * ∫ x, x ∂μ := by
  rw [integral_map (measurable_mulLeft c).aemeasurable (by fun_prop), integral_const_mul]

/-- The second moment under a pushforward by `x ↦ c x`. -/
private lemma integral_sq_map {μ : Measure ℝ} (c : ℝ) :
    ∫ x, x ^ 2 ∂(μ.map (fun x => c * x)) = c ^ 2 * ∫ x, x ^ 2 ∂μ := by
  rw [integral_map (measurable_mulLeft c).aemeasurable (by fun_prop), ← integral_const_mul]
  simp [mul_pow]

theorem ofIID_isGenWigner {ν ν' : Measure ℝ} (h : WignerLaws ν ν') {N : ℕ} (hN : 0 < N) :
    (ofIID ν ν' N).IsGenWigner |∫ x, x ^ 2 ∂ν' - 1| := by
  have := h.prob
  have := h.prob'
  have hN0 : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  refine ⟨⟨fun _ => ?_, fun _ => ?_⟩, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_,
    fun _ => ?_, fun _ => ?_⟩
  · change IsProbabilityMeasure (ν'.map _)
    infer_instance
  · change IsProbabilityMeasure (ν.map _)
    infer_instance
  · exact integrable_sq_map h.sq_int' _
  · exact integrable_sq_map h.sq_int _
  · change ∫ x, x ∂(ν'.map _) = 0
    rw [integral_id_map, h.mean', mul_zero]
  · change ∫ x, x ∂(ν.map _) = 0
    rw [integral_id_map, h.mean, mul_zero]
  · change ∫ x, x ^ 2 ∂(ν.map _) = _
    rw [integral_sq_map, h.var, invSqrt_sq, mul_one]
  · change |∫ x, x ^ 2 ∂(ν'.map _) - (N : ℝ)⁻¹| ≤ _
    rw [integral_sq_map, invSqrt_sq]
    have : (N : ℝ)⁻¹ * ∫ x, x ^ 2 ∂ν' - (N : ℝ)⁻¹ = (∫ x, x ^ 2 ∂ν' - 1) * (N : ℝ)⁻¹ := by ring
    rw [this, abs_mul, abs_of_nonneg hN0]

/-! ### Gaussian tails and moments -/

/-- A centered Gaussian of variance `w` has a sub-Gaussian moment generating function with
parameter `w`. -/
private lemma hasSubgaussianMGF_id_gaussianReal (w : NNReal) :
    HasSubgaussianMGF id w (gaussianReal 0 w) := by
  refine ⟨fun t => by simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := w) t, fun t => ?_⟩
  rw [mgf_id_gaussianReal]
  simp

/-- Tail of a centered Gaussian of variance `w`: `P(ε < |x|) ≤ 2 exp(-ε²/(2w))`. -/
private lemma gaussianReal_tail_le (w : NNReal) {ε : ℝ} (hε : 0 ≤ ε) :
    gaussianReal 0 w {x | ε < |x|} ≤ ENNReal.ofReal (2 * Real.exp (-ε ^ 2 / (2 * w))) := by
  have h := hasSubgaussianMGF_id_gaussianReal w
  have h1 := h.measure_ge_le hε
  have h2 := h.neg.measure_ge_le hε
  have hsub : {x : ℝ | ε < |x|} ⊆ {x | ε ≤ id x} ∪ {x | ε ≤ (-id) x} := by
    intro x hx
    have hx' : ε < |x| := hx
    rcases le_or_gt 0 x with h0 | h0
    · left; rw [abs_of_nonneg h0] at hx'; exact hx'.le
    · right; rw [abs_of_neg h0] at hx'; exact hx'.le
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [two_mul, ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
  refine add_le_add ?_ ?_
  · exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr h1
  · exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr h2

/-- `2 e^{-t} ≤ e^{-u}` when `u ≥ 8` and `t ≥ u²/4`. -/
private lemma two_mul_exp_neg_le {u t : ℝ} (hu : 8 ≤ u) (ht : u ^ 2 / 4 ≤ t) :
    2 * Real.exp (-t) ≤ Real.exp (-u) := by
  have h1 : Real.exp (-t) ≤ Real.exp (-(2 * u)) := Real.exp_le_exp.mpr (by nlinarith)
  have h2 : Real.exp (-(2 * u)) = Real.exp (-u) * Real.exp (-u) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (-u) ≤ 1 / 2 := by
    have h4 : Real.exp (-u) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have h5 : Real.exp (-1) < 1 / 2 := by
      have := Real.exp_one_gt_d9
      rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
      linarith
    linarith
  have h6 : 0 < Real.exp (-u) := Real.exp_pos _
  calc 2 * Real.exp (-t) ≤ 2 * (Real.exp (-u) * Real.exp (-u)) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = (2 * Real.exp (-u)) * Real.exp (-u) := by ring
    _ ≤ 1 * Real.exp (-u) := by
        refine mul_le_mul_of_nonneg_right ?_ h6.le
        linarith
    _ = Real.exp (-u) := one_mul _

/-- Tail bound for a centered Gaussian of variance `σ / N`, `σ ≤ 2`, at the scale `ε` with
`ε² N = u²`, `u ≥ 8`. -/
private lemma gaussianReal_tail_scaled {N : ℕ} {ε u : ℝ} (hN : 0 < N) (hε0 : 0 ≤ ε)
    (σ : NNReal) (hσ0 : 0 < σ) (hσ : σ ≤ 2) (hu : 8 ≤ u) (hεu : ε ^ 2 * N = u ^ 2) :
    gaussianReal 0 ((N : NNReal)⁻¹ * σ) {x | ε < |x|} ≤ ENNReal.ofReal (Real.exp (-u)) := by
  refine (gaussianReal_tail_le _ hε0).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [neg_div]
  refine two_mul_exp_neg_le hu ?_
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hσr : (0 : ℝ) < σ := by exact_mod_cast hσ0
  have hσr2 : (σ : ℝ) ≤ 2 := by exact_mod_cast hσ
  have hw : (((N : NNReal)⁻¹ * σ : NNReal) : ℝ) = (N : ℝ)⁻¹ * σ := by simp
  rw [hw, ← hεu, div_le_div_iff₀ (by norm_num) (by positivity)]
  have : 0 ≤ ε ^ 2 := sq_nonneg ε
  field_simp
  nlinarith

/-- Explicit form of the bounded-support statement for the GOE: with `c = (1 - 2 φs) / 2`, the
condition holds as soon as `N ≥ 8^{1/c}`. -/
private lemma goeLaws_boundedSupport_of_le {φs : ℝ} (h1 : φs < 1 / 2) {N : ℕ}
    (hN : (8 : ℝ) ^ (1 / ((1 - 2 * φs) / 2)) ≤ N) :
    (goeLaws N).BoundedSupport ((N : ℝ) ^ φs) ((1 - 2 * φs) / 2) := by
  set c : ℝ := (1 - 2 * φs) / 2 with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hNr : (0 : ℝ) < N := lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hN
  have hNpos : 0 < N := by exact_mod_cast hNr
  have hu : 8 ≤ (N : ℝ) ^ c := by
    calc (8 : ℝ) = ((8 : ℝ) ^ (1 / c)) ^ c := by
          rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hcpos.ne', Real.rpow_one]
      _ ≤ (N : ℝ) ^ c := Real.rpow_le_rpow (by positivity) hN hcpos.le
  have hq : 0 < (N : ℝ) ^ φs := Real.rpow_pos_of_pos hNr _
  have hεu : (((N : ℝ) ^ φs)⁻¹) ^ 2 * N = ((N : ℝ) ^ c) ^ 2 := by
    have e1 : (N : ℝ) ^ c * (N : ℝ) ^ φs = Real.sqrt N := by
      rw [← Real.rpow_add hNr, Real.sqrt_eq_rpow]
      congr 1
      rw [hc]; ring
    have e2 : ((N : ℝ) ^ c * (N : ℝ) ^ φs) ^ 2 = N := by
      rw [e1, Real.sq_sqrt hNr.le]
    have key : ∀ a b n : ℝ, b ≠ 0 → (a * b) ^ 2 = n → (b⁻¹) ^ 2 * n = a ^ 2 := by
      intro a b n hb h
      rw [← h]
      field_simp
    exact key _ _ _ hq.ne' e2
  refine ⟨fun i => ?_, fun p => ?_⟩
  · rw [goeLaws_diag]
    exact gaussianReal_tail_scaled hNpos (inv_nonneg.mpr hq.le) 2 (by norm_num) le_rfl hu hεu
  · rw [goeLaws_off]
    exact gaussianReal_tail_scaled hNpos (inv_nonneg.mpr hq.le) 1 (by norm_num) (by norm_num)
      hu hεu

theorem goeLaws_boundedSupport {φs : ℝ} (h0 : 0 < φs) (h1 : φs < 1 / 2) :
    ∃ c > 0, ∃ N0 : ℕ, ∀ N ≥ N0, (goeLaws N).BoundedSupport ((N : ℝ) ^ φs) c := by
  have _ := h0
  have hcpos : 0 < (1 - 2 * φs) / 2 := by linarith
  refine ⟨(1 - 2 * φs) / 2, hcpos, ⌈(8 : ℝ) ^ (1 / ((1 - 2 * φs) / 2))⌉₊, fun N hN => ?_⟩
  exact goeLaws_boundedSupport_of_le h1 ((Nat.le_ceil _).trans (by exact_mod_cast hN))

/-! ### The moment conditions of Theorem 3.6 -/

/-- The fourth derivative at `0` of `exp (t² / 2)` gives `E Z⁴ = 3` for `Z ∼ N(0, 1)`. -/
private lemma hasDerivAt_expHalfSq (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 / 2)) (t * Real.exp (t ^ 2 / 2)) t := by
  have h := ((hasDerivAt_pow 2 t).div_const 2).exp
  convert h using 1
  simp only [Nat.cast_ofNat]
  ring

/-- Product rule for `P t * exp (t² / 2)`. -/
private lemma hasDerivAt_mul_expHalfSq {P : ℝ → ℝ} {P' t : ℝ} (hP : HasDerivAt P P' t) :
    HasDerivAt (fun t => P t * Real.exp (t ^ 2 / 2)) ((P' + t * P t) * Real.exp (t ^ 2 / 2)) t := by
  have := hP.mul (hasDerivAt_expHalfSq t)
  convert this using 1
  ring

/-- The fourth moment of the standard Gaussian. -/
private lemma integral_pow_four_gaussianReal : ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal 0 1)) := by simp
  have h := iteratedDeriv_mgf_zero h0 4
  have hm : mgf id (gaussianReal 0 1) = fun t : ℝ => Real.exp (t ^ 2 / 2) := by
    rw [mgf_id_gaussianReal]; funext t; simp
  rw [hm] at h
  have e1 : iteratedDeriv 1 (fun t : ℝ => Real.exp (t ^ 2 / 2)) =
      fun t => t * Real.exp (t ^ 2 / 2) := by
    rw [iteratedDeriv_one]; funext t; exact (hasDerivAt_expHalfSq t).deriv
  have e2 : iteratedDeriv 2 (fun t : ℝ => Real.exp (t ^ 2 / 2)) =
      fun t => (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, e1]; funext t
    have := (hasDerivAt_mul_expHalfSq (P := fun t => t) (hasDerivAt_id t)).deriv
    rw [this]; congr 1; ring
  have e3 : iteratedDeriv 3 (fun t : ℝ => Real.exp (t ^ 2 / 2)) =
      fun t => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, e2]; funext t
    have hp : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t).const_add 1
    have := (hasDerivAt_mul_expHalfSq hp).deriv
    rw [this]; congr 1; ring
  have e4 : iteratedDeriv 4 (fun t : ℝ => Real.exp (t ^ 2 / 2)) =
      fun t => (3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, e3]; funext t
    have hp : HasDerivAt (fun t : ℝ => 3 * t + t ^ 3) (3 + 3 * t ^ 2) t := by
      have h1 := ((hasDerivAt_id t).const_mul 3).fun_add (hasDerivAt_pow 3 t)
      simpa using h1
    have := (hasDerivAt_mul_expHalfSq hp).deriv
    rw [this]; congr 1; ring
  rw [e4] at h
  simp at h
  exact h.symm

/-- Every absolute moment of a centered Gaussian is integrable. -/
private lemma integrable_abs_pow_gaussianReal (v : NNReal) (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k) (gaussianReal 0 v) := by
  have h : MemLp id (k : ℕ) (gaussianReal 0 v) := by
    simpa using memLp_id_gaussianReal' (μ := 0) (v := v) (k : ENNReal) (ENNReal.natCast_ne_top k)
  simpa using h.integrable_norm_pow'

/-- `x²` is integrable under a centered Gaussian. -/
private lemma integrable_sq_gaussianReal (v : NNReal) :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by
  simpa using integrable_abs_pow_gaussianReal v 2

/-- `x⁴` is integrable under a centered Gaussian. -/
private lemma integrable_pow_four_gaussianReal (v : NNReal) :
    Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 v) := by
  have := integrable_abs_pow_gaussianReal v 4
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp [Even.pow_abs (by decide : Even 4)]

/-- The second moment of a centered Gaussian is its variance. -/
lemma integral_sq_gaussianReal (v : NNReal) : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 v) = v := by
  have h := variance_eq_integral (X := id) (μ := gaussianReal 0 v) aemeasurable_id
  rw [variance_id_gaussianReal] at h
  simpa [integral_id_gaussianReal] using h.symm

/-- `E |Z|³ ≤ 2` for a standard Gaussian `Z`. -/
private lemma integral_abs_pow_three_le : ∫ x : ℝ, |x| ^ 3 ∂(gaussianReal 0 1) ≤ 2 := by
  have h2 := integrable_sq_gaussianReal 1
  have h4 := integrable_pow_four_gaussianReal 1
  have h3 := integrable_abs_pow_gaussianReal 1 3
  calc ∫ x : ℝ, |x| ^ 3 ∂(gaussianReal 0 1)
      ≤ ∫ x : ℝ, (x ^ 2 + x ^ 4) / 2 ∂(gaussianReal 0 1) := by
        refine integral_mono h3 ((h2.add h4).div_const 2) fun x => ?_
        have hx : 0 ≤ |x| := abs_nonneg x
        have e2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
        have e4 : x ^ 4 = |x| ^ 4 := (Even.pow_abs (by decide : Even 4) x).symm
        simp only [e2, e4]
        nlinarith [sq_nonneg (|x| * (1 - |x|)), sq_nonneg |x|]
    _ = 2 := by
        rw [integral_div, integral_add h2 h4, integral_sq_gaussianReal,
          integral_pow_four_gaussianReal]
        norm_num

theorem goeLaws_momentCond {N : ℕ} (hN : 3 ≤ N) : (goeLaws N).MomentCond 3 := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hc0 : 0 ≤ (Real.sqrt N)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hNinv : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.mpr hNpos
  have hdiag : ∀ i, (goeLaws N).diag i = gaussianReal 0 ((N : NNReal)⁻¹ * 2) := goeLaws_diag N
  have hoff : ∀ p, (goeLaws N).off p = gaussianReal 0 ((N : NNReal)⁻¹ * 1) := goeLaws_off N
  have hcoe : ∀ σ : NNReal, (((N : NNReal)⁻¹ * σ : NNReal) : ℝ) = (N : ℝ)⁻¹ * σ := fun σ => by simp
  refine ⟨⟨fun i => ?_, fun p => ?_⟩, fun i => ?_, fun p => ?_, fun i => ?_, fun i => ?_,
    fun i => ?_, fun p => ?_, fun p => ?_, fun p => ?_⟩
  · rw [hdiag]; infer_instance
  · rw [hoff]; infer_instance
  · rw [hdiag]; exact integrable_sq_gaussianReal _
  · rw [hoff]; exact integrable_pow_four_gaussianReal _
  · rw [hdiag]; exact integral_id_gaussianReal
  · rw [hoff]; exact integral_id_gaussianReal
  · have h2 : ((2 : NNReal) : ℝ) = 2 := by norm_num
    rw [hdiag, integral_sq_gaussianReal, hcoe, h2, div_eq_inv_mul]
    nlinarith
  · rw [hoff, integral_sq_gaussianReal, hcoe]; simp
  · change ∫ x : ℝ, |x| ^ 3 ∂((gaussianReal 0 1).map (fun x => (Real.sqrt N)⁻¹ * x)) ≤ _
    rw [integral_map (measurable_mulLeft _).aemeasurable (by fun_prop)]
    have e : ∀ z : ℝ, |(Real.sqrt N)⁻¹ * z| ^ 3 = ((Real.sqrt N)⁻¹) ^ 3 * |z| ^ 3 := fun z => by
      rw [abs_mul, abs_of_nonneg hc0, mul_pow]
    simp_rw [e]
    rw [integral_const_mul, invSqrt_pow_three]
    have hpos : 0 < (N : ℝ) ^ (-(3 : ℝ) / 2) := Real.rpow_pos_of_pos hNpos _
    nlinarith [integral_abs_pow_three_le]
  · change ∫ x : ℝ, x ^ 4 ∂((gaussianReal 0 1).map (fun x => (Real.sqrt N)⁻¹ * x)) ≤ _
    rw [integral_map (measurable_mulLeft _).aemeasurable (by fun_prop)]
    have e4 : ((Real.sqrt N)⁻¹) ^ 4 = ((N : ℝ)⁻¹) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, invSqrt_sq]
    have e : ∀ z : ℝ, ((Real.sqrt N)⁻¹ * z) ^ 4 = ((N : ℝ)⁻¹) ^ 2 * z ^ 4 := fun z => by
      rw [mul_pow, e4]
    simp_rw [e]
    rw [integral_const_mul, integral_pow_four_gaussianReal]
    have hlog : 1 ≤ Real.log N := by
      rw [Real.le_log_iff_exp_le hNpos]
      have := Real.exp_one_lt_d9
      linarith
    rw [le_div_iff₀ (by positivity), inv_pow]
    field_simp
    linarith

example : (goeLaws 3).MomentCond 3 := goeLaws_momentCond (le_refl 3)

/-! ### Compiled witnesses -/

/-- `N = 2`, diagonal entries `a, b`, upper entry `u`: `H_2 = 2^{-1/2} [[a, u], [u, b]]`, and the
upper entry of `H_2` is `2^{-1/2} u`. -/
example (a b u : ℝ) :
    wignerMatrix 2 (![a, b], fun _ => u) 0 1 = (Real.sqrt 2)⁻¹ * u ∧
      symOfEntries ((Real.sqrt (2 : ℕ))⁻¹ • ((![a, b], fun _ => u) : Entries 2)) 0 1 =
        (Real.sqrt 2)⁻¹ * u := by
  have h := congrFun (congrFun (wignerMatrix_eq_symOfEntries 2 (![a, b], fun _ => u)) 0) 1
  have h0 : wignerMatrix 2 (![a, b], fun _ => u) 0 1 = (Real.sqrt 2)⁻¹ * u := by
    simp [wignerMatrix]
  exact ⟨h0, h.symm.trans h0⟩

/-- `N = 3`, Gaussian entry laws: the pushforward identity of the entry law. -/
example :
    (entryLaw (gaussianReal 0 1) (gaussianReal 0 2) 3).map (fun ω => (Real.sqrt (3 : ℕ))⁻¹ • ω) =
      (ofIID (gaussianReal 0 1) (gaussianReal 0 2) 3).law :=
  map_entryLaw_eq_law_ofIID _ _ 3

/-- `N = 3`, `s = 0`, Gaussian entry laws: the distribution functions agree. -/
example :
    edgeCdf (gaussianReal 0 1) (gaussianReal 0 2) 3 0 =
      edgeCdfL (ofIID (gaussianReal 0 1) (gaussianReal 0 2) 3) 0 :=
  edgeCdf_eq_edgeCdfL _ _ 3 0

/-- `N = 3`, `s = 0`: the GOE distribution functions agree. -/
example : goeCdf 3 0 = edgeCdfL (goeLaws 3) 0 := goeCdf_eq_edgeCdfL 3 0

/-- `N = 3`, GOE laws: the entry laws are generalized Wigner with `C0 = 1`
(`∫ x² ∂N(0, 2) = 2`). -/
example : (ofIID (gaussianReal 0 1) (gaussianReal 0 2) 3).IsGenWigner 1 := by
  have h := ofIID_isGenWigner goe_wignerLaws (N := 3) (by norm_num)
  have e : |∫ x, x ^ 2 ∂(gaussianReal 0 2) - 1| = 1 := by
    rw [integral_sq_gaussianReal]; norm_num
  rwa [e] at h

/-- `N = 3`, Rademacher off-diagonal entries and `N(0, 2)` diagonal entries. -/
example : (ofIID rademacher (gaussianReal 0 2) 3).IsGenWigner 1 := by
  have h := ofIID_isGenWigner rademacher_wignerLaws (N := 3) (by norm_num)
  have e : |∫ x, x ^ 2 ∂(gaussianReal 0 2) - 1| = 1 := by
    rw [integral_sq_gaussianReal]; norm_num
  rwa [e] at h

/-- `φs = 1/4`: the exponent is `c = 1/4` and `N = 4096 = 8⁴` is admissible. -/
example : (goeLaws 4096).BoundedSupport (((4096 : ℕ) : ℝ) ^ (1 / 4 : ℝ)) (1 / 4) := by
  have h := goeLaws_boundedSupport_of_le (φs := 1 / 4) (N := 4096) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example : ∃ c > 0, ∃ N0 : ℕ, ∀ N ≥ N0,
    (goeLaws N).BoundedSupport ((N : ℝ) ^ (1 / 4 : ℝ)) c :=
  goeLaws_boundedSupport (by norm_num) (by norm_num)

/-- At `N = 3`: the rescaled largest eigenvalue and the symmetric matrix are measurable and
continuous functions of the entries, the resolvent entries at `y + i` are jointly continuous in
`(ω, y)`, and `∫ x² dN(0, 2) = 2`. -/
example : Measurable (fun ω : Entries 3 =>
      ((3 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2)) ∧
    Continuous (fun ω : Entries 3 => symOfEntries ω) ∧
    Continuous (fun p : Entries 3 × ℝ => resolventC (symOfEntries p.1) (⟨p.2, 1⟩ : ℂ) 0 1) ∧
    ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 2) = 2 :=
  ⟨measurable_edgeScaledSym 3, continuous_symOfEntries 3,
    continuous_resolventC_symOfEntries_prod one_pos 0 1, by rw [integral_sq_gaussianReal]; norm_num⟩

#print axioms wignerMatrix_eq_symOfEntries
#print axioms map_entryLaw_eq_law_ofIID
#print axioms edgeCdf_eq_edgeCdfL
#print axioms goeCdf_eq_edgeCdfL
#print axioms ofIID_isGenWigner
#print axioms goeLaws_boundedSupport
#print axioms goeLaws_momentCond

end WEdgeNS
