import WEdgeNS.Model.HighProb
import WEdgeNS.Model.Ensembles

/-!
# Admissible support parameters and the spectral domain of Lemma 3.1
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

namespace EntryLaws

variable {N : ℕ}

/-- Tail variance of every off-diagonal entry beyond `q⁻¹` is at most `exp(-N^c)`. -/
def TailVarOff (L : EntryLaws N) (q c : ℝ) : Prop :=
  ∀ p, ∫ x in {x : ℝ | q⁻¹ < |x|}, x ^ 2 ∂(L.off p) ≤ Real.exp (-(N : ℝ) ^ c)

/-- `q ≥ Q` is an admissible support parameter: Definition 2.4 with `c`, plus `TailVarOff`. -/
def SupportParam (L : EntryLaws N) (Q c q : ℝ) : Prop :=
  Q ≤ q ∧ L.BoundedSupport q c ∧ L.TailVarOff q c

end EntryLaws

open EntryLaws

/-- `S(C)` of (3.1). -/
def specDomain (N : ℕ) (C : ℝ) : Set ℂ :=
  {z | |z.re| ≤ 5 ∧ phi N ^ C / N < z.im ∧ z.im ≤ 10}

/-- Almost surely bounded entries have no off-diagonal tail variance beyond `q⁻¹`. -/
theorem EntryLaws.BoundedSupportAS.tailVarOff {N : ℕ} {L : EntryLaws N} {q : ℝ}
    (h : L.BoundedSupportAS q) (c : ℝ) : L.TailVarOff q c := by
  intro p
  have h0 : (L.off p).restrict {x : ℝ | q⁻¹ < |x|} = 0 := Measure.restrict_eq_zero.mpr (h.2 p)
  rw [h0, integral_zero_measure]
  exact (Real.exp_pos _).le

/-- `TailVarOff` is preserved by `interp`. -/
theorem EntryLaws.interp_tailVarOff {N : ℕ} {Φ : Fin N ⊕ OffDiag N → ℕ} {γ : ℕ}
    {Lv Lw : EntryLaws N} {q c : ℝ} (hv : Lv.TailVarOff q c) (hw : Lw.TailVarOff q c) :
    (interp Φ γ Lv Lw).TailVarOff q c := by
  intro p
  simp only [interp]
  split_ifs
  exacts [hv p, hw p]

/-- `SupportParam` is preserved by `interp`. -/
theorem EntryLaws.interp_supportParam {N : ℕ} {Φ : Fin N ⊕ OffDiag N → ℕ} {γ : ℕ}
    {Lv Lw : EntryLaws N} {Q q c : ℝ} (hv : Lv.SupportParam Q c q) (hw : Lw.SupportParam Q c q) :
    (interp Φ γ Lv Lw).SupportParam Q c q :=
  ⟨hv.1, interp_boundedSupport hv.2.1 hw.2.1, interp_tailVarOff hv.2.2 hw.2.2⟩

/-- The laws of Theorem 3.6 are generalized Wigner laws. -/
theorem EntryLaws.MomentCond.isGenWigner {N : ℕ} {L : EntryLaws N} {C1 : ℝ}
    (h : L.MomentCond C1) : L.IsGenWigner (max C1 1) := by
  refine ⟨h.isProb, h.sq_int_diag, fun p => ?_, h.mean_diag, h.mean_off, h.var_off, fun i => ?_⟩
  · have := h.isProb.off p
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add (h.fourth_int_off p))
      (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg x]
  · have h0 : 0 ≤ ∫ x, x ^ 2 ∂(L.diag i) := integral_nonneg fun x => sq_nonneg x
    have h1 := h.var_diag_le i
    have hN : 0 ≤ (N : ℝ)⁻¹ := by positivity
    have hm1 : C1 ≤ max C1 1 := le_max_left _ _
    have hm2 : 1 ≤ max C1 1 := le_max_right _ _
    rw [div_eq_mul_inv] at h1
    rw [abs_le]
    constructor <;> nlinarith

/-- Weighted Cauchy–Schwarz: `∫_A x² ≤ (l ∫ x⁴ + μ(A)/l) / 2` for every `l > 0`. -/
private lemma setIntegral_sq_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h2 : Integrable (fun x : ℝ => x ^ 2) μ) (h4 : Integrable (fun x : ℝ => x ^ 4) μ)
    {A : Set ℝ} (hA : MeasurableSet A) {l : ℝ} (hl : 0 < l) :
    ∫ x in A, x ^ 2 ∂μ ≤ (l * ∫ x, x ^ 4 ∂μ + μ.real A / l) / 2 := by
  have hpt : ∀ x : ℝ, x ^ 2 ≤ (l * x ^ 4 + 1 / l) / 2 := by
    intro x
    have e : (l * x ^ 4 + 1 / l) / 2 - x ^ 2 = (l * x ^ 2 - 1) ^ 2 / l / 2 := by
      field_simp; ring
    have : 0 ≤ (l * x ^ 2 - 1) ^ 2 / l / 2 := by positivity
    linarith
  have hg : Integrable (fun x : ℝ => (l * x ^ 4 + 1 / l) / 2) μ :=
    ((h4.const_mul l).add (integrable_const _)).div_const 2
  calc ∫ x in A, x ^ 2 ∂μ ≤ ∫ x in A, (l * x ^ 4 + 1 / l) / 2 ∂μ :=
        setIntegral_mono_on h2.integrableOn hg.integrableOn hA fun x _ => hpt x
    _ = (l * ∫ x in A, x ^ 4 ∂μ + μ.real A / l) / 2 := by
        rw [integral_div, integral_add (h4.const_mul l).integrableOn
          (integrable_const _).integrableOn, integral_const_mul, setIntegral_const]
        simp only [smul_eq_mul]
        ring
    _ ≤ (l * ∫ x, x ^ 4 ∂μ + μ.real A / l) / 2 := by
        have : ∫ x in A, x ^ 4 ∂μ ≤ ∫ x, x ^ 4 ∂μ :=
          setIntegral_le_integral h4 (Eventually.of_forall fun x => by positivity)
        have := mul_le_mul_of_nonneg_left this hl.le
        linarith

/-- The laws of Theorem 3.6 satisfy `TailVarOff` with `c / 2`. -/
theorem EntryLaws.momentCond_tailVarOff {C1 c : ℝ} (hc : 0 < c) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (L : EntryLaws N) (q : ℝ), L.MomentCond C1 →
      L.BoundedSupport q c → L.TailVarOff q (c / 2) := by
  set K : ℝ := max C1 0 + 1 with hK
  have hC0 : 0 ≤ max C1 0 := le_max_right C1 0
  have hK1 : 1 ≤ K := by linarith
  refine ⟨max 1 ⌈(2 * K + 2) ^ (2 / c)⌉₊, fun N hN L q hM hB p => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  set t : ℝ := (N : ℝ) ^ (c / 2) with ht
  have ht2 : t ^ 2 = (N : ℝ) ^ c := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    congr 1; push_cast; ring
  have htK : 2 * K + 2 ≤ t := by
    have hle : (2 * K + 2) ^ (2 / c) ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
    calc 2 * K + 2 = ((2 * K + 2) ^ (2 / c)) ^ (c / 2) := by
          rw [← Real.rpow_mul (by positivity)]
          have : 2 / c * (c / 2) = 1 := by field_simp
          rw [this, Real.rpow_one]
      _ ≤ (N : ℝ) ^ (c / 2) := Real.rpow_le_rpow (by positivity) hle (by positivity)
  have hprob := hM.isProb.off p
  have hP : (L.off p).real {x : ℝ | q⁻¹ < |x|} ≤ Real.exp (-t ^ 2) := by
    rw [ht2]
    exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le (hB.2 p)
  have hM4 : ∫ x, x ^ 4 ∂(L.off p) ≤ max C1 0 / N := by
    refine (hM.fourth_off_le p).trans ?_
    have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hNr
    have hlogN : Real.log N ≤ N := Real.log_le_self hNpos.le
    rw [div_le_div_iff₀ (by positivity) hNpos]
    have h1 : C1 * Real.log N ≤ max C1 0 * N :=
      mul_le_mul (le_max_left _ _) hlogN hlog0 hC0
    nlinarith
  have hE : 0 < Real.exp (-t ^ 2 / 2) := Real.exp_pos _
  have hl : 0 < (N : ℝ) * Real.exp (-t ^ 2 / 2) := by positivity
  have hY := setIntegral_sq_le (hM.isGenWigner.sq_int_off p) (hM.fourth_int_off p)
    (measurableSet_lt measurable_const measurable_abs : MeasurableSet {x : ℝ | q⁻¹ < |x|}) hl
  have h1 : (N : ℝ) * Real.exp (-t ^ 2 / 2) * ∫ x, x ^ 4 ∂(L.off p) ≤
      max C1 0 * Real.exp (-t ^ 2 / 2) := by
    calc _ ≤ (N : ℝ) * Real.exp (-t ^ 2 / 2) * (max C1 0 / N) := by gcongr
      _ = max C1 0 * Real.exp (-t ^ 2 / 2) := by field_simp
  have h2 : (L.off p).real {x : ℝ | q⁻¹ < |x|} / ((N : ℝ) * Real.exp (-t ^ 2 / 2)) ≤
      Real.exp (-t ^ 2 / 2) := by
    rw [div_le_iff₀ hl]
    have e : Real.exp (-t ^ 2) = Real.exp (-t ^ 2 / 2) * Real.exp (-t ^ 2 / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc _ ≤ Real.exp (-t ^ 2) := hP
      _ = Real.exp (-t ^ 2 / 2) * Real.exp (-t ^ 2 / 2) := e
      _ ≤ Real.exp (-t ^ 2 / 2) * ((N : ℝ) * Real.exp (-t ^ 2 / 2)) := by
          gcongr
          exact le_mul_of_one_le_left hE.le hNr
  have h3 : K * Real.exp (-t ^ 2 / 2) ≤ Real.exp (-t) := by
    have hKt : K ≤ t ^ 2 / 2 - t := by nlinarith
    have hKe : K ≤ Real.exp K := by linarith [Real.add_one_le_exp K]
    calc K * Real.exp (-t ^ 2 / 2) ≤ Real.exp (t ^ 2 / 2 - t) * Real.exp (-t ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right (hKe.trans (Real.exp_le_exp.mpr hKt)) hE.le
      _ = Real.exp (-t) := by rw [← Real.exp_add]; congr 1; ring
  have hC : max C1 0 * Real.exp (-t ^ 2 / 2) + Real.exp (-t ^ 2 / 2) =
      K * Real.exp (-t ^ 2 / 2) := by rw [hK]; ring
  calc ∫ x in {x : ℝ | q⁻¹ < |x|}, x ^ 2 ∂(L.off p)
      ≤ _ := hY
    _ ≤ (max C1 0 * Real.exp (-t ^ 2 / 2) + Real.exp (-t ^ 2 / 2)) / 2 := by linarith
    _ ≤ K * Real.exp (-t ^ 2 / 2) := by rw [hC]; nlinarith
    _ ≤ Real.exp (-t) := h3

/-- Tail variance of a centered Gaussian of variance `v` beyond `t`, for every `s > 0`. -/
private lemma gaussianReal_tailVar_le (v : NNReal) {t s : ℝ} (hs : 0 < s) :
    ∫ x in {x : ℝ | t < |x|}, x ^ 2 ∂(gaussianReal 0 v) ≤
      4 / s ^ 2 * Real.exp (-(s * t) + 2 * v * s ^ 2) := by
  have hA : MeasurableSet {x : ℝ | t < |x|} := measurableSet_lt measurable_const measurable_abs
  have h2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  have hI1 := integrable_exp_mul_gaussianReal (μ := 0) (v := v) (2 * s)
  have hI2 := integrable_exp_mul_gaussianReal (μ := 0) (v := v) (-(2 * s))
  set g : ℝ → ℝ := fun x => 2 / s ^ 2 * Real.exp (-(s * t)) *
    (Real.exp (2 * s * x) + Real.exp (-(2 * s) * x)) with hg_def
  have hg : Integrable g (gaussianReal 0 v) := (hI1.add hI2).const_mul _
  have hpt : ∀ x ∈ {x : ℝ | t < |x|}, x ^ 2 ≤ g x := by
    intro x hx
    have hx' : t < |x| := hx
    have h1 : (s * |x|) ^ 2 / 2 ≤ Real.exp (s * |x|) := by
      have := Real.pow_div_factorial_le_exp (s * |x|) (by positivity) 2
      simpa [Nat.factorial] using this
    have h2 : Real.exp (s * |x|) ≤ Real.exp (-(s * t)) * Real.exp (2 * s * |x|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_pos hs (sub_pos.2 hx')]
    have h3 : Real.exp (2 * s * |x|) ≤ Real.exp (2 * s * x) + Real.exp (-(2 * s) * x) := by
      rcases abs_choice x with h | h
      · rw [h]; linarith [Real.exp_pos (-(2 * s) * x)]
      · rw [h, show 2 * s * -x = -(2 * s) * x by ring]; linarith [Real.exp_pos (2 * s * x)]
    have hx2 : x ^ 2 = 2 / s ^ 2 * ((s * |x|) ^ 2 / 2) := by
      rw [mul_pow, sq_abs]; field_simp
    have hc : 0 ≤ 2 / s ^ 2 := by positivity
    calc x ^ 2 = 2 / s ^ 2 * ((s * |x|) ^ 2 / 2) := hx2
      _ ≤ 2 / s ^ 2 * Real.exp (s * |x|) := by gcongr
      _ ≤ 2 / s ^ 2 * (Real.exp (-(s * t)) * Real.exp (2 * s * |x|)) := by gcongr
      _ ≤ 2 / s ^ 2 * (Real.exp (-(s * t)) * (Real.exp (2 * s * x) + Real.exp (-(2 * s) * x))) := by
          gcongr
      _ = g x := by rw [hg_def]; ring
  have hmgf : ∀ a : ℝ, ∫ x, Real.exp (a * x) ∂(gaussianReal 0 v) = Real.exp (v * a ^ 2 / 2) := by
    intro a
    have := congrFun (mgf_id_gaussianReal (μ := 0) (v := v)) a
    simpa [mgf] using this
  calc ∫ x in {x : ℝ | t < |x|}, x ^ 2 ∂(gaussianReal 0 v)
      ≤ ∫ x in {x : ℝ | t < |x|}, g x ∂(gaussianReal 0 v) :=
        setIntegral_mono_on h2.integrableOn hg.integrableOn hA hpt
    _ ≤ ∫ x, g x ∂(gaussianReal 0 v) :=
        setIntegral_le_integral hg (Eventually.of_forall fun x => by positivity)
    _ = 4 / s ^ 2 * Real.exp (-(s * t) + 2 * v * s ^ 2) := by
        rw [hg_def]
        simp only
        rw [integral_const_mul, integral_add hI1 hI2, hmgf, hmgf]
        have e : Real.exp (v * (2 * s) ^ 2 / 2) = Real.exp (2 * v * s ^ 2) := by
          congr 1; ring
        have e' : Real.exp (v * (-(2 * s)) ^ 2 / 2) = Real.exp (2 * v * s ^ 2) := by
          congr 1; ring
        rw [e, e', Real.exp_add]
        ring

/-- Gaussian entries of variance at most `2/N` have small tail variance. -/
theorem gaussianReal_tailVar {φs : ℝ} (h0 : 0 < φs) (h1 : φs < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N ≥ N0, ∀ v : NNReal, (v : ℝ) ≤ 2 / N →
      ∫ x in {x : ℝ | ((N : ℝ) ^ φs)⁻¹ < |x|}, x ^ 2 ∂(gaussianReal 0 v) ≤
        Real.exp (-(N : ℝ) ^ c) := by
  have _ := h0
  set c : ℝ := (1 - 2 * φs) / 2 with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  refine ⟨c, hcpos, max 256 ⌈(16 : ℝ) ^ (1 / c)⌉₊, fun N hN v hv => ?_⟩
  have hNr : (256 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_left _ _) hN
  have hNpos : (0 : ℝ) < N := by linarith
  set u : ℝ := (N : ℝ) ^ c with hu
  have hu16 : 16 ≤ u := by
    have hle : (16 : ℝ) ^ (1 / c) ≤ N :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
    calc (16 : ℝ) = ((16 : ℝ) ^ (1 / c)) ^ c := by
          rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hcpos.ne', Real.rpow_one]
      _ ≤ u := Real.rpow_le_rpow (by positivity) hle hcpos.le
  have hq : 0 < (N : ℝ) ^ φs := Real.rpow_pos_of_pos hNpos _
  set t : ℝ := ((N : ℝ) ^ φs)⁻¹ with ht
  have hNt : t ^ 2 * N = u ^ 2 := by
    have e1 : (N : ℝ) ^ φs * (N : ℝ) ^ c = Real.sqrt N := by
      rw [← Real.rpow_add hNpos, Real.sqrt_eq_rpow]
      congr 1
      rw [hc]; ring
    have e2 : ((N : ℝ) ^ φs * (N : ℝ) ^ c) ^ 2 = N := by
      rw [e1, Real.sq_sqrt hNpos.le]
    have key : ∀ a b n : ℝ, a ≠ 0 → (a * b) ^ 2 = n → (a⁻¹) ^ 2 * n = b ^ 2 := by
      intro a b n ha h
      rw [← h]
      field_simp
    exact key _ _ _ hq.ne' e2
  have ht0 : 0 < t := inv_pos.mpr hq
  set s : ℝ := N * t / 8 with hs_def
  have hs : 0 < s := by positivity
  have hs2 : s ^ 2 = N * u ^ 2 / 64 := by
    rw [hs_def, ← hNt]; ring
  have hst : s * t = u ^ 2 / 8 := by
    rw [hs_def, ← hNt]; ring
  have hv' : (v : ℝ) ≤ 2 / N := hv
  have hvs : 2 * (v : ℝ) * s ^ 2 ≤ u ^ 2 / 16 := by
    calc 2 * (v : ℝ) * s ^ 2 ≤ 2 * (2 / N) * s ^ 2 := by gcongr
      _ = u ^ 2 / 16 := by rw [hs2]; field_simp; ring
  have h4s : 4 / s ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity), hs2]
    nlinarith
  calc ∫ x in {x : ℝ | t < |x|}, x ^ 2 ∂(gaussianReal 0 v)
      ≤ 4 / s ^ 2 * Real.exp (-(s * t) + 2 * v * s ^ 2) := gaussianReal_tailVar_le v hs
    _ ≤ 1 * Real.exp (-(u ^ 2 / 16)) :=
        mul_le_mul h4s (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le zero_le_one
    _ ≤ Real.exp (-u) := by
        rw [one_mul]
        exact Real.exp_le_exp.mpr (by nlinarith)

/-- The tail set `{x | q⁻¹ < |x|}` is measurable. -/
private lemma measurableSet_tail (q : ℝ) : MeasurableSet {x : ℝ | q⁻¹ < |x|} :=
  measurableSet_lt measurable_const measurable_abs

/-- The upper index pair `(0, 1)` (needs `N ≥ 2`). -/
private def offIdx01 {N : ℕ} (hN : 2 ≤ N) : OffDiag N :=
  ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.lt_def]⟩

/-- Variance split at the cut `q⁻¹`: the part inside the cut is at most `max q⁻¹ 0 ^ 2`. -/
private lemma inv_var_le_tail_add {N : ℕ} {L : EntryLaws N} {C0 : ℝ} (hL : L.IsGenWigner C0)
    (p : OffDiag N) (q : ℝ) :
    (N : ℝ)⁻¹ ≤ (∫ x in {x : ℝ | q⁻¹ < |x|}, x ^ 2 ∂(L.off p)) + (max q⁻¹ 0) ^ 2 := by
  have := hL.isProb.off p
  have hsplit := integral_add_compl (measurableSet_tail q) (hL.sq_int_off p)
  rw [hL.var_off p] at hsplit
  have hb : ‖∫ x in {x : ℝ | q⁻¹ < |x|}ᶜ, x ^ 2 ∂(L.off p)‖ ≤
      (max q⁻¹ 0) ^ 2 * (L.off p).real {x : ℝ | q⁻¹ < |x|}ᶜ := by
    refine norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) (fun x hx => ?_)
    have hx' : |x| ≤ q⁻¹ := by simpa using hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
    have : |x| ≤ max q⁻¹ 0 := hx'.trans (le_max_left _ _)
    calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ ≤ (max q⁻¹ 0) ^ 2 := by gcongr
  have hr : (L.off p).real {x : ℝ | q⁻¹ < |x|}ᶜ ≤ 1 := measureReal_le_one
  have h0 : 0 ≤ (max q⁻¹ 0) ^ 2 := sq_nonneg _
  have h1 := (le_abs_self _).trans hb
  nlinarith

/-- Every admissible `q` is positive and at most `1 + (N⁻¹ - exp(-N^c))⁻¹`. -/
private lemma supportParam_pos_le {N : ℕ} {L : EntryLaws N} {C0 Q c q : ℝ}
    (hL : L.IsGenWigner C0) (hN : 2 ≤ N) (hNc : Real.exp (-(N : ℝ) ^ c) < (N : ℝ)⁻¹)
    (hq : L.SupportParam Q c q) :
    0 < q ∧ q ≤ 1 + ((N : ℝ)⁻¹ - Real.exp (-(N : ℝ) ^ c))⁻¹ := by
  have hp := inv_var_le_tail_add hL (offIdx01 hN) q
  have ht := hq.2.2 (offIdx01 hN)
  have hδ : 0 < (N : ℝ)⁻¹ - Real.exp (-(N : ℝ) ^ c) := sub_pos.mpr hNc
  have hmax : (N : ℝ)⁻¹ - Real.exp (-(N : ℝ) ^ c) ≤ (max q⁻¹ 0) ^ 2 := by linarith
  have hqpos : 0 < q := by
    by_contra hneg
    have hneg := not_lt.mp hneg
    rw [max_eq_right (inv_nonpos.mpr hneg)] at hmax
    norm_num at hmax
    linarith
  refine ⟨hqpos, ?_⟩
  rw [max_eq_left (inv_nonneg.mpr hqpos.le), inv_pow] at hmax
  have h2 : q ^ 2 ≤ ((N : ℝ)⁻¹ - Real.exp (-(N : ℝ) ^ c))⁻¹ :=
    (le_inv_comm₀ hδ (by positivity)).mp hmax
  nlinarith [sq_nonneg (q - 1)]

/-- The set of admissible parameters is bounded above. -/
private lemma supportParam_bddAbove {N : ℕ} {L : EntryLaws N} {C0 Q c : ℝ}
    (hL : L.IsGenWigner C0) (hN : 2 ≤ N) (hNc : Real.exp (-(N : ℝ) ^ c) < (N : ℝ)⁻¹) :
    BddAbove {q | L.SupportParam Q c q} :=
  ⟨_, fun _ hq => (supportParam_pos_le hL hN hNc hq).2⟩

/-- The largest admissible support parameter is admissible. -/
theorem EntryLaws.supportParam_sSup {N : ℕ} {L : EntryLaws N} {C0 Q c : ℝ}
    (hL : L.IsGenWigner C0) (hN : 2 ≤ N) (hNc : Real.exp (-(N : ℝ) ^ c) < (N : ℝ)⁻¹)
    (hne : ∃ q, L.SupportParam Q c q) :
    L.SupportParam Q c (sSup {q | L.SupportParam Q c q}) := by
  set S : Set ℝ := {q | L.SupportParam Q c q} with hS
  have hbdd : BddAbove S := supportParam_bddAbove hL hN hNc
  have hSne : S.Nonempty := hne
  obtain ⟨u, hmono, hlim, huS⟩ := exists_seq_tendsto_sSup hSne hbdd
  set s := sSup S with hs
  obtain ⟨q0, hq0⟩ := hSne
  have hs0 : 0 < s := (supportParam_pos_le hL hN hNc hq0).1.trans_le (le_csSup hbdd hq0)
  -- the increasing sets `A_{u n}` exhaust `A_s`
  have hAmono : Monotone fun n => {x : ℝ | (u n)⁻¹ < |x|} := by
    intro m n hmn x hx
    have hum : 0 < u m := (supportParam_pos_le hL hN hNc (huS m)).1
    exact lt_of_le_of_lt (inv_anti₀ hum (hmono hmn)) hx
  have hAunion : (⋃ n, {x : ℝ | (u n)⁻¹ < |x|}) = {x : ℝ | s⁻¹ < |x|} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      have hun : 0 < u n := (supportParam_pos_le hL hN hNc (huS n)).1
      exact lt_of_le_of_lt (inv_anti₀ hun (le_csSup hbdd (huS n))) hn
    · intro hx
      have hx0 : 0 < |x| := lt_of_le_of_lt (inv_nonneg.mpr hs0.le) hx
      have hlt : |x|⁻¹ < s := by
        rw [inv_lt_comm₀ hx0 hs0]; exact hx
      obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds hlt)).exists
      have hun : 0 < u n := (supportParam_pos_le hL hN hNc (huS n)).1
      exact ⟨n, by rw [inv_lt_comm₀ hun hx0]; exact hn⟩
  refine ⟨?_, ⟨fun i => ?_, fun p => ?_⟩, fun p => ?_⟩
  · exact (hq0.1).trans (le_csSup hbdd hq0)
  · rw [← hAunion, hAmono.measure_iUnion]
    exact iSup_le fun n => (huS n).2.1.1 i
  · rw [← hAunion, hAmono.measure_iUnion]
    exact iSup_le fun n => (huS n).2.1.2 p
  · have hint : IntegrableOn (fun x : ℝ => x ^ 2) (⋃ n, {x : ℝ | (u n)⁻¹ < |x|}) (L.off p) :=
      (hL.sq_int_off p).integrableOn
    have hT := tendsto_setIntegral_of_monotone (fun n => measurableSet_tail (u n)) hAmono hint
    rw [hAunion] at hT
    exact le_of_tendsto' hT fun n => (huS n).2.2 p

/-- For large `N`, `exp(-N^c) < N⁻¹`. -/
private lemma exists_exp_neg_rpow_lt {c : ℝ} (hc : 0 < c) :
    ∃ N1 : ℕ, ∀ N ≥ N1, 2 ≤ N ∧ Real.exp (-(N : ℝ) ^ c) < (N : ℝ)⁻¹ := by
  have h := (isLittleO_log_rpow_atTop hc).bound (show (0 : ℝ) < 1 / 2 by norm_num)
  have h' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (h'.and (eventually_ge_atTop 2))
  refine ⟨N1, fun N hN => ?_⟩
  obtain ⟨hb, h2⟩ := hN1 N hN
  refine ⟨h2, ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hpos : 0 < (N : ℝ) ^ c := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hN1'),
    abs_of_nonneg hpos.le] at hb
  calc Real.exp (-(N : ℝ) ^ c) < Real.exp (-Real.log N) := Real.exp_lt_exp.mpr (by linarith)
    _ = (N : ℝ)⁻¹ := by rw [Real.exp_neg, Real.exp_log hN0]

/-- From bounds uniform in the support parameter to the `∀ q` form. -/
theorem highProbOn_forall_param {ζ C0 c : ℝ} (hc : 0 < c) {Q : ℕ → ℝ}
    {Ω : ∀ N : ℕ, ℝ → Set (Entries N)}
    (hmono : ∀ N q q', 0 < q → q ≤ q' → Ω N q' ⊆ Ω N q)
    (h : ∃ c' > 0, ∃ C' > 0, ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (L : EntryLaws N) (q : ℝ),
      L.IsGenWigner C0 → L.SupportParam (Q N) c q →
        L.law (Ω N q)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ C' * Real.exp (-c' * phi N ^ ζ))) :
    HighProbOn ζ (fun _ L => L.IsGenWigner C0)
      (fun N L => {ω | ∀ q, L.SupportParam (Q N) c q → ω ∈ Ω N q}) := by
  obtain ⟨c', hc', C', hC', N0, h⟩ := h
  obtain ⟨N1, hN1⟩ := exists_exp_neg_rpow_lt hc
  refine ⟨c', hc', C', hC', max N0 N1, fun N hN L hL => ?_⟩
  have hN0 : N0 ≤ N := le_trans (le_max_left _ _) hN
  obtain ⟨hN2, hNc⟩ := hN1 N (le_trans (le_max_right _ _) hN)
  by_cases hne : ∃ q, L.SupportParam (Q N) c q
  · have hmem := supportParam_sSup hL hN2 hNc hne
    have hbdd := supportParam_bddAbove (Q := Q N) hL hN2 hNc
    refine (measure_mono ?_).trans (h N hN0 L _ hL hmem)
    intro ω hω hω'
    exact hω fun q hq =>
      hmono N q _ (supportParam_pos_le hL hN2 hNc hq).1 (le_csSup hbdd hq) hω'
  · have hnull : L.law {ω : Entries N | ∀ q, L.SupportParam (Q N) c q → ω ∈ Ω N q}ᶜ = 0 :=
      measure_mono_null (fun ω hω => (hω fun q hq => absurd ⟨q, hq⟩ hne).elim) measure_empty
    rw [hnull]
    exact zero_le

/-! ### Compiled witnesses -/

/-- `(1-w)/2 (δ_a + δ_{-a}) + w/2 (δ_b + δ_{-b})`. -/
private def sym2 (a b w : ℝ) : Measure ℝ :=
  ENNReal.ofReal ((1 - w) / 2) • (Measure.dirac a + Measure.dirac (-a)) +
    ENNReal.ofReal (w / 2) • (Measure.dirac b + Measure.dirac (-b))

private lemma sym2_prob {a b w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) :
    IsProbabilityMeasure (sym2 a b w) := by
  constructor
  simp only [sym2, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul]
  have e1 : ENNReal.ofReal ((1 - w) / 2) * (1 + 1) = ENNReal.ofReal (1 - w) := by
    rw [one_add_one_eq_two, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by linarith)]
    congr 1; ring
  have e2 : ENNReal.ofReal (w / 2) * (1 + 1) = ENNReal.ofReal w := by
    rw [one_add_one_eq_two, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by linarith)]
    congr 1; ring
  rw [e1, e2, ← ENNReal.ofReal_add (by linarith) h0]
  simp

private lemma sym2_integrable (a b w : ℝ) (f : ℝ → ℝ) : Integrable f (sym2 a b w) := by
  have hi : ∀ c : ℝ, Integrable f (Measure.dirac c) := fun c => integrable_dirac (by simp)
  exact (((hi a).add_measure (hi (-a))).smul_measure (by simp)).add_measure
    (((hi b).add_measure (hi (-b))).smul_measure (by simp))

private lemma sym2_integral {a b w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) (f : ℝ → ℝ) :
    ∫ x, f x ∂(sym2 a b w) = (1 - w) / 2 * (f a + f (-a)) + w / 2 * (f b + f (-b)) := by
  have hi : ∀ c : ℝ, Integrable f (Measure.dirac c) := fun c => integrable_dirac (by simp)
  unfold sym2
  rw [integral_add_measure (((hi a).add_measure (hi (-a))).smul_measure (by simp))
      (((hi b).add_measure (hi (-b))).smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure,
    integral_add_measure (hi a) (hi (-a)), integral_add_measure (hi b) (hi (-b)),
    integral_dirac, integral_dirac, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
  simp only [smul_eq_mul]

private lemma sym2_tail_zero {a b w q : ℝ} (ha : |a| ≤ q⁻¹) (hb : |b| ≤ q⁻¹) :
    sym2 a b w {x | q⁻¹ < |x|} = 0 := by
  have hm : MeasurableSet {x : ℝ | q⁻¹ < |x|} := measurableSet_lt measurable_const measurable_abs
  have h1 : a ∉ {x : ℝ | q⁻¹ < |x|} := by simpa using ha
  have h2 : -a ∉ {x : ℝ | q⁻¹ < |x|} := by simpa using ha
  have h3 : b ∉ {x : ℝ | q⁻¹ < |x|} := by simpa using hb
  have h4 : -b ∉ {x : ℝ | q⁻¹ < |x|} := by simpa using hb
  simp [sym2, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hm, h1, h2, h3, h4]

private lemma sym2_mean {a b w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) :
    ∫ x, x ∂(sym2 a b w) = 0 := by
  rw [sym2_integral h0 h1 (fun x => x)]; ring

private lemma sym2_var {a b w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) :
    ∫ x, x ^ 2 ∂(sym2 a b w) = (1 - w) * a ^ 2 + w * b ^ 2 := by
  rw [sym2_integral h0 h1 (fun x => x ^ 2)]; ring

/-- Rademacher-type laws: upper entries `±N^{-1/2}`, diagonal entries `±(2/N)^{1/2}`. -/
private def radN (N : ℕ) : EntryLaws N :=
  ⟨fun _ => sym2 (Real.sqrt (2 / N)) 0 0, fun _ => sym2 (Real.sqrt (1 / N)) 0 0⟩

/-- Three-point laws: upper entries `0` or `±(2/N)^{1/2}` with masses `1/2, 1/4, 1/4`,
diagonal entries `±(2/N)^{1/2}`. -/
private def threeN (N : ℕ) : EntryLaws N :=
  ⟨fun _ => sym2 (Real.sqrt (2 / N)) 0 0, fun _ => sym2 0 (Real.sqrt (2 / N)) (1 / 2)⟩

private lemma radN_isGenWigner (N : ℕ) : (radN N).IsGenWigner 1 := by
  have h0 : (0 : ℝ) ≤ 0 := le_rfl
  have h1 : (0 : ℝ) ≤ 1 := zero_le_one
  refine ⟨⟨fun _ => sym2_prob h0 h1, fun _ => sym2_prob h0 h1⟩, fun _ => sym2_integrable _ _ _ _,
    fun _ => sym2_integrable _ _ _ _, fun _ => sym2_mean h0 h1, fun _ => sym2_mean h0 h1,
    fun _ => ?_, fun _ => ?_⟩
  · simp only [radN]
    rw [sym2_var h0 h1, Real.sq_sqrt (by positivity)]; ring
  · simp only [radN]
    rw [sym2_var h0 h1, Real.sq_sqrt (by positivity)]
    have : (1 - 0) * (2 / (N : ℝ)) + 0 * 0 ^ 2 - (N : ℝ)⁻¹ = (N : ℝ)⁻¹ := by ring
    rw [this, abs_of_nonneg (by positivity), one_mul]

private lemma threeN_isGenWigner (N : ℕ) : (threeN N).IsGenWigner 1 := by
  have h0 : (0 : ℝ) ≤ 0 := le_rfl
  have h1 : (0 : ℝ) ≤ 1 := zero_le_one
  have h2 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have h3 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  refine ⟨⟨fun _ => sym2_prob h0 h1, fun _ => sym2_prob h2 h3⟩, fun _ => sym2_integrable _ _ _ _,
    fun _ => sym2_integrable _ _ _ _, fun _ => sym2_mean h0 h1, fun _ => sym2_mean h2 h3,
    fun _ => ?_, fun _ => ?_⟩
  · simp only [threeN]
    rw [sym2_var h2 h3, Real.sq_sqrt (by positivity)]; ring
  · simp only [threeN]
    rw [sym2_var h0 h1, Real.sq_sqrt (by positivity)]
    have : (1 - 0) * (2 / (N : ℝ)) + 0 * 0 ^ 2 - (N : ℝ)⁻¹ = (N : ℝ)⁻¹ := by ring
    rw [this, abs_of_nonneg (by positivity), one_mul]

/-- For `x ≥ 32`, `√(2 / x) ≤ x ^ (-2/5)`. -/
lemma sqrt_two_div_le {x : ℝ} (hx : 32 ≤ x) : Real.sqrt (2 / x) ≤ (x ^ (2 / 5 : ℝ))⁻¹ := by
  have hx0 : 0 < x := by linarith
  have h2 : (2 : ℝ) ≤ x ^ (1 / 5 : ℝ) := by
    have e : (32 : ℝ) ^ (1 / 5 : ℝ) = 2 := by
      rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num)]
      norm_num
    calc (2 : ℝ) = 32 ^ (1 / 5 : ℝ) := e.symm
      _ ≤ x ^ (1 / 5 : ℝ) := Real.rpow_le_rpow (by norm_num) hx (by norm_num)
  have hy : 0 ≤ (x ^ (2 / 5 : ℝ))⁻¹ := by positivity
  rw [← Real.sqrt_sq hy]
  apply Real.sqrt_le_sqrt
  have e2 : ((x ^ (2 / 5 : ℝ))⁻¹) ^ 2 * x = x ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_neg hx0.le, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    nth_rewrite 2 [← Real.rpow_one x]
    rw [← Real.rpow_add hx0]
    norm_num
  rw [div_le_iff₀ hx0, e2]
  exact h2

private lemma sqrt_one_div_le {x : ℝ} (hx : 32 ≤ x) : Real.sqrt (1 / x) ≤ (x ^ (2 / 5 : ℝ))⁻¹ := by
  have hx0 : 0 < x := by linarith
  calc Real.sqrt (1 / x) ≤ Real.sqrt (2 / x) :=
        Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by norm_num) hx0.le)
    _ ≤ _ := sqrt_two_div_le hx

private lemma radN_boundedSupportAS {N : ℕ} (hN : 32 ≤ N) :
    (radN N).BoundedSupportAS ((N : ℝ) ^ (2 / 5 : ℝ)) := by
  have hx : (32 : ℝ) ≤ N := by exact_mod_cast hN
  have h0 : |(0 : ℝ)| ≤ ((N : ℝ) ^ (2 / 5 : ℝ))⁻¹ := by
    simp only [abs_zero, inv_nonneg]; positivity
  refine ⟨fun _ => sym2_tail_zero ?_ h0, fun _ => sym2_tail_zero ?_ h0⟩
  · rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact sqrt_two_div_le hx
  · rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact sqrt_one_div_le hx

private lemma threeN_boundedSupportAS {N : ℕ} (hN : 32 ≤ N) :
    (threeN N).BoundedSupportAS ((N : ℝ) ^ (2 / 5 : ℝ)) := by
  have hx : (32 : ℝ) ≤ N := by exact_mod_cast hN
  have h0 : |(0 : ℝ)| ≤ ((N : ℝ) ^ (2 / 5 : ℝ))⁻¹ := by
    simp only [abs_zero, inv_nonneg]; positivity
  have h2 : |Real.sqrt (2 / N)| ≤ ((N : ℝ) ^ (2 / 5 : ℝ))⁻¹ := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact sqrt_two_div_le hx
  exact ⟨fun _ => sym2_tail_zero h2 h0, fun _ => sym2_tail_zero h0 h2⟩

private lemma supportParam_of_as {N : ℕ} {L : EntryLaws N} {Q q : ℝ} (hQ : Q ≤ q)
    (h : L.BoundedSupportAS q) (c : ℝ) : L.SupportParam Q c q :=
  ⟨hQ, h.boundedSupport c, h.tailVarOff c⟩

/-- `BoundedSupportAS.tailVarOff` at `N = 32`: Rademacher-type laws, `q = 32^{2/5}`, `c = 1/2`. -/
example : (radN 32).TailVarOff (((32 : ℕ) : ℝ) ^ (2 / 5 : ℝ)) (1 / 2) :=
  (radN_boundedSupportAS (N := 32) (by norm_num)).tailVarOff (1 / 2)

/-- `interp_tailVarOff` and `interp_supportParam` at `N = 32`: `H_γ` with `γ = 100` between the
Rademacher-type and the three-point laws. The upper entry `(0, 1)` follows the first law, the
upper entry `(30, 31)` the second, and the two laws differ (mass of `{0}` is `0` and `1/2`). -/
example :
    (interp (lexPos 32) 100 (radN 32) (threeN 32)).TailVarOff
        (((32 : ℕ) : ℝ) ^ (2 / 5 : ℝ)) (1 / 2) ∧
      (interp (lexPos 32) 100 (radN 32) (threeN 32)).SupportParam
        (((32 : ℕ) : ℝ) ^ (2 / 5 : ℝ)) (1 / 2) (((32 : ℕ) : ℝ) ^ (2 / 5 : ℝ)) ∧
      (interp (lexPos 32) 100 (radN 32) (threeN 32)).off ⟨(0, 1), by decide⟩ =
        (radN 32).off ⟨(0, 1), by decide⟩ ∧
      (interp (lexPos 32) 100 (radN 32) (threeN 32)).off ⟨(30, 31), by decide⟩ =
        (threeN 32).off ⟨(30, 31), by decide⟩ ∧
      (radN 32).off ⟨(0, 1), by decide⟩ {0} ≠ (threeN 32).off ⟨(0, 1), by decide⟩ {0} := by
  have hrad := supportParam_of_as (Q := ((32 : ℕ) : ℝ) ^ (2 / 5 : ℝ)) le_rfl
    (radN_boundedSupportAS (N := 32) (by norm_num)) (1 / 2)
  have hthree := supportParam_of_as (Q := ((32 : ℕ) : ℝ) ^ (2 / 5 : ℝ)) le_rfl
    (threeN_boundedSupportAS (N := 32) (by norm_num)) (1 / 2)
  refine ⟨interp_tailVarOff hrad.2.2 hthree.2.2, interp_supportParam hrad hthree, ?_, ?_, ?_⟩
  · simp [interp, lexPos]
  · simp [interp, lexPos]
  · have hm : MeasurableSet ({0} : Set ℝ) := measurableSet_singleton 0
    have ha : Real.sqrt (1 / ((32 : ℕ) : ℝ)) ≠ 0 := by positivity
    simp only [radN, threeN, sym2, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply' _ hm, Set.indicator, Set.mem_singleton_iff, ha, neg_eq_zero,
      Pi.one_apply, smul_eq_mul]
    norm_num

/-- `MomentCond.isGenWigner` for the GOE laws at `N = 3`, where `MomentCond 3` holds. -/
example : (goeLaws 3).IsGenWigner (max 3 1) :=
  (goeLaws_momentCond (le_refl 3)).isGenWigner

/-- `momentCond_tailVarOff` for the GOE laws: `MomentCond 3` and bounded support at
`q = N^{1/4}` give `TailVarOff` with `c / 2`, at some `N ≥ 3` beyond the threshold. -/
example : ∃ N : ℕ, 3 ≤ N ∧ ∃ c : ℝ, 0 < c ∧ (goeLaws N).MomentCond 3 ∧
    (goeLaws N).BoundedSupport ((N : ℝ) ^ (1 / 4 : ℝ)) c ∧
    (goeLaws N).TailVarOff ((N : ℝ) ^ (1 / 4 : ℝ)) (c / 2) := by
  obtain ⟨c, hc, N1, h1⟩ := goeLaws_boundedSupport (φs := 1 / 4) (by norm_num) (by norm_num)
  obtain ⟨N0, h0⟩ := EntryLaws.momentCond_tailVarOff (C1 := 3) hc
  set N : ℕ := max (max N0 N1) 3 with hN
  have hN3 : 3 ≤ N := le_max_right _ _
  have hM : (goeLaws N).MomentCond 3 := goeLaws_momentCond hN3
  have hB : (goeLaws N).BoundedSupport ((N : ℝ) ^ (1 / 4 : ℝ)) c :=
    h1 N (le_trans (le_max_right _ _) (le_max_left _ _))
  exact ⟨N, hN3, c, hc, hM, hB, h0 N (le_trans (le_max_left _ _) (le_max_left _ _)) _ _ hM hB⟩

private lemma exp_neg_sqrt32_lt :
    Real.exp (-((32 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) < ((32 : ℕ) : ℝ)⁻¹ := by
  have h5 : (5 : ℝ) ≤ ((32 : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    apply Real.le_sqrt_of_sq_le
    norm_num
  have h32 : (32 : ℝ) < Real.exp 5 := by
    have h1 : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have h4 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h4]
    nlinarith [pow_lt_pow_left₀ h1 (by norm_num) (by norm_num : (5 : ℕ) ≠ 0)]
  calc Real.exp (-((32 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) ≤ Real.exp (-5) := Real.exp_le_exp.mpr (by linarith)
    _ < ((32 : ℕ) : ℝ)⁻¹ := by
        rw [Real.exp_neg, Nat.cast_ofNat, inv_lt_inv₀ (Real.exp_pos 5) (by norm_num)]
        exact h32

/-- `supportParam_sSup` at `N = 32`, `c = 1/2`: Rademacher-type laws, nonempty admissible set
(it contains `32^{2/5}`), `exp(-32^{1/2}) < 1/32`. -/
example : (radN 32).SupportParam (((32 : ℕ) : ℝ) ^ (2 / 5 : ℝ)) (1 / 2)
    (sSup {q | (radN 32).SupportParam (((32 : ℕ) : ℝ) ^ (2 / 5 : ℝ)) (1 / 2) q}) :=
  EntryLaws.supportParam_sSup (radN_isGenWigner 32) (by norm_num) exp_neg_sqrt32_lt
    ⟨_, supportParam_of_as le_rfl (radN_boundedSupportAS (N := 32) (by norm_num)) (1 / 2)⟩

/-- The event that every upper entry is at most `q⁻¹` in absolute value. -/
private def offBdd (N : ℕ) (q : ℝ) : Set (Entries N) := {ω | ∀ p, |ω.2 p| ≤ q⁻¹}

private lemma offBdd_anti (N : ℕ) {q q' : ℝ} (hq : 0 < q) (h : q ≤ q') :
    offBdd N q' ⊆ offBdd N q :=
  fun _ hω p => (hω p).trans (inv_anti₀ hq h)

private lemma law_offEntry {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) (p : OffDiag N) {A : Set ℝ}
    (hA : MeasurableSet A) : L.law {ω | ω.2 p ∈ A} = L.off p A := by
  have := hL.diag
  have := hL.off
  have hset : {ω : Entries N | ω.2 p ∈ A} =
      (Set.univ : Set (Fin N → ℝ)) ×ˢ (Function.eval p ⁻¹' A) := by
    ext ω; simp
  unfold EntryLaws.law
  rw [hset, Measure.prod_prod, measure_univ, one_mul]
  exact (measurePreserving_eval L.off p).measure_preimage hA.nullMeasurableSet

private lemma law_offBdd_compl_le {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) {q c : ℝ}
    (hB : L.BoundedSupport q c) :
    L.law (offBdd N q)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ 2 * Real.exp (-(N : ℝ) ^ c)) := by
  have hcompl : (offBdd N q)ᶜ = ⋃ p : OffDiag N, {ω : Entries N | ω.2 p ∈ {x : ℝ | q⁻¹ < |x|}} := by
    ext ω
    simp [offBdd]
  rw [hcompl]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  have hcard : (Fintype.card (OffDiag N) : ℝ) ≤ (N : ℝ) ^ 2 := by
    have h1 : Fintype.card (OffDiag N) ≤ N * N := by
      calc Fintype.card (OffDiag N) ≤ Fintype.card (Fin N × Fin N) := Fintype.card_subtype_le _
        _ = N * N := by simp
    calc (Fintype.card (OffDiag N) : ℝ) ≤ (N : ℝ) * N := by exact_mod_cast h1
      _ = (N : ℝ) ^ 2 := by ring
  calc ∑ p, L.law {ω : Entries N | ω.2 p ∈ {x : ℝ | q⁻¹ < |x|}}
      = ∑ p, L.off p {x : ℝ | q⁻¹ < |x|} :=
        Finset.sum_congr rfl fun p _ => law_offEntry hL p (measurableSet_tail q)
    _ ≤ ∑ _p : OffDiag N, ENNReal.ofReal (Real.exp (-(N : ℝ) ^ c)) :=
        Finset.sum_le_sum fun p _ => hB.2 p
    _ = ENNReal.ofReal ((Fintype.card (OffDiag N) : ℝ) * Real.exp (-(N : ℝ) ^ c)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le)

/-- `highProbOn_forall_param` for the events "every upper entry is at most `q⁻¹`": the bound for
each admissible `q` is a union bound over the upper entries, and the event for all admissible
`q` holds with `1`-high probability. At `N = 32` the event is a proper subset of the whole space
for the Rademacher-type laws, whose admissible set is nonempty. -/
example :
    HighProbOn 1 (fun _ L => L.IsGenWigner 1)
      (fun N L => {ω | ∀ q, L.SupportParam ((fun _ : ℕ => (0 : ℝ)) N) (1 / 2) q →
        ω ∈ offBdd N q}) ∧
    (radN 32).IsGenWigner 1 ∧
    (∃ q, (radN 32).SupportParam 0 (1 / 2) q) ∧
    ∃ ω : Entries 32, ω ∉ {ω | ∀ q, (radN 32).SupportParam 0 (1 / 2) q → ω ∈ offBdd 32 q} := by
  refine ⟨?_, radN_isGenWigner 32, ?_, ?_⟩
  · obtain ⟨N1, hN1⟩ := eventually_atTop.mp (phi_rpow_le_rpow 1 (c := 1 / 2) (by norm_num))
    refine highProbOn_forall_param (ζ := 1) (C0 := 1) (c := 1 / 2) (by norm_num)
      (Q := fun _ => 0) (Ω := offBdd) (fun N q q' hq hqq' => offBdd_anti N hq hqq')
      ⟨1, one_pos, 2, two_pos, N1, fun N hN L q hL hq => ?_⟩
    refine (law_offBdd_compl_le hL.isProb hq.2.1).trans (ENNReal.ofReal_le_ofReal ?_)
    have hN1' : phi N ^ (1 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := hN1 N hN
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    linarith
  · exact ⟨_, supportParam_of_as (Q := 0) (by positivity)
      (radN_boundedSupportAS (N := 32) (by norm_num)) (1 / 2)⟩
  · refine ⟨(0, fun _ => 1), fun hω => ?_⟩
    have hq := supportParam_of_as (Q := 0) (by positivity)
      (radN_boundedSupportAS (N := 32) (by norm_num)) (1 / 2)
    have h1 : (1 : ℝ) < ((32 : ℕ) : ℝ) ^ (2 / 5 : ℝ) :=
      Real.one_lt_rpow (by norm_num) (by norm_num)
    have := hω _ hq ⟨(0, 1), by decide⟩
    simp only [abs_one] at this
    have h2 := inv_lt_one_of_one_lt₀ h1
    linarith

/-- `specDomain`: for every exponent `C`, the point `i` lies in `S(C)` once `N` is large. -/
example (C : ℝ) : ∀ᶠ N : ℕ in atTop, Complex.I ∈ specDomain N C := by
  filter_upwards [phi_rpow_le_rpow C (c := 1 / 2) (by norm_num), eventually_ge_atTop 2]
    with N hN hN2
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hlt : (N : ℝ) ^ (1 / 2 : ℝ) < N := by
    calc (N : ℝ) ^ (1 / 2 : ℝ) < (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
      _ = N := Real.rpow_one _
  refine ⟨by simp, ?_, by simp⟩
  simp only [Complex.I_im]
  rw [div_lt_one (by linarith)]
  exact lt_of_le_of_lt hN hlt

/-- `gaussianReal_tailVar` at `φs = 1/4`: a concrete `N ≥ 2` beyond the
threshold and the variance `2/N`. -/
example : ∃ N : ℕ, 2 ≤ N ∧ ∃ v : NNReal, 0 < v ∧ (v : ℝ) ≤ 2 / N ∧ ∃ c : ℝ, 0 < c ∧
    ∫ x in {x : ℝ | ((N : ℝ) ^ (1 / 4 : ℝ))⁻¹ < |x|}, x ^ 2 ∂(gaussianReal 0 v) ≤
      Real.exp (-(N : ℝ) ^ c) := by
  obtain ⟨c, hc, N0, h⟩ := gaussianReal_tailVar (φs := 1 / 4) (by norm_num) (by norm_num)
  set N : ℕ := max N0 2 with hN
  have hN2 : 2 ≤ N := le_max_right _ _
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hv : (((2 / (N : ℝ)).toNNReal : NNReal) : ℝ) = 2 / N := Real.coe_toNNReal _ (by positivity)
  refine ⟨N, hN2, (2 / (N : ℝ)).toNNReal, Real.toNNReal_pos.mpr (by positivity), hv.le, c, hc, ?_⟩
  exact h N (le_max_left _ _) _ hv.le

#print axioms EntryLaws.BoundedSupportAS.tailVarOff
#print axioms EntryLaws.interp_tailVarOff
#print axioms EntryLaws.interp_supportParam
#print axioms EntryLaws.MomentCond.isGenWigner
#print axioms EntryLaws.momentCond_tailVarOff
#print axioms EntryLaws.supportParam_sSup
#print axioms highProbOn_forall_param
#print axioms gaussianReal_tailVar

end WEdgeNS
