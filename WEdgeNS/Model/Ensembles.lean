import WEdgeNS.Model.Transfer

/-!
# The ensembles of Sections 3–4: truncation, interpolation order, Rademacher laws
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- Law of `x - E[x | |x| ≤ T]` for `x ∼ ν` conditioned on `|x| ≤ T` ((4.14), centred). -/
def truncCentered (ν : Measure ℝ) (T : ℝ) : Measure ℝ :=
  (cond ν {x | |x| ≤ T}).map (fun x => x - ∫ y, y ∂(cond ν {x | |x| ≤ T}))

/-- Entry laws of `H^S` ((4.14)–(4.16)): cut-off at `N^{1/2-ε}`, centred, scaled by `N^{-1/2}`. -/
def truncLaws (ν ν' : Measure ℝ) (ε : ℝ) (N : ℕ) : EntryLaws N :=
  ofIID (truncCentered ν ((N : ℝ) ^ (1 / 2 - ε))) (truncCentered ν' ((N : ℝ) ^ (1 / 2 - ε))) N

/-- Entry laws of `H̃^S = (E|x^S_12|²)^{-1/2} H^S` (before (4.20)). -/
def truncLawsNorm (ν ν' : Measure ℝ) (ε : ℝ) (N : ℕ) : EntryLaws N :=
  (truncLaws ν ν' ε N).scale
    (Real.sqrt (∫ x, x ^ 2 ∂(truncCentered ν ((N : ℝ) ^ (1 / 2 - ε)))))⁻¹

/-- Lexicographic position of `(i, j)`, `i ≤ j`, among the upper index pairs (the map `Φ`
of (3.21)). -/
def lexPos (N : ℕ) : Fin N ⊕ OffDiag N → ℕ
  | Sum.inl i => i.val * N - i.val * (i.val - 1) / 2 + 1
  | Sum.inr p => p.1.1.val * N - p.1.1.val * (p.1.1.val - 1) / 2 + (p.1.2.val - p.1.1.val) + 1

/-- Start of row `i` in the lexicographic order of the upper index pairs. -/
private def lexRow (N i : ℕ) : ℕ := i * N - i * (i - 1) / 2

private lemma lexRow_succ {N i : ℕ} (hi : i < N) : lexRow N (i + 1) = lexRow N i + (N - i) := by
  have h2 : (i + 1) * (i + 1 - 1) / 2 = i * (i - 1) / 2 + i := by
    rcases i with _ | i
    · simp
    · have : (i + 1 + 1) * (i + 1) = i * (i + 1) + 2 * (i + 1) := by ring
      simp only [Nat.add_sub_cancel]
      rw [this, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2), Nat.mul_comm (i + 1) i]
  have h3 : i * (i - 1) / 2 ≤ i * N := by
    calc i * (i - 1) / 2 ≤ i * (i - 1) := Nat.div_le_self _ _
      _ ≤ i * N := Nat.mul_le_mul_left _ (by omega)
  unfold lexRow
  rw [h2]
  have : (i + 1) * N = i * N + N := by ring
  rw [this]
  have h4 : i ≤ N := hi.le
  have h5 : i * (i - 1) / 2 + i ≤ i * N + N := by omega
  omega

private lemma lexRow_mono {N : ℕ} {i i' : ℕ} (h : i ≤ i') (hi' : i' ≤ N) :
    lexRow N i ≤ lexRow N i' := by
  induction i', h using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    rw [lexRow_succ (by omega)]
    exact (ih (by omega)).trans (Nat.le_add_right _ _)

private lemma lexRow_lt {N : ℕ} {i i' a : ℕ} (h : i < i') (hi' : i' < N) (ha : a < N - i) :
    lexRow N i + a < lexRow N i' := by
  have h1 := lexRow_succ (N := N) (i := i) (by omega)
  have h2 := lexRow_mono (N := N) (show i + 1 ≤ i' from h) hi'.le
  omega

private lemma lexRow_inj {N : ℕ} {i i' a a' : ℕ} (hi : i < N) (hi' : i' < N) (ha : a < N - i)
    (ha' : a' < N - i') (h : lexRow N i + a = lexRow N i' + a') : i = i' ∧ a = a' := by
  have hii : i = i' := by
    rcases lt_trichotomy i i' with h1 | h1 | h1
    · have := lexRow_lt h1 hi' ha; omega
    · exact h1
    · have := lexRow_lt h1 hi ha'; omega
  subst hii
  exact ⟨rfl, by omega⟩

private lemma lexPos_inl (N : ℕ) (j : Fin N) : lexPos N (Sum.inl j) = lexRow N j + 0 + 1 := rfl

private lemma lexPos_inr (N : ℕ) (p : OffDiag N) :
    lexPos N (Sum.inr p) = lexRow N p.1.1 + (p.1.2.val - p.1.1.val) + 1 := rfl

theorem lexPos_injective (N : ℕ) : Function.Injective (lexPos N) := by
  rintro (j | p) (k | q) h <;> simp only [lexPos_inl, lexPos_inr] at h
  · have := lexRow_inj (N := N) (a := 0) (a' := 0) j.2 k.2 (by have := j.2; omega)
      (by have := k.2; omega) (by omega)
    exact congrArg Sum.inl (Fin.ext this.1)
  · have h1 := q.2; simp only [Fin.lt_def] at h1
    have := lexRow_inj (N := N) (a := 0) (a' := q.1.2.val - q.1.1.val) j.2 q.1.1.2
      (by have := j.2; omega) (by have := q.1.2.2; omega) (by omega)
    omega
  · have h1 := p.2; simp only [Fin.lt_def] at h1
    have := lexRow_inj (N := N) (a := p.1.2.val - p.1.1.val) (a' := 0) p.1.1.2 k.2
      (by have := p.1.2.2; omega) (by have := k.2; omega) (by omega)
    omega
  · have h1 := p.2; have h2 := q.2; simp only [Fin.lt_def] at h1 h2
    have := lexRow_inj (N := N) (a := p.1.2.val - p.1.1.val) (a' := q.1.2.val - q.1.1.val)
      p.1.1.2 q.1.1.2 (by have := p.1.2.2; omega) (by have := q.1.2.2; omega) (by omega)
    refine congrArg Sum.inr (Subtype.ext (Prod.ext (Fin.ext this.1) (Fin.ext ?_)))
    omega

/-- Rademacher entries `±N^{-1/2}`, diagonal `±(2/N)^{1/2}`. -/
def radLaws (N : ℕ) : EntryLaws N := ofIID rademacher (rademacher.map (fun x => Real.sqrt 2 * x)) N

example : lexPos 3 (Sum.inl 0) = 1 ∧ lexPos 3 (Sum.inr ⟨(0, 1), by decide⟩) = 2 ∧
    lexPos 3 (Sum.inr ⟨(0, 2), by decide⟩) = 3 ∧ lexPos 3 (Sum.inl 1) = 4 ∧
    lexPos 3 (Sum.inr ⟨(1, 2), by decide⟩) = 5 ∧ lexPos 3 (Sum.inl 2) = 6 := by
  decide

/-- The interpolation `H_4` at `N = 3`: entries `(1,1), (1,2), (1,3), (2,2)` are Rademacher,
entries `(2,3), (3,3)` are Gaussian. -/
example : (interp (lexPos 3) 4 (radLaws 3) (goeLaws 3)).off ⟨(0, 1), by decide⟩ =
      (radLaws 3).off ⟨(0, 1), by decide⟩ ∧
    (interp (lexPos 3) 4 (radLaws 3) (goeLaws 3)).off ⟨(1, 2), by decide⟩ =
      (goeLaws 3).off ⟨(1, 2), by decide⟩ ∧
    (interp (lexPos 3) 4 (radLaws 3) (goeLaws 3)).diag 1 = (radLaws 3).diag 1 ∧
    (interp (lexPos 3) 4 (radLaws 3) (goeLaws 3)).diag 2 = (goeLaws 3).diag 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [interp, lexPos]

private lemma measurable_sqrt_two_mul : Measurable fun x : ℝ => Real.sqrt 2 * x := by fun_prop

/-- Integrals against the Rademacher law are averages over `±1`. -/
lemma integral_rademacher (f : ℝ → ℝ) :
    ∫ x, f x ∂rademacher = (f (-1) + f 1) / 2 := by
  unfold rademacher
  rw [integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
    (integrable_dirac (by simp)), integral_dirac, integral_dirac]
  simp [ENNReal.toReal_inv]
  ring

/-- The off-diagonal fourth moment of `radLaws N` is `N⁻²`. -/
theorem integral_pow_four_radLaws_off {N : ℕ} (hN : 0 < N) (p : OffDiag N) :
    ∫ x, x ^ 4 ∂((radLaws N).off p) = ((N : ℝ) ^ 2)⁻¹ := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hm : Measurable fun x : ℝ => (Real.sqrt N)⁻¹ * x := by fun_prop
  change ∫ x, x ^ 4 ∂(rademacher.map fun x : ℝ => (Real.sqrt N)⁻¹ * x) = _
  rw [integral_map hm.aemeasurable (by fun_prop), integral_rademacher]
  have hs : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNr.le
  have : ((Real.sqrt N)⁻¹ * -1) ^ 4 = ((Real.sqrt N)⁻¹) ^ 4 := by ring
  rw [this]
  have h4 : ((Real.sqrt N)⁻¹) ^ 4 = ((N : ℝ) ^ 2)⁻¹ := by
    rw [inv_pow, show Real.sqrt N ^ 4 = (Real.sqrt N ^ 2) ^ 2 by ring, hs]
  rw [mul_one, h4]
  ring

/-- The off-diagonal third absolute moment of `radLaws N` is `N^{-3/2}`. -/
theorem integral_abs_pow_three_radLaws_off {N : ℕ} (hN : 0 < N) (p : OffDiag N) :
    ∫ x, |x| ^ 3 ∂((radLaws N).off p) = (N : ℝ) ^ (-(3 : ℝ) / 2) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hm : Measurable fun x : ℝ => (Real.sqrt N)⁻¹ * x := by fun_prop
  change ∫ x, |x| ^ 3 ∂(rademacher.map fun x : ℝ => (Real.sqrt N)⁻¹ * x) = _
  rw [integral_map hm.aemeasurable (by fun_prop), integral_rademacher]
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
  simp only [mul_neg, mul_one, abs_neg, abs_inv, abs_of_pos hs]
  rw [Real.sqrt_eq_rpow, inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul hNr.le,
    ← Real.rpow_neg hNr.le]
  norm_num

private lemma rademacher_scaled_wignerLaws :
    WignerLaws rademacher (rademacher.map (fun x => Real.sqrt 2 * x)) := by
  have h := rademacher_wignerLaws
  have hm : AEMeasurable (fun x : ℝ => Real.sqrt 2 * x) rademacher :=
    (measurable_sqrt_two_mul).aemeasurable
  have hprob : IsProbabilityMeasure (rademacher.map (fun x => Real.sqrt 2 * x)) := by
    have := h.prob
    exact (Measure.isProbabilityMeasure_map_iff hm).2 this
  have hint : ∀ f : ℝ → ℝ, Integrable f rademacher := fun f => by
    unfold rademacher
    exact ((integrable_dirac (by simp)).add_measure (integrable_dirac (by simp))).smul_measure
      (by simp)
  refine ⟨h.prob, hprob, h.sq_int, ?_, h.mean, h.var, ?_⟩
  · rw [integrable_map_measure (by fun_prop) hm]
    exact hint _
  · rw [integral_map hm (by fun_prop), integral_rademacher]
    simp

theorem radLaws_isGenWigner {N : ℕ} (hN : 0 < N) : (radLaws N).IsGenWigner 1 := by
  have h := ofIID_isGenWigner rademacher_scaled_wignerLaws hN
  have h2 : ∫ x, x ^ 2 ∂(rademacher.map (fun x => Real.sqrt 2 * x)) = 2 := by
    rw [integral_map (measurable_sqrt_two_mul).aemeasurable (by fun_prop), integral_rademacher]
    simp only [mul_one, mul_neg]
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  rw [h2] at h
  norm_num at h
  exact h

example : (interp (lexPos 3) 4 (radLaws 3) (goeLaws 3)).IsGenWigner
    (max 1 |∫ x, x ^ 2 ∂(gaussianReal 0 2) - 1|) :=
  interp_isGenWigner (radLaws_isGenWigner (by norm_num))
    (ofIID_isGenWigner goe_wignerLaws (N := 3) (by norm_num))

/-- The Rademacher law has second moment `1`; at `N = 16` the off-diagonal entries of `radLaws 16`
have fourth moment `1/256` and a positive third absolute moment. -/
example : ∫ x, x ^ 2 ∂rademacher = 1 ∧ ∀ p : OffDiag 16,
    ∫ x, x ^ 4 ∂((radLaws 16).off p) = 1 / 256 ∧ 0 < ∫ x, |x| ^ 3 ∂((radLaws 16).off p) := by
  refine ⟨by rw [integral_rademacher]; norm_num, fun p => ⟨?_, ?_⟩⟩
  · rw [integral_pow_four_radLaws_off (by norm_num) p]; norm_num
  · rw [integral_abs_pow_three_radLaws_off (by norm_num) p]; positivity

#print axioms lexPos_injective
#print axioms radLaws_isGenWigner

end WEdgeNS
