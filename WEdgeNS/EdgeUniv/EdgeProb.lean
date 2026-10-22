import WEdgeNS.EdgeUniv.EdgeSandwich
import WEdgeNS.Probability.ProductSpace

/-!
# The distribution of the largest eigenvalue against smoothed traces
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- `ω ↦ Tr (χ_{[a,b]} * θ_η)(H(ω))` is continuous in the entries for `η > 0`. -/
private lemma continuous_smoothCount_entries {N : ℕ} {η : ℝ} (hη : 0 < η) (a b : ℝ) :
    Continuous fun ω : Entries N => smoothCount (symOfEntries_isHermitian ω) η a b := by
  have h : (fun ω : Entries N => smoothCount (symOfEntries_isHermitian ω) η a b) = fun ω =>
      (N : ℝ) / Real.pi * ∫ y in a..b, (stieltjesM (symOfEntries ω) ⟨y, η⟩).im := by
    funext ω
    exact smoothCount_eq (symOfEntries_isHermitian ω) hη a b
  rw [h]
  refine continuous_const.mul ?_
  have hjoint :
      Continuous fun p : Entries N × ℝ => (stieltjesM (symOfEntries p.1) ⟨p.2, η⟩).im := by
    have : (fun p : Entries N × ℝ => (stieltjesM (symOfEntries p.1) ⟨p.2, η⟩).im) = fun p =>
        ((N : ℂ)⁻¹ * ∑ i, resolventC (symOfEntries p.1) (⟨p.2, η⟩ : ℂ) i i).im := by
      funext p
      simp [stieltjesM, Matrix.trace]
    rw [this]
    exact Complex.continuous_im.comp (continuous_const.mul
      (continuous_finsetSum _ fun i _ => continuous_resolventC_symOfEntries_prod hη i i))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun ω y => (stieltjesM (symOfEntries ω) ⟨y, η⟩).im) hjoint a b

/-- `λ_N(symOfEntries ω)` is continuous in the entries. -/
private lemma continuous_lambdaMax_symOfEntries' {N : ℕ} (hN : 0 < N) :
    Continuous fun ω : Entries N => lambdaMax (symOfEntries ω) := by
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  have h : (fun ω : Entries N => lambdaMax (symOfEntries ω)) =
      (fun ω => lambdaMax (wignerMatrix N ω)) ∘ (fun ω => Real.sqrt N • ω) := by
    funext ω
    simp only [Function.comp, wignerMatrix_eq_symOfEntries, smul_smul, inv_mul_cancel₀ hs,
      one_smul]
  rw [h]
  exact (continuous_lambdaMax_wignerMatrix N).comp (continuous_const_smul _)

/-- `Tr (χ_{[a,b]} * θ_η)(H) ≥ 0` for `a ≤ b` and `η > 0`. -/
private lemma smoothCount_nonneg' {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {η : ℝ} (hη : 0 < η) {a b : ℝ} (hab : a ≤ b) : 0 ≤ smoothCount hH η a b := by
  unfold smoothCount
  refine Finset.sum_nonneg fun α _ => ?_
  exact intervalIntegral.integral_nonneg hab fun x _ => by unfold thetaEta; positivity

/-- `λ_N < E` exactly when no eigenvalue is `≥ E`. -/
private lemma lambdaMax_lt_iff_countIci {N : ℕ} [NeZero N] (ω : Entries N) (E : ℝ) :
    lambdaMax (symOfEntries ω) < E ↔ countIci (symOfEntries_isHermitian ω) E = 0 := by
  have hg := lambdaMax_isGreatest (symOfEntries_isHermitian ω)
  unfold countIci
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h α _ hα
    have := hg.2 ⟨α, rfl⟩
    linarith
  · intro h
    obtain ⟨α, hα⟩ := hg.1
    rw [← hα]
    exact not_le.1 (h (Finset.mem_univ α))

/-- [26] (6.21) for one law, with the mass of the bad event written out:
`E K(Tr χ_{E-ℓ} * θ_η) - P(Ωᶜ) ≤ P(λ_N < E) ≤ E K(Tr χ_{E+ℓ} * θ_η) + P(Ωᶜ)`. -/
theorem prob_lambdaMax_lt_sandwich {C : ℝ} (hC : 0 < C) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 10 → ∃ N0 : ℕ, ∀ N ≥ N0, ∀ L : EntryLaws N, L.IsProb →
      ∀ E : ℝ, |E - 2| ≤ phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) →
        (∫ ω, edgeCutoff (smoothCount (symOfEntries_isHermitian ω)
            ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε)) (E - (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2)
            (edgeEL N C)) ∂L.law) - (L.law (edgeInputEvent N C)ᶜ).toReal ≤
          (L.law {ω | lambdaMax (symOfEntries ω) < E}).toReal ∧
        (L.law {ω | lambdaMax (symOfEntries ω) < E}).toReal ≤
          (∫ ω, edgeCutoff (smoothCount (symOfEntries_isHermitian ω)
            ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε)) (E + (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2)
            (edgeEL N C)) ∂L.law) + (L.law (edgeInputEvent N C)ᶜ).toReal := by
  intro ε hε hε1
  obtain ⟨N1, hN1⟩ := smoothCount_sandwich hC ε hε hε1
  have e9 : ∀ᶠ N : ℕ in atTop, (9 : ℝ) ≤ (N : ℝ) ^ ε :=
    (tendsto_rpow_atTop hε |>.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1
    ((eventually_ge_atTop N1).and ((eventually_ge_atTop 3).and e9))
  refine ⟨N0, fun N hN L hL E hE => ?_⟩
  obtain ⟨hNN1, hN3, h9⟩ := hN0 N hN
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hX : (0 : ℝ) < N := by linarith
  have : NeZero N := ⟨by omega⟩
  have hμ : IsProbabilityMeasure L.law := EntryLaws.isProbabilityMeasure_law hL
  have hsand := fun ω (hω : ω ∈ edgeInputEvent N C) => hN1 N hNN1 ω hω E hE
  -- the scales
  have hφ1 : 1 ≤ phi N := by rw [phi_eq_exp hN3]; exact Real.one_le_exp (sq_nonneg _)
  have hw1 : 1 ≤ phi N ^ C := Real.one_le_rpow hφ1 hC.le
  have hp0 : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hX _
  have hq0 : 0 < (N : ℝ) ^ (-ε) := Real.rpow_pos_of_pos hX _
  have hq9 : (N : ℝ) ^ (-ε) ≤ 1 / 9 := by
    rw [Real.rpow_neg hX.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h9
  have hηpos : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε) := Real.rpow_pos_of_pos hX _
  have hℓ : (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2 =
      (N : ℝ) ^ (-(2 : ℝ) / 3) * (N : ℝ) ^ (-ε) / 2 := by
    rw [sub_eq_add_neg, Real.rpow_add hX]
  have hℓpos : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2 := by
    have := Real.rpow_pos_of_pos hX (-(2 : ℝ) / 3 - ε)
    positivity
  have hEL : edgeEL N C = 2 + 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) := rfl
  have hwp : 0 ≤ phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) := by positivity
  have hℓw : (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2 ≤ phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) / 2 := by
    have h1 : (N : ℝ) ^ (-(2 : ℝ) / 3) * (N : ℝ) ^ (-ε) ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) hp0.le
    have h2 : (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) :=
      le_mul_of_one_le_left hp0.le hw1
    rw [hℓ]
    linarith
  have hEabs := abs_le.1 hE
  have hEℓ : E + (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2 ≤ edgeEL N C := by
    rw [hEL]
    linarith [hEabs.2]
  -- the pointwise inequalities on the event
  have hΩ : ∀ ω ∈ edgeInputEvent N C,
      edgeCutoff (smoothCount (symOfEntries_isHermitian ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε))
          (E - (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2) (edgeEL N C)) ≤
        {ω | lambdaMax (symOfEntries ω) < E}.indicator 1 ω ∧
      {ω | lambdaMax (symOfEntries ω) < E}.indicator 1 ω ≤
        edgeCutoff (smoothCount (symOfEntries_isHermitian ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε))
          (E + (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2) (edgeEL N C)) := by
    intro ω hω
    obtain ⟨hlo, hup⟩ := hsand ω hω
    obtain ⟨-, hK01, hK1, hK0⟩ := edgeCutoff_props
    have hiff := lambdaMax_lt_iff_countIci ω E
    by_cases hA : lambdaMax (symOfEntries ω) < E
    · have hX0 : countIci (symOfEntries_isHermitian ω) E = 0 := hiff.1 hA
      rw [hX0] at hlo
      rw [Set.indicator_of_mem (show ω ∈ {ω | lambdaMax (symOfEntries ω) < E} from hA)]
      refine ⟨by simpa using (hK01 _).2, ?_⟩
      have hnn := smoothCount_nonneg' (symOfEntries_isHermitian ω) hηpos hEℓ
      have habs : |smoothCount (symOfEntries_isHermitian ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε))
          (E + (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2) (edgeEL N C)| ≤ 1 / 9 := by
        rw [abs_of_nonneg hnn]
        simp only [Nat.cast_zero] at hlo
        linarith
      simp [hK1 _ habs]
    · have hX1 : countIci (symOfEntries_isHermitian ω) E ≠ 0 := fun h => hA (hiff.2 h)
      have hX1' : (1 : ℝ) ≤ countIci (symOfEntries_isHermitian ω) E := by
        exact_mod_cast Nat.one_le_iff_ne_zero.2 hX1
      rw [Set.indicator_of_notMem (show ω ∉ {ω | lambdaMax (symOfEntries ω) < E} from hA)]
      refine ⟨?_, by simpa using (hK01 _).1⟩
      have habs : (2 : ℝ) / 9 ≤ |smoothCount (symOfEntries_isHermitian ω)
          ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε)) (E - (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2)
          (edgeEL N C)| := by
        refine le_trans ?_ (le_abs_self _)
        linarith
      simp [hK0 _ habs]
  -- integration
  have hlam := continuous_lambdaMax_symOfEntries' (N := N) (by omega)
  have hAm : MeasurableSet {ω : Entries N | lambdaMax (symOfEntries ω) < E} :=
    (isOpen_lt hlam continuous_const).measurableSet
  have hK : Continuous edgeCutoff := (edgeCutoff_props.1 0).continuous
  have hKm := hK.comp (continuous_smoothCount_entries (N := N) hηpos
    (E - (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2) (edgeEL N C))
  have hKp := hK.comp (continuous_smoothCount_entries (N := N) hηpos
    (E + (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2) (edgeEL N C))
  have hK01 := edgeCutoff_props.2.1
  have hKmi : Integrable (fun ω : Entries N => edgeCutoff (smoothCount
      (symOfEntries_isHermitian ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε))
      (E - (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2) (edgeEL N C))) L.law :=
    Integrable.of_bound hKm.aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hK01 _).1]; exact (hK01 _).2)
  have hKpi : Integrable (fun ω : Entries N => edgeCutoff (smoothCount
      (symOfEntries_isHermitian ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε))
      (E + (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2) (edgeEL N C))) L.law :=
    Integrable.of_bound hKp.aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hK01 _).1]; exact (hK01 _).2)
  -- the measurable hull of the complement of the event
  have hBm : MeasurableSet (toMeasurable L.law (edgeInputEvent N C)ᶜ) :=
    measurableSet_toMeasurable _ _
  have hBμ : L.law (toMeasurable L.law (edgeInputEvent N C)ᶜ) = L.law (edgeInputEvent N C)ᶜ :=
    measure_toMeasurable _
  have hIA : Integrable ({ω : Entries N | lambdaMax (symOfEntries ω) < E}.indicator
      (1 : Entries N → ℝ)) L.law := (integrable_const (1 : ℝ)).indicator hAm
  have hIB : Integrable ((toMeasurable L.law (edgeInputEvent N C)ᶜ).indicator
      (1 : Entries N → ℝ)) L.law := (integrable_const (1 : ℝ)).indicator hBm
  have hIAint : ∫ ω, {ω : Entries N | lambdaMax (symOfEntries ω) < E}.indicator
      (1 : Entries N → ℝ) ω ∂L.law = (L.law {ω | lambdaMax (symOfEntries ω) < E}).toReal := by
    rw [integral_indicator_one hAm, measureReal_def]
  have hIBint : ∫ ω, (toMeasurable L.law (edgeInputEvent N C)ᶜ).indicator
      (1 : Entries N → ℝ) ω ∂L.law = (L.law (edgeInputEvent N C)ᶜ).toReal := by
    rw [integral_indicator_one hBm, measureReal_def, hBμ]
  have hBnn : ∀ ω, 0 ≤ (toMeasurable L.law (edgeInputEvent N C)ᶜ).indicator
      (1 : Entries N → ℝ) ω := fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have hAnn : ∀ ω, 0 ≤ {ω : Entries N | lambdaMax (symOfEntries ω) < E}.indicator
      (1 : Entries N → ℝ) ω := fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have hBle : ∀ ω, (toMeasurable L.law (edgeInputEvent N C)ᶜ).indicator
      (1 : Entries N → ℝ) ω ≤ 1 := fun ω =>
    Set.indicator_le_self' (fun _ _ => zero_le_one) ω |>.trans (by simp)
  have hAle : ∀ ω, {ω : Entries N | lambdaMax (symOfEntries ω) < E}.indicator
      (1 : Entries N → ℝ) ω ≤ 1 := fun ω =>
    Set.indicator_le_self' (fun _ _ => zero_le_one) ω |>.trans (by simp)
  -- the pointwise inequalities everywhere
  have hlow : ∀ ω, edgeCutoff (smoothCount (symOfEntries_isHermitian ω)
      ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε)) (E - (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2)
      (edgeEL N C)) ≤ {ω : Entries N | lambdaMax (symOfEntries ω) < E}.indicator
        (1 : Entries N → ℝ) ω + (toMeasurable L.law (edgeInputEvent N C)ᶜ).indicator
        (1 : Entries N → ℝ) ω := by
    intro ω
    by_cases hω : ω ∈ edgeInputEvent N C
    · exact (hΩ ω hω).1.trans (le_add_of_nonneg_right (hBnn ω))
    · have hωB : ω ∈ toMeasurable L.law (edgeInputEvent N C)ᶜ :=
        subset_toMeasurable _ _ (show ω ∈ (edgeInputEvent N C)ᶜ from hω)
      rw [Set.indicator_of_mem hωB]
      have := (hK01 (smoothCount (symOfEntries_isHermitian ω)
        ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε)) (E - (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2)
        (edgeEL N C))).2
      have := hAnn ω
      simp only [Pi.one_apply] at *
      linarith
  have hupp : ∀ ω, {ω : Entries N | lambdaMax (symOfEntries ω) < E}.indicator
        (1 : Entries N → ℝ) ω ≤ edgeCutoff (smoothCount (symOfEntries_isHermitian ω)
      ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε)) (E + (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2)
      (edgeEL N C)) + (toMeasurable L.law (edgeInputEvent N C)ᶜ).indicator
        (1 : Entries N → ℝ) ω := by
    intro ω
    by_cases hω : ω ∈ edgeInputEvent N C
    · exact (hΩ ω hω).2.trans (le_add_of_nonneg_right (hBnn ω))
    · have hωB : ω ∈ toMeasurable L.law (edgeInputEvent N C)ᶜ :=
        subset_toMeasurable _ _ (show ω ∈ (edgeInputEvent N C)ᶜ from hω)
      rw [Set.indicator_of_mem hωB]
      have := (hK01 (smoothCount (symOfEntries_isHermitian ω)
        ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε)) (E + (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2)
        (edgeEL N C))).1
      have := hAle ω
      simp only [Pi.one_apply] at *
      linarith
  have h1 := integral_mono hKmi (hIA.add hIB) hlow
  have h2 := integral_mono hIA (hKpi.add hIB) hupp
  rw [integral_add' hIA hIB, hIAint, hIBint] at h1
  rw [integral_add' hKpi hIB, hIBint, hIAint] at h2
  exact ⟨by linarith, h2⟩

/-! ## Checks -/

/-- The sandwich at the GOE entry laws, `C = 1`, `ε = 1/20`, `E = 2`, and a size `N ≥ 3`:
all hypotheses hold at this point. -/
example : ∃ N : ℕ, 3 ≤ N ∧
    (∫ ω, edgeCutoff (smoothCount (symOfEntries_isHermitian ω)
        ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * (1 / 20 : ℝ)))
        (2 - (N : ℝ) ^ (-(2 : ℝ) / 3 - (1 / 20 : ℝ)) / 2) (edgeEL N 1)) ∂(goeLaws N).law) -
      ((goeLaws N).law (edgeInputEvent N 1)ᶜ).toReal ≤
      ((goeLaws N).law {ω | lambdaMax (symOfEntries ω) < 2}).toReal ∧
    ((goeLaws N).law {ω | lambdaMax (symOfEntries ω) < 2}).toReal ≤
      (∫ ω, edgeCutoff (smoothCount (symOfEntries_isHermitian ω)
        ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * (1 / 20 : ℝ)))
        (2 + (N : ℝ) ^ (-(2 : ℝ) / 3 - (1 / 20 : ℝ)) / 2) (edgeEL N 1)) ∂(goeLaws N).law) +
      ((goeLaws N).law (edgeInputEvent N 1)ᶜ).toReal := by
  obtain ⟨N0, hN0⟩ := prob_lambdaMax_lt_sandwich (C := 1) one_pos (1 / 20) (by norm_num)
    (by norm_num)
  have hN3 : 3 ≤ max N0 3 := le_max_right _ _
  have hprob : (goeLaws (max N0 3)).IsProb :=
    (ofIID_isGenWigner goe_wignerLaws (N := max N0 3) (by omega)).isProb
  have hwin : |(2 : ℝ) - 2| ≤
      phi (max N0 3) ^ (1 : ℝ) * ((max N0 3 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) := by
    rw [sub_self, abs_zero, phi_eq_exp hN3]
    exact mul_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact ⟨max N0 3, hN3, hN0 (max N0 3) (le_max_left _ _) (goeLaws (max N0 3)) hprob 2 hwin⟩

#print axioms prob_lambdaMax_lt_sandwich

end WEdgeNS
