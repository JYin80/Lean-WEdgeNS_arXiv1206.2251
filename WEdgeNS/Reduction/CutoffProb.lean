import WEdgeNS.Reduction.Cutoff

/-!
# Probability of the entry cut-off
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-! ### Tail of a law with a finite second moment -/

private lemma cutoffProb_measurableSet_tail (T : ℝ) : MeasurableSet {x : ℝ | T < |x|} :=
  measurableSet_lt measurable_const continuous_abs.measurable

/-- The part of `∫ x² dμ` beyond `T` tends to `0` as `T → ∞`. -/
private lemma cutoffProb_tendsto_setIntegral_sq_tail {μ : Measure ℝ}
    (h : Integrable (fun x : ℝ => x ^ 2) μ) :
    Tendsto (fun T : ℝ => ∫ x in {x : ℝ | T < |x|}, x ^ 2 ∂μ) atTop (𝓝 0) := by
  have key : Tendsto (fun T : ℝ => ∫ x, ({x : ℝ | T < |x|}).indicator (fun x => x ^ 2) x ∂μ)
      atTop (𝓝 (∫ _x, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => x ^ 2) ?_ ?_ h ?_
    · exact Eventually.of_forall fun T =>
        (h.1.indicator (cutoffProb_measurableSet_tail T))
    · refine Eventually.of_forall fun T => Eventually.of_forall fun x => ?_
      by_cases hx : T < |x|
      · simp [Set.indicator_of_mem (show x ∈ {x : ℝ | T < |x|} from hx)]
      · rw [Set.indicator_of_notMem (show x ∉ {x : ℝ | T < |x|} from hx), norm_zero]
        positivity
    · refine Eventually.of_forall fun x => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop |x|] with T hT
      simp [Set.indicator_of_notMem (show x ∉ {x : ℝ | T < |x|} from not_lt.mpr hT)]
  simp only [integral_zero] at key
  refine key.congr fun T => ?_
  exact integral_indicator (cutoffProb_measurableSet_tail T)

/-- Chebyshev: `T² μ(|x| > T)` is at most the part of `∫ x² dμ` beyond `T`. -/
private lemma cutoffProb_sq_mul_measure_le {μ : Measure ℝ} [IsFiniteMeasure μ]
    (h : Integrable (fun x : ℝ => x ^ 2) μ) {T : ℝ} (hT : 0 ≤ T) :
    T ^ 2 * (μ {x : ℝ | T < |x|}).toReal ≤ ∫ x in {x : ℝ | T < |x|}, x ^ 2 ∂μ := by
  have h1 : ∫ _x in {x : ℝ | T < |x|}, T ^ 2 ∂μ ≤ ∫ x in {x : ℝ | T < |x|}, x ^ 2 ∂μ := by
    refine setIntegral_mono_on (integrableOn_const (by simp [measure_ne_top])) h.integrableOn
      (cutoffProb_measurableSet_tail T) fun x hx => ?_
    have hx' : T < |x| := hx
    rw [← sq_abs x]
    exact pow_le_pow_left₀ hT hx'.le 2
  rw [setIntegral_const, smul_eq_mul, measureReal_def] at h1
  linarith

/-- For a law with a finite second moment, `T² μ(|x| > T) → 0`. -/
private lemma cutoffProb_tendsto_sq_mul_measure {μ : Measure ℝ} [IsFiniteMeasure μ]
    (h : Integrable (fun x : ℝ => x ^ 2) μ) :
    Tendsto (fun T : ℝ => T ^ 2 * (μ {x : ℝ | T < |x|}).toReal) atTop (𝓝 0) :=
  squeeze_zero' (Eventually.of_forall fun T => by positivity)
    ((eventually_ge_atTop (0 : ℝ)).mono fun T hT => cutoffProb_sq_mul_measure_le h hT)
    (cutoffProb_tendsto_setIntegral_sq_tail h)

/-! ### The three blocks of the auxiliary space have total mass at most `1` -/

/-! ### One coordinate of an entry vector -/

/-- A coordinate of a product of identical laws of total mass at most `1` has at most the mass
of the coordinate law. -/
private lemma cutoffProb_pi_coord {ι : Type*} [Fintype ι] (L : Measure ℝ) (h : L Set.univ ≤ 1)
    (i : ι) {B : Set ℝ} (hB : MeasurableSet B) :
    (Measure.pi fun _ : ι => L) {w | w i ∈ B} ≤ L B := by
  classical
  have : IsFiniteMeasure L := ⟨lt_of_le_of_lt h ENNReal.one_lt_top⟩
  have h1 := Measure.pi_map_eval (fun _ : ι => L) i
  have h2 : (Measure.pi fun _ : ι => L) {w | w i ∈ B} =
      ((Measure.pi fun _ : ι => L).map (Function.eval i)) B := by
    rw [Measure.map_apply (measurable_pi_apply i) hB]
    rfl
  rw [h2, h1, Measure.smul_apply, smul_eq_mul]
  calc _ ≤ 1 * L B := mul_le_mul' (Finset.prod_le_one (fun j _ => h)) le_rfl
    _ = L B := one_mul _

/-- A diagonal coordinate of the entry vector has at most the mass of the diagonal law. -/
private lemma cutoffProb_entryLaw_diag {L L' : Measure ℝ} (N : ℕ) (h : L Set.univ ≤ 1)
    (h' : L' Set.univ ≤ 1) (i : Fin N) {B : Set ℝ} (hB : MeasurableSet B) :
    entryLaw L L' N {w | w.1 i ∈ B} ≤ L' B := by
  have : IsFiniteMeasure L := ⟨lt_of_le_of_lt h ENNReal.one_lt_top⟩
  have : IsFiniteMeasure L' := ⟨lt_of_le_of_lt h' ENNReal.one_lt_top⟩
  unfold entryLaw
  have hset : {w : Entries N | w.1 i ∈ B} = {v : Fin N → ℝ | v i ∈ B} ×ˢ Set.univ := by
    ext w
    simp
  rw [hset, Measure.prod_prod]
  calc _ ≤ L' B * 1 := mul_le_mul' (cutoffProb_pi_coord L' h' i hB)
        (by rw [Measure.pi_univ]; exact Finset.prod_le_one (fun _ _ => h))
    _ = L' B := mul_one _

/-- An upper coordinate of the entry vector has at most the mass of the upper law. -/
private lemma cutoffProb_entryLaw_upper {L L' : Measure ℝ} (N : ℕ) (h : L Set.univ ≤ 1)
    (h' : L' Set.univ ≤ 1) (p : OffDiag N) {B : Set ℝ} (hB : MeasurableSet B) :
    entryLaw L L' N {w | w.2 p ∈ B} ≤ L B := by
  have : IsFiniteMeasure L := ⟨lt_of_le_of_lt h ENNReal.one_lt_top⟩
  have : IsFiniteMeasure L' := ⟨lt_of_le_of_lt h' ENNReal.one_lt_top⟩
  unfold entryLaw
  have hset : {w : Entries N | w.2 p ∈ B} = Set.univ ×ˢ {v : OffDiag N → ℝ | v p ∈ B} := by
    ext w
    simp
  rw [hset, Measure.prod_prod]
  calc _ ≤ 1 * L B := mul_le_mul'
        (by rw [Measure.pi_univ]; exact Finset.prod_le_one (fun _ _ => h'))
        (cutoffProb_pi_coord L h p hB)
    _ = L B := one_mul _

/-! ### An event on three blocks of total mass at most `1` -/

/-- If the first block misses `P₁` and the third misses `P₃` almost surely, the product measure
of an event inside `P₁ × ℝ × ℝ ∪ ℝ × ℝ × P₃ ∪ ℝ × Q₂ × Q₃` is at most `M₂ Q₂ · M₃ Q₃`. -/
private lemma cutoffProb_triple {Ω : Type*} [MeasurableSpace Ω] (M1 M2 M3 : Measure Ω)
    (h1 : M1 Set.univ ≤ 1) (h2 : M2 Set.univ ≤ 1) (h3 : M3 Set.univ ≤ 1)
    {R : Set (Ω × Ω × Ω)} {P1 P3 Q2 Q3 : Set Ω} (hP1 : M1 P1 = 0) (hP3 : M3 P3 = 0)
    (hR : R ⊆ (P1 ×ˢ Set.univ) ∪ (Set.univ ×ˢ (Set.univ ×ˢ P3)) ∪
      (Set.univ ×ˢ (Q2 ×ˢ Q3))) :
    (M1.prod (M2.prod M3)) R ≤ M2 Q2 * M3 Q3 := by
  have : IsFiniteMeasure M1 := ⟨lt_of_le_of_lt h1 ENNReal.one_lt_top⟩
  have : IsFiniteMeasure M2 := ⟨lt_of_le_of_lt h2 ENNReal.one_lt_top⟩
  have : IsFiniteMeasure M3 := ⟨lt_of_le_of_lt h3 ENNReal.one_lt_top⟩
  refine (measure_mono hR).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add (measure_union_le _ _) le_rfl).trans ?_
  simp only [Measure.prod_prod, hP1, hP3, zero_mul, mul_zero, zero_add, add_zero]
  calc _ ≤ 1 * (M2 Q2 * M3 Q3) := mul_le_mul' h1 le_rfl
    _ = _ := one_mul _

/-! ### The laws of one coordinate triple -/

/-- Under the small-part law, `|x + m| ≤ T` almost surely, where `m` is the centring. -/
private lemma cutoffProb_small_null (ρ : Measure ℝ) (T : ℝ) :
    truncCentered ρ T {x | T < |x + cutoffMean ρ T|} = 0 := by
  have hA : MeasurableSet {x : ℝ | |x| ≤ T} :=
    measurableSet_le continuous_abs.measurable measurable_const
  have hB : MeasurableSet {x : ℝ | T < |x + cutoffMean ρ T|} :=
    measurableSet_lt measurable_const (by fun_prop)
  unfold truncCentered
  rw [Measure.map_apply (by fun_prop) hB, cond_apply hA]
  have : {x : ℝ | |x| ≤ T} ∩ ((fun x => x - ∫ y, y ∂(cond ρ {x | |x| ≤ T})) ⁻¹'
      {x | T < |x + cutoffMean ρ T|}) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, cutoffMean,
      sub_add_cancel, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
    exact fun h => h
  rw [this, measure_empty, mul_zero]

/-- The selector takes only the values `0` and `1`. -/
private lemma cutoffProb_sel_null (ρ : Measure ℝ) (T : ℝ) :
    ρ.map (largeInd T) {c | c ≠ 0 ∧ c ≠ 1} = 0 := by
  have hm : MeasurableSet {c : ℝ | c ≠ 0 ∧ c ≠ 1} :=
    (measurableSet_singleton (0 : ℝ)).compl.inter (measurableSet_singleton (1 : ℝ)).compl
  rw [Measure.map_apply (measurable_largeInd T) hm]
  have : largeInd T ⁻¹' {c : ℝ | c ≠ 0 ∧ c ≠ 1} = ∅ := by
    ext x
    unfold largeInd
    by_cases h : T < |x| <;> simp [h]
  rw [this, measure_empty]

/-- The mass of `{x | s < |x + m|}` under the large-part law, times the probability that the
selector is `1`, is at most the tail mass of the original law beyond `s`. -/
private lemma cutoffProb_large_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (T s : ℝ) :
    truncLargeCentered ρ T {x | s < |x + cutoffMean ρ T|} * ρ.map (largeInd T) {1} ≤
      ρ {x | s < |x|} := by
  have hsel : ρ.map (largeInd T) {1} = ρ {x | T < |x|} := by
    rw [Measure.map_apply (measurable_largeInd T) (measurableSet_singleton (1 : ℝ))]
    congr 1
    ext x
    unfold largeInd
    by_cases h : T < |x| <;> simp [h]
  rw [hsel]
  by_cases h0 : ρ {x | T < |x|} = 0
  · rw [h0, mul_zero]
    exact bot_le
  · have hB : MeasurableSet {x : ℝ | s < |x + cutoffMean ρ T|} :=
      measurableSet_lt measurable_const (by fun_prop)
    simp only [truncLargeCentered, h0, ↓reduceIte]
    rw [Measure.map_apply (by fun_prop) hB, cond_apply (cutoffProb_measurableSet_tail T)]
    have : {x : ℝ | T < |x|} ∩ ((fun x => x - cutoffMean ρ T) ⁻¹'
        {x | s < |x + cutoffMean ρ T|}) = {x | T < |x|} ∩ {x | s < |x|} := by
      ext x
      simp
    rw [this, mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel h0 (measure_ne_top _ _), one_mul]
    exact measure_mono Set.inter_subset_right

/-! ### One coordinate of the event -/

/-- The event at one coordinate: `|(N^{-1/2} x^L_e - N^{-1/2} x^S_e) c_e| > 3/4`. -/
private def cutoffProb_bad {N : ℕ} (ev : Entries N → ℝ) : Set (CoupleSpace N) :=
  {u | 3 / 4 < |((Real.sqrt N)⁻¹ * ev u.2.1 - (Real.sqrt N)⁻¹ * ev u.1) * ev u.2.2|}

/-- The elementary inequality behind (4.21), with `q = √N` and `4 T ≤ q`: if
`|(q⁻¹ b - q⁻¹ a) c| > 3/4`, then `|a + m| > T`, or `c ∉ {0, 1}`, or `c = 1` and
`|b + m| > q/2`. -/
private lemma cutoffProb_geom {a b c m T q : ℝ} (hq : 0 < q) (hT : 4 * T ≤ q)
    (h : 3 / 4 < |(q⁻¹ * b - q⁻¹ * a) * c|) :
    T < |a + m| ∨ (c ≠ 0 ∧ c ≠ 1) ∨ (q / 2 < |b + m| ∧ c = 1) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  by_cases hc : c = 0
  · subst hc
    simp at h
    linarith
  · have hc1 : c = 1 := h2 hc
    have hb : |b + m| ≤ q / 2 := by
      by_contra hb
      exact h3 (not_le.mp hb) hc1
    subst hc1
    have hba : |b - a| ≤ 3 / 4 * q := by
      calc |b - a| = |(b + m) - (a + m)| := by ring_nf
        _ ≤ |b + m| + |a + m| := abs_sub _ _
        _ ≤ 3 / 4 * q := by linarith
    have : |(q⁻¹ * b - q⁻¹ * a) * 1| ≤ 3 / 4 := by
      rw [mul_one, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hq), inv_mul_le_iff₀ hq]
      linarith
    linarith

/-- The bound for one coordinate of the event, from the laws of its three entries. -/
private lemma cutoffProb_coord_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {N : ℕ} (hN : 1 ≤ N)
    {T : ℝ} (hT : 4 * T ≤ Real.sqrt N) {M1 M2 M3 : Measure (Entries N)}
    (h1 : M1 Set.univ ≤ 1) (h2 : M2 Set.univ ≤ 1) (h3 : M3 Set.univ ≤ 1)
    (ev : Entries N → ℝ)
    (e1 : ∀ B, MeasurableSet B → M1 {w | ev w ∈ B} ≤ truncCentered ρ T B)
    (e2 : ∀ B, MeasurableSet B → M2 {w | ev w ∈ B} ≤ truncLargeCentered ρ T B)
    (e3 : ∀ B, MeasurableSet B → M3 {w | ev w ∈ B} ≤ ρ.map (largeInd T) B) :
    (M1.prod (M2.prod M3)) (cutoffProb_bad ev) ≤ ρ {x | Real.sqrt N / 2 < |x|} := by
  have hq : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hS : MeasurableSet {x : ℝ | T < |x + cutoffMean ρ T|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hC : MeasurableSet {c : ℝ | c ≠ 0 ∧ c ≠ 1} :=
    (measurableSet_singleton (0 : ℝ)).compl.inter (measurableSet_singleton (1 : ℝ)).compl
  have hL : MeasurableSet {x : ℝ | Real.sqrt N / 2 < |x + cutoffMean ρ T|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hP1 : M1 {w | ev w ∈ {x : ℝ | T < |x + cutoffMean ρ T|}} = 0 :=
    le_antisymm ((e1 _ hS).trans (cutoffProb_small_null ρ T).le) bot_le
  have hP3 : M3 {w | ev w ∈ {c : ℝ | c ≠ 0 ∧ c ≠ 1}} = 0 :=
    le_antisymm ((e3 _ hC).trans (cutoffProb_sel_null ρ T).le) bot_le
  refine (cutoffProb_triple M1 M2 M3 h1 h2 h3 hP1 hP3 (R := cutoffProb_bad ev)
    (Q2 := {w | ev w ∈ {x : ℝ | Real.sqrt N / 2 < |x + cutoffMean ρ T|}})
    (Q3 := {w | ev w ∈ ({1} : Set ℝ)}) ?_).trans ?_
  · intro u hu
    rcases cutoffProb_geom (m := cutoffMean ρ T) hq hT hu with h | h | h
    · exact Or.inl (Or.inl ⟨h, Set.mem_univ _⟩)
    · exact Or.inl (Or.inr ⟨Set.mem_univ _, Set.mem_univ _, h⟩)
    · exact Or.inr ⟨Set.mem_univ _, h.1, Set.mem_singleton_iff.mpr h.2⟩
  · refine (mul_le_mul' (e2 _ hL) (e3 _ (measurableSet_singleton (1 : ℝ)))).trans ?_
    exact cutoffProb_large_le ρ T _

/-! ### The union over coordinates -/

/-- A value above `3/4` of an entry of `(H^L - H^S) ∘ H^C` is a value above `3/4` of the event at
one diagonal or upper coordinate. -/
private lemma cutoffProb_entry_mem {N : ℕ} (u : CoupleSpace N) (i j : Fin N)
    (h : 3 / 4 < |(largeMat u - smallMat u) i j * selMat u i j|) :
    (∃ k : Fin N, u ∈ cutoffProb_bad (fun w : Entries N => w.1 k)) ∨
      (∃ p : OffDiag N, u ∈ cutoffProb_bad (fun w : Entries N => w.2 p)) := by
  by_cases hij : i = j
  · subst hij
    left
    refine ⟨i, ?_⟩
    simpa [cutoffProb_bad, largeMat, smallMat, selMat, symOfEntries] using h
  · by_cases hlt : i < j
    · right
      refine ⟨⟨(i, j), hlt⟩, ?_⟩
      simpa [cutoffProb_bad, largeMat, smallMat, selMat, symOfEntries, hij, hlt] using h
    · right
      refine ⟨⟨(j, i), lt_of_le_of_ne (not_lt.mp hlt) (fun e => hij e.symm)⟩, ?_⟩
      simpa [cutoffProb_bad, largeMat, smallMat, selMat, symOfEntries, hij, hlt] using h

/-- The exponent bookkeeping: `N^{1/2-ε}` is at most `√N / 4` once `N^ε ≥ 4`. -/
private lemma cutoffProb_four_le {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (h : 4 ≤ (N : ℝ) ^ ε) :
    4 * (N : ℝ) ^ (1 / 2 - ε) ≤ Real.sqrt N := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have e : Real.sqrt N = (N : ℝ) ^ (1 / 2 - ε) * (N : ℝ) ^ ε := by
    rw [← Real.rpow_add hpos, Real.sqrt_eq_rpow]
    congr 1
    ring
  rw [e, mul_comm]
  exact mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hpos.le _)

/-- The selector law has total mass `1`. -/
private lemma cutoffProb_mass_sel (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (T : ℝ) :
    ρ.map (largeInd T) Set.univ ≤ 1 := by
  rw [Measure.map_apply (measurable_largeInd T) MeasurableSet.univ,
    Set.preimage_univ, measure_univ]

/-- (4.21)–(4.23) as a bound: once `N^ε ≥ 4`, the cut-off fails with probability at most
`N ν'{|x| > ½√N} + N² ν{|x| ≥ ½√N}`. -/
private lemma cutoffProb_le {ν ν' : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    {ε : ℝ} {N : ℕ} (hN : 1 ≤ N) (h : 4 ≤ (N : ℝ) ^ ε) :
    coupleLaw ν ν' ε N
        {u | ∃ i j, 3 / 4 < |(largeMat u - smallMat u) i j * selMat u i j|} ≤
      N * ν' {x | Real.sqrt N / 2 < |x|} + N ^ 2 * ν {x | Real.sqrt N / 2 ≤ |x|} := by
  have hT := cutoffProb_four_le hN h
  set T : ℝ := (N : ℝ) ^ (1 / 2 - ε) with hTdef
  have m1 := entryLaw_univ_le_one N (truncCentered_univ_le_one ν T)
    (truncCentered_univ_le_one ν' T)
  have m2 := entryLaw_univ_le_one N (truncLargeCentered_univ_le_one ν T)
    (truncLargeCentered_univ_le_one ν' T)
  have m3 := entryLaw_univ_le_one N (cutoffProb_mass_sel ν T) (cutoffProb_mass_sel ν' T)
  have hdiag : ∀ k : Fin N, coupleLaw ν ν' ε N (cutoffProb_bad fun w : Entries N => w.1 k) ≤
      ν' {x | Real.sqrt N / 2 < |x|} := fun k =>
    cutoffProb_coord_le ν' hN hT m1 m2 m3 _
      (fun B hB => cutoffProb_entryLaw_diag N (truncCentered_univ_le_one ν T)
        (truncCentered_univ_le_one ν' T) k hB)
      (fun B hB => cutoffProb_entryLaw_diag N (truncLargeCentered_univ_le_one ν T)
        (truncLargeCentered_univ_le_one ν' T) k hB)
      (fun B hB => cutoffProb_entryLaw_diag N (cutoffProb_mass_sel ν T)
        (cutoffProb_mass_sel ν' T) k hB)
  have hup : ∀ p : OffDiag N, coupleLaw ν ν' ε N (cutoffProb_bad fun w : Entries N => w.2 p) ≤
      ν {x | Real.sqrt N / 2 < |x|} := fun p =>
    cutoffProb_coord_le ν hN hT m1 m2 m3 _
      (fun B hB => cutoffProb_entryLaw_upper N (truncCentered_univ_le_one ν T)
        (truncCentered_univ_le_one ν' T) p hB)
      (fun B hB => cutoffProb_entryLaw_upper N (truncLargeCentered_univ_le_one ν T)
        (truncLargeCentered_univ_le_one ν' T) p hB)
      (fun B hB => cutoffProb_entryLaw_upper N (cutoffProb_mass_sel ν T)
        (cutoffProb_mass_sel ν' T) p hB)
  have hsub : {u : CoupleSpace N | ∃ i j, 3 / 4 < |(largeMat u - smallMat u) i j * selMat u i j|} ⊆
      (⋃ k : Fin N, cutoffProb_bad fun w : Entries N => w.1 k) ∪
        ⋃ p : OffDiag N, cutoffProb_bad fun w : Entries N => w.2 p := by
    rintro u ⟨i, j, hij⟩
    rcases cutoffProb_entry_mem u i j hij with ⟨k, hk⟩ | ⟨p, hp⟩
    · exact Or.inl (Set.mem_iUnion.mpr ⟨k, hk⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨p, hp⟩)
  have hcard : (Fintype.card (OffDiag N) : ENNReal) ≤ (N : ENNReal) ^ 2 := by
    have : Fintype.card (OffDiag N) ≤ Fintype.card (Fin N × Fin N) :=
      Fintype.card_subtype_le _
    simp only [Fintype.card_prod, Fintype.card_fin] at this
    exact_mod_cast this.trans_eq (by ring)
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add (measure_iUnion_fintype_le _ _) (measure_iUnion_fintype_le _ _)
    _ ≤ (∑ _k : Fin N, ν' {x | Real.sqrt N / 2 < |x|}) +
          ∑ _p : OffDiag N, ν {x | Real.sqrt N / 2 ≤ |x|} :=
        add_le_add
          (Finset.sum_le_sum fun k _ => hdiag k)
          (Finset.sum_le_sum fun p _ => (hup p).trans
            (measure_mono fun x (hx : Real.sqrt N / 2 < |x|) => le_of_lt hx))
    _ ≤ N * ν' {x | Real.sqrt N / 2 < |x|} + N ^ 2 * ν {x | Real.sqrt N / 2 ≤ |x|} := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact add_le_add le_rfl (mul_le_mul_left hcard _)

/-! ### The limit -/

/-- The real-valued form of `cutoffProb_le`, written with `s = ½√N`: `N = 4 s²`, `N² = 16 s⁴`. -/
private lemma cutoffProb_toReal_le {ν ν' : Measure ℝ} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] {ε : ℝ} {N : ℕ} (hN : 1 ≤ N) (h : 4 ≤ (N : ℝ) ^ ε) :
    (coupleLaw ν ν' ε N
        {u | ∃ i j, 3 / 4 < |(largeMat u - smallMat u) i j * selMat u i j|}).toReal ≤
      4 * ((Real.sqrt N / 2) ^ 2 * (ν' {x | Real.sqrt N / 2 < |x|}).toReal) +
        16 * ((Real.sqrt N / 2) ^ 4 * (ν {x | Real.sqrt N / 2 ≤ |x|}).toReal) := by
  have hm : (N : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top N
  have ha := measure_ne_top ν {x | Real.sqrt N / 2 ≤ |x|}
  have ha' := measure_ne_top ν' {x | Real.sqrt N / 2 < |x|}
  have h1 : (N : ENNReal) * ν' {x | Real.sqrt N / 2 < |x|} ≠ ⊤ := ENNReal.mul_ne_top hm ha'
  have h2 : (N : ENNReal) ^ 2 * ν {x | Real.sqrt N / 2 ≤ |x|} ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top hm) ha
  have hb := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨h1, h2⟩) (cutoffProb_le (ν := ν)
    (ν' := ν') hN h)
  rw [ENNReal.toReal_add h1 h2] at hb
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast] at hb
  have hsq : (Real.sqrt N / 2) ^ 2 = N / 4 := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    norm_num
  have h4 : (Real.sqrt N / 2) ^ 4 = (N : ℝ) ^ 2 / 16 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq]
    ring
  rw [hsq, h4]
  have e1 : 4 * ((N : ℝ) / 4 * (ν' {x | Real.sqrt N / 2 < |x|}).toReal) =
      N * (ν' {x | Real.sqrt N / 2 < |x|}).toReal := by ring
  have e2 : 16 * ((N : ℝ) ^ 2 / 16 * (ν {x | Real.sqrt N / 2 ≤ |x|}).toReal) =
      N ^ 2 * (ν {x | Real.sqrt N / 2 ≤ |x|}).toReal := by ring
  rw [e1, e2]
  exact hb

/-- (4.21)–(4.23): `P(max_ij |H̃_ij H^C_ij| > 3/4) → 0`. -/
theorem tendsto_coupleLaw_cutoff {ν ν' : Measure ℝ} (hW : WignerLaws ν ν') (h14 : TailCond ν)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    Tendsto (fun N : ℕ => (coupleLaw ν ν' ε N
      {u | ∃ i j, 3 / 4 < |(largeMat u - smallMat u) i j * selMat u i j|}).toReal)
      atTop (𝓝 0) := by
  have _ := hε
  have := hW.prob
  have := hW.prob'
  have hs : Tendsto (fun N : ℕ => Real.sqrt N / 2) atTop atTop :=
    ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const
      (by norm_num : (0 : ℝ) < 2))
  have t1 := (cutoffProb_tendsto_sq_mul_measure hW.sq_int').comp hs
  have t2 := h14.comp hs
  have hlim := (t1.const_mul 4).add (t2.const_mul 16)
  simp only [mul_zero, add_zero] at hlim
  have hev : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ 4 ≤ (N : ℝ) ^ ε :=
    (eventually_ge_atTop 1).and
      (((tendsto_rpow_atTop hε0).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4)
  refine squeeze_zero' (Eventually.of_forall fun N => ENNReal.toReal_nonneg)
    (hev.mono fun N hN => cutoffProb_toReal_le hN.1 hN.2) hlim

/-! ### A nondegenerate instance: Rademacher off-diagonal entries, `N(0, 2)` diagonal entries,
`ε = 1/100` -/

/-- The hypotheses hold at Rademacher off-diagonal entries and `N(0, 2)` diagonal entries with
`ε = 1/100`; there the off-diagonal selector vanishes and the diagonal selector does not. -/
example : Tendsto (fun N : ℕ => (coupleLaw rademacher (gaussianReal 0 2) (1 / 100) N
    {u | ∃ i j, 3 / 4 < |(largeMat u - smallMat u) i j * selMat u i j|}).toReal)
    atTop (𝓝 0) :=
  tendsto_coupleLaw_cutoff rademacher_wignerLaws rademacher_tailCond (by norm_num)
    (by norm_num)

#print axioms tendsto_coupleLaw_cutoff

end WEdgeNS
