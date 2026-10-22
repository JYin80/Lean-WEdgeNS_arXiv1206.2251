import WEdgeNS.Reduction.Cutoff

/-!
# Probability of the admissible selector patterns
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-! ### The first two blocks of the auxiliary space have total mass at most `1` -/

/-- An event on the selector block has at most its probability under the third factor. -/
private lemma selProb_coupleLaw_le {ν ν' : Measure ℝ} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] (ε : ℝ) (N : ℕ) (B : Set (Entries N)) :
    coupleLaw ν ν' ε N {u | u.2.2 ∈ B} ≤
      entryLaw (ν.map (largeInd ((N : ℝ) ^ (1 / 2 - ε))))
        (ν'.map (largeInd ((N : ℝ) ^ (1 / 2 - ε)))) N B := by
  have h1 := entryLaw_univ_le_one (L := truncCentered ν ((N : ℝ) ^ (1 / 2 - ε)))
    (L' := truncCentered ν' ((N : ℝ) ^ (1 / 2 - ε))) N (truncCentered_univ_le_one _ _)
    (truncCentered_univ_le_one _ _)
  have h2 := entryLaw_univ_le_one (L := truncLargeCentered ν ((N : ℝ) ^ (1 / 2 - ε)))
    (L' := truncLargeCentered ν' ((N : ℝ) ^ (1 / 2 - ε))) N (truncLargeCentered_univ_le_one _ _)
    (truncLargeCentered_univ_le_one _ _)
  have hset : {u : CoupleSpace N | u.2.2 ∈ B} = Set.univ ×ˢ (Set.univ ×ˢ B) := by
    ext u; simp
  have : IsFiniteMeasure (entryLaw (truncLargeCentered ν ((N : ℝ) ^ (1 / 2 - ε)))
      (truncLargeCentered ν' ((N : ℝ) ^ (1 / 2 - ε))) N) := ⟨lt_of_le_of_lt h2 ENNReal.one_lt_top⟩
  have : IsFiniteMeasure (entryLaw (truncCentered ν ((N : ℝ) ^ (1 / 2 - ε)))
      (truncCentered ν' ((N : ℝ) ^ (1 / 2 - ε))) N) := ⟨lt_of_le_of_lt h1 ENNReal.one_lt_top⟩
  unfold coupleLaw
  rw [hset, Measure.prod_prod, Measure.prod_prod]
  calc _ ≤ 1 * (1 * _) := mul_le_mul' h1 (mul_le_mul' h2 le_rfl)
    _ = _ := by rw [one_mul, one_mul]

/-! ### Entries of the symmetric matrix as coordinates of the entry space -/

/-- The index of the upper entry carrying the unordered pair `{s, x}`. -/
private def selProb_pairOf {N : ℕ} (s x : Fin N) (h : s ≠ x) : OffDiag N :=
  if h' : s < x then ⟨(s, x), h'⟩ else ⟨(x, s), lt_of_le_of_ne (not_lt.mp h') h.symm⟩

/-- A diagonal entry of the symmetric matrix is a diagonal coordinate. -/
private lemma selProb_sym_diag {N : ℕ} (c : Entries N) (i : Fin N) :
    symOfEntries c i i = c.1 i := by
  simp [symOfEntries]

/-- An off-diagonal entry of the symmetric matrix is the upper coordinate of its pair. -/
private lemma selProb_sym_offDiag {N : ℕ} (c : Entries N) {s x : Fin N} (h : s ≠ x) :
    symOfEntries c s x = c.2 (selProb_pairOf s x h) := by
  unfold symOfEntries selProb_pairOf
  by_cases h' : s < x <;> simp [h, h']

/-- The upper index of `{s, x}` is `(s, x)` or `(x, s)`. -/
private lemma selProb_pairOf_val {N : ℕ} {s x : Fin N} (h : s ≠ x) :
    (selProb_pairOf s x h).1 = (s, x) ∨ (selProb_pairOf s x h).1 = (x, s) := by
  unfold selProb_pairOf
  by_cases h' : s < x <;> simp [h']

/-- Distinct partners of `s` give distinct upper entries. -/
private lemma selProb_pairOf_inj {N : ℕ} {s x y : Fin N} (hx : s ≠ x) (hy : s ≠ y)
    (h : selProb_pairOf s x hx = selProb_pairOf s y hy) : x = y := by
  have h1 := selProb_pairOf_val hx
  have h2 := selProb_pairOf_val hy
  rw [h] at h1
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1] at h2 <;>
    simp only [Prod.mk.injEq] at h2
  · exact h2.2
  · exact absurd h2.1 hy
  · exact absurd h2.2 hy
  · exact h2.1

/-- The symmetric matrix of an entry vector is symmetric. -/
private lemma selProb_sym_comm {N : ℕ} (c : Entries N) (i j : Fin N) :
    symOfEntries c i j = symOfEntries c j i := by
  simpa using ((symOfEntries_isHermitian c).apply i j).symm

/-- Each entry of the symmetric matrix is a measurable function of the entry vector. -/
private lemma selProb_measurable_sym {N : ℕ} (i j : Fin N) :
    Measurable (fun c : Entries N => symOfEntries c i j) := by
  by_cases h : i = j
  · subst h
    simp only [selProb_sym_diag]
    fun_prop
  · simp only [selProb_sym_offDiag _ h]
    fun_prop

/-! ### Probabilities of the nonzero-entry events under the product of the selector laws -/

/-- Under a product of identical probability laws, the coordinates in a finite set all lie in
`A` with probability `L(A)` to the power of the cardinality. -/
private lemma selProb_pi_finset {ι : Type*} [Fintype ι] (L : Measure ℝ) [IsProbabilityMeasure L]
    (A : Set ℝ) (t : Finset ι) :
    (Measure.pi fun _ : ι => L) {w | ∀ i ∈ t, w i ∈ A} = L A ^ t.card := by
  have := Measure.pi_pi_finset (fun _ : ι => L) (fun _ => A) t
  have h : {w : ι → ℝ | ∀ i ∈ t, w i ∈ A} = (↑t : Set ι).pi (fun _ => A) := by
    ext w; simp [Set.mem_pi]
  rw [h, this, Finset.prod_const]

/-- One entry of the symmetric selector matrix is nonzero. -/
private lemma selProb_event_single {Lu Ld : Measure ℝ} [IsProbabilityMeasure Lu]
    [IsProbabilityMeasure Ld] {N : ℕ} (i j : Fin N) :
    entryLaw Lu Ld N {c | symOfEntries c i j ≠ 0} ≤
      if i = j then Ld {t | t ≠ 0} else Lu {t | t ≠ 0} := by
  unfold entryLaw
  by_cases h : i = j
  · subst h
    simp only [ite_true]
    have hsub : {c : Entries N | symOfEntries c i i ≠ 0} ⊆
        {w : Fin N → ℝ | ∀ k ∈ ({i} : Finset (Fin N)), w k ∈ {t : ℝ | t ≠ 0}} ×ˢ Set.univ := by
      intro c hc
      simp only [Set.mem_ofPred_eq, selProb_sym_diag] at hc
      simp [hc]
    refine (measure_mono hsub).trans ?_
    rw [Measure.prod_prod, selProb_pi_finset, measure_univ, mul_one]
    simp
  · simp only [h, ite_false]
    have hsub : {c : Entries N | symOfEntries c i j ≠ 0} ⊆
        Set.univ ×ˢ {v : OffDiag N → ℝ | ∀ k ∈ ({selProb_pairOf i j h} : Finset (OffDiag N)),
          v k ∈ {t : ℝ | t ≠ 0}} := by
      intro c hc
      simp only [Set.mem_ofPred_eq, selProb_sym_offDiag c h] at hc
      simp [hc]
    refine (measure_mono hsub).trans ?_
    rw [Measure.prod_prod, selProb_pi_finset, measure_univ, one_mul]
    simp

/-- The diagonal entry at `s` and an upper entry on the index `s` are both nonzero. -/
private lemma selProb_event_diag_upper {Lu Ld : Measure ℝ} [IsProbabilityMeasure Lu]
    [IsProbabilityMeasure Ld] {N : ℕ} {s y : Fin N} (h : s ≠ y) :
    entryLaw Lu Ld N {c | symOfEntries c s s ≠ 0 ∧ symOfEntries c s y ≠ 0} ≤
      Ld {t | t ≠ 0} * Lu {t | t ≠ 0} := by
  unfold entryLaw
  have hsub : {c : Entries N | symOfEntries c s s ≠ 0 ∧ symOfEntries c s y ≠ 0} ⊆
      {w : Fin N → ℝ | ∀ k ∈ ({s} : Finset (Fin N)), w k ∈ {t : ℝ | t ≠ 0}} ×ˢ
        {v : OffDiag N → ℝ | ∀ k ∈ ({selProb_pairOf s y h} : Finset (OffDiag N)),
          v k ∈ {t : ℝ | t ≠ 0}} := by
    intro c hc
    simp only [Set.mem_ofPred_eq, selProb_sym_offDiag c h, selProb_sym_diag] at hc
    simp [hc.1, hc.2]
  refine (measure_mono hsub).trans ?_
  rw [Measure.prod_prod, selProb_pi_finset, selProb_pi_finset]
  simp

/-- Two distinct upper entries sharing the index `s` are both nonzero. -/
private lemma selProb_event_upper_upper {Lu Ld : Measure ℝ} [IsProbabilityMeasure Lu]
    [IsProbabilityMeasure Ld] {N : ℕ} {s x y : Fin N} (hx : s ≠ x) (hy : s ≠ y) (hxy : x ≠ y) :
    entryLaw Lu Ld N {c | symOfEntries c s x ≠ 0 ∧ symOfEntries c s y ≠ 0} ≤
      Lu {t | t ≠ 0} * Lu {t | t ≠ 0} := by
  unfold entryLaw
  have hne : selProb_pairOf s x hx ≠ selProb_pairOf s y hy := fun h =>
    hxy (selProb_pairOf_inj hx hy h)
  have hsub : {c : Entries N | symOfEntries c s x ≠ 0 ∧ symOfEntries c s y ≠ 0} ⊆
      Set.univ ×ˢ {v : OffDiag N → ℝ | ∀ k ∈ ({selProb_pairOf s x hx, selProb_pairOf s y hy} :
        Finset (OffDiag N)), v k ∈ {t : ℝ | t ≠ 0}} := by
    intro c hc
    simp only [Set.mem_ofPred_eq, selProb_sym_offDiag c hx, selProb_sym_offDiag c hy] at hc
    simp [hc.1, hc.2]
  refine (measure_mono hsub).trans ?_
  rw [Measure.prod_prod, selProb_pi_finset, measure_univ, one_mul, Finset.card_pair hne, pow_two]

/-! ### The number of nonzero entries -/

/-- The number of nonzero entries is a measurable function of the entry vector. -/
private lemma selProb_measurable_nzCount {N : ℕ} :
    Measurable (fun c : Entries N => (nzCount (symOfEntries c) : ENNReal)) := by
  classical
  have hf : ∀ c : Entries N, (nzCount (symOfEntries c) : ENNReal) =
      ∑ p : Fin N × Fin N, {c' : Entries N | symOfEntries c' p.1 p.2 ≠ 0}.indicator 1 c := by
    intro c
    unfold nzCount
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : symOfEntries c p.1 p.2 = 0 <;> simp [Set.indicator, hp]
  simp_rw [hf]
  refine Finset.measurable_sum _ fun p _ => ?_
  exact (measurable_one.indicator
    ((selProb_measurable_sym p.1 p.2) (measurableSet_singleton (0 : ℝ)).compl))

/-- The expected number of nonzero entries is at most `N α̃ + N² α`. -/
private lemma selProb_lintegral_nzCount {Lu Ld : Measure ℝ} [IsProbabilityMeasure Lu]
    [IsProbabilityMeasure Ld] (N : ℕ) :
    ∫⁻ c, (nzCount (symOfEntries c) : ENNReal) ∂(entryLaw Lu Ld N) ≤
      N * Ld {t | t ≠ 0} + N ^ 2 * Lu {t | t ≠ 0} := by
  classical
  have hf : ∀ c : Entries N, (nzCount (symOfEntries c) : ENNReal) =
      ∑ p : Fin N × Fin N, {c' : Entries N | symOfEntries c' p.1 p.2 ≠ 0}.indicator 1 c := by
    intro c
    unfold nzCount
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : symOfEntries c p.1 p.2 = 0 <;> simp [Set.indicator, hp]
  have hm : ∀ p : Fin N × Fin N, MeasurableSet {c' : Entries N | symOfEntries c' p.1 p.2 ≠ 0} :=
    fun p => (selProb_measurable_sym p.1 p.2) (measurableSet_singleton (0 : ℝ)).compl
  simp_rw [hf]
  rw [lintegral_finsetSum _ (fun p _ => measurable_one.indicator (hm p))]
  simp_rw [lintegral_indicator_one (hm _)]
  calc ∑ p : Fin N × Fin N, entryLaw Lu Ld N {c | symOfEntries c p.1 p.2 ≠ 0}
      ≤ ∑ p : Fin N × Fin N, ((if p.1 = p.2 then Ld {t | t ≠ 0} else 0) + Lu {t | t ≠ 0}) :=
        Finset.sum_le_sum fun p _ => (selProb_event_single p.1 p.2).trans
          (by split_ifs <;> simp)
    _ = N * Ld {t | t ≠ 0} + N ^ 2 * Lu {t | t ≠ 0} := by
        rw [Fintype.sum_prod_type]
        simp [Finset.sum_add_distrib, Finset.sum_ite_eq, pow_two, mul_assoc]

/-- First-moment bound: the number of nonzero entries exceeds `K` with probability at most
`(N α̃ + N² α) / K`. -/
private lemma selProb_count_bound {Lu Ld : Measure ℝ} [IsProbabilityMeasure Lu]
    [IsProbabilityMeasure Ld] (N : ℕ) {K : ℝ} (hK : 0 < K) :
    entryLaw Lu Ld N {c | K < (nzCount (symOfEntries c) : ℝ)} ≤
      (N * Ld {t | t ≠ 0} + N ^ 2 * Lu {t | t ≠ 0}) / ENNReal.ofReal K := by
  refine le_trans (measure_mono ?_) ((meas_ge_le_lintegral_div
    selProb_measurable_nzCount.aemeasurable (by simpa using hK) ENNReal.ofReal_ne_top).trans
    (ENNReal.div_le_div_right (selProb_lintegral_nzCount N) _))
  intro c hc
  simp only [Set.mem_ofPred_eq] at hc ⊢
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hc.le

/-! ### Overlapping nonzero entries -/

/-- A nonzero entry `(i, j)` and an index `s` of the pair `{i, j}` give a partner `x` with
`{i, j} = {s, x}` and the entry `(s, x)` nonzero. -/
private lemma selProb_pair_cases {N : ℕ} (c : Entries N) {i j s : Fin N}
    (h : symOfEntries c i j ≠ 0) (hs : s ∈ ({i, j} : Finset (Fin N))) :
    ∃ x, ({i, j} : Finset (Fin N)) = {s, x} ∧ symOfEntries c s x ≠ 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  · exact ⟨j, rfl, h⟩
  · exact ⟨i, Finset.pair_comm _ _, by rw [selProb_sym_comm]; exact h⟩

/-- If the support of `symOfEntries c` is not a pair pattern, two nonzero entries share an index
`s` with different partners, and either both partners differ from `s`, or one of them is `s`. -/
private lemma selProb_not_pairPattern {N : ℕ} (c : Entries N)
    (h : ¬ PairPattern (symOfEntries c)) :
    (∃ s x y : Fin N, s ≠ x ∧ s ≠ y ∧ x ≠ y ∧ symOfEntries c s x ≠ 0 ∧
        symOfEntries c s y ≠ 0) ∨
      (∃ s y : Fin N, s ≠ y ∧ symOfEntries c s s ≠ 0 ∧ symOfEntries c s y ≠ 0) := by
  unfold PairPattern at h
  push Not at h
  obtain ⟨i, j, k, l, h1, h2, h3, h4⟩ := h
  obtain ⟨s, hs1, hs2⟩ := Finset.not_disjoint_iff.mp h4
  obtain ⟨x, hx1, hx2⟩ := selProb_pair_cases c h1 hs1
  obtain ⟨y, hy1, hy2⟩ := selProb_pair_cases c h2 hs2
  have hxy : x ≠ y := by
    rintro rfl
    exact h3 (hx1.trans hy1.symm)
  by_cases hx : s = x
  · by_cases hy : s = y
    · exact absurd (hx.symm.trans hy) hxy
    · subst hx
      exact Or.inr ⟨s, y, hy, hx2, hy2⟩
  · by_cases hy : s = y
    · subst hy
      exact Or.inr ⟨s, x, hx, hy2, hx2⟩
    · exact Or.inl ⟨s, x, y, hx, hy, hxy, hx2, hy2⟩

/-- The pattern fails with probability at most `N³ α² + N² α̃ α`. -/
private lemma selProb_pair_bound {Lu Ld : Measure ℝ} [IsProbabilityMeasure Lu]
    [IsProbabilityMeasure Ld] (N : ℕ) :
    entryLaw Lu Ld N {c | ¬ PairPattern (symOfEntries c)} ≤
      N ^ 3 * (Lu {t | t ≠ 0} * Lu {t | t ≠ 0}) + N ^ 2 * (Ld {t | t ≠ 0} * Lu {t | t ≠ 0}) := by
  set E1 : Fin N × Fin N × Fin N → Set (Entries N) := fun t =>
    {c | t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ symOfEntries c t.1 t.2.1 ≠ 0 ∧
      symOfEntries c t.1 t.2.2 ≠ 0} with hE1
  set E2 : Fin N × Fin N → Set (Entries N) := fun t =>
    {c | t.1 ≠ t.2 ∧ symOfEntries c t.1 t.1 ≠ 0 ∧ symOfEntries c t.1 t.2 ≠ 0} with hE2
  have hsub : {c : Entries N | ¬ PairPattern (symOfEntries c)} ⊆ (⋃ t, E1 t) ∪ (⋃ t, E2 t) := by
    intro c hc
    rcases selProb_not_pairPattern c hc with ⟨s, x, y, h1, h2, h3, h4, h5⟩ | ⟨s, y, h1, h2, h3⟩
    · exact Or.inl (Set.mem_iUnion.mpr ⟨(s, x, y), h1, h2, h3, h4, h5⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨(s, y), h1, h2, h3⟩)
  have b1 : ∀ t, entryLaw Lu Ld N (E1 t) ≤ Lu {t | t ≠ 0} * Lu {t | t ≠ 0} := by
    intro t
    by_cases hP : t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2
    · refine le_trans (measure_mono (t := {c | symOfEntries c t.1 t.2.1 ≠ 0 ∧
          symOfEntries c t.1 t.2.2 ≠ 0}) ?_) (selProb_event_upper_upper hP.1 hP.2.1 hP.2.2)
      intro c hc
      exact ⟨hc.2.2.2.1, hc.2.2.2.2⟩
    · have : E1 t = ∅ := by
        ext c
        simp only [hE1, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hc => hP ⟨hc.1, hc.2.1, hc.2.2.1⟩
      rw [this, measure_empty]
      exact bot_le
  have b2 : ∀ t, entryLaw Lu Ld N (E2 t) ≤ Ld {t | t ≠ 0} * Lu {t | t ≠ 0} := by
    intro t
    by_cases hP : t.1 ≠ t.2
    · refine le_trans (measure_mono (t := {c | symOfEntries c t.1 t.1 ≠ 0 ∧
          symOfEntries c t.1 t.2 ≠ 0}) ?_) (selProb_event_diag_upper hP)
      intro c hc
      exact ⟨hc.2.1, hc.2.2⟩
    · have : E2 t = ∅ := by
        ext c
        simp only [hE2, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hc => hP hc.1
      rw [this, measure_empty]
      exact bot_le
  calc entryLaw Lu Ld N {c | ¬ PairPattern (symOfEntries c)}
      ≤ entryLaw Lu Ld N ((⋃ t, E1 t) ∪ (⋃ t, E2 t)) := measure_mono hsub
    _ ≤ entryLaw Lu Ld N (⋃ t, E1 t) + entryLaw Lu Ld N (⋃ t, E2 t) := measure_union_le _ _
    _ ≤ (∑ t, entryLaw Lu Ld N (E1 t)) + ∑ t, entryLaw Lu Ld N (E2 t) :=
        add_le_add (measure_iUnion_fintype_le _ _) (measure_iUnion_fintype_le _ _)
    _ ≤ (∑ _t : Fin N × Fin N × Fin N, Lu {t | t ≠ 0} * Lu {t | t ≠ 0}) +
          ∑ _t : Fin N × Fin N, Ld {t | t ≠ 0} * Lu {t | t ≠ 0} :=
        add_le_add (Finset.sum_le_sum fun t _ => b1 t) (Finset.sum_le_sum fun t _ => b2 t)
    _ = N ^ 3 * (Lu {t | t ≠ 0} * Lu {t | t ≠ 0}) + N ^ 2 * (Ld {t | t ≠ 0} * Lu {t | t ≠ 0}) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        ring

/-! ### The bound on the auxiliary space -/

/-- The selector is nonzero exactly beyond the cut-off. -/
private lemma selProb_map_largeInd_ne (ν : Measure ℝ) (T : ℝ) :
    (ν.map (largeInd T)) {t | t ≠ 0} = ν {x | T < |x|} := by
  have hm : MeasurableSet {t : ℝ | t ≠ 0} := (measurableSet_singleton (0 : ℝ)).compl
  rw [Measure.map_apply (measurable_largeInd T) hm]
  congr 1
  ext x
  by_cases h : T < |x| <;> simp [largeInd, h]

/-- (4.24)–(4.25) as a bound: with `α = ν{|x| > T}` and `α̃ = ν'{|x| > T}`, the selector is not
admissible with probability at most `(N α̃ + N² α) / N^{5ε} + N³ α² + N² α̃ α`. -/
private lemma selProb_le {ν ν' : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    {ε : ℝ} (N : ℕ) (hN : 1 ≤ N) :
    coupleLaw ν ν' ε N {u | ¬ SelGood ε u.2.2} ≤
      (N * ν' {x | (N : ℝ) ^ (1 / 2 - ε) < |x|} + N ^ 2 * ν {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}) /
          ENNReal.ofReal ((N : ℝ) ^ (5 * ε)) +
        (N ^ 3 * (ν {x | (N : ℝ) ^ (1 / 2 - ε) < |x|} * ν {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}) +
          N ^ 2 * (ν' {x | (N : ℝ) ^ (1 / 2 - ε) < |x|} *
            ν {x | (N : ℝ) ^ (1 / 2 - ε) < |x|})) := by
  have hK : 0 < (N : ℝ) ^ (5 * ε) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hN) _
  have h1 := selProb_coupleLaw_le (ν := ν) (ν' := ν') ε N {c | ¬ SelGood ε c}
  have h2 := selProb_count_bound (Lu := ν.map (largeInd ((N : ℝ) ^ (1 / 2 - ε))))
    (Ld := ν'.map (largeInd ((N : ℝ) ^ (1 / 2 - ε)))) N hK
  have h3 := selProb_pair_bound (Lu := ν.map (largeInd ((N : ℝ) ^ (1 / 2 - ε))))
    (Ld := ν'.map (largeInd ((N : ℝ) ^ (1 / 2 - ε)))) N
  rw [selProb_map_largeInd_ne, selProb_map_largeInd_ne] at h2 h3
  have hsub : {c : Entries N | ¬ SelGood ε c} ⊆
      {c | (N : ℝ) ^ (5 * ε) < (nzCount (symOfEntries c) : ℝ)} ∪
        {c | ¬ PairPattern (symOfEntries c)} := by
    intro c hc
    by_cases h : (nzCount (symOfEntries c) : ℝ) ≤ (N : ℝ) ^ (5 * ε)
    · exact Or.inr fun hp => hc ⟨h, hp⟩
    · exact Or.inl (not_le.mp h)
  calc coupleLaw ν ν' ε N {u | ¬ SelGood ε u.2.2}
      ≤ _ := h1
    _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add h2 h3

/-- Conversion of the bound to real numbers. -/
private lemma selProb_toReal_aux {a a' : ENNReal} (ha : a ≠ ⊤) (ha' : a' ≠ ⊤) {K : ℝ}
    (m : ℕ) (hK : 0 < K) :
    ((m * a' + m ^ 2 * a) / ENNReal.ofReal K + (m ^ 3 * (a * a) + m ^ 2 * (a' * a))).toReal =
      K⁻¹ * (m * a'.toReal + m ^ 2 * a.toReal) +
        (m ^ 3 * (a.toReal * a.toReal) + m ^ 2 * (a'.toReal * a.toReal)) := by
  have hm : (m : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top m
  have hm2 : (m : ENNReal) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hm
  have hm3 : (m : ENNReal) ^ 3 ≠ ⊤ := ENNReal.pow_ne_top hm
  have h1 : (m : ENNReal) * a' ≠ ⊤ := ENNReal.mul_ne_top hm ha'
  have h2 : (m : ENNReal) ^ 2 * a ≠ ⊤ := ENNReal.mul_ne_top hm2 ha
  have h3 : (m : ENNReal) ^ 3 * (a * a) ≠ ⊤ := ENNReal.mul_ne_top hm3 (ENNReal.mul_ne_top ha ha)
  have h4 : (m : ENNReal) ^ 2 * (a' * a) ≠ ⊤ :=
    ENNReal.mul_ne_top hm2 (ENNReal.mul_ne_top ha' ha)
  have hKe : ENNReal.ofReal K ≠ 0 := (ENNReal.ofReal_pos.mpr hK).ne'
  have h12 : (m : ENNReal) * a' + m ^ 2 * a ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨h1, h2⟩
  have hdiv : ((m : ENNReal) * a' + m ^ 2 * a) / ENNReal.ofReal K ≠ ⊤ :=
    ENNReal.div_ne_top h12 hKe
  have h34 : (m : ENNReal) ^ 3 * (a * a) + m ^ 2 * (a' * a) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨h3, h4⟩
  rw [ENNReal.toReal_add hdiv h34, ENNReal.toReal_div, ENNReal.toReal_add h1 h2,
    ENNReal.toReal_add h3 h4, ENNReal.toReal_ofReal hK.le]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  ring

/-- The bound of `selProb_le` in real numbers, with `α = ν{|x| > T}` and `α̃ = ν'{|x| > T}`. -/
private lemma selProb_toReal_le {ν ν' : Measure ℝ} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] {ε : ℝ} (N : ℕ) (hN : 1 ≤ N) :
    (coupleLaw ν ν' ε N {u | ¬ SelGood ε u.2.2}).toReal ≤
      ((N : ℝ) ^ (5 * ε))⁻¹ * (N * (ν' {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}).toReal +
          N ^ 2 * (ν {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}).toReal) +
        (N ^ 3 * ((ν {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}).toReal *
            (ν {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}).toReal) +
          N ^ 2 * ((ν' {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}).toReal *
            (ν {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}).toReal)) := by
  have hK : 0 < (N : ℝ) ^ (5 * ε) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hN) _
  have h := selProb_le (ν := ν) (ν' := ν') (ε := ε) N hN
  have hfin : ((N * ν' {x | (N : ℝ) ^ (1 / 2 - ε) < |x|} +
      N ^ 2 * ν {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}) / ENNReal.ofReal ((N : ℝ) ^ (5 * ε)) +
        (N ^ 3 * (ν {x | (N : ℝ) ^ (1 / 2 - ε) < |x|} * ν {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}) +
          N ^ 2 * (ν' {x | (N : ℝ) ^ (1 / 2 - ε) < |x|} *
            ν {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}))) ≠ ⊤ := by
    have ha := measure_ne_top ν {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}
    have ha' := measure_ne_top ν' {x | (N : ℝ) ^ (1 / 2 - ε) < |x|}
    have hm : (N : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top N
    have hKe : ENNReal.ofReal ((N : ℝ) ^ (5 * ε)) ≠ 0 := (ENNReal.ofReal_pos.mpr hK).ne'
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.div_ne_top (ENNReal.add_ne_top.mpr ⟨?_, ?_⟩) hKe,
      ENNReal.add_ne_top.mpr ⟨?_, ?_⟩⟩
    · exact ENNReal.mul_ne_top hm ha'
    · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top hm) ha
    · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top hm) (ENNReal.mul_ne_top ha ha)
    · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top hm) (ENNReal.mul_ne_top ha' ha)
  refine (ENNReal.toReal_mono hfin h).trans_eq ?_
  exact selProb_toReal_aux (measure_ne_top ν _) (measure_ne_top ν' _) _ hK

/-! ### The limit -/

/-- The exponent bookkeeping of the bound: each term is a power of `N` with a negative exponent
times products of `N^{2-4ε} α` and `N^{1-2ε} α̃`. -/
private lemma selProb_bound_eq {n α α' ε : ℝ} (hn : 0 < n) :
    (n ^ (5 * ε))⁻¹ * (n * α' + n ^ 2 * α) + (n ^ 3 * (α * α) + n ^ 2 * (α' * α)) =
      n ^ (-(3 * ε)) * (n ^ (1 - 2 * ε) * α') + n ^ (-ε) * (n ^ (2 - 4 * ε) * α) +
        n ^ (8 * ε - 1) * ((n ^ (2 - 4 * ε) * α) * (n ^ (2 - 4 * ε) * α)) +
        n ^ (6 * ε - 1) * ((n ^ (1 - 2 * ε) * α') * (n ^ (2 - 4 * ε) * α)) := by
  have e2 : n ^ 2 = n ^ (2 : ℝ) := (Real.rpow_two n).symm
  have e3 : n ^ 3 = n ^ (3 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
  have f1 : (n ^ (5 * ε))⁻¹ * n = n ^ (-(3 * ε)) * n ^ (1 - 2 * ε) := by
    rw [← Real.rpow_neg hn.le, ← Real.rpow_add_one hn.ne', ← Real.rpow_add hn]
    congr 1; ring
  have f2 : (n ^ (5 * ε))⁻¹ * n ^ 2 = n ^ (-ε) * n ^ (2 - 4 * ε) := by
    rw [e2, ← Real.rpow_neg hn.le, ← Real.rpow_add hn, ← Real.rpow_add hn]
    congr 1; ring
  have f3 : n ^ 3 = n ^ (8 * ε - 1) * (n ^ (2 - 4 * ε) * n ^ (2 - 4 * ε)) := by
    rw [e3, ← Real.rpow_add hn, ← Real.rpow_add hn]
    congr 1; ring
  have f4 : n ^ 2 = n ^ (6 * ε - 1) * (n ^ (1 - 2 * ε) * n ^ (2 - 4 * ε)) := by
    rw [e2, ← Real.rpow_add hn, ← Real.rpow_add hn]
    congr 1; ring
  linear_combination α' * f1 + α * f2 + (α * α) * f3 + (α' * α) * f4

/-- (4.24)–(4.25): `P(H̃^C ≠ H^C) → 0`. -/
theorem tendsto_coupleLaw_not_selGood {ν ν' : Measure ℝ} (hW : WignerLaws ν ν')
    (h14 : TailCond ν) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 8) :
    Tendsto (fun N : ℕ => (coupleLaw ν ν' ε N {u | ¬ SelGood ε u.2.2}).toReal) atTop (𝓝 0) := by
  have := hW.prob
  have := hW.prob'
  obtain ⟨hx, hy, -⟩ := cutoff_tail_bounds hW h14 hε0 (by linarith)
  have hpow : ∀ r : ℝ, r < 0 → Tendsto (fun N : ℕ => (N : ℝ) ^ r) atTop (𝓝 0) := fun r hr => by
    have := (tendsto_rpow_neg_atTop (y := -r) (by linarith)).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using this
  have t1 := hpow (-(3 * ε)) (by linarith)
  have t2 := hpow (-ε) (by linarith)
  have t3 := hpow (8 * ε - 1) (by linarith)
  have t4 := hpow (6 * ε - 1) (by linarith)
  have hlim := (((t1.mul hy).add (t2.mul hx)).add (t3.mul (hx.mul hx))).add (t4.mul (hy.mul hx))
  simp only [mul_zero, add_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun N => ENNReal.toReal_nonneg)
    ((eventually_ge_atTop 1).mono fun N hN => ?_) hlim
  rw [← selProb_bound_eq (by exact_mod_cast hN : (0 : ℝ) < N)]
  exact selProb_toReal_le N hN

/-! ### A nondegenerate instance: Rademacher off-diagonal entries, `N(0, 2)` diagonal entries,
`ε = 1/100` -/

/-- The hypotheses hold at Rademacher off-diagonal entries and `N(0, 2)` diagonal entries with
`ε = 1/100`; there the off-diagonal selector vanishes and the diagonal selector does not. -/
example : Tendsto (fun N : ℕ => (coupleLaw rademacher (gaussianReal 0 2) (1 / 100) N
    {u | ¬ SelGood (1 / 100) u.2.2}).toReal) atTop (𝓝 0) :=
  tendsto_coupleLaw_not_selGood rademacher_wignerLaws rademacher_tailCond (by norm_num)
    (by norm_num)

#print axioms tendsto_coupleLaw_not_selGood

end WEdgeNS
