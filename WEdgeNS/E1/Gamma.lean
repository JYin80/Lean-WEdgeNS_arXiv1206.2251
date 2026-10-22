import WEdgeNS.Model.LambdaMax

/-!
# The events of the necessity proof

The event `Γ'_N` of (4.5) that some off-diagonal entry is large, the event `Γ_N` of (4.2) that in
addition the two corresponding diagonal entries are small, their probabilities (4.6)–(4.8), and the
inclusion `Γ_N ⊆ {λ_N ≥ 3}` of (4.4).
-/

open MeasureTheory ProbabilityTheory

namespace WEdgeNS

/-- The event `Γ'_N` of (4.5): some `|x_ij| ≥ 4 √N` with `i < j`. -/
def bigEntryEvent (N : ℕ) : Set (Entries N) :=
  {ω | ∃ p : OffDiag N, 4 * Real.sqrt N ≤ |ω.2 p|}

/-- The event `Γ_N` of (4.2): some `|x_ij| ≥ 4 √N` with `|x_ii| ≤ √N` and `|x_jj| ≤ √N`. -/
def gammaEvent (N : ℕ) : Set (Entries N) :=
  {ω | ∃ p : OffDiag N, 4 * Real.sqrt N ≤ |ω.2 p| ∧ |ω.1 p.1.1| ≤ Real.sqrt N ∧
    |ω.1 p.1.2| ≤ Real.sqrt N}

/-- There are `N.choose 2` index pairs `i < j`. -/
private lemma card_offDiag (N : ℕ) : Fintype.card (OffDiag N) = N.choose 2 := by
  rw [Fintype.card_subtype, Fintype.card_product_filter_lt, Fintype.card_fin]

/-- The diagonal entries of `H_N`. -/
private lemma wignerMatrix_diag (N : ℕ) (ω : Entries N) (i : Fin N) :
    wignerMatrix N ω i i = (Real.sqrt N)⁻¹ * ω.1 i := by
  simp [wignerMatrix]

/-- The entry `H_ij` of `H_N` for `i < j`. -/
private lemma wignerMatrix_offDiag (N : ℕ) (ω : Entries N) (p : OffDiag N) :
    wignerMatrix N ω p.1.1 p.1.2 = (Real.sqrt N)⁻¹ * ω.2 p := by
  simp [wignerMatrix, p.2.ne, p.2]

/-- The modulus of an entry of `H_N` in terms of the modulus of `x_ij`. -/
private lemma abs_inv_sqrt_mul (N : ℕ) (x : ℝ) : |(Real.sqrt N)⁻¹ * x| = |x| / Real.sqrt N := by
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), inv_mul_eq_div]

/-- (4.4): on `Γ_N`, `λ_N ≥ 3`. -/
theorem gammaEvent_subset (N : ℕ) :
    gammaEvent N ⊆ {ω | 3 ≤ lambdaMax (wignerMatrix N ω)} := by
  rintro ω ⟨p, h1, h2, h3⟩
  have hN : 0 < Real.sqrt N :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Fin.pos p.1.1))
  refine three_le_lambdaMax (wignerMatrix_isHermitian N ω) p.2.ne ?_ ?_ ?_
  · rw [wignerMatrix_offDiag, abs_inv_sqrt_mul, le_div_iff₀ hN]
    linarith
  · rw [wignerMatrix_diag, abs_inv_sqrt_mul, div_le_iff₀ hN]
    linarith
  · rw [wignerMatrix_diag, abs_inv_sqrt_mul, div_le_iff₀ hN]
    linarith

/-- The set where one coordinate has modulus at least `a` is measurable. -/
private lemma measurableSet_abs_ge {ι : Type*} (p : ι) (a : ℝ) :
    MeasurableSet {y : ι → ℝ | a ≤ |y p|} :=
  measurableSet_le measurable_const (measurable_pi_apply p).abs

/-- The event `Γ'_N` is measurable. -/
private lemma measurableSet_bigEntryEvent (N : ℕ) : MeasurableSet (bigEntryEvent N) := by
  have : bigEntryEvent N =
      ⋃ p : OffDiag N, Set.univ ×ˢ {y : OffDiag N → ℝ | 4 * Real.sqrt N ≤ |y p|} := by
    ext ω
    simp [bigEntryEvent]
  rw [this]
  exact MeasurableSet.iUnion fun p => MeasurableSet.univ.prod (measurableSet_abs_ge p _)

/-- (4.6): `P(Γ'_N) = 1 - (1 - P(|x_12| ≥ 4 √N))^{N(N-1)/2}`. -/
theorem entryLaw_bigEntryEvent {ν ν' : Measure ℝ} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] (N : ℕ) :
    (entryLaw ν ν' N (bigEntryEvent N)).toReal =
      1 - (1 - (ν {x | 4 * Real.sqrt N ≤ |x|}).toReal) ^ N.choose 2 := by
  set a := 4 * Real.sqrt N with ha
  have hc : (bigEntryEvent N)ᶜ =
      Set.univ ×ˢ Set.univ.pi (fun _ : OffDiag N => {x : ℝ | |x| < a}) := by
    ext ω
    simp [bigEntryEvent, Set.mem_pi, not_exists, not_le, ha]
  have h1 : (entryLaw ν ν' N).real (bigEntryEvent N)ᶜ = (ν.real {x | |x| < a}) ^ N.choose 2 := by
    simp only [Measure.real]
    rw [hc]
    unfold entryLaw
    rw [Measure.prod_prod, Measure.pi_pi]
    simp [card_offDiag, ENNReal.toReal_pow]
  have hm : MeasurableSet {x : ℝ | a ≤ |x|} :=
    measurableSet_le measurable_const measurable_id.abs
  have h2 : ν.real {x | |x| < a} = 1 - ν.real {x | a ≤ |x|} := by
    have : {x : ℝ | |x| < a} = {x | a ≤ |x|}ᶜ := by ext; simp
    rw [this, probReal_compl_eq_one_sub hm]
  have h3 := probReal_compl_eq_one_sub (μ := entryLaw ν ν' N) (measurableSet_bigEntryEvent N)
  rw [h1, h2] at h3
  change (entryLaw ν ν' N).real (bigEntryEvent N) = 1 - (1 - ν.real {x | a ≤ |x|}) ^ N.choose 2
  linarith

/-- (4.7): by Markov's inequality, `P(|x_11| > √N) ≤ 1/2` once `N ≥ 2 E x_11^2`. -/
theorem diag_tail_le_half {ν' : Measure ℝ} [IsProbabilityMeasure ν']
    (hint : Integrable (fun x : ℝ => x ^ 2) ν') {N : ℕ} (hN0 : 0 < N)
    (hN : 2 * ∫ x, x ^ 2 ∂ν' ≤ N) : (ν' {x | Real.sqrt N < |x|}).toReal ≤ 1 / 2 := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN0
  have hsub : {x : ℝ | Real.sqrt N < |x|} ⊆ {x | (N : ℝ) ≤ x ^ 2} := by
    intro x hx
    have h1 : (Real.sqrt N) ^ 2 < |x| ^ 2 := pow_lt_pow_left₀ hx (Real.sqrt_nonneg _) two_ne_zero
    rw [Real.sq_sqrt hNpos.le, sq_abs] at h1
    exact h1.le
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := ν') (f := fun x : ℝ => x ^ 2)
    (Filter.Eventually.of_forall fun x => sq_nonneg x) hint (N : ℝ)
  have hmono : ν'.real {x | Real.sqrt N < |x|} ≤ ν'.real {x | (N : ℝ) ≤ x ^ 2} :=
    measureReal_mono hsub
  change ν'.real {x | Real.sqrt N < |x|} ≤ 1 / 2
  have h2 : (N : ℝ) * ν'.real {x | Real.sqrt N < |x|} ≤ N * (1 / 2) := by
    calc (N : ℝ) * ν'.real {x | Real.sqrt N < |x|} ≤ N * ν'.real {x | (N : ℝ) ≤ x ^ 2} := by
          gcongr
      _ ≤ ∫ x, x ^ 2 ∂ν' := hmark
      _ ≤ N * (1 / 2) := by linarith
  exact le_of_mul_le_mul_left h2 hNpos

/-- The vectors `y` for which `p` is the first coordinate, in the order of `key`, with
`a ≤ |y p|`. -/
private def firstLarge {ι : Type*} (a : ℝ) (key : ι → ℕ) (p : ι) : Set (ι → ℝ) :=
  {y | a ≤ |y p| ∧ ∀ q, key q < key p → |y q| < a}

/-- The sets `firstLarge a key p` are measurable. -/
private lemma measurableSet_firstLarge {ι : Type*} [Finite ι] (a : ℝ) (key : ι → ℕ) (p : ι) :
    MeasurableSet (firstLarge a key p) := by
  have : firstLarge a key p =
      {y : ι → ℝ | a ≤ |y p|} ∩ ⋂ q ∈ {q | key q < key p}, {y : ι → ℝ | |y q| < a} := by
    ext y
    simp [firstLarge]
  rw [this]
  refine (measurableSet_abs_ge p a).inter (MeasurableSet.biInter (Set.to_countable _) fun q _ => ?_)
  exact measurableSet_lt (measurable_pi_apply q).abs measurable_const

/-- The sets `firstLarge a key p` are pairwise disjoint when `key` is injective. -/
private lemma pairwise_disjoint_firstLarge {ι : Type*} (a : ℝ) {key : ι → ℕ}
    (hkey : Function.Injective key) : Pairwise (Function.onFun Disjoint (firstLarge a key)) := by
  intro p p' hpp'
  have hne : key p ≠ key p' := fun h => hpp' (hkey h)
  rw [Function.onFun, Set.disjoint_left]
  rintro y ⟨hp1, hp2⟩ ⟨hq1, hq2⟩
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd (hq2 p h) (not_lt.mpr hp1)
  · exact absurd (hp2 p' h) (not_lt.mpr hq1)

/-- The sets `firstLarge a key p` cover the vectors with some coordinate of modulus at least
`a`. -/
private lemma iUnion_firstLarge {ι : Type*} [Finite ι] (a : ℝ) (key : ι → ℕ) :
    ⋃ p, firstLarge a key p = {y | ∃ p, a ≤ |y p|} := by
  ext y
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨p, hp, -⟩
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    have := Fintype.ofFinite ι
    classical
    obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun r => a ≤ |y r|) key
      ⟨p, by simpa using hp⟩
    refine ⟨q, (Finset.mem_filter.mp hq).2, fun r hr => ?_⟩
    by_contra hcon
    exact absurd (hmin r (by simpa using not_lt.mp hcon)) (not_le.mpr hr)

/-- The probability that two prescribed diagonal coordinates are both of modulus at most `b`
under a product law with marginal `ν'` is the square of the one-coordinate probability. -/
private lemma pi_two_coords {n : ℕ} (ν' : Measure ℝ) [IsProbabilityMeasure ν'] (b : ℝ)
    {i j : Fin n} (hij : i ≠ j) :
    Measure.pi (fun _ : Fin n => ν') {x : Fin n → ℝ | |x i| ≤ b ∧ |x j| ≤ b} =
      ν' {x | |x| ≤ b} * ν' {x | |x| ≤ b} := by
  classical
  set S : Set ℝ := {x | |x| ≤ b}
  have hset : {x : Fin n → ℝ | |x i| ≤ b ∧ |x j| ≤ b} =
      Set.univ.pi (fun k : Fin n => if k = i ∨ k = j then S else Set.univ) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨h1, h2⟩ k
      split_ifs with hk
      · rcases hk with rfl | rfl <;> assumption
      · trivial
    · intro h
      have h1 := h i
      have h2 := h j
      simp only [true_or, or_true, ite_true] at h1 h2
      exact ⟨h1, h2⟩
  rw [hset, Measure.pi_pi]
  rw [Finset.prod_eq_mul_of_mem i j (Finset.mem_univ _) (Finset.mem_univ _) hij]
  · simp [hij]
  · rintro c - ⟨hci, hcj⟩
    simp [hci, hcj]

/-- (4.8): `P(Γ_N) ≥ P(Γ'_N) / 4`, conditioning on the first large off-diagonal entry. -/
theorem entryLaw_gammaEvent_ge {ν ν' : Measure ℝ} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] {N : ℕ} (hdiag : (ν' {x | Real.sqrt N < |x|}).toReal ≤ 1 / 2) :
    (entryLaw ν ν' N (bigEntryEvent N)).toReal / 4 ≤ (entryLaw ν ν' N (gammaEvent N)).toReal := by
  set b := Real.sqrt N with hb
  set a := 4 * b with ha
  let key : OffDiag N → ℕ := fun p => (Fintype.equivFin (OffDiag N) p : ℕ)
  have hkey : Function.Injective key :=
    Fin.val_injective.comp (Fintype.equivFin (OffDiag N)).injective
  set A : OffDiag N → Set (OffDiag N → ℝ) := firstLarge a key with hA
  set D : OffDiag N → Set (Fin N → ℝ) := fun p => {x | |x p.1.1| ≤ b ∧ |x p.1.2| ≤ b} with hD
  have hDmeas : ∀ p, MeasurableSet (D p) := fun p =>
    (measurableSet_le (measurable_pi_apply _).abs measurable_const).inter
      (measurableSet_le (measurable_pi_apply _).abs measurable_const)
  have hDge : ∀ p, (4 : ENNReal)⁻¹ ≤ Measure.pi (fun _ : Fin N => ν') (D p) := by
    intro p
    rw [hD, pi_two_coords ν' b p.2.ne]
    have h1 : ν' {x : ℝ | b < |x|} ≤ 2⁻¹ := by
      have hfin : ν' {x : ℝ | b < |x|} ≠ ⊤ := measure_ne_top _ _
      have : (ν' {x : ℝ | b < |x|}).toReal ≤ (2⁻¹ : ENNReal).toReal := by
        simpa using hdiag
      exact (ENNReal.toReal_le_toReal hfin (by simp)).mp this
    have h2 : (2 : ENNReal)⁻¹ ≤ ν' {x : ℝ | |x| ≤ b} := by
      have : {x : ℝ | |x| ≤ b} = {x | b < |x|}ᶜ := by ext; simp
      have hT : MeasurableSet {x : ℝ | b < |x|} :=
        measurableSet_lt measurable_const measurable_id.abs
      rw [this, prob_compl_eq_one_sub hT]
      calc (2 : ENNReal)⁻¹ = 1 - 2⁻¹ := ENNReal.one_sub_inv_two.symm
        _ ≤ 1 - ν' {x : ℝ | b < |x|} := tsub_le_tsub_left h1 _
    calc (4 : ENNReal)⁻¹ = 2⁻¹ * 2⁻¹ := by
          rw [← ENNReal.mul_inv (by simp) (by simp)]; norm_num
      _ ≤ _ := mul_le_mul' h2 h2
  have hBeq : bigEntryEvent N = Set.univ ×ˢ ⋃ p, A p := by
    rw [hA, iUnion_firstLarge]
    ext ω
    simp [bigEntryEvent, ha, hb]
  have hAmeas : ∀ p, MeasurableSet (A p) := fun p => measurableSet_firstLarge a key p
  have hAdisj : Pairwise (Function.onFun Disjoint A) := pairwise_disjoint_firstLarge a hkey
  have h1 : entryLaw ν ν' N (bigEntryEvent N) =
      ∑' p, Measure.pi (fun _ : OffDiag N => ν) (A p) := by
    rw [hBeq]
    unfold entryLaw
    rw [Measure.prod_prod, measure_univ, one_mul, measure_iUnion hAdisj hAmeas]
  have hsub : (⋃ p, D p ×ˢ A p) ⊆ gammaEvent N := by
    intro ω hω
    obtain ⟨p, hp1, hp2⟩ := Set.mem_iUnion.mp hω
    exact ⟨p, hp2.1, hp1.1, hp1.2⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun p => D p ×ˢ A p) := by
    intro p p' hpp'
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨-, h1⟩ ⟨-, h2⟩
    exact Set.disjoint_left.mp (hAdisj hpp') h1 h2
  have hmeas : ∀ p, MeasurableSet (D p ×ˢ A p) := fun p => (hDmeas p).prod (hAmeas p)
  have h2 : entryLaw ν ν' N (⋃ p, D p ×ˢ A p) =
      ∑' p, Measure.pi (fun _ : Fin N => ν') (D p) * Measure.pi (fun _ : OffDiag N => ν) (A p) := by
    unfold entryLaw
    rw [measure_iUnion hdisj hmeas]
    exact tsum_congr fun p => Measure.prod_prod _ _
  have h3 : (4 : ENNReal)⁻¹ * entryLaw ν ν' N (bigEntryEvent N) ≤
      entryLaw ν ν' N (gammaEvent N) := by
    calc (4 : ENNReal)⁻¹ * entryLaw ν ν' N (bigEntryEvent N)
        = ∑' p, (4 : ENNReal)⁻¹ * Measure.pi (fun _ : OffDiag N => ν) (A p) := by
          rw [h1, ENNReal.tsum_mul_left]
      _ ≤ ∑' p, Measure.pi (fun _ : Fin N => ν') (D p) *
            Measure.pi (fun _ : OffDiag N => ν) (A p) :=
          ENNReal.tsum_le_tsum fun p => mul_le_mul' (hDge p) le_rfl
      _ = entryLaw ν ν' N (⋃ p, D p ×ˢ A p) := h2.symm
      _ ≤ entryLaw ν ν' N (gammaEvent N) := measure_mono hsub
  have h4 := ENNReal.toReal_mono (measure_ne_top _ _) h3
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv] at h4
  simp at h4
  linarith

/-- The event `Γ_N` is measurable. -/
private lemma measurableSet_gammaEvent (N : ℕ) : MeasurableSet (gammaEvent N) := by
  have : gammaEvent N = ⋃ p : OffDiag N,
      {x : Fin N → ℝ | |x p.1.1| ≤ Real.sqrt N ∧ |x p.1.2| ≤ Real.sqrt N} ×ˢ
        {y : OffDiag N → ℝ | 4 * Real.sqrt N ≤ |y p|} := by
    ext ω
    simp only [gammaEvent, Set.mem_iUnion, Set.mem_prod, Set.mem_ofPred_eq]
    tauto
  rw [this]
  refine MeasurableSet.iUnion fun p => MeasurableSet.prod ?_ (measurableSet_abs_ge p _)
  exact (measurableSet_le (measurable_pi_apply _).abs measurable_const).inter
    (measurableSet_le (measurable_pi_apply _).abs measurable_const)

/-- The second moment of `N(0, 2)` is `2`. -/
private lemma integral_sq_gaussianReal_two : ∫ x, x ^ 2 ∂(gaussianReal 0 2) = 2 := by
  have h := variance_eq_integral (X := id) (μ := gaussianReal 0 2) aemeasurable_id
  rw [variance_id_gaussianReal] at h
  simpa [integral_id_gaussianReal] using h.symm

/-- The events `Γ'_2` and `Γ_2` are measurable, `Γ_2` contains the vector with all off-diagonal
entries `6 ≥ 4 √2` and zero diagonal, and `Γ'_2` misses the zero vector. -/
example : MeasurableSet (bigEntryEvent 2) ∧ MeasurableSet (gammaEvent 2) ∧
    (gammaEvent 2).Nonempty ∧ (bigEntryEvent 2)ᶜ.Nonempty := by
  have hs : Real.sqrt ((2 : ℕ) : ℝ) ≤ 3 / 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hpos : 0 < Real.sqrt ((2 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨measurableSet_bigEntryEvent 2, measurableSet_gammaEvent 2, ?_, ?_⟩
  · refine ⟨(0, fun _ => 6), ⟨(0, 1), by decide⟩, ?_, ?_, ?_⟩
    · change 4 * Real.sqrt ((2 : ℕ) : ℝ) ≤ |(6 : ℝ)|
      rw [abs_of_pos (by norm_num)]
      generalize Real.sqrt ((2 : ℕ) : ℝ) = s at hs ⊢
      linarith
    · simp
    · simp
  · refine ⟨(0, 0), ?_⟩
    rintro ⟨p, hp⟩
    have h0 : |((0 : Fin 2 → ℝ), (0 : OffDiag 2 → ℝ)).2 p| = 0 := by simp
    rw [h0] at hp
    generalize Real.sqrt ((2 : ℕ) : ℝ) = s at hpos hp
    linarith

/-- (4.7) at `ν' = N(0, 2)`, `N = 4`: `2 E x_11^2 = 4 ≤ N`. -/
example : (gaussianReal 0 2 {x : ℝ | Real.sqrt ((4 : ℕ) : ℝ) < |x|}).toReal ≤ 1 / 2 :=
  diag_tail_le_half (N := 4) goe_wignerLaws.sq_int' (by norm_num)
    (by rw [integral_sq_gaussianReal_two]; norm_num)

/-- (4.8) at `ν = N(0, 1)`, `ν' = N(0, 2)`, `N = 4`. -/
example : (entryLaw (gaussianReal 0 1) (gaussianReal 0 2) 4 (bigEntryEvent 4)).toReal / 4 ≤
    (entryLaw (gaussianReal 0 1) (gaussianReal 0 2) 4 (gammaEvent 4)).toReal :=
  entryLaw_gammaEvent_ge (N := 4)
    (diag_tail_le_half (N := 4) goe_wignerLaws.sq_int' (by norm_num)
      (by rw [integral_sq_gaussianReal_two]; norm_num))

#print axioms gammaEvent_subset
#print axioms entryLaw_bigEntryEvent
#print axioms diag_tail_le_half
#print axioms entryLaw_gammaEvent_ge

end WEdgeNS
