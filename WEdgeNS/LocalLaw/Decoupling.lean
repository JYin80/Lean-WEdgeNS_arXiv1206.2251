import WEdgeNS.Probability.ProductSpace

/-!
# The abstract decoupling lemma

Theorem 5.6 of [15] (§5.1), with its proof (5.13)–(5.31): the high-moment expansion of
`|[Z]|^p` through the graded terms (5.1)–(5.2), Hölder's inequality in the case `n ≥ 2s`, the
vanishing of partial expectations (5.5) together with the saturations `[Ξ]_i` of (5.8) in the
case `n ≤ 2s − 1`, and Markov's inequality.
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-! ### Conjugation patterns -/

/-- The identity (`false`) or complex conjugation (`true`). -/
private def cf (b : Bool) : ℂ →+* ℂ := if b then starRingEnd ℂ else RingHom.id ℂ

private lemma norm_cf (b : Bool) (z : ℂ) : ‖cf b z‖ = ‖z‖ := by
  cases b <;> simp [cf]

private lemma enorm_cf (b : Bool) (z : ℂ) : ‖cf b z‖ₑ = ‖z‖ₑ := by
  cases b <;> simp [cf]

private lemma continuous_cf (b : Bool) : Continuous (cf b) := by
  cases b
  · exact continuous_id
  · exact Complex.continuous_conj

private lemma cf_natCast_inv (b : Bool) (N : ℕ) : cf b ((N : ℂ)⁻¹) = (N : ℂ)⁻¹ := by
  cases b <;> simp [cf]

private lemma integral_cf {α : Type*} [MeasurableSpace α] {μ : Measure α} (b : Bool)
    (f : α → ℂ) : ∫ x, cf b (f x) ∂μ = cf b (∫ x, f x ∂μ) := by
  cases b
  · simp [cf]
  · simpa [cf] using integral_conj (μ := μ) (f := f)

/-! ### Graded terms -/

private lemma gradedTerm_apply {N : ℕ} (A : Finset (Fin N) → Entries N → ℂ)
    (S U : Finset (Fin N)) (ω : Entries N) :
    gradedTerm A S U ω = ∑ T ∈ U.powerset, (-1 : ℂ) ^ T.card * A ((S \ U) ∪ T) ω := by
  simp [gradedTerm, Finset.sum_apply, zsmul_eq_mul]

private lemma subset_of_mem_powerset_sdiff {N : ℕ} {S U T : Finset (Fin N)} (hU : U ⊆ S)
    (hT : T ∈ U.powerset) : (S \ U) ∪ T ⊆ S :=
  Finset.union_subset Finset.sdiff_subset ((Finset.mem_powerset.mp hT).trans hU)

private lemma integrable_gradedTerm {N : ℕ} {μ : Measure (Entries N)}
    {A : Finset (Fin N) → Entries N → ℂ} {S U : Finset (Fin N)}
    (hA : ∀ V ⊆ S, Integrable (A V) μ) (hU : U ⊆ S) : Integrable (gradedTerm A S U) μ := by
  have h : gradedTerm A S U = fun ω => ∑ T ∈ U.powerset, (-1 : ℂ) ^ T.card * A ((S \ U) ∪ T) ω :=
    funext (gradedTerm_apply A S U)
  rw [h]
  exact integrable_finsetSum _ fun T hT =>
    (hA _ (subset_of_mem_powerset_sdiff hU hT)).const_mul _

private lemma norm_gradedTerm_le {N : ℕ} {A : Finset (Fin N) → Entries N → ℂ}
    {S U : Finset (Fin N)} {ω : Entries N} {B : ℝ} (hA : ∀ V ⊆ S, ‖A V ω‖ ≤ B) (hU : U ⊆ S) :
    ‖gradedTerm A S U ω‖ ≤ 2 ^ U.card * B := by
  rw [gradedTerm_apply]
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ T ∈ U.powerset, ‖(-1 : ℂ) ^ T.card * A ((S \ U) ∪ T) ω‖ ≤ B := fun T hT => by
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact hA _ (subset_of_mem_powerset_sdiff hU hT)
  refine (Finset.sum_le_sum h).trans ?_
  rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
  push_cast
  rfl

private lemma rowIndep_gradedTerm_singleton {N : ℕ} {Z : Finset (Fin N) → Fin N → Entries N → ℂ}
    {i k : Fin N} {S U : Finset (Fin N)} (hZ : ∀ V, i ∉ V → RowIndep V (Z V i)) (hi : i ∉ S)
    (hU : U ⊆ S) (hk : k ∈ S) (hkU : k ∉ U) :
    RowIndep {k} (gradedTerm (fun V => Z V i) S U) := by
  intro ω
  rw [gradedTerm_apply, gradedTerm_apply]
  refine Finset.sum_congr rfl fun T hT => ?_
  congr 1
  have hV := subset_of_mem_powerset_sdiff hU hT
  have hkV : k ∈ (S \ U) ∪ T := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hk, hkU⟩)
  have hiV : i ∉ (S \ U) ∪ T := fun h => hi (hV h)
  have h1 := hZ _ hiV (zeroEntries {k} ω)
  have h2 := hZ _ hiV ω
  rw [zeroEntries_zeroEntries, Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr hkV)]
    at h1
  change Z ((S \ U) ∪ T) i (zeroEntries {k} ω) = Z ((S \ U) ∪ T) i ω
  rw [← h1, h2]

/-! ### Vanishing of partial expectations -/

/-- If `H` is independent of the row `k` and bounded, then `E(H · Z_k^{[V]}) = 0` for every
`V ∌ k`, by (5.5); hence `E(H · Z_k^{S,U}) = 0` for `k ∉ S` (the first equality in (5.23)). -/
private lemma integral_mul_gradedTerm_eq_zero {N : ℕ} {L : EntryLaws N} (hL : L.IsProb)
    {Z : Finset (Fin N) → Fin N → Entries N → ℂ} {k : Fin N}
    (hint : ∀ V, k ∉ V → Integrable (Z V k) L.law)
    (hE : ∀ V, k ∉ V → ∀ᵐ ω ∂L.law, L.rowsExp {k} (Z V k) ω = 0)
    {S U : Finset (Fin N)} (hk : k ∉ S) (hU : U ⊆ S) {H : Entries N → ℂ} (hH : RowIndep {k} H)
    (hHm : AEStronglyMeasurable H L.law) {B : ℝ} (hB : ∀ ω, ‖H ω‖ ≤ B) (b : Bool) :
    ∫ ω, H ω * cf b (gradedTerm (fun V => Z V k) S U ω) ∂L.law = 0 := by
  have hone : ∀ V, k ∉ V → ∫ ω, H ω * cf b (Z V k ω) ∂L.law = 0 := by
    intro V hV
    have hcf : Integrable (fun ω => cf b (Z V k ω)) L.law :=
      (hint V hV).mono ((continuous_cf b).comp_aestronglyMeasurable
        (hint V hV).aestronglyMeasurable) (ae_of_all _ fun ω => (norm_cf b _).le)
    have hprod : Integrable (H * fun ω => cf b (Z V k ω)) L.law :=
      hcf.bdd_mul hHm (ae_of_all _ hB)
    have h1 := EntryLaws.integral_rowsExp hL {k} hprod
    rw [EntryLaws.rowsExp_mul_of_rowIndep L hH] at h1
    have h2 : L.rowsExp {k} (fun ω => cf b (Z V k ω)) =
        fun ω => cf b (L.rowsExp {k} (Z V k) ω) := by
      funext ω
      simp only [EntryLaws.rowsExp]
      exact integral_cf b _
    rw [h2] at h1
    change ∫ ω, (H * fun ω => cf b (Z V k ω)) ω ∂L.law = 0
    rw [← h1]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hE V hV] with ω hω
    simp [hω]
  have hsum : (fun ω => H ω * cf b (gradedTerm (fun V => Z V k) S U ω)) = fun ω =>
      ∑ T ∈ U.powerset, cf b ((-1 : ℂ) ^ T.card) * (H ω * cf b (Z ((S \ U) ∪ T) k ω)) := by
    funext ω
    rw [gradedTerm_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [map_mul]
    ring
  have hkV : ∀ T ∈ U.powerset, k ∉ (S \ U) ∪ T := fun T hT h =>
    hk (subset_of_mem_powerset_sdiff hU hT h)
  rw [hsum, integral_finsetSum]
  · refine Finset.sum_eq_zero fun T hT => ?_
    rw [integral_const_mul, hone _ (hkV T hT), mul_zero]
  · intro T hT
    have hcf : Integrable (fun ω => cf b (Z ((S \ U) ∪ T) k ω)) L.law :=
      (hint _ (hkV T hT)).mono ((continuous_cf b).comp_aestronglyMeasurable
        (hint _ (hkV T hT)).aestronglyMeasurable) (ae_of_all _ fun ω => (norm_cf b _).le)
    exact (hcf.bdd_mul hHm (ae_of_all _ hB)).const_mul _

/-! ### Hölder and Schwarz bounds -/

private lemma enorm_prod_cf {ι : Type*} [Fintype ι] (b : ι → Bool) (g : ι → ℂ) :
    ‖∏ j, cf (b j) (g j)‖ₑ = ∏ j, ‖g j‖ₑ := by
  rw [← ofReal_norm, norm_prod, ENNReal.ofReal_prod_of_nonneg fun j _ => norm_nonneg _]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [norm_cf, ofReal_norm]

/-- Hölder's inequality with `p` factors in `L^p(1(Ξ) dP)`, (5.20)–(5.21). -/
private lemma norm_setIntegral_prod_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ι : Type*} [Fintype ι] {p : ℕ} (hp : Fintype.card ι = p) (hp0 : p ≠ 0) (Ξ : Set α)
    (b : ι → Bool) {G : ι → α → ℂ} (hG : ∀ j, AEStronglyMeasurable (G j) μ) {a : ι → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hbd : ∀ j, ∫⁻ ω in Ξ, ‖G j ω‖ₑ ^ p ∂μ ≤ ENNReal.ofReal (a j ^ p)) :
    ‖∫ ω in Ξ, ∏ j, cf (b j) (G j ω) ∂μ‖ ≤ ∏ j, a j := by
  have h1 := enorm_integral_le_lintegral_enorm (μ := μ.restrict Ξ)
    (fun ω => ∏ j, cf (b j) (G j ω))
  simp only [enorm_prod_cf] at h1
  have h2 : (fun ω => ∏ j, ‖G j ω‖ₑ) = fun ω => ∏ j ∈ Finset.univ,
      (fun j ω => ‖G j ω‖ₑ ^ p) j ω ^ (fun _ => ((p : ℝ))⁻¹) j := by
    funext ω
    refine Finset.prod_congr rfl fun j _ => ?_
    exact (ENNReal.pow_rpow_inv_natCast hp0 _).symm
  have h3 := ENNReal.lintegral_prod_norm_pow_le (μ := μ.restrict Ξ) Finset.univ
    (f := fun j ω => ‖G j ω‖ₑ ^ p) (fun j _ => ((hG j).restrict.enorm.pow_const p))
    (p := fun _ => ((p : ℝ))⁻¹) (by
      rw [Finset.sum_const, Finset.card_univ, hp, nsmul_eq_mul]
      field_simp)
    (fun _ _ => by positivity)
  rw [← h2] at h3
  have h4 : ∏ j ∈ Finset.univ, (∫⁻ ω in Ξ, ‖G j ω‖ₑ ^ p ∂μ) ^ ((p : ℝ))⁻¹ ≤
      ∏ j, ENNReal.ofReal (a j) := by
    refine Finset.prod_le_prod fun j _ => ?_
    calc (∫⁻ ω in Ξ, ‖G j ω‖ₑ ^ p ∂μ) ^ ((p : ℝ))⁻¹ ≤ (ENNReal.ofReal (a j ^ p)) ^ ((p : ℝ))⁻¹ :=
          ENNReal.rpow_le_rpow (hbd j) (by positivity)
      _ = ENNReal.ofReal (a j) := by
          rw [ENNReal.ofReal_pow (ha j), ENNReal.pow_rpow_inv_natCast hp0]
  have h5 := (h1.trans h3).trans h4
  rw [← ENNReal.ofReal_prod_of_nonneg fun j _ => ha j, ← ofReal_norm] at h5
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.prod_nonneg fun j _ => ha j)).mp h5

/-- Schwarz's inequality `∫ g ≤ μ(Ω)^{1/2} (∫ g²)^{1/2}`, the step (5.30). -/
private lemma lintegral_le_sqrt_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ENNReal} (hg : AEMeasurable g μ) :
    ∫⁻ a, g a ∂μ ≤ μ Set.univ ^ (1 / 2 : ℝ) * (∫⁻ a, g a ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (f := fun _ => 1) (g := g) aemeasurable_const hg
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const, one_mul] at h
  simp only [ENNReal.rpow_two] at h
  exact h

/-! ### The case `n ≤ 2s − 1` -/

/-- (5.23)–(5.30): if the factors `j ≠ k` are independent of the row `i`, bounded on `Ξ`, and the
factor `k` is a graded term `Z_i^{S,U}` with `i ∉ S`, then the expectation on `Ξ` is bounded by
`(∏_{j ≠ k} c_j) · P(Ξᶜ)^{1/2} · (E 1([Ξ]_i) |Z_i^{S,U}|²)^{1/2}`. -/
private lemma norm_setIntegral_prod_le_of_rowIndep {N : ℕ} {L : EntryLaws N} (hL : L.IsProb)
    {Z : Finset (Fin N) → Fin N → Entries N → ℂ} {Ξ : Set (Entries N)} (hΞ : MeasurableSet Ξ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → Bool) (G : ι → Entries N → ℂ)
    (hG : ∀ j, AEStronglyMeasurable (G j) L.law) (k : ι) (i : Fin N)
    (hsat : MeasurableSet (rowSat {i} Ξ)) (hrow : ∀ j ≠ k, RowIndep {i} (G j))
    {c : ι → ℝ} (hc : ∀ j, 0 ≤ c j) (hbd : ∀ j ≠ k, ∀ ω ∈ Ξ, ‖G j ω‖ ≤ c j)
    (hint : ∀ V, i ∉ V → Integrable (Z V i) L.law)
    (hE : ∀ V, i ∉ V → ∀ᵐ ω ∂L.law, L.rowsExp {i} (Z V i) ω = 0)
    {S U : Finset (Fin N)} (hi : i ∉ S) (hU : U ⊆ S)
    (hGk : G k = gradedTerm (fun V => Z V i) S U) {ε M : ℝ} (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hΞc : L.law Ξᶜ ≤ ENNReal.ofReal ε)
    (hL2 : ∫⁻ ω in rowSat {i} Ξ, ‖G k ω‖ₑ ^ 2 ∂L.law ≤ ENNReal.ofReal M) :
    ‖∫ ω in Ξ, ∏ j, cf (b j) (G j ω) ∂L.law‖ ≤
      (∏ j ∈ Finset.univ.erase k, c j) * ε ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ) := by
  set Ξk := rowSat {i} Ξ with hΞk
  set F : Entries N → ℂ := fun ω => ∏ j ∈ Finset.univ.erase k, cf (b j) (G j ω) with hFdef
  set B := ∏ j ∈ Finset.univ.erase k, c j with hBdef
  have hB0 : 0 ≤ B := Finset.prod_nonneg fun j _ => hc j
  have hFrow : RowIndep {i} F := by
    intro ω
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [hrow j (Finset.ne_of_mem_erase hj) ω]
  have hFbd : ∀ ω ∈ Ξk, ‖F ω‖ ≤ B := by
    intro ω hω
    obtain ⟨ξ, hξ, hπ⟩ := hω
    have hFω : F ω = F ξ := by rw [← hFrow ω, ← hπ, hFrow ξ]
    rw [hFω, norm_prod]
    refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j hj => ?_
    rw [norm_cf]
    exact hbd j (Finset.ne_of_mem_erase hj) ξ hξ
  have hFm : AEStronglyMeasurable F L.law :=
    Finset.aestronglyMeasurable_fun_prod _ fun j _ =>
      (continuous_cf _).comp_aestronglyMeasurable (hG j)
  have hGkint : Integrable (G k) L.law := by
    rw [hGk]
    exact integrable_gradedTerm (fun V hV => hint V fun h => hi (hV h)) hU
  have hcfk : Integrable (fun ω => cf (b k) (G k ω)) L.law :=
    hGkint.mono ((continuous_cf _).comp_aestronglyMeasurable hGkint.aestronglyMeasurable)
      (ae_of_all _ fun ω => (norm_cf _ _).le)
  have hP : ∀ ω, ∏ j, cf (b j) (G j ω) = F ω * cf (b k) (G k ω) := fun ω => by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), mul_comm]
  have hPint : IntegrableOn (fun ω => ∏ j, cf (b j) (G j ω)) Ξk L.law := by
    have h := hcfk.restrict.bdd_mul hFm.restrict (ae_restrict_of_forall_mem hsat hFbd)
    simp only [hP]
    exact h
  have hzero : ∫ ω in Ξk, ∏ j, cf (b j) (G j ω) ∂L.law = 0 := by
    rw [← integral_indicator hsat]
    have hind : Ξk.indicator (fun ω => ∏ j, cf (b j) (G j ω)) =
        fun ω => Ξk.indicator F ω * cf (b k) (gradedTerm (fun V => Z V i) S U ω) := by
      funext ω
      by_cases h : ω ∈ Ξk
      · simp only [Set.indicator_of_mem h, hP, hGk]
      · simp only [Set.indicator_of_notMem h, zero_mul]
    rw [hind]
    refine integral_mul_gradedTerm_eq_zero hL hint hE hi hU ?_ (hFm.indicator hsat) (B := B)
      ?_ (b k)
    · intro ω
      have hm := rowIndep_mem_rowSat {i} Ξ ω
      simp only at hm
      by_cases h : ω ∈ Ξk
      · have h' : zeroEntries {i} ω ∈ Ξk := by rw [hΞk, hm]; exact h
        rw [Set.indicator_of_mem h, Set.indicator_of_mem h', hFrow ω]
      · have h' : zeroEntries {i} ω ∉ Ξk := by rw [hΞk, hm]; exact h
        rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
    · intro ω
      by_cases h : ω ∈ Ξk
      · rw [Set.indicator_of_mem h]; exact hFbd ω h
      · rw [Set.indicator_of_notMem h, norm_zero]; exact hB0
  have hsplit := setIntegral_sdiff hΞ hPint (subset_rowSat {i} Ξ)
  rw [hzero, zero_sub] at hsplit
  have hnorm : ‖∫ ω in Ξ, ∏ j, cf (b j) (G j ω) ∂L.law‖ =
      ‖∫ ω in Ξk \ Ξ, ∏ j, cf (b j) (G j ω) ∂L.law‖ := by
    rw [hsplit, norm_neg]
  rw [hnorm]
  have h1 := enorm_integral_le_lintegral_enorm (μ := L.law.restrict (Ξk \ Ξ))
    (fun ω => ∏ j, cf (b j) (G j ω))
  have h2 : ∫⁻ ω in Ξk \ Ξ, ‖∏ j, cf (b j) (G j ω)‖ₑ ∂L.law ≤
      ∫⁻ ω in Ξk \ Ξ, ENNReal.ofReal B * ‖G k ω‖ₑ ∂L.law := by
    refine setLIntegral_mono' (hsat.diff hΞ) fun ω hω => ?_
    rw [hP, enorm_mul, enorm_cf, ← ofReal_norm]
    gcongr
    exact hFbd ω hω.1
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h2
  have h3 := lintegral_le_sqrt_mul (μ := L.law.restrict (Ξk \ Ξ)) (hG k).restrict.enorm
  rw [Measure.restrict_apply_univ] at h3
  have h4 : L.law (Ξk \ Ξ) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal ε ^ (1 / 2 : ℝ) := by
    refine ENNReal.rpow_le_rpow ((measure_mono ?_).trans hΞc) (by norm_num)
    intro ω hω
    exact hω.2
  have h5 : (∫⁻ ω in Ξk \ Ξ, ‖G k ω‖ₑ ^ 2 ∂L.law) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal M ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow ((lintegral_mono_set Set.sdiff_subset).trans hL2) (by norm_num)
  have h7 : ENNReal.ofReal B * ∫⁻ ω in Ξk \ Ξ, ‖G k ω‖ₑ ∂L.law ≤
      ENNReal.ofReal B * (ENNReal.ofReal ε ^ (1 / 2 : ℝ) * ENNReal.ofReal M ^ (1 / 2 : ℝ)) := by
    gcongr
    exact h3.trans (mul_le_mul' h4 h5)
  have h6 := h1.trans (h2.trans h7)
  rw [ENNReal.ofReal_rpow_of_nonneg hε (by norm_num), ENNReal.ofReal_rpow_of_nonneg hM
    (by norm_num), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hB0,
    ← ofReal_norm, ← mul_assoc] at h6
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h6

/-! ### Combinatorics -/

/-- If `α_j ∈ U_j ⊆ {α_1, …, α_p}` and `∑_j |U_j| < 2 |{α_1, …, α_p}|`, then some `α_k` lies in
no `U_j` with `j ≠ k` (the case `n ≤ 2s − 1` of the proof of Theorem 5.6). -/
private lemma exists_index_not_mem {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (α : ι → κ) (U : ι → Finset κ) (hαU : ∀ j, α j ∈ U j)
    (hUS : ∀ j, U j ⊆ Finset.univ.image α)
    (h : ∑ j, (U j).card < 2 * (Finset.univ.image α).card) : ∃ k, ∀ j ≠ k, α k ∉ U j := by
  classical
  by_contra hcon
  push Not at hcon
  set S := Finset.univ.image α with hS
  have hcard : ∀ j, (U j).card = ∑ x ∈ S, if x ∈ U j then 1 else 0 := by
    intro j
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hUS j)]
  have hge : ∀ x ∈ S, 2 ≤ ∑ j, if x ∈ U j then 1 else 0 := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hjk, hj⟩ := hcon k
    rw [← Finset.card_filter]
    have hsub : ({k, j} : Finset ι) ⊆ Finset.univ.filter (fun j' => α k ∈ U j') := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> simp [hαU, hj]
    calc 2 = ({k, j} : Finset ι).card := (Finset.card_pair hjk.symm).symm
      _ ≤ _ := Finset.card_le_card hsub
  have h2 : 2 * S.card ≤ ∑ j, (U j).card := by
    calc 2 * S.card = ∑ x ∈ S, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ x ∈ S, ∑ j, if x ∈ U j then 1 else 0 := Finset.sum_le_sum hge
      _ = ∑ j, ∑ x ∈ S, if x ∈ U j then 1 else 0 := Finset.sum_comm
      _ = ∑ j, (U j).card := by simp only [hcard]
  omega

/-- `∑_{U'_j ⊆ S_j} ∏_j p^{-(|U'_j| + 1)} ≤ (e/p)^p` when `|S_j| ≤ p` and there are `p` indices. -/
private lemma sum_piFinset_prod_inv_pow_le {ι κ : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}
    (hp : Fintype.card ι = p) (hp0 : 0 < p) (S : ι → Finset κ) (hS : ∀ j, (S j).card ≤ p) :
    ∑ U ∈ Fintype.piFinset (fun j => (S j).powerset), ∏ j, ((p : ℝ)⁻¹) ^ ((U j).card + 1) ≤
      (Real.exp 1 / p) ^ p := by
  have hps := Finset.prod_univ_sum (fun j => (S j).powerset)
    (fun (_ : ι) (T : Finset κ) => ((p : ℝ)⁻¹) ^ (T.card + 1))
  rw [← hps]
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp0
  have h1 : ∀ j, ∑ T ∈ (S j).powerset, ((p : ℝ)⁻¹) ^ (T.card + 1) ≤ Real.exp 1 / p := by
    intro j
    have h2 : ∑ T ∈ (S j).powerset, ((p : ℝ)⁻¹) ^ (T.card + 1) =
        (p : ℝ)⁻¹ * ((p : ℝ)⁻¹ + 1) ^ (S j).card := by
      rw [← Finset.sum_pow_mul_eq_add_pow, Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [one_pow, mul_one, pow_succ]
      ring
    rw [h2, div_eq_mul_inv, mul_comm (Real.exp 1)]
    gcongr
    calc ((p : ℝ)⁻¹ + 1) ^ (S j).card ≤ ((p : ℝ)⁻¹ + 1) ^ p :=
          pow_le_pow_right₀ (by linarith [inv_nonneg.mpr hp'.le]) (hS j)
      _ ≤ (Real.exp (p : ℝ)⁻¹) ^ p :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp ((p : ℝ)⁻¹)]) p
      _ = Real.exp 1 := by
          rw [← Real.exp_nat_mul, mul_inv_cancel₀ hp'.ne']
  calc ∏ j, ∑ T ∈ (S j).powerset, ((p : ℝ)⁻¹) ^ (T.card + 1) ≤ ∏ _j : ι, Real.exp 1 / p :=
        Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg fun T _ => by positivity)
          fun j _ => h1 j
    _ = (Real.exp 1 / p) ^ p := by rw [Finset.prod_const, Finset.card_univ, hp]

/-- `#{α : ι → Fin N : |{α_j}| = s} ≤ C(N, s) s^p`. -/
private lemma card_filter_card_image_le {ι : Type*} [Fintype ι] [DecidableEq ι] {N p : ℕ}
    (hp : Fintype.card ι = p) (s : ℕ) :
    (Finset.univ.filter fun α : ι → Fin N => (Finset.univ.image α).card = s).card ≤
      N.choose s * s ^ p := by
  have hsub : (Finset.univ.filter fun α : ι → Fin N => (Finset.univ.image α).card = s) ⊆
      (Finset.powersetCard s (Finset.univ : Finset (Fin N))).biUnion
        (fun S => Fintype.piFinset fun _ : ι => S) := by
    intro α hα
    rw [Finset.mem_filter] at hα
    rw [Finset.mem_biUnion]
    refine ⟨Finset.univ.image α, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hα.2⟩, ?_⟩
    rw [Fintype.mem_piFinset]
    intro j
    exact Finset.mem_image_of_mem α (Finset.mem_univ j)
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  have h : ∀ S ∈ Finset.powersetCard s (Finset.univ : Finset (Fin N)),
      (Fintype.piFinset fun _ : ι => S).card = s ^ p := by
    intro S hS
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, hp,
      (Finset.mem_powersetCard.mp hS).2]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- `∑_α ρ^{|{α_j}|} ≤ (p + 1) p^p max(1, Nρ)^p`, the count `N^s s^p` of (5.14). -/
private lemma sum_pow_card_image_le {ι : Type*} [Fintype ι] [DecidableEq ι] {N p : ℕ}
    (hp : Fintype.card ι = p) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∑ α : ι → Fin N, ρ ^ (Finset.univ.image α).card ≤
      (p + 1) * (p : ℝ) ^ p * max 1 (N * ρ) ^ p := by
  have hmaps : ∀ α ∈ (Finset.univ : Finset (ι → Fin N)),
      (Finset.univ.image α).card ∈ Finset.range (p + 1) := by
    intro α _
    rw [Finset.mem_range, Nat.lt_succ_iff, ← hp]
    exact Finset.card_image_le.trans (by rw [Finset.card_univ])
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ s ∈ Finset.range (p + 1),
      ∑ α ∈ (Finset.univ : Finset (ι → Fin N)) with (Finset.univ.image α).card = s,
        ρ ^ (Finset.univ.image α).card ≤
        (p : ℝ) ^ p * (N * ρ) ^ s := by
    intro s hs
    have hsp : s ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    have hcongr : ∀ α ∈ Finset.univ.filter fun α : ι → Fin N => (Finset.univ.image α).card = s,
        ρ ^ (Finset.univ.image α).card = ρ ^ s := fun α hα => by
      rw [(Finset.mem_filter.mp hα).2]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]
    have hc := card_filter_card_image_le (N := N) hp s
    have hc' : ((Finset.univ.filter fun α : ι → Fin N => (Finset.univ.image α).card = s).card : ℝ)
        ≤ (N : ℝ) ^ s * (p : ℝ) ^ p := by
      have h1 : ((N.choose s * s ^ p : ℕ) : ℝ) ≤ (N : ℝ) ^ s * (p : ℝ) ^ p := by
        push_cast
        gcongr
        · exact_mod_cast Nat.choose_le_pow N s
      exact (Nat.cast_le.mpr hc).trans h1
    calc _ ≤ (N : ℝ) ^ s * (p : ℝ) ^ p * ρ ^ s := by gcongr
      _ = (p : ℝ) ^ p * (N * ρ) ^ s := by ring
  refine (Finset.sum_le_sum hfib).trans ?_
  have hmax : ∀ s ∈ Finset.range (p + 1), (p : ℝ) ^ p * (N * ρ) ^ s ≤
      (p : ℝ) ^ p * max 1 (N * ρ) ^ p := by
    intro s hs
    have hsp : s ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    gcongr
    calc (N * ρ) ^ s ≤ max 1 (N * ρ) ^ s :=
          pow_le_pow_left₀ (by positivity) (le_max_right _ _) s
      _ ≤ max 1 (N * ρ) ^ p := pow_le_pow_right₀ (le_max_left _ _) hsp
  refine (Finset.sum_le_sum hmax).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring_nf
  rfl

/-! ### One term of the expansion (5.18) -/

/-- The constant `2 N^{|C10|} N^{|C9|/2} e^{-c11 (log N)^{3/2}/2}` of the case `n ≤ 2s − 1`. -/
private def betaN (N : ℕ) (C9 C10 c11 : ℝ) : ℝ :=
  2 * (N : ℝ) ^ |C10| * (N : ℝ) ^ (|C9| / 2) * Real.exp (-c11 * Real.log N ^ ((3 : ℝ) / 2) / 2)

private lemma betaN_nonneg (N : ℕ) (C9 C10 c11 : ℝ) : 0 ≤ betaN N C9 C10 c11 := by
  unfold betaN; positivity

/-- The bound (5.18) for one term `E 1(Ξ) ∏_j [Z^#_{α_j}]^{S_j, U'_j}` of (5.17), with
`s = |S(α)|`, `n = ∑_j (|U'_j| + 1)` and the weight `p^{-n}`: both cases `n ≥ 2s` and
`n ≤ 2s − 1`. -/
private lemma norm_setIntegral_term_le {N : ℕ} {L : EntryLaws N} (hL : L.IsProb)
    {Z : Finset (Fin N) → Fin N → Entries N → ℂ} {Ξ : Set (Entries N)} {p : ℕ}
    {X Y C6 C9 C10 c11 : ℝ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hp : Fintype.card ι = p) (hpe : Even p) (hp1 : 1 ≤ p) (hN : 1 ≤ N)
    (hΞ : MeasurableSet Ξ) (hsat : ∀ i, MeasurableSet (rowSat {i} Ξ)) (hX : 0 ≤ X)
    (hY : 1 ≤ Y) (hr : |C6| * X * (p : ℝ) ^ 2 ≤ 1)
    (hi : ∀ U i, i ∉ U → Integrable (Z U i) L.law ∧ RowIndep U (Z U i) ∧
        ∀ᵐ ω ∂L.law, L.rowsExp {i} (Z U i) ω = 0)
    (hii : ∀ S U i, U ⊆ S → i ∉ S → S.card ≤ p →
        ∫⁻ ω in Ξ, ‖gradedTerm (fun V => Z V i) S U ω‖ₑ ^ p ∂L.law ≤
          ENNReal.ofReal ((Y * (C6 * X * (U.card + 1)) ^ (U.card + 1)) ^ p))
    (hiii : ∀ S U i, U ⊆ S → i ∉ S → S.card ≤ p →
        ∫⁻ ω in rowSat {i} Ξ, ‖gradedTerm (fun V => Z V i) S U ω‖ₑ ^ 2 ∂L.law ≤
          ENNReal.ofReal ((N : ℝ) ^ (C9 * p)))
    (hiv : ∀ U i, i ∉ U → ∀ ω ∈ Ξ, ‖Z U i ω‖ ≤ Y * (N : ℝ) ^ C10)
    (hv : L.law Ξᶜ ≤ ENNReal.ofReal (Real.exp (-c11 * Real.log N ^ ((3 : ℝ) / 2) * p)))
    (b : ι → Bool) (α : ι → Fin N) (U' : ι → Finset (Fin N))
    (hU' : U' ∈ Fintype.piFinset fun j => ((Finset.univ.image α).erase (α j)).powerset) :
    ‖∫ ω in Ξ, ∏ j, cf (b j) (gradedTerm (fun V => Z V (α j))
        ((Finset.univ.image α).erase (α j)) (U' j) ω) ∂L.law‖ ≤
      Y ^ p * (((|C6| * X * (p : ℝ) ^ 2) ^ 2) ^ (Finset.univ.image α).card +
        betaN N C9 C10 c11 ^ p * (p : ℝ) ^ (2 * (Finset.univ.image α).card)) *
      ∏ j, ((p : ℝ)⁻¹) ^ ((U' j).card + 1) := by
  set S := Finset.univ.image α with hSdef
  set s := S.card with hsdef
  set G : ι → Entries N → ℂ := fun j =>
    gradedTerm (fun V => Z V (α j)) (S.erase (α j)) (U' j) with hGdef
  have hmem : ∀ j, U' j ⊆ S.erase (α j) := fun j =>
    Finset.mem_powerset.mp (Fintype.mem_piFinset.mp hU' j)
  have hnotin : ∀ j, α j ∉ S.erase (α j) := fun j => Finset.notMem_erase _ _
  have hαS : ∀ j, α j ∈ S := fun j => Finset.mem_image_of_mem α (Finset.mem_univ j)
  have hSp : s ≤ p := by
    rw [hsdef, ← hp]
    exact Finset.card_image_le.trans (by rw [Finset.card_univ])
  have hSjp : ∀ j, (S.erase (α j)).card ≤ p := fun j => Finset.card_erase_le.trans hSp
  have hUp : ∀ j, (U' j).card + 1 ≤ p := by
    intro j
    have h1 := Finset.card_le_card (hmem j)
    rw [Finset.card_erase_of_mem (hαS j)] at h1
    have h2 : 1 ≤ s := Finset.card_pos.mpr ⟨α j, hαS j⟩
    omega
  have hint' : ∀ j, Integrable (G j) L.law := fun j =>
    integrable_gradedTerm (fun V hV => (hi V (α j) fun h => hnotin j (hV h)).1) (hmem j)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
  set q : ℝ := (p : ℝ)⁻¹ with hqdef
  have hq0 : 0 ≤ q := inv_nonneg.mpr hp0.le
  set n := ∑ j, ((U' j).card + 1) with hndef
  have hprodq : ∏ j, q ^ ((U' j).card + 1) = q ^ n := Finset.prod_pow_eq_pow_sum _ _ _
  rw [hprodq]
  set ρ := (|C6| * X * (p : ℝ) ^ 2) ^ 2 with hρdef
  set β := betaN N C9 C10 c11 with hβdef
  have hβ0 : 0 ≤ β := betaN_nonneg N C9 C10 c11
  have hρ0 : 0 ≤ ρ := sq_nonneg _
  by_cases hcase : 2 * s ≤ n
  · -- the case `n ≥ 2s`: Hölder, (5.20)–(5.21)
    set a : ι → ℝ := fun j => |Y * (C6 * X * ((U' j).card + 1)) ^ ((U' j).card + 1)| with hadef
    have h1 := norm_setIntegral_prod_le (μ := L.law) hp (by omega) Ξ b (G := G)
      (fun j => (hint' j).aestronglyMeasurable) (a := a) (fun j => abs_nonneg _)
      (fun j => by
        rw [hadef]
        simp only
        rw [Even.pow_abs hpe]
        exact hii _ _ _ (hmem j) (hnotin j) (hSjp j))
    set r := |C6| * X * (p : ℝ) with hrdef
    have hr0 : 0 ≤ r := by positivity
    have h2 : ∀ j ∈ Finset.univ, a j ≤ Y * r ^ ((U' j).card + 1) := by
      intro j _
      have hu : ((U' j).card : ℝ) + 1 ≤ p := by exact_mod_cast hUp j
      rw [hadef]
      simp only
      rw [abs_mul, abs_pow, abs_mul, abs_mul, abs_of_nonneg hX,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (U' j).card + 1),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ Y)]
      gcongr
      rw [hrdef]
      gcongr
    have h3 : ∏ j, a j ≤ Y ^ p * r ^ n := by
      refine (Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) h2).trans (le_of_eq ?_)
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hp,
        Finset.prod_pow_eq_pow_sum]
    have h4 : r ^ n ≤ ρ ^ s * q ^ n := by
      have hr' : r = (|C6| * X * (p : ℝ) ^ 2) * q := by
        rw [hrdef, hqdef]
        field_simp
      rw [hr', mul_pow, hρdef, ← pow_mul]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by positivity) hr hcase)
        (by positivity)
    calc _ ≤ ∏ j, a j := h1
      _ ≤ Y ^ p * r ^ n := h3
      _ ≤ Y ^ p * (ρ ^ s * q ^ n) := by gcongr
      _ ≤ Y ^ p * (ρ ^ s + β ^ p * (p : ℝ) ^ (2 * s)) * q ^ n := by
          rw [mul_add, add_mul]
          have : 0 ≤ Y ^ p * (β ^ p * (p : ℝ) ^ (2 * s)) * q ^ n := by positivity
          nlinarith
  · -- the case `n ≤ 2s − 1`: (5.22)–(5.31)
    push Not at hcase
    have hins : ∀ j, (insert (α j) (U' j)).card = (U' j).card + 1 := fun j =>
      Finset.card_insert_of_notMem fun h => hnotin j (hmem j h)
    obtain ⟨k, hk⟩ := exists_index_not_mem α (fun j => insert (α j) (U' j))
      (fun j => Finset.mem_insert_self _ _)
      (fun j => Finset.insert_subset (hαS j) ((hmem j).trans (Finset.erase_subset _ _)))
      (by simp only [hins]; exact hcase)
    have hk' : ∀ j ≠ k, α k ≠ α j ∧ α k ∉ U' j := by
      intro j hj
      have := hk j hj
      simp only [Finset.mem_insert, not_or] at this
      exact this
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    set D := Y * (N : ℝ) ^ |C10| with hDdef
    have hD1 : 1 ≤ D := by
      have := Real.one_le_rpow hN1 (abs_nonneg C10)
      nlinarith
    set c : ι → ℝ := fun j => 2 ^ (U' j).card * D with hcdef
    have hc1 : ∀ j, 1 ≤ c j := fun j => by
      rw [hcdef]
      simp only
      have := one_le_pow₀ (M₀ := ℝ) (a := 2) (by norm_num) (n := (U' j).card)
      nlinarith
    have hNC : (N : ℝ) ^ C10 ≤ (N : ℝ) ^ |C10| :=
      Real.rpow_le_rpow_of_exponent_le hN1 (le_abs_self _)
    have h1 := norm_setIntegral_prod_le_of_rowIndep hL (Z := Z) hΞ b G
      (fun j => (hint' j).aestronglyMeasurable) k (α k) (hsat (α k))
      (fun j hj => rowIndep_gradedTerm_singleton (fun V hV => (hi V (α j) hV).2.1) (hnotin j)
        (hmem j) (Finset.mem_erase.mpr ⟨(hk' j hj).1, hαS k⟩) (hk' j hj).2)
      (c := c) (fun j => by linarith [hc1 j])
      (fun j _ ω hω => norm_gradedTerm_le (fun V hV => (hiv V (α j)
          (fun h => hnotin j (hV h)) ω hω).trans (by
            have : 0 ≤ Y := by linarith
            exact mul_le_mul_of_nonneg_left hNC this)) (hmem j))
      (fun V hV => (hi V (α k) hV).1) (fun V hV => (hi V (α k) hV).2.2) (hnotin k) (hmem k) rfl
      (Real.exp_nonneg _) (by positivity) hv (hiii _ _ _ (hmem k) (hnotin k) (hSjp k))
    -- the factors `j ≠ k`, (5.27)–(5.28)
    have hsumU : ∑ j, (U' j).card ≤ p := by
      have : n = ∑ j, (U' j).card + p := by
        rw [hndef, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hp, smul_eq_mul,
          mul_one]
      omega
    have h2 : ∏ j ∈ Finset.univ.erase k, c j ≤ (2 * D) ^ p := by
      calc ∏ j ∈ Finset.univ.erase k, c j ≤ c k * ∏ j ∈ Finset.univ.erase k, c j :=
            le_mul_of_one_le_left (Finset.prod_nonneg fun j _ => by linarith [hc1 j]) (hc1 k)
        _ = ∏ j, c j := Finset.mul_prod_erase _ _ (Finset.mem_univ k)
        _ = 2 ^ (∑ j, (U' j).card) * D ^ p := by
            rw [hcdef]
            simp only
            rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_const,
              Finset.card_univ, hp]
        _ ≤ 2 ^ p * D ^ p := by
            gcongr
            · norm_num
        _ = (2 * D) ^ p := (mul_pow _ _ _).symm
    -- `P(Ξᶜ)^{1/2}` and `(N^{C9 p})^{1/2}`, (5.30)–(5.31)
    have h3 : Real.exp (-c11 * Real.log N ^ ((3 : ℝ) / 2) * p) ^ (1 / 2 : ℝ) =
        Real.exp (-c11 * Real.log N ^ ((3 : ℝ) / 2) / 2) ^ p := by
      rw [← Real.exp_mul, ← Real.exp_nat_mul]
      congr 1
      ring
    have h4 : ((N : ℝ) ^ (C9 * p)) ^ (1 / 2 : ℝ) ≤ ((N : ℝ) ^ (|C9| / 2)) ^ p := by
      rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul_natCast (by positivity)]
      refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
      have := le_abs_self C9
      nlinarith
    have h5 : (∏ j ∈ Finset.univ.erase k, c j) *
        Real.exp (-c11 * Real.log N ^ ((3 : ℝ) / 2) * p) ^ (1 / 2 : ℝ) *
        ((N : ℝ) ^ (C9 * p)) ^ (1 / 2 : ℝ) ≤ Y ^ p * β ^ p := by
      rw [h3]
      calc _ ≤ (2 * D) ^ p * Real.exp (-c11 * Real.log N ^ ((3 : ℝ) / 2) / 2) ^ p *
            ((N : ℝ) ^ (|C9| / 2)) ^ p := by
            gcongr
        _ = Y ^ p * β ^ p := by
            rw [← mul_pow, ← mul_pow, ← mul_pow, hβdef, betaN, hDdef]
            congr 1
            ring
    have h6 : 1 ≤ (p : ℝ) ^ (2 * s) * q ^ n := by
      rw [hqdef, inv_pow, ← div_eq_mul_inv, one_le_div (by positivity)]
      exact pow_le_pow_right₀ (by exact_mod_cast hp1) hcase.le
    calc _ ≤ Y ^ p * β ^ p := h1.trans h5
      _ ≤ Y ^ p * β ^ p * ((p : ℝ) ^ (2 * s) * q ^ n) :=
          le_mul_of_one_le_right (by positivity) h6
      _ ≤ Y ^ p * (ρ ^ s + β ^ p * (p : ℝ) ^ (2 * s)) * q ^ n := by
          have : 0 ≤ Y ^ p * ρ ^ s * q ^ n := by positivity
          nlinarith

/-! ### The moment bound (5.19) -/

/-- `|w|^{2m} = ∏_{(b, k) ∈ Bool × Fin m} w^#`, with `#` the conjugation for `b = true`
(the expansion (5.13)). -/
private lemma norm_pow_eq_prod_cf (m : ℕ) (w : ℂ) :
    ((‖w‖ ^ (m + m) : ℝ) : ℂ) = ∏ j : Bool × Fin m, cf j.1 w := by
  rw [Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, cf, ite_true,
    Bool.false_eq_true, ite_false, RingHom.id_apply]
  rw [← mul_pow, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← two_mul, pow_mul]
  push_cast
  rfl

/-- (5.13)–(5.16): `|[Z]|^p = N^{-p} ∑_α ∑_{U'_j ⊆ S_j} ∏_j [Z^#_{α_j}]^{S_j, U'_j}` pointwise,
with `S_j = S(α) \ {α_j}`. -/
private lemma norm_pow_eq_sum {N : ℕ} (Z : Finset (Fin N) → Fin N → Entries N → ℂ) (m : ℕ)
    (ω : Entries N) :
    ((‖(N : ℂ)⁻¹ * ∑ i, Z ∅ i ω‖ ^ (m + m) : ℝ) : ℂ) = ((N : ℂ)⁻¹) ^ (m + m) *
      ∑ α : Bool × Fin m → Fin N, ∑ U' ∈ Fintype.piFinset
        (fun j => ((Finset.univ.image α).erase (α j)).powerset),
        ∏ j, cf j.1 (gradedTerm (fun V => Z V (α j)) ((Finset.univ.image α).erase (α j))
          (U' j) ω) := by
  rw [norm_pow_eq_prod_cf]
  simp only [map_mul, map_sum, cf_natCast_inv]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_bool, Fintype.card_fin, two_mul, Fintype.prod_sum]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  have h : ∀ j : Bool × Fin m, cf j.1 (Z ∅ (α j) ω) = ∑ U ∈ ((Finset.univ.image α).erase
      (α j)).powerset, cf j.1 (gradedTerm (fun V => Z V (α j))
        ((Finset.univ.image α).erase (α j)) U ω) := by
    intro j
    rw [← map_sum]
    congr 1
    have := congrFun (sum_gradedTerm (fun V => Z V (α j)) ((Finset.univ.image α).erase (α j))) ω
    rw [Finset.sum_apply] at this
    exact this.symm
  simp only [h]
  exact Finset.prod_univ_sum (fun j => ((Finset.univ.image α).erase (α j)).powerset)
    (fun j U => cf j.1 (gradedTerm (fun V => Z V (α j)) ((Finset.univ.image α).erase (α j))
      U ω))

/-- The arithmetic closing (5.18)–(5.19). -/
private lemma moment_arith {N p : ℕ} {X Y C6 β : ℝ} (hN : 1 ≤ N) (hp : 2 ≤ p) (hY : 1 ≤ Y)
    (hβ0 : 0 ≤ β) (hβ : β ≤ (N : ℝ)⁻¹) :
    ((N : ℝ)⁻¹) ^ p * (Y ^ p * (Real.exp 1 / p) ^ p *
      ((p + 1) * (p : ℝ) ^ p * max 1 (N * (|C6| * X * (p : ℝ) ^ 2) ^ 2) ^ p +
        (N : ℝ) ^ p * (β ^ p * (p : ℝ) ^ (2 * p)))) ≤
      (2 * Real.exp 1 * max 1 (C6 ^ 2) * (p : ℝ) ^ 4 * Y * (X ^ 2 + (N : ℝ)⁻¹)) ^ p := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ) ≤ p := by linarith
  set e := Real.exp 1 with he
  have he0 : 0 < e := Real.exp_pos 1
  set C1 := max 1 (C6 ^ 2) with hC1
  have hC1 : 1 ≤ C1 := le_max_left _ _
  set M := max 1 (N * (|C6| * X * (p : ℝ) ^ 2) ^ 2) with hM
  set A := e * C1 * (p : ℝ) ^ 4 * Y * (X ^ 2 + (N : ℝ)⁻¹) with hA
  have hp4 : (1 : ℝ) ≤ (p : ℝ) ^ 4 := one_le_pow₀ hp1
  have hpp4 : (p : ℝ) ≤ (p : ℝ) ^ 4 := by
    calc (p : ℝ) = (p : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (p : ℝ) ^ 4 := pow_le_pow_right₀ hp1 (by norm_num)
  have hY0 : 0 ≤ Y := by linarith
  -- `N⁻¹ max(1, Nρ) ≤ C1 p⁴ (X² + N⁻¹)`
  have hM' : (N : ℝ)⁻¹ * M ≤ C1 * (p : ℝ) ^ 4 * (X ^ 2 + (N : ℝ)⁻¹) := by
    have h1 : M ≤ C1 * (p : ℝ) ^ 4 * (N * X ^ 2 + 1) := by
      refine max_le ?_ ?_
      · have : 1 ≤ C1 * (p : ℝ) ^ 4 := one_le_mul_of_one_le_of_one_le hC1 hp4
        nlinarith [mul_nonneg hN0.le (sq_nonneg X), mul_nonneg (by linarith : (0 : ℝ) ≤ C1)
          (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 4)]
      · have h2 : (|C6| * X * (p : ℝ) ^ 2) ^ 2 = C6 ^ 2 * X ^ 2 * (p : ℝ) ^ 4 := by
          rw [mul_pow, mul_pow, sq_abs]; ring
        rw [h2]
        have h3 : C6 ^ 2 ≤ C1 := le_max_right _ _
        have h4 : 0 ≤ (N : ℝ) * X ^ 2 * (p : ℝ) ^ 4 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right h3 h4, mul_nonneg (by linarith : (0 : ℝ) ≤ C1)
          (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 4)]
    calc (N : ℝ)⁻¹ * M ≤ (N : ℝ)⁻¹ * (C1 * (p : ℝ) ^ 4 * (N * X ^ 2 + 1)) := by gcongr
      _ = C1 * (p : ℝ) ^ 4 * (X ^ 2 + (N : ℝ)⁻¹) := by field_simp
  have hT1 : (N : ℝ)⁻¹ * Y * e * M ≤ A := by
    rw [hA]
    have := mul_le_mul_of_nonneg_left hM' (mul_nonneg hY0 he0.le)
    nlinarith
  have hT2 : Y * e * β * p ≤ A := by
    rw [hA]
    have h1 : β * p ≤ (N : ℝ)⁻¹ * p := by gcongr
    have h2 : (N : ℝ)⁻¹ * p ≤ C1 * (p : ℝ) ^ 4 * (X ^ 2 + (N : ℝ)⁻¹) := by
      have h3 : (p : ℝ) ≤ C1 * (p : ℝ) ^ 4 := by nlinarith
      have h4 : (N : ℝ)⁻¹ ≤ X ^ 2 + (N : ℝ)⁻¹ := by nlinarith [sq_nonneg X]
      calc (N : ℝ)⁻¹ * p = p * (N : ℝ)⁻¹ := mul_comm _ _
        _ ≤ C1 * (p : ℝ) ^ 4 * (X ^ 2 + (N : ℝ)⁻¹) :=
          mul_le_mul h3 h4 (by positivity) (by positivity)
    have h5 := mul_le_mul_of_nonneg_left (h1.trans h2) (mul_nonneg hY0 he0.le)
    nlinarith
  have hA0 : 0 ≤ A := by positivity
  have heq : ((N : ℝ)⁻¹) ^ p * (Y ^ p * (e / p) ^ p *
      ((p + 1) * (p : ℝ) ^ p * M ^ p + (N : ℝ) ^ p * (β ^ p * (p : ℝ) ^ (2 * p)))) =
      (p + 1) * ((N : ℝ)⁻¹ * Y * e * M) ^ p + (Y * e * β * p) ^ p := by
    rw [div_pow, pow_mul]
    simp only [mul_pow, inv_pow]
    field_simp
    ring
  rw [heq]
  have h2p : ((p : ℝ) + 2) ≤ 2 ^ p := by
    have h := Nat.lt_two_pow_self (n := p - 1)
    have h' : (p : ℕ) + 2 ≤ 2 ^ p := by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      have : 1 ≤ q := by omega
      have h1 : 2 ≤ 2 ^ q := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) this
      simp only [Nat.add_sub_cancel] at h
      rw [pow_succ]
      omega
    exact_mod_cast h'
  calc (p + 1) * ((N : ℝ)⁻¹ * Y * e * M) ^ p + (Y * e * β * p) ^ p ≤
      (p + 1) * A ^ p + A ^ p := by
        gcongr
    _ = ((p : ℝ) + 2) * A ^ p := by ring
    _ ≤ 2 ^ p * A ^ p := by gcongr
    _ = (2 * e * C1 * (p : ℝ) ^ 4 * Y * (X ^ 2 + (N : ℝ)⁻¹)) ^ p := by
        rw [← mul_pow, hA]
        ring

/-- (5.19): `E 1(Ξ) |[Z]|^p ≤ (2e max(1, C6²) p⁴ Y (X² + N⁻¹))^p`, given `|C6| X p² ≤ 1`
(from (5.7)) and `betaN ≤ N⁻¹` (from (5.11)). -/
private lemma setLIntegral_enorm_pow_le {N : ℕ} {L : EntryLaws N} (hL : L.IsProb)
    {Z : Finset (Fin N) → Fin N → Entries N → ℂ} {Ξ : Set (Entries N)} {p : ℕ}
    {X Y C6 C9 C10 c11 : ℝ} (hpe : Even p) (hp2 : 2 ≤ p) (hN : 1 ≤ N)
    (hΞ : MeasurableSet Ξ) (hsat : ∀ i, MeasurableSet (rowSat {i} Ξ)) (hX : 0 ≤ X)
    (hY : 1 ≤ Y) (hr : |C6| * X * (p : ℝ) ^ 2 ≤ 1) (hβ : betaN N C9 C10 c11 ≤ (N : ℝ)⁻¹)
    (hi : ∀ U i, i ∉ U → Integrable (Z U i) L.law ∧ RowIndep U (Z U i) ∧
        ∀ᵐ ω ∂L.law, L.rowsExp {i} (Z U i) ω = 0)
    (hii : ∀ S U i, U ⊆ S → i ∉ S → S.card ≤ p →
        ∫⁻ ω in Ξ, ‖gradedTerm (fun V => Z V i) S U ω‖ₑ ^ p ∂L.law ≤
          ENNReal.ofReal ((Y * (C6 * X * (U.card + 1)) ^ (U.card + 1)) ^ p))
    (hiii : ∀ S U i, U ⊆ S → i ∉ S → S.card ≤ p →
        ∫⁻ ω in rowSat {i} Ξ, ‖gradedTerm (fun V => Z V i) S U ω‖ₑ ^ 2 ∂L.law ≤
          ENNReal.ofReal ((N : ℝ) ^ (C9 * p)))
    (hiv : ∀ U i, i ∉ U → ∀ ω ∈ Ξ, ‖Z U i ω‖ ≤ Y * (N : ℝ) ^ C10)
    (hv : L.law Ξᶜ ≤ ENNReal.ofReal (Real.exp (-c11 * Real.log N ^ ((3 : ℝ) / 2) * p))) :
    ∫⁻ ω in Ξ, ‖(N : ℂ)⁻¹ * ∑ i, Z ∅ i ω‖ₑ ^ p ∂L.law ≤ ENNReal.ofReal
      ((2 * Real.exp 1 * max 1 (C6 ^ 2) * (p : ℝ) ^ 4 * Y * (X ^ 2 + (N : ℝ)⁻¹)) ^ p) := by
  have := EntryLaws.isProbabilityMeasure_law hL
  obtain ⟨m, hm⟩ := hpe
  subst hm
  set p := m + m with hpdef
  have hcard : Fintype.card (Bool × Fin m) = p := by
    rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, two_mul]
  set W : Entries N → ℂ := fun ω => (N : ℂ)⁻¹ * ∑ i, Z ∅ i ω with hWdef
  set T : (Bool × Fin m → Fin N) → Finset (Bool × Fin m → Finset (Fin N)) := fun α =>
    Fintype.piFinset (fun j => ((Finset.univ.image α).erase (α j)).powerset) with hTdef
  set P : (Bool × Fin m → Fin N) → (Bool × Fin m → Finset (Fin N)) → Entries N → ℂ :=
    fun α U' ω => ∏ j, cf j.1 (gradedTerm (fun V => Z V (α j))
      ((Finset.univ.image α).erase (α j)) (U' j) ω) with hPdef
  have hexp : ∀ ω, ((‖W ω‖ ^ p : ℝ) : ℂ) =
      ((N : ℂ)⁻¹) ^ p * ∑ α, ∑ U' ∈ T α, P α U' ω := fun ω => norm_pow_eq_sum Z m ω
  -- every term is integrable on `Ξ`
  have hPint : ∀ α, ∀ U' ∈ T α, Integrable (P α U') (L.law.restrict Ξ) := by
    intro α U' hU'
    have hmem : ∀ j, U' j ⊆ (Finset.univ.image α).erase (α j) := fun j =>
      Finset.mem_powerset.mp (Fintype.mem_piFinset.mp hU' j)
    have hnotin : ∀ j, α j ∉ (Finset.univ.image α).erase (α j) := fun j =>
      Finset.notMem_erase _ _
    refine Integrable.of_bound ?_ (∏ j, 2 ^ (U' j).card * (Y * (N : ℝ) ^ C10))
      (ae_restrict_of_forall_mem hΞ fun ω hω => ?_)
    · refine (Finset.aestronglyMeasurable_fun_prod _ fun j _ => ?_).restrict
      exact (continuous_cf _).comp_aestronglyMeasurable (integrable_gradedTerm
        (fun V hV => (hi V (α j) fun h => hnotin j (hV h)).1) (hmem j)).aestronglyMeasurable
    · rw [hPdef]
      simp only
      rw [norm_prod]
      refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => ?_
      rw [norm_cf]
      exact norm_gradedTerm_le (fun V hV => hiv V (α j) (fun h => hnotin j (hV h)) ω hω) (hmem j)
  have hsumint : Integrable (fun ω => ((N : ℂ)⁻¹) ^ p * ∑ α, ∑ U' ∈ T α, P α U' ω)
      (L.law.restrict Ξ) :=
    (integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun U' hU' =>
      hPint α U' hU').const_mul _
  have hWint : Integrable (fun ω => ‖W ω‖ ^ p) (L.law.restrict Ξ) := by
    have h := hsumint.norm
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only
    rw [← hexp ω, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  -- `E 1(Ξ)|[Z]|^p ≤ N^{-p} ∑_α ∑_{U'} |E 1(Ξ) ∏_j …|`, (5.14)–(5.17)
  have h1 : ∫ ω in Ξ, ‖W ω‖ ^ p ∂L.law ≤
      ((N : ℝ)⁻¹) ^ p * ∑ α, ∑ U' ∈ T α, ‖∫ ω in Ξ, P α U' ω ∂L.law‖ := by
    have hc : ((∫ ω in Ξ, ‖W ω‖ ^ p ∂L.law : ℝ) : ℂ) =
        ((N : ℂ)⁻¹) ^ p * ∑ α, ∑ U' ∈ T α, ∫ ω in Ξ, P α U' ω ∂L.law := by
      rw [← integral_complex_ofReal]
      simp only [hexp]
      rw [integral_const_mul, integral_finsetSum _ fun α _ => integrable_finsetSum _
        fun U' hU' => hPint α U' hU']
      congr 1
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [integral_finsetSum _ fun U' hU' => hPint α U' hU']
    calc ∫ ω in Ξ, ‖W ω‖ ^ p ∂L.law ≤ ‖((∫ ω in Ξ, ‖W ω‖ ^ p ∂L.law : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact le_abs_self _
      _ ≤ ((N : ℝ)⁻¹) ^ p * ∑ α, ∑ U' ∈ T α, ‖∫ ω in Ξ, P α U' ω ∂L.law‖ := by
          rw [hc, norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
          gcongr
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => norm_sum_le _ _)
  -- the sum over `U'`, then over `α`, (5.17)–(5.18)
  have hp1 : 1 ≤ p := by omega
  have hS : ∀ α : Bool × Fin m → Fin N, (Finset.univ.image α).card ≤ p := fun α =>
    Finset.card_image_le.trans (by rw [Finset.card_univ, hcard])
  set e := Real.exp 1 with he
  set ρ := (|C6| * X * (p : ℝ) ^ 2) ^ 2 with hρdef
  set β := betaN N C9 C10 c11 with hβdef
  have hβ0 : 0 ≤ β := betaN_nonneg N C9 C10 c11
  have hY0 : 0 ≤ Y := by linarith
  have h2 : ∀ α, ∑ U' ∈ T α, ‖∫ ω in Ξ, P α U' ω ∂L.law‖ ≤
      Y ^ p * (ρ ^ (Finset.univ.image α).card +
        β ^ p * (p : ℝ) ^ (2 * (Finset.univ.image α).card)) * (e / p) ^ p := by
    intro α
    calc ∑ U' ∈ T α, ‖∫ ω in Ξ, P α U' ω ∂L.law‖ ≤ ∑ U' ∈ T α,
        Y ^ p * (ρ ^ (Finset.univ.image α).card +
          β ^ p * (p : ℝ) ^ (2 * (Finset.univ.image α).card)) *
          ∏ j, ((p : ℝ)⁻¹) ^ ((U' j).card + 1) :=
          Finset.sum_le_sum fun U' hU' => norm_setIntegral_term_le hL hcard ⟨m, rfl⟩ hp1 hN hΞ
            hsat hX hY hr hi hii hiii hiv hv Prod.fst α U' hU'
      _ = Y ^ p * (ρ ^ (Finset.univ.image α).card +
          β ^ p * (p : ℝ) ^ (2 * (Finset.univ.image α).card)) *
          ∑ U' ∈ T α, ∏ j, ((p : ℝ)⁻¹) ^ ((U' j).card + 1) := by rw [Finset.mul_sum]
      _ ≤ _ := by
          gcongr
          exact sum_piFinset_prod_inv_pow_le hcard (by omega) _ fun j =>
            Finset.card_erase_le.trans (hS α)
  have h3 : ∑ α, ∑ U' ∈ T α, ‖∫ ω in Ξ, P α U' ω ∂L.law‖ ≤ Y ^ p * (e / p) ^ p *
      ((p + 1) * (p : ℝ) ^ p * max 1 (N * ρ) ^ p + (N : ℝ) ^ p * (β ^ p * (p : ℝ) ^ (2 * p))) := by
    calc ∑ α, ∑ U' ∈ T α, ‖∫ ω in Ξ, P α U' ω ∂L.law‖ ≤ ∑ α : Bool × Fin m → Fin N,
        Y ^ p * (ρ ^ (Finset.univ.image α).card + β ^ p * (p : ℝ) ^ (2 * p)) * (e / p) ^ p := by
          refine Finset.sum_le_sum fun α _ => (h2 α).trans ?_
          gcongr
          · exact_mod_cast hp1
          · exact hS α
      _ = Y ^ p * (e / p) ^ p * (∑ α : Bool × Fin m → Fin N, ρ ^ (Finset.univ.image α).card +
          (N : ℝ) ^ p * (β ^ p * (p : ℝ) ^ (2 * p))) := by
          have h : ∀ α : Bool × Fin m → Fin N, Y ^ p * (ρ ^ (Finset.univ.image α).card +
              β ^ p * (p : ℝ) ^ (2 * p)) * (e / p) ^ p = Y ^ p * (e / p) ^ p *
              ρ ^ (Finset.univ.image α).card + Y ^ p * (e / p) ^ p *
              (β ^ p * (p : ℝ) ^ (2 * p)) := fun α => by ring
          rw [Finset.sum_congr rfl fun α _ => h α, Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hcard,
            nsmul_eq_mul]
          push_cast
          ring
      _ ≤ _ := by
          gcongr
          exact sum_pow_card_image_le hcard (sq_nonneg _)
  have h4 : ∫ ω in Ξ, ‖W ω‖ ^ p ∂L.law ≤
      (2 * Real.exp 1 * max 1 (C6 ^ 2) * (p : ℝ) ^ 4 * Y * (X ^ 2 + (N : ℝ)⁻¹)) ^ p :=
    h1.trans ((mul_le_mul_of_nonneg_left h3 (by positivity)).trans
      (moment_arith hN hp2 hY hβ0 hβ))
  calc ∫⁻ ω in Ξ, ‖(N : ℂ)⁻¹ * ∑ i, Z ∅ i ω‖ₑ ^ p ∂L.law =
      ENNReal.ofReal (∫ ω in Ξ, ‖W ω‖ ^ p ∂L.law) := by
        rw [ofReal_integral_eq_lintegral_ofReal hWint (ae_of_all _ fun ω => by positivity)]
        refine lintegral_congr fun ω => ?_
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ ≤ _ := ENNReal.ofReal_le_ofReal h4

/-! ### Theorem 5.6 -/

/-- Theorem 5.6 of [15] (abstract decoupling lemma). `Z U i` is `Z_i^{[U]}`; (5.6) is used at
`r = p`, (5.9) at `r = 2`; the saturations `[Ξ]_i` are measurable and (5.10) holds pointwise
on `Ξ`. -/
theorem decoupling (C6 C9 C10 c11 : ℝ) (hc11 : 0 < c11) :
    ∃ C > 0, ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (L : EntryLaws N)
      (Z : Finset (Fin N) → Fin N → Entries N → ℂ) (Ξ : Set (Entries N)) (p : ℕ) (X Y : ℝ),
      L.IsProb → MeasurableSet Ξ → (∀ i, MeasurableSet (rowSat {i} Ξ)) → Even p → 2 ≤ p →
      p ≤ N → 0 ≤ X → 1 ≤ Y → X ≤ 1 / ((p : ℝ) ^ 5 * Real.log N) →
      (∀ U i, i ∉ U → Integrable (Z U i) L.law ∧ RowIndep U (Z U i) ∧
        ∀ᵐ ω ∂L.law, L.rowsExp {i} (Z U i) ω = 0) →
      (∀ S U i, U ⊆ S → i ∉ S → S.card ≤ p →
        ∫⁻ ω in Ξ, ‖gradedTerm (fun V => Z V i) S U ω‖ₑ ^ p ∂L.law ≤
          ENNReal.ofReal ((Y * (C6 * X * (U.card + 1)) ^ (U.card + 1)) ^ p)) →
      (∀ S U i, U ⊆ S → i ∉ S → S.card ≤ p →
        ∫⁻ ω in rowSat {i} Ξ, ‖gradedTerm (fun V => Z V i) S U ω‖ₑ ^ 2 ∂L.law ≤
          ENNReal.ofReal ((N : ℝ) ^ (C9 * p))) →
      (∀ U i, i ∉ U → ∀ ω ∈ Ξ, ‖Z U i ω‖ ≤ Y * (N : ℝ) ^ C10) →
      L.law Ξᶜ ≤ ENNReal.ofReal (Real.exp (-c11 * Real.log N ^ ((3 : ℝ) / 2) * p)) →
      L.law {ω | ω ∈ Ξ ∧ (p : ℝ) ^ 12 * Y * (X ^ 2 + (N : ℝ)⁻¹) ≤
        ‖(N : ℂ)⁻¹ * ∑ i, Z ∅ i ω‖} ≤ ENNReal.ofReal ((C / p) ^ p) := by
  set C1 := max 1 (C6 ^ 2) with hC1
  set M := max (max 1 |C6|) ((2 * (2 + |C10| + |C9| / 2) / c11) ^ 2) with hM
  refine ⟨6 * C1, by positivity, ⌈Real.exp M⌉₊, ?_⟩
  intro N hN L Z Ξ p X Y hL hΞ hsat hpe hp2 hpN hX hY hX5 hi hii hiii hiv hv
  have := EntryLaws.isProbabilityMeasure_law hL
  have hNexp : Real.exp M ≤ N := Nat.ceil_le.mp hN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos M) hNexp
  have hN1 : 1 ≤ N := by omega
  have hlog : M ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    exact hNexp
  set Lg := Real.log N with hLg
  have hL1 : 1 ≤ Lg := ((le_max_left _ _).trans (le_max_left _ _)).trans hlog
  have hLC6 : |C6| ≤ Lg := ((le_max_right _ _).trans (le_max_left _ _)).trans hlog
  have hLA : (2 * (2 + |C10| + |C9| / 2) / c11) ^ 2 ≤ Lg := (le_max_right _ _).trans hlog
  have hp1 : (1 : ℝ) ≤ p := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  -- (5.7) gives `|C6| X p² ≤ 1`
  have hr : |C6| * X * (p : ℝ) ^ 2 ≤ 1 := by
    have hpos : 0 < (p : ℝ) ^ 5 * Lg := by positivity
    have h1 : X * ((p : ℝ) ^ 5 * Lg) ≤ 1 := by
      rw [div_eq_mul_inv, one_mul] at hX5
      have := mul_le_mul_of_nonneg_right hX5 hpos.le
      rwa [inv_mul_cancel₀ hpos.ne'] at this
    have h2 : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ 5 := pow_le_pow_right₀ hp1 (by norm_num)
    calc |C6| * X * (p : ℝ) ^ 2 ≤ Lg * X * (p : ℝ) ^ 5 := by gcongr
      _ = X * ((p : ℝ) ^ 5 * Lg) := by ring
      _ ≤ 1 := h1
  -- (5.11) gives `betaN ≤ N⁻¹`
  have hβ : betaN N C9 C10 c11 ≤ (N : ℝ)⁻¹ := by
    unfold betaN
    have hsq : 2 * (2 + |C10| + |C9| / 2) / c11 ≤ Real.sqrt Lg := by
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * (2 + |C10| + |C9| / 2) / c11)]
      exact Real.sqrt_le_sqrt hLA
    have h32 : Lg ^ ((3 : ℝ) / 2) = Lg * Real.sqrt Lg := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one,
        Real.sqrt_eq_rpow]
    have hkey : 2 * (2 + |C10| + |C9| / 2) * Lg ≤ c11 * Real.sqrt Lg * Lg := by
      have h1 := mul_le_mul_of_nonneg_left hsq hc11.le
      rw [mul_div_cancel₀ _ hc11.ne'] at h1
      exact mul_le_mul_of_nonneg_right h1 (by linarith)
    have e1 : (N : ℝ) ^ |C10| = Real.exp (Lg * |C10|) := Real.rpow_def_of_pos hN0 _
    have e2 : (N : ℝ) ^ (|C9| / 2) = Real.exp (Lg * (|C9| / 2)) := Real.rpow_def_of_pos hN0 _
    have e3 : (N : ℝ)⁻¹ = Real.exp (-Lg) := by rw [Real.exp_neg, hLg, Real.exp_log hN0]
    have e4 : (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    rw [e1, e2, e3, h32]
    calc 2 * Real.exp (Lg * |C10|) * Real.exp (Lg * (|C9| / 2)) *
        Real.exp (-c11 * (Lg * Real.sqrt Lg) / 2) = Real.exp (Real.log 2 + Lg * |C10| +
          Lg * (|C9| / 2) + -c11 * (Lg * Real.sqrt Lg) / 2) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_add, ← e4]
      _ ≤ Real.exp (-Lg) := by
          refine Real.exp_le_exp.mpr ?_
          nlinarith
  -- (5.19), then Markov's inequality
  have hmom := setLIntegral_enorm_pow_le hL hpe hp2 hN1 hΞ hsat hX hY hr hβ hi hii hiii hiv hv
  set t := (p : ℝ) ^ 12 * Y * (X ^ 2 + (N : ℝ)⁻¹) with ht
  have ht0 : 0 < t := by
    have : 0 < Y := by linarith
    positivity
  set W : Entries N → ℂ := fun ω => (N : ℂ)⁻¹ * ∑ i, Z ∅ i ω with hW
  have hWm : AEStronglyMeasurable W L.law :=
    ((integrable_finsetSum _ fun i _ => (hi ∅ i (Finset.notMem_empty i)).1).const_mul
      _).aestronglyMeasurable
  have hf : AEMeasurable (Ξ.indicator fun ω => ‖W ω‖ₑ ^ p) L.law :=
    (hWm.enorm.pow_const p).indicator hΞ
  have hmk := mul_meas_ge_le_lintegral₀ hf (ENNReal.ofReal (t ^ p))
  rw [lintegral_indicator hΞ] at hmk
  have hsub : {ω | ω ∈ Ξ ∧ t ≤ ‖W ω‖} ⊆
      {ω | ENNReal.ofReal (t ^ p) ≤ Ξ.indicator (fun ω => ‖W ω‖ₑ ^ p) ω} := by
    rintro ω ⟨hω, htω⟩
    simp only [Set.mem_ofPred_eq, Set.indicator_of_mem hω]
    rw [ENNReal.ofReal_pow ht0.le, ← ofReal_norm]
    gcongr
  have htp : 0 < t ^ p := pow_pos ht0 p
  have h1 : ENNReal.ofReal (t ^ p) * L.law {ω | ω ∈ Ξ ∧ t ≤ ‖W ω‖} ≤ ENNReal.ofReal
      ((2 * Real.exp 1 * C1 * (p : ℝ) ^ 4 * Y * (X ^ 2 + (N : ℝ)⁻¹)) ^ p) := by
    calc ENNReal.ofReal (t ^ p) * L.law {ω | ω ∈ Ξ ∧ t ≤ ‖W ω‖} ≤ ENNReal.ofReal (t ^ p) *
        L.law {ω | ENNReal.ofReal (t ^ p) ≤ Ξ.indicator (fun ω => ‖W ω‖ₑ ^ p) ω} := by
          gcongr
      _ ≤ _ := hmk.trans hmom
  have h2 : L.law {ω | ω ∈ Ξ ∧ t ≤ ‖W ω‖} ≤ ENNReal.ofReal
      ((2 * Real.exp 1 * C1 * (p : ℝ) ^ 4 * Y * (X ^ 2 + (N : ℝ)⁻¹)) ^ p / t ^ p) := by
    rw [ENNReal.ofReal_div_of_pos htp, ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.ofReal_pos.mpr htp).ne') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact h1
  refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [← div_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ p
  have hp0 : (0 : ℝ) < p := by linarith
  have hQ : 0 < Y * (X ^ 2 + (N : ℝ)⁻¹) := by
    have : 0 < Y := by linarith
    positivity
  rw [div_le_div_iff₀ ht0 hp0]
  have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hC10 : 0 ≤ C1 := by positivity
  have h5 : (p : ℝ) ^ 5 ≤ (p : ℝ) ^ 12 := pow_le_pow_right₀ hp1 (by norm_num)
  calc 2 * Real.exp 1 * C1 * (p : ℝ) ^ 4 * Y * (X ^ 2 + (N : ℝ)⁻¹) * p =
      (2 * Real.exp 1) * (C1 * (p : ℝ) ^ 5 * (Y * (X ^ 2 + (N : ℝ)⁻¹))) := by ring
    _ ≤ 6 * (C1 * (p : ℝ) ^ 12 * (Y * (X ^ 2 + (N : ℝ)⁻¹))) := by
        refine mul_le_mul (by linarith) ?_ (by positivity) (by norm_num)
        gcongr
    _ = 6 * C1 * t := by rw [ht]; ring

/-! ### A compiled instance at `N = 4`

The entry laws are `radLaws 4` (off-diagonal entries `±1/2`, diagonal entries `±2^{-1/2}`),
`Z_i^{[U]} = sin h_ii − E sin h_ii` for every `U ∌ i`, and `Ξ = {|h_ii| ≤ 1 for all i}`, a closed
proper subset of full measure; `p = 2`, `X = 1/50`, `Y = 1`, `C6 = 100`, `C9 = C10 = c11 = 1`. -/

/-- `Z_i^{[U]} = sin h_ii − E sin h_ii` (independent of `U`). -/
private def exZ : Finset (Fin 4) → Fin 4 → Entries 4 → ℂ := fun _ i ω =>
  ((Real.sin (ω.1 i) : ℝ) : ℂ) - ∫ ω', ((Real.sin (ω'.1 i) : ℝ) : ℂ) ∂(radLaws 4).law

/-- `Ξ = {|h_ii| ≤ 1 for all i}`. -/
private def exΞ : Set (Entries 4) := {ω | ∀ i, |ω.1 i| ≤ 1}

private lemma radLaws_four_isProb : (radLaws 4).IsProb :=
  (radLaws_isGenWigner (by norm_num)).isProb

private lemma integrable_sin_diag (i : Fin 4) :
    Integrable (fun ω : Entries 4 => ((Real.sin (ω.1 i) : ℝ) : ℂ)) (radLaws 4).law := by
  have := EntryLaws.isProbabilityMeasure_law radLaws_four_isProb
  refine Integrable.of_bound (by fun_prop : Continuous fun ω : Entries 4 =>
    ((Real.sin (ω.1 i) : ℝ) : ℂ)).aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_sin_le_one _

private lemma norm_exZ_le (U : Finset (Fin 4)) (i : Fin 4) (ω : Entries 4) :
    ‖exZ U i ω‖ ≤ 2 := by
  have := EntryLaws.isProbabilityMeasure_law radLaws_four_isProb
  have h1 : ‖((Real.sin (ω.1 i) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  have h2 : ‖∫ ω', ((Real.sin (ω'.1 i) : ℝ) : ℂ) ∂(radLaws 4).law‖ ≤ 1 := by
    have h := norm_integral_le_of_norm_le_const (μ := (radLaws 4).law) (C := 1)
      (f := fun ω' : Entries 4 => ((Real.sin (ω'.1 i) : ℝ) : ℂ)) (ae_of_all _ fun ω' => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact Real.abs_sin_le_one _)
    rwa [probReal_univ, mul_one] at h
  calc ‖exZ U i ω‖ ≤ ‖((Real.sin (ω.1 i) : ℝ) : ℂ)‖ +
      ‖∫ ω', ((Real.sin (ω'.1 i) : ℝ) : ℂ) ∂(radLaws 4).law‖ := norm_sub_le _ _
    _ ≤ 2 := by linarith

/-- A graded term of a family that does not depend on the set is the family itself for
`U = ∅` and zero otherwise. -/
private lemma gradedTerm_const {N : ℕ} (f : Entries N → ℂ) (S U : Finset (Fin N)) :
    gradedTerm (fun _ => f) S U = if U = ∅ then f else 0 := by
  unfold gradedTerm
  rw [← Finset.sum_smul, Finset.sum_powerset_neg_one_pow_card]
  split_ifs <;> simp

private lemma norm_gradedTerm_exZ_le (S U : Finset (Fin 4)) (i : Fin 4) (ω : Entries 4) :
    ‖gradedTerm (fun V => exZ V i) S U ω‖ ≤ 2 := by
  change ‖gradedTerm (fun _ => exZ ∅ i) S U ω‖ ≤ 2
  rw [gradedTerm_const]
  split_ifs
  · exact norm_exZ_le ∅ i ω
  · simp

private lemma lintegral_gradedTerm_exZ_le (A : Set (Entries 4)) (S U : Finset (Fin 4))
    (i : Fin 4) (k : ℕ) :
    ∫⁻ ω in A, ‖gradedTerm (fun V => exZ V i) S U ω‖ₑ ^ k ∂(radLaws 4).law ≤
      ENNReal.ofReal (2 ^ k) := by
  have := EntryLaws.isProbabilityMeasure_law radLaws_four_isProb
  calc ∫⁻ ω in A, ‖gradedTerm (fun V => exZ V i) S U ω‖ₑ ^ k ∂(radLaws 4).law ≤
      ∫⁻ _ in A, ENNReal.ofReal 2 ^ k ∂(radLaws 4).law := by
        refine lintegral_mono fun ω => ?_
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (norm_gradedTerm_exZ_le S U i ω)
    _ = ENNReal.ofReal 2 ^ k * (radLaws 4).law A := by
        rw [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal 2 ^ k * 1 := by gcongr; exact prob_le_one
    _ = ENNReal.ofReal (2 ^ k) := by rw [mul_one, ENNReal.ofReal_pow (by norm_num)]

/-- The diagonal entries of `radLaws 4` are `±2^{-1/2}`, inside `[-1, 1]`. -/
private lemma radLaws_four_diag_tail (i : Fin 4) : (radLaws 4).diag i {x | 1 < |x|} = 0 := by
  have hm : MeasurableSet {x : ℝ | 1 < |x|} := measurableSet_lt measurable_const measurable_abs
  have h4 : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h20 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  simp only [radLaws, ofIID]
  rw [Measure.map_apply (by fun_prop) hm, Measure.map_apply (by fun_prop)
    (hm.preimage (by fun_prop))]
  have hpre : (fun x : ℝ => Real.sqrt 2 * x) ⁻¹'
      ((fun x : ℝ => (Real.sqrt ((4 : ℕ) : ℝ))⁻¹ * x) ⁻¹' {x | 1 < |x|}) =
      {x : ℝ | 2 < |Real.sqrt 2 * x|} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, h4, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
    constructor <;> intro h <;> linarith
  rw [hpre]
  simp [rademacher, Measure.smul_apply, Measure.add_apply, abs_of_nonneg h20]

private lemma isClosed_exΞ : IsClosed exΞ := by
  have : exΞ = ⋂ i, {ω : Entries 4 | |ω.1 i| ≤ 1} := by
    ext ω
    simp [exΞ]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const

private lemma law_exΞ_compl : (radLaws 4).law exΞᶜ = 0 := by
  have hsub : exΞᶜ ⊆ ⋃ i : Fin 4, Prod.fst ⁻¹' (Function.eval i ⁻¹' {x : ℝ | 1 < |x|}) := by
    intro ω hω
    simp only [exΞ, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨i, hi⟩ := hω
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have h1 := radLaws_four_isProb.diag
  have h2 := radLaws_four_isProb.off
  refine measure_mono_null hsub (measure_iUnion_null fun i => ?_)
  rw [← Set.prod_univ]
  change ((Measure.pi (radLaws 4).diag).prod (Measure.pi (radLaws 4).off))
    ((Function.eval i ⁻¹' {x : ℝ | 1 < |x|}) ×ˢ Set.univ) = 0
  rw [Measure.prod_prod, Measure.pi_eval_preimage_null _ (radLaws_four_diag_tail i), zero_mul]

private lemma exZ_hyp (U : Finset (Fin 4)) (i : Fin 4) (hi : i ∉ U) :
    Integrable (exZ U i) (radLaws 4).law ∧ RowIndep U (exZ U i) ∧
      ∀ᵐ ω ∂(radLaws 4).law, (radLaws 4).rowsExp {i} (exZ U i) ω = 0 := by
  have := EntryLaws.isProbabilityMeasure_law radLaws_four_isProb
  refine ⟨(integrable_sin_diag i).sub (integrable_const _), fun ω => ?_, ae_of_all _ fun ω => ?_⟩
  · simp [exZ, zeroEntries, rowsMix, hi]
  · simp only [EntryLaws.rowsExp, exZ]
    have h : ∀ ω' : Entries 4, (rowsMix {i} ω ω').1 i = ω'.1 i := fun ω' => by simp [rowsMix]
    simp only [h]
    rw [integral_sub (integrable_sin_diag i) (integrable_const _), integral_const, probReal_univ,
      one_smul, sub_self]

/-- The hypotheses of `decoupling` at the instance above, and its nondegeneracy. -/
private lemma exHyps : (radLaws 4).IsProb ∧ MeasurableSet exΞ ∧
    (∀ i, MeasurableSet (rowSat {i} exΞ)) ∧
    Even 2 ∧ 2 ≤ 2 ∧ 2 ≤ 4 ∧ (0 : ℝ) ≤ 1 / 50 ∧ (1 : ℝ) ≤ 1 ∧
    (1 / 50 : ℝ) ≤ 1 / (((2 : ℕ) : ℝ) ^ 5 * Real.log ((4 : ℕ) : ℝ)) ∧
    (∀ U i, i ∉ U → Integrable (exZ U i) (radLaws 4).law ∧ RowIndep U (exZ U i) ∧
      ∀ᵐ ω ∂(radLaws 4).law, (radLaws 4).rowsExp {i} (exZ U i) ω = 0) ∧
    (∀ S U i, U ⊆ S → i ∉ S → S.card ≤ 2 →
      ∫⁻ ω in exΞ, ‖gradedTerm (fun V => exZ V i) S U ω‖ₑ ^ 2 ∂(radLaws 4).law ≤
        ENNReal.ofReal ((1 * (100 * (1 / 50) * (U.card + 1)) ^ (U.card + 1)) ^ 2)) ∧
    (∀ S U i, U ⊆ S → i ∉ S → S.card ≤ 2 →
      ∫⁻ ω in rowSat {i} exΞ, ‖gradedTerm (fun V => exZ V i) S U ω‖ₑ ^ 2 ∂(radLaws 4).law ≤
        ENNReal.ofReal (((4 : ℕ) : ℝ) ^ (1 * ((2 : ℕ) : ℝ)))) ∧
    (∀ U i, i ∉ U → ∀ ω ∈ exΞ, ‖exZ U i ω‖ ≤ 1 * ((4 : ℕ) : ℝ) ^ (1 : ℝ)) ∧
    (radLaws 4).law exΞᶜ ≤
      ENNReal.ofReal (Real.exp (-1 * Real.log ((4 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ((2 : ℕ) : ℝ))) ∧
    exΞ ≠ Set.univ ∧ ∃ ω ∈ exΞ, exZ ∅ 0 ω ≠ 0 := by
  have hlog4 : Real.log ((4 : ℕ) : ℝ) < 1.39 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  have hlog4' : 0 < Real.log ((4 : ℕ) : ℝ) := Real.log_pos (by norm_num)
  refine ⟨radLaws_four_isProb, isClosed_exΞ.measurableSet,
    fun i => measurableSet_rowSat_of_isClosed {i} isClosed_exΞ, even_two, le_rfl,
    by norm_num, by norm_num, le_rfl, ?_, exZ_hyp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine one_div_le_one_div_of_le (by positivity) ?_
    push_cast
    linarith
  · intro S U i _ _ _
    by_cases hU : U = ∅
    · subst hU
      refine (lintegral_gradedTerm_exZ_le _ _ _ _ _).trans (ENNReal.ofReal_le_ofReal ?_)
      norm_num
    · have h0 : gradedTerm (fun V => exZ V i) S U = 0 := by
        change gradedTerm (fun _ => exZ ∅ i) S U = 0
        rw [gradedTerm_const]
        simp [hU]
      simp [h0]
  · intro S U i _ _ _
    refine (lintegral_gradedTerm_exZ_le _ _ _ _ _).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [one_mul, Real.rpow_natCast]
    norm_num
  · intro U i _ ω _
    rw [Real.rpow_one]
    have := norm_exZ_le U i ω
    push_cast
    linarith
  · rw [law_exΞ_compl]
    exact zero_le
  · intro h
    have hmem : ((fun _ => (2 : ℝ)), (0 : OffDiag 4 → ℝ)) ∈ exΞ := h ▸ Set.mem_univ _
    have h0 : |(2 : ℝ)| ≤ 1 := hmem 0
    norm_num at h0
  · by_contra hcon
    push Not at hcon
    have h1 := hcon ((fun _ => (1 : ℝ)), 0) (fun i => by simp)
    have h2 := hcon ((fun _ => (-1 : ℝ)), 0) (fun i => by simp)
    simp only [exZ, sub_eq_zero] at h1 h2
    rw [← h2, Real.sin_neg, Complex.ofReal_inj] at h1
    have hs : 0 < Real.sin 1 := Real.sin_pos_of_pos_of_lt_pi one_pos
      (lt_trans (by norm_num) Real.pi_gt_three)
    linarith

/-- At `N = 4`, `p = 2`, `X = 1/50`, `Y = 1`, `C6 = 100`, `C9 = C10 = c11 = 1`, every hypothesis
of `decoupling` holds for `radLaws 4`, `Z_i^{[U]} = sin h_ii − E sin h_ii` and
`Ξ = {|h_ii| ≤ 1}`; moreover `Ξ` is a proper subset and `Z_0^{[∅]}` is not identically zero on
`Ξ`. -/
example : (radLaws 4).IsProb ∧ MeasurableSet exΞ ∧ (∀ i, MeasurableSet (rowSat {i} exΞ)) ∧
    Even 2 ∧ 2 ≤ 2 ∧ 2 ≤ 4 ∧ (0 : ℝ) ≤ 1 / 50 ∧ (1 : ℝ) ≤ 1 ∧
    (1 / 50 : ℝ) ≤ 1 / (((2 : ℕ) : ℝ) ^ 5 * Real.log ((4 : ℕ) : ℝ)) ∧
    (∀ U i, i ∉ U → Integrable (exZ U i) (radLaws 4).law ∧ RowIndep U (exZ U i) ∧
      ∀ᵐ ω ∂(radLaws 4).law, (radLaws 4).rowsExp {i} (exZ U i) ω = 0) ∧
    (∀ S U i, U ⊆ S → i ∉ S → S.card ≤ 2 →
      ∫⁻ ω in exΞ, ‖gradedTerm (fun V => exZ V i) S U ω‖ₑ ^ 2 ∂(radLaws 4).law ≤
        ENNReal.ofReal ((1 * (100 * (1 / 50) * (U.card + 1)) ^ (U.card + 1)) ^ 2)) ∧
    (∀ S U i, U ⊆ S → i ∉ S → S.card ≤ 2 →
      ∫⁻ ω in rowSat {i} exΞ, ‖gradedTerm (fun V => exZ V i) S U ω‖ₑ ^ 2 ∂(radLaws 4).law ≤
        ENNReal.ofReal (((4 : ℕ) : ℝ) ^ (1 * ((2 : ℕ) : ℝ)))) ∧
    (∀ U i, i ∉ U → ∀ ω ∈ exΞ, ‖exZ U i ω‖ ≤ 1 * ((4 : ℕ) : ℝ) ^ (1 : ℝ)) ∧
    (radLaws 4).law exΞᶜ ≤
      ENNReal.ofReal (Real.exp (-1 * Real.log ((4 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ((2 : ℕ) : ℝ))) ∧
    exΞ ≠ Set.univ ∧ ∃ ω ∈ exΞ, exZ ∅ 0 ω ≠ 0 :=
  exHyps

/-- The instance above has the exact shape of the hypotheses of `decoupling` at
`C6 = 100`, `C9 = C10 = c11 = 1`: whenever the threshold `N0` of `decoupling` is at most `4`, it
yields (5.12) for this instance. -/
example : ∃ C > 0, ∃ N0 : ℕ, N0 ≤ 4 →
    (radLaws 4).law {ω | ω ∈ exΞ ∧ ((2 : ℕ) : ℝ) ^ 12 * 1 * ((1 / 50) ^ 2 + ((4 : ℕ) : ℝ)⁻¹) ≤
      ‖((4 : ℕ) : ℂ)⁻¹ * ∑ i, exZ ∅ i ω‖} ≤ ENNReal.ofReal ((C / ((2 : ℕ) : ℝ)) ^ 2) := by
  obtain ⟨C, hC, N0, h⟩ := decoupling 100 1 1 1 one_pos
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, -⟩ := exHyps
  exact ⟨C, hC, N0, fun hN0 => h 4 hN0 (radLaws 4) exZ exΞ 2 (1 / 50) 1 h1 h2 h3 h4 h5 h6 h7 h8
    h9 h10 h11 h12 h13 h14⟩

#print axioms decoupling

end WEdgeNS
