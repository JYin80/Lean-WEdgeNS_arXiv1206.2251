import WEdgeNS.LocalLaw.Class
import WEdgeNS.Resolvent.Minors

/-!
# The entry law as a product measure, rows, partial expectations and graded terms
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- The entry law as a single product measure over `Fin N ⊕ OffDiag N`. -/
def EntryLaws.lawPi {N : ℕ} (L : EntryLaws N) : Measure (Fin N ⊕ OffDiag N → ℝ) :=
  Measure.pi (fun e => Sum.elim L.diag L.off e)

/-- The entry law is the image of `lawPi`. -/
theorem EntryLaws.law_eq_map_lawPi {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) :
    L.law = L.lawPi.map (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ)) := by
  have h1 := hL.diag
  have h2 := hL.off
  have h : ∀ e : Fin N ⊕ OffDiag N, SigmaFinite (Sum.elim L.diag L.off e) := by
    rintro (i | p)
    · have := h1 i; change SigmaFinite (L.diag i); infer_instance
    · have := h2 p; change SigmaFinite (L.off p); infer_instance
  exact (measurePreserving_sumPiEquivProdPi (X := fun _ : Fin N ⊕ OffDiag N => ℝ)
    (Sum.elim L.diag L.off)).map_eq.symm

/-- The entries are independent under `lawPi`. -/
theorem EntryLaws.iIndepFun_lawPi {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) :
    iIndepFun (fun (e : Fin N ⊕ OffDiag N) (x : Fin N ⊕ OffDiag N → ℝ) => x e) L.lawPi := by
  have h1 := hL.diag
  have h2 := hL.off
  have h : ∀ e : Fin N ⊕ OffDiag N, IsProbabilityMeasure (Sum.elim L.diag L.off e) := by
    rintro (i | p)
    · exact h1 i
    · exact h2 p
  exact iIndepFun_pi (X := fun _ => (id : ℝ → ℝ)) (μ := fun e => Sum.elim L.diag L.off e)
    (fun _ => aemeasurable_id)

/-- Resolvent entries are continuous in the entries off the real axis. -/
theorem continuous_resolventC_symOfEntries {N : ℕ} {z : ℂ} (hz : z.im ≠ 0) (i j : Fin N) :
    Continuous (fun ω : Entries N => resolventC (symOfEntries ω) z i j) := by
  have hsym : Continuous (fun ω : Entries N => symOfEntries ω) := by
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
  have hM : Continuous (fun ω : Entries N => (symOfEntries ω).map (fun x : ℝ => (x : ℂ)) -
      z • (1 : Matrix (Fin N) (Fin N) ℂ)) :=
    (hsym.matrix_map Complex.continuous_ofReal).sub continuous_const
  have hdet : ∀ ω : Entries N, ((symOfEntries ω).map (fun x : ℝ => (x : ℂ)) -
      z • (1 : Matrix (Fin N) (Fin N) ℂ)).det ≠ 0 := by
    intro ω
    have hH := symOfEntries_isHermitian ω
    have hne : ∀ α, (hH.eigenvalues α : ℂ) ≠ z := by
      intro α h
      apply hz
      rw [← h, Complex.ofReal_im]
    have h1 := resolventC_mul_eq_one hH hne
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_one] at h2
    exact left_ne_zero_of_mul_eq_one h2
  have hinv : (fun ω : Entries N => resolventC (symOfEntries ω) z) = fun ω =>
      (((symOfEntries ω).map (fun x : ℝ => (x : ℂ)) -
        z • (1 : Matrix (Fin N) (Fin N) ℂ)).det)⁻¹ •
      ((symOfEntries ω).map (fun x : ℝ => (x : ℂ)) -
        z • (1 : Matrix (Fin N) (Fin N) ℂ)).adjugate := by
    funext ω
    unfold resolventC
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  have : Continuous (fun ω : Entries N => resolventC (symOfEntries ω) z) := by
    rw [hinv]
    exact (hM.matrix_det.inv₀ hdet).smul hM.matrix_adjugate
  exact this.matrix_elem i j

/-- The point whose entries in the rows and columns `T` (`h_kl` with `k ∈ T` or `l ∈ T`)
are those of `ω'`, all other entries those of `ω`. -/
def rowsMix {N : ℕ} (T : Finset (Fin N)) (ω ω' : Entries N) : Entries N :=
  (fun k => if k ∈ T then ω'.1 k else ω.1 k,
   fun p => if p.1.1 ∈ T ∨ p.1.2 ∈ T then ω'.2 p else ω.2 p)

/-- `π_T` of (3.10) of [15]: the entries in the rows and columns `T` set to zero. -/
def zeroEntries {N : ℕ} (T : Finset (Fin N)) (ω : Entries N) : Entries N := rowsMix T ω 0

/-- `π_T` on entries is the minor `H^{(T)}` (Definition 3.3 and Remark 5.4 of [15]). -/
theorem symOfEntries_zeroEntries {N : ℕ} (T : Finset (Fin N)) (ω : Entries N) :
    symOfEntries (zeroEntries T ω) = zeroRC T (symOfEntries ω) := by
  funext i j
  by_cases h : i = j
  · subst h
    simp [symOfEntries, zeroEntries, rowsMix, zeroRC]
  · by_cases h' : i < j
    · simp [symOfEntries, zeroEntries, rowsMix, zeroRC, h, h']
    · simp [symOfEntries, zeroEntries, rowsMix, zeroRC, h, h', or_comm]

/-- `π_U ∘ π_V = π_{U ∪ V}` (Remark 5.3 of [15]). -/
theorem zeroEntries_zeroEntries {N : ℕ} (U V : Finset (Fin N)) (ω : Entries N) :
    zeroEntries U (zeroEntries V ω) = zeroEntries (U ∪ V) ω := by
  refine Prod.ext (funext fun k => ?_) (funext fun p => ?_)
  · by_cases hU : k ∈ U <;> by_cases hV : k ∈ V <;> simp [zeroEntries, rowsMix, hU, hV]
  · by_cases hU : p.1.1 ∈ U ∨ p.1.2 ∈ U <;> by_cases hV : p.1.1 ∈ V ∨ p.1.2 ∈ V <;>
      simp [zeroEntries, rowsMix, hU, hV] <;> tauto

private lemma continuous_rowsMix {N : ℕ} (T : Finset (Fin N)) :
    Continuous (fun q : Entries N × Entries N => rowsMix T q.1 q.2) := by
  refine Continuous.prodMk (continuous_pi fun k => ?_) (continuous_pi fun p => ?_)
  · by_cases hk : k ∈ T
    · simp only [hk, ite_true]
      exact ((continuous_apply k).comp continuous_fst).comp continuous_snd
    · simp only [hk, ite_false]
      exact ((continuous_apply k).comp continuous_fst).comp continuous_fst
  · by_cases hp : p.1.1 ∈ T ∨ p.1.2 ∈ T
    · simp only [hp, ite_true]
      exact ((continuous_apply p).comp continuous_snd).comp continuous_snd
    · simp only [hp, ite_false]
      exact ((continuous_apply p).comp continuous_snd).comp continuous_fst

private lemma continuous_zeroEntries {N : ℕ} (T : Finset (Fin N)) :
    Continuous (zeroEntries T : Entries N → Entries N) :=
  (continuous_rowsMix T).comp (continuous_id.prodMk continuous_const)

/-- Definition 5.5 of [15]: `X` is independent of the rows `T`, i.e. `X = X ∘ π_T`. -/
def RowIndep {N : ℕ} {α : Type*} (T : Finset (Fin N)) (X : Entries N → α) : Prop :=
  ∀ ω, X (zeroEntries T ω) = X ω

private lemma zeroEntries_rowsMix {N : ℕ} (T : Finset (Fin N)) (ω ω' : Entries N) :
    zeroEntries T (rowsMix T ω ω') = zeroEntries T ω := by
  refine Prod.ext (funext fun k => ?_) (funext fun p => ?_)
  · by_cases hk : k ∈ T <;> simp [zeroEntries, rowsMix, hk]
  · by_cases hp : p.1.1 ∈ T ∨ p.1.2 ∈ T <;> simp [zeroEntries, rowsMix, hp]

private lemma rowsMix_zeroEntries {N : ℕ} (T : Finset (Fin N)) (ω ω' : Entries N) :
    rowsMix T (zeroEntries T ω) ω' = rowsMix T ω ω' := by
  refine Prod.ext (funext fun k => ?_) (funext fun p => ?_)
  · by_cases hk : k ∈ T <;> simp [zeroEntries, rowsMix, hk]
  · by_cases hp : p.1.1 ∈ T ∨ p.1.2 ∈ T <;> simp [zeroEntries, rowsMix, hp]

theorem rowIndep_iff_rowsMix {N : ℕ} {α : Type*} {T : Finset (Fin N)} {X : Entries N → α} :
    RowIndep T X ↔ ∀ ω ω', X (rowsMix T ω ω') = X ω := by
  constructor
  · intro h ω ω'
    rw [← h (rowsMix T ω ω'), zeroEntries_rowsMix, h ω]
  · intro h ω
    exact h ω 0

/-- Entries outside the rows `T` are independent of `T`. -/
theorem rowIndep_symOfEntries_apply {N : ℕ} {T : Finset (Fin N)} {k l : Fin N} (hk : k ∉ T)
    (hl : l ∉ T) : RowIndep T (fun ω => symOfEntries ω k l) := by
  intro ω
  change symOfEntries (zeroEntries T ω) k l = symOfEntries ω k l
  rw [symOfEntries_zeroEntries]
  simp [zeroRC, hk, hl]

/-- Resolvent entries of a minor `H^{(V)}` are independent of the rows `T ⊆ V`. -/
theorem rowIndep_resolventC_zeroRC {N : ℕ} {T V : Finset (Fin N)} (hTV : T ⊆ V) (z : ℂ)
    (i j : Fin N) : RowIndep T (fun ω => resolventC (zeroRC V (symOfEntries ω)) z i j) := by
  intro ω
  change resolventC (zeroRC V (symOfEntries (zeroEntries T ω))) z i j =
    resolventC (zeroRC V (symOfEntries ω)) z i j
  rw [symOfEntries_zeroEntries, zeroRC_zeroRC, Finset.union_eq_left.mpr hTV]

/-- Taking the coordinates flagged by `b` from the second factor and the others from the first
preserves a product of probability measures. -/
private lemma map_mix_pi {E : Type*} [Fintype E] (μ : E → Measure ℝ)
    [∀ e, IsProbabilityMeasure (μ e)] (b : E → Bool) :
    ((Measure.pi μ).prod (Measure.pi μ)).map
      (fun q : (E → ℝ) × (E → ℝ) => fun e => if b e then q.2 e else q.1 e) = Measure.pi μ := by
  have hm : Measurable (fun q : (E → ℝ) × (E → ℝ) => fun e => if b e then q.2 e else q.1 e) := by
    refine measurable_pi_iff.mpr fun e => ?_
    by_cases h : b e = true
    · simp only [h, ite_true]
      exact (measurable_pi_apply e).comp measurable_snd
    · simp only [h]
      exact (measurable_pi_apply e).comp measurable_fst
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun q : (E → ℝ) × (E → ℝ) => fun e => if b e then q.2 e else q.1 e) ⁻¹'
      (Set.univ.pi s) = (Set.univ.pi fun e => if b e then Set.univ else s e) ×ˢ
        (Set.univ.pi fun e => if b e then s e else Set.univ) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun e => ?_, fun e => ?_⟩
      · have := h e
        by_cases hb : b e = true <;> simp_all
      · have := h e
        by_cases hb : b e = true <;> simp_all
    · rintro ⟨h1, h2⟩ e
      have := h1 e
      have := h2 e
      by_cases hb : b e = true <;> simp_all
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ => ?_
  by_cases hb : b e = true <;> simp [hb]

/-- The coordinates of `Fin N ⊕ OffDiag N` in the rows and columns `T`. -/
private def rowBool {N : ℕ} (T : Finset (Fin N)) : Fin N ⊕ OffDiag N → Bool :=
  Sum.elim (fun k => decide (k ∈ T)) (fun p => decide (p.1.1 ∈ T ∨ p.1.2 ∈ T))

private lemma rowsMix_sumPiEquivProdPi {N : ℕ} (T : Finset (Fin N))
    (x x' : Fin N ⊕ OffDiag N → ℝ) :
    rowsMix T (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ) x)
        (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ) x') =
      MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ)
        (fun e => if rowBool T e then x' e else x e) := by
  refine Prod.ext (funext fun k => ?_) (funext fun p => ?_)
  · by_cases hk : k ∈ T
    · simp only [rowsMix, hk, ite_true]
      change x' (Sum.inl k) = if rowBool T (Sum.inl k) = true then x' (Sum.inl k) else x (Sum.inl k)
      simp [rowBool, hk]
    · simp only [rowsMix, hk, ite_false]
      change x (Sum.inl k) = if rowBool T (Sum.inl k) = true then x' (Sum.inl k) else x (Sum.inl k)
      simp [rowBool, hk]
  · by_cases hp : p.1.1 ∈ T ∨ p.1.2 ∈ T
    · simp only [rowsMix, hp, ite_true]
      change x' (Sum.inr p) = if rowBool T (Sum.inr p) = true then x' (Sum.inr p) else x (Sum.inr p)
      simp [rowBool, hp]
    · simp only [rowsMix, hp, ite_false]
      change x (Sum.inr p) = if rowBool T (Sum.inr p) = true then x' (Sum.inr p) else x (Sum.inr p)
      simp [rowBool, hp]

/-- Mixing the rows `T` of two independent copies of the entries gives a copy of the entries. -/
private lemma measurePreserving_rowsMix {N : ℕ} {L : EntryLaws N} (hL : L.IsProb)
    (T : Finset (Fin N)) :
    MeasurePreserving (fun q : Entries N × Entries N => rowsMix T q.1 q.2)
      (L.law.prod L.law) L.law := by
  refine ⟨(continuous_rowsMix T).measurable, ?_⟩
  have hprob : ∀ i, IsProbabilityMeasure (Sum.elim L.diag L.off i) := by
    rintro (i | p)
    · exact hL.diag i
    · exact hL.off p
  have he := (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ OffDiag N => ℝ)).measurable
  have : IsProbabilityMeasure L.lawPi := by unfold EntryLaws.lawPi; infer_instance
  have h1 := law_eq_map_lawPi hL
  have hmap : L.law.prod L.law = (L.lawPi.prod L.lawPi).map (Prod.map
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ OffDiag N => ℝ))
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ OffDiag N => ℝ))) := by
    rw [h1]
    exact Measure.map_prod_map _ _ he he
  have hm : Measurable (fun q : (Fin N ⊕ OffDiag N → ℝ) × (Fin N ⊕ OffDiag N → ℝ) =>
      fun e => if rowBool T e then q.2 e else q.1 e) := by
    refine measurable_pi_iff.mpr fun e => ?_
    by_cases h : rowBool T e = true
    · simp only [h]
      exact (measurable_pi_apply e).comp measurable_snd
    · simp only [h]
      exact (measurable_pi_apply e).comp measurable_fst
  rw [hmap, Measure.map_map (continuous_rowsMix T).measurable (he.prodMap he)]
  have hcomp : (fun q : Entries N × Entries N => rowsMix T q.1 q.2) ∘ Prod.map
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ OffDiag N => ℝ))
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ OffDiag N => ℝ)) =
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ OffDiag N => ℝ)) ∘
        (fun q : (Fin N ⊕ OffDiag N → ℝ) × (Fin N ⊕ OffDiag N → ℝ) =>
          fun e => if rowBool T e then q.2 e else q.1 e) := by
    funext q
    exact rowsMix_sumPiEquivProdPi T q.1 q.2
  rw [hcomp, ← Measure.map_map he hm]
  have h2 := map_mix_pi (Sum.elim L.diag L.off) (rowBool T)
  have h3 : (L.lawPi.prod L.lawPi).map (fun q : (Fin N ⊕ OffDiag N → ℝ) × (Fin N ⊕ OffDiag N → ℝ) =>
      fun e => if rowBool T e then q.2 e else q.1 e) = L.lawPi := h2
  rw [h3, h1]

namespace EntryLaws

/-- The entries as one family indexed by `Fin N ⊕ OffDiag N`. -/
def entryCoord {N : ℕ} (e : Fin N ⊕ OffDiag N) (ω : Entries N) : ℝ :=
  Sum.elim (fun i => ω.1 i) (fun p => ω.2 p) e

/-- The entries are independent under `L.law`. -/
theorem iIndepFun_entryCoord {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) :
    iIndepFun (fun e (ω : Entries N) => entryCoord e ω) L.law := by
  have h1 := law_eq_map_lawPi hL
  have h := iIndepFun_lawPi hL
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S sets hsets
  have key : ∀ i, MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ OffDiag N => ℝ) ⁻¹'
      ((fun ω : Entries N => entryCoord i ω) ⁻¹' sets i) =
      (fun x : Fin N ⊕ OffDiag N → ℝ => x i) ⁻¹' sets i := by
    intro i
    cases i <;> rfl
  rw [h1]
  simp only [MeasurableEquiv.map_apply, Set.preimage_iInter, key]
  exact h S hsets

/-- The partial expectation `E_T` over the entries in the rows `T` (Definition 3.6 of [15]
for `T = {i}`). -/
def rowsExp {N : ℕ} (L : EntryLaws N) (T : Finset (Fin N)) (X : Entries N → ℂ) :
    Entries N → ℂ :=
  fun ω => ∫ ω', X (rowsMix T ω ω') ∂L.law

theorem rowIndep_rowsExp {N : ℕ} (L : EntryLaws N) (T : Finset (Fin N)) (X : Entries N → ℂ) :
    RowIndep T (L.rowsExp T X) := by
  intro ω
  simp only [rowsExp, rowsMix_zeroEntries]

theorem rowsExp_of_rowIndep {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) {T : Finset (Fin N)}
    {X : Entries N → ℂ} (hX : RowIndep T X) : L.rowsExp T X = X := by
  have := isProbabilityMeasure_law hL
  funext ω
  simp only [rowsExp, rowIndep_iff_rowsMix.mp hX ω]
  simp

theorem rowsExp_mul_of_rowIndep {N : ℕ} (L : EntryLaws N) {T : Finset (Fin N)}
    {F X : Entries N → ℂ} (hF : RowIndep T F) : L.rowsExp T (F * X) = F * L.rowsExp T X := by
  funext ω
  simp only [rowsExp, Pi.mul_apply, rowIndep_iff_rowsMix.mp hF ω]
  exact integral_const_mul _ _

theorem aestronglyMeasurable_rowsExp {N : ℕ} {L : EntryLaws N} (hL : L.IsProb)
    (T : Finset (Fin N)) {X : Entries N → ℂ} (hX : AEStronglyMeasurable X L.law) :
    AEStronglyMeasurable (L.rowsExp T X) L.law := by
  have := isProbabilityMeasure_law hL
  exact (hX.comp_measurePreserving (measurePreserving_rowsMix hL T)).integral_prod_right'

/-- `E E_T X = E X`. -/
theorem integral_rowsExp {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) (T : Finset (Fin N))
    {X : Entries N → ℂ} (hX : Integrable X L.law) :
    ∫ ω, L.rowsExp T X ω ∂L.law = ∫ ω, X ω ∂L.law := by
  have := isProbabilityMeasure_law hL
  have hmp := measurePreserving_rowsMix hL T
  have hint : Integrable (fun q : Entries N × Entries N => X (rowsMix T q.1 q.2))
      (L.law.prod L.law) := hmp.integrable_comp_of_integrable hX
  have h1 := integral_prod _ hint
  have h2 : ∫ q : Entries N × Entries N, X (rowsMix T q.1 q.2) ∂(L.law.prod L.law) =
      ∫ ω, X ω ∂L.law := by
    have h := integral_map (μ := L.law.prod L.law) hmp.measurable.aemeasurable
      (φ := fun q : Entries N × Entries N => rowsMix T q.1 q.2) (f := X)
      (by rw [hmp.map_eq]; exact hX.aestronglyMeasurable)
    rw [hmp.map_eq] at h
    exact h.symm
  rw [← h2, h1]
  rfl

/-- Conditioning on the entries outside the rows `T`. -/
theorem law_eq_lintegral_rowsMix {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) (T : Finset (Fin N))
    {A : Set (Entries N)} (hA : MeasurableSet A) :
    L.law A = ∫⁻ ω, L.law {ω' | rowsMix T ω ω' ∈ A} ∂L.law := by
  have := isProbabilityMeasure_law hL
  have hmp := measurePreserving_rowsMix hL T
  rw [← hmp.measure_preimage hA.nullMeasurableSet, Measure.prod_apply (hmp.measurable hA)]
  rfl

end EntryLaws

/-- `[Ξ]_T = π_T⁻¹(π_T(Ξ))` of (5.8) of [15]. -/
def rowSat {N : ℕ} (T : Finset (Fin N)) (Ξ : Set (Entries N)) : Set (Entries N) :=
  zeroEntries T ⁻¹' (zeroEntries T '' Ξ)

theorem subset_rowSat {N : ℕ} (T : Finset (Fin N)) (Ξ : Set (Entries N)) : Ξ ⊆ rowSat T Ξ := by
  intro ω hω
  exact ⟨ω, hω, rfl⟩

theorem rowIndep_mem_rowSat {N : ℕ} (T : Finset (Fin N)) (Ξ : Set (Entries N)) :
    RowIndep T (fun ω => ω ∈ rowSat T Ξ) := by
  intro ω
  simp only [rowSat, Set.mem_preimage, zeroEntries_zeroEntries, Finset.union_self]

/-- The saturation of a closed set is Borel (`Entries N` is σ-compact). -/
theorem measurableSet_rowSat_of_isClosed {N : ℕ} (T : Finset (Fin N)) {Ξ : Set (Entries N)}
    (hΞ : IsClosed Ξ) : MeasurableSet (rowSat T Ξ) := by
  have hσ : IsSigmaCompact (Set.univ : Set (Entries N)) := isSigmaCompact_univ
  have hΞσ : IsSigmaCompact Ξ := hσ.of_isClosed_subset hΞ (Set.subset_univ _)
  obtain ⟨K, hK, hcov⟩ := hΞσ.image (continuous_zeroEntries T)
  have hI : MeasurableSet (zeroEntries T '' Ξ) := by
    rw [← hcov]
    exact MeasurableSet.iUnion fun n => (hK n).measurableSet
  exact (continuous_zeroEntries T).measurable hI

/-- `A^{S,U}` of (5.1) of [15]. -/
def gradedTerm {N : ℕ} {β : Type*} [AddCommGroup β] (A : Finset (Fin N) → β)
    (S U : Finset (Fin N)) : β :=
  ∑ T ∈ U.powerset, ((-1 : ℤ) ^ T.card) • A ((S \ U) ∪ T)

/-- Lemma 5.1 of [15], (5.2). -/
theorem sum_gradedTerm {N : ℕ} {β : Type*} [AddCommGroup β] (A : Finset (Fin N) → β)
    (S : Finset (Fin N)) : ∑ U ∈ S.powerset, gradedTerm A S U = A ∅ := by
  classical
  unfold gradedTerm
  rw [Finset.sum_sigma' S.powerset (fun U => U.powerset)
    (fun U T => ((-1 : ℤ) ^ T.card) • A ((S \ U) ∪ T))]
  have h1 : ∀ W ∈ S.powerset, ∑ T ∈ W.powerset, ((-1 : ℤ) ^ T.card) • A W =
      if W = ∅ then A ∅ else 0 := by
    intro W _
    rw [← Finset.sum_smul, Finset.sum_powerset_neg_one_pow_card]
    by_cases hW : W = ∅
    · subst hW; simp
    · simp [hW]
  have h2 : ∑ W ∈ S.powerset, (if W = ∅ then A ∅ else 0) = A ∅ := by
    rw [Finset.sum_ite_eq' S.powerset ∅ (fun _ => A ∅)]
    simp
  rw [← h2, ← Finset.sum_congr rfl h1, Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun x => (⟨(S \ x.1) ∪ x.2, x.2⟩ : (_ : Finset (Fin N)) × Finset (Fin N)))
    (fun x => (⟨(S \ x.1) ∪ x.2, x.2⟩ : (_ : Finset (Fin N)) × Finset (Fin N))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨U, T⟩ h
    simp only [Finset.mem_sigma, Finset.mem_powerset] at h ⊢
    obtain ⟨hU, hT⟩ := h
    refine ⟨?_, fun x hx => Finset.mem_union_right _ hx⟩
    intro x hx
    simp only [Finset.mem_union, Finset.mem_sdiff] at hx
    rcases hx with ⟨hx, _⟩ | hx
    · exact hx
    · exact hU (hT hx)
  · rintro ⟨W, T⟩ h
    simp only [Finset.mem_sigma, Finset.mem_powerset] at h ⊢
    obtain ⟨hW, hT⟩ := h
    refine ⟨?_, fun x hx => Finset.mem_union_right _ hx⟩
    intro x hx
    simp only [Finset.mem_union, Finset.mem_sdiff] at hx
    rcases hx with ⟨hx, _⟩ | hx
    · exact hx
    · exact hW (hT hx)
  · rintro ⟨U, T⟩ h
    simp only [Finset.mem_sigma, Finset.mem_powerset] at h
    obtain ⟨hU, hT⟩ := h
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    have h1 := @hU x
    have h2 := @hT x
    tauto
  · rintro ⟨W, T⟩ h
    simp only [Finset.mem_sigma, Finset.mem_powerset] at h
    obtain ⟨hW, hT⟩ := h
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    have h1 := @hW x
    have h2 := @hT x
    tauto
  · rintro ⟨U, T⟩ _
    rfl

/-- (5.41) of [15]. -/
theorem gradedTerm_empty {N : ℕ} {β : Type*} [AddCommGroup β] (A : Finset (Fin N) → β)
    (S : Finset (Fin N)) : gradedTerm A S ∅ = A S := by
  simp [gradedTerm]

/-- `A^{S,U}` is independent of `S \ U` when every `A V`, `V ⊇ S \ U`, is. -/
theorem RowIndep.gradedTerm {N : ℕ} {T S U : Finset (Fin N)}
    {A : Finset (Fin N) → Entries N → ℂ} (hA : ∀ V, T ⊆ V → RowIndep T (A V))
    (hT : T ⊆ S \ U) : RowIndep T (gradedTerm A S U) := by
  intro ω
  simp only [WEdgeNS.gradedTerm, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun T' _ => ?_
  rw [hA _ (hT.trans Finset.subset_union_left) ω]

/-! ### Compiled instances at `N = 3` with the Rademacher-type entry laws `radLaws 3`
(off-diagonal entries `±3^{-1/2}`, diagonal entries `±(2/3)^{1/2}`). -/

private lemma radLaws_three_isProb : (radLaws 3).IsProb :=
  (radLaws_isGenWigner (by norm_num)).isProb

example : (radLaws 3).law =
    (radLaws 3).lawPi.map (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ)) :=
  EntryLaws.law_eq_map_lawPi radLaws_three_isProb

example : iIndepFun (fun (e : Fin 3 ⊕ OffDiag 3) (x : Fin 3 ⊕ OffDiag 3 → ℝ) => x e)
    (radLaws 3).lawPi :=
  EntryLaws.iIndepFun_lawPi radLaws_three_isProb

example : iIndepFun (fun e (ω : Entries 3) => EntryLaws.entryCoord e ω) (radLaws 3).law :=
  EntryLaws.iIndepFun_entryCoord radLaws_three_isProb

/-- The resolvent entry `G_00(i)` is a continuous function of the entries. -/
example : Continuous (fun ω : Entries 3 => resolventC (symOfEntries ω) Complex.I 0 0) :=
  continuous_resolventC_symOfEntries (by simp) 0 0

/-- `h_12` is independent of the row `0`, and not of the row `1`. -/
example : RowIndep ({0} : Finset (Fin 3)) (fun ω => symOfEntries ω 1 2) :=
  rowIndep_symOfEntries_apply (by decide) (by decide)

example : ¬ RowIndep ({1} : Finset (Fin 3)) (fun ω => symOfEntries ω 1 2) := by
  intro h
  have := h ((fun _ => 0), fun _ => 1)
  simp [symOfEntries, zeroEntries, rowsMix] at this

/-- `G^{(01)}_{22}(i)` is independent of the row `0`. -/
example : RowIndep ({0} : Finset (Fin 3))
    (fun ω => resolventC (zeroRC {0, 1} (symOfEntries ω)) Complex.I 2 2) :=
  rowIndep_resolventC_zeroRC (by decide) Complex.I 2 2

/-- The entry `h_12` and the entry `h_01` as functions on `Entries 3`. -/
private def psEntry12 : Entries 3 → ℂ := fun ω => ((ω.2 ⟨(1, 2), by decide⟩ : ℝ) : ℂ)

private def psEntry01 : Entries 3 → ℂ := fun ω => ((ω.2 ⟨(0, 1), by decide⟩ : ℝ) : ℂ)

private lemma rowIndep_psEntry12 : RowIndep ({0} : Finset (Fin 3)) psEntry12 := by
  intro ω
  simp [psEntry12, zeroEntries, rowsMix]

private lemma aestronglyMeasurable_psEntry01 : AEStronglyMeasurable psEntry01 (radLaws 3).law :=
  (Complex.continuous_ofReal.comp ((continuous_apply _).comp continuous_snd)).aestronglyMeasurable

example : (radLaws 3).rowsExp {0} psEntry12 = psEntry12 :=
  EntryLaws.rowsExp_of_rowIndep radLaws_three_isProb rowIndep_psEntry12

example : (radLaws 3).rowsExp {0} (psEntry12 * psEntry01) =
    psEntry12 * (radLaws 3).rowsExp {0} psEntry01 :=
  EntryLaws.rowsExp_mul_of_rowIndep (radLaws 3) rowIndep_psEntry12

example : AEStronglyMeasurable ((radLaws 3).rowsExp {1} psEntry01) (radLaws 3).law :=
  EntryLaws.aestronglyMeasurable_rowsExp radLaws_three_isProb {1}
    aestronglyMeasurable_psEntry01

/-- A bounded non-constant function of the diagonal entry `h_11`. -/
private def psCos : Entries 3 → ℂ := fun ω => ((Real.cos (ω.1 1) : ℝ) : ℂ)

private lemma integrable_psCos : Integrable psCos (radLaws 3).law := by
  have := EntryLaws.isProbabilityMeasure_law radLaws_three_isProb
  have h : Continuous psCos := by unfold psCos; fun_prop
  refine Integrable.of_bound (C := 1) h.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  change ‖((Real.cos (ω.1 1) : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_cos_le_one _

example : ∫ ω, (radLaws 3).rowsExp {1} psCos ω ∂(radLaws 3).law =
    ∫ ω, psCos ω ∂(radLaws 3).law :=
  EntryLaws.integral_rowsExp radLaws_three_isProb {1} integrable_psCos

example : (radLaws 3).law {ω : Entries 3 | 0 < ω.1 1} =
    ∫⁻ ω, (radLaws 3).law {ω' | rowsMix {1} ω ω' ∈ {ω : Entries 3 | 0 < ω.1 1}}
      ∂(radLaws 3).law :=
  EntryLaws.law_eq_lintegral_rowsMix radLaws_three_isProb {1}
    (measurableSet_lt measurable_const (by fun_prop))

/-- The closed hyperbola `h_00 h_11 = 1`: its saturation in the row `0` is the open set
`h_11 ≠ 0`, which is Borel, strictly larger than the hyperbola and not closed. -/
example : IsClosed {ω : Entries 3 | ω.1 0 * ω.1 1 = 1} :=
  isClosed_eq (by fun_prop) continuous_const

example : MeasurableSet (rowSat ({0} : Finset (Fin 3)) {ω : Entries 3 | ω.1 0 * ω.1 1 = 1}) :=
  measurableSet_rowSat_of_isClosed {0} (isClosed_eq (by fun_prop) continuous_const)

example : rowSat ({0} : Finset (Fin 3)) {ω : Entries 3 | ω.1 0 * ω.1 1 = 1} =
    {ω : Entries 3 | ω.1 1 ≠ 0} := by
  ext ω
  constructor
  · rintro ⟨ξ, hξ, h⟩
    have h1 : ξ.1 1 = ω.1 1 := by
      have := congrFun (congrArg Prod.fst h) 1
      simpa [zeroEntries, rowsMix] using this
    intro h0
    rw [h0] at h1
    have : ξ.1 0 * ξ.1 1 = 1 := hξ
    rw [h1] at this
    simp at this
  · intro hω
    refine ⟨(Function.update ω.1 0 (ω.1 1)⁻¹, ω.2), ?_, ?_⟩
    · change Function.update ω.1 0 (ω.1 1)⁻¹ 0 * Function.update ω.1 0 (ω.1 1)⁻¹ 1 = 1
      simpa using inv_mul_cancel₀ (show ω.1 1 ≠ 0 from hω)
    · refine Prod.ext (funext fun k => ?_) (funext fun p => ?_)
      · by_cases hk : k = 0 <;> simp [zeroEntries, rowsMix, hk]
      · simp [zeroEntries, rowsMix]

example : (({0, 1} : Finset (Fin 3)).powerset.sum fun U =>
      gradedTerm (fun V : Finset (Fin 3) => (V.card : ℤ)) {0, 1} U) = 0 ∧
    gradedTerm (fun V : Finset (Fin 3) => (V.card : ℤ)) {0, 1} {1} = -1 := by
  decide

/-- The graded term of the resolvent entries of the minors is independent of the row `0`. -/
example : RowIndep ({0} : Finset (Fin 3))
    (gradedTerm (fun V : Finset (Fin 3) => fun ω : Entries 3 =>
      resolventC (zeroRC V (symOfEntries ω)) Complex.I 1 1) {0, 1} {1}) :=
  RowIndep.gradedTerm (fun V hV => rowIndep_resolventC_zeroRC hV Complex.I 1 1) (by decide)

#print axioms EntryLaws.law_eq_map_lawPi
#print axioms EntryLaws.iIndepFun_lawPi
#print axioms continuous_resolventC_symOfEntries
#print axioms symOfEntries_zeroEntries
#print axioms zeroEntries_zeroEntries
#print axioms rowIndep_iff_rowsMix
#print axioms rowIndep_symOfEntries_apply
#print axioms rowIndep_resolventC_zeroRC
#print axioms EntryLaws.iIndepFun_entryCoord
#print axioms EntryLaws.rowIndep_rowsExp
#print axioms EntryLaws.rowsExp_of_rowIndep
#print axioms EntryLaws.rowsExp_mul_of_rowIndep
#print axioms EntryLaws.aestronglyMeasurable_rowsExp
#print axioms EntryLaws.integral_rowsExp
#print axioms EntryLaws.law_eq_lintegral_rowsMix
#print axioms subset_rowSat
#print axioms rowIndep_mem_rowSat
#print axioms measurableSet_rowSat_of_isClosed
#print axioms sum_gradedTerm
#print axioms gradedTerm_empty
#print axioms RowIndep.gradedTerm

end WEdgeNS
