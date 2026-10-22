import WEdgeNS.EdgeUniv.RBound
import WEdgeNS.EdgeUniv.WardReduction
import WEdgeNS.Resolvent.Minors

/-!
# The expectation gain of one off-diagonal entry
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

open private resolventC_symm resolventC_sub_zeroRC_single from WEdgeNS.Resolvent.Minors

/-- Removing the entry `e = (b, d)` does not change the minor `H^{(b)}`. -/
private lemma eg_zeroRC_zeroEntry {N : ℕ} {p : OffDiag N} {b : Fin N} (hb : b = p.1.1 ∨ b = p.1.2)
    (ω : Entries N) :
    zeroRC {b} (symOfEntries (zeroEntry (Sum.inr p) ω)) = zeroRC {b} (symOfEntries ω) := by
  funext k l
  unfold zeroRC
  by_cases h : k ∈ ({b} : Finset (Fin N)) ∨ l ∈ ({b} : Finset (Fin N))
  · simp only [h, ite_true]
  · simp only [h, ite_false]
    rw [symOfEntries_eq_zeroEntry_add (Sum.inr p) ω, Matrix.add_apply, Matrix.smul_apply]
    have hk : k ≠ b := fun e => h (Or.inl (by simp [e]))
    have hl : l ≠ b := fun e => h (Or.inr (by simp [e]))
    have : (k, l) ∉ entryPairs (Sum.inr p) := by
      simp only [entryPairs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, not_or,
        not_and]
      rcases hb with rfl | rfl
      · exact ⟨fun e => absurd e hk, fun _ e => absurd e hl⟩
      · exact ⟨fun _ e => absurd e hl, fun e => absurd e hk⟩
    simp [entryMat, this]

/-- The row `b` of `Q`: the entry `Q_bd` is zero, the others are those of `H`. -/
private lemma eg_zeroEntry_row {N : ℕ} {p : OffDiag N} {b d : Fin N}
    (hbd : (b = p.1.1 ∧ d = p.1.2) ∨ (b = p.1.2 ∧ d = p.1.1)) (ω : Entries N) (k : Fin N) :
    symOfEntries (zeroEntry (Sum.inr p) ω) b k = if k = d then 0 else symOfEntries ω b k := by
  have hp := p.2
  by_cases hk : k = d
  · subst hk
    simp only [ite_true]
    rcases hbd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [symOfEntries, zeroEntry, hp.ne, hp]
    · simp [symOfEntries, zeroEntry, hp.ne', not_lt.2 hp.le]
  · simp only [hk, ite_false]
    rw [symOfEntries_eq_zeroEntry_add (Sum.inr p) ω, Matrix.add_apply, Matrix.smul_apply]
    have : (b, k) ∉ entryPairs (Sum.inr p) := by
      simp only [entryPairs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, not_or,
        not_and]
      rcases hbd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨fun _ e => hk e, fun e => absurd e hp.ne⟩
      · exact ⟨fun e => absurd e hp.ne', fun _ e => hk e⟩
    simp [entryMat, this]


open private fa_mean_sym fa_integral_mul_sym fa_map_sym fa_entryLaw_sq_int
  from WEdgeNS.LocalLaw.FluctAvg

/-- [16] Lemma 6.10, one-sided form: for `i ≠ b`, `G_ib = -G_bb Σ_k H_bk G^{(b)}_ki`. -/
private lemma eg_schur {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) {i b : Fin N} (hib : i ≠ b) :
    resolventC H z i b =
      -(resolventC H z b b * ∑ k, (H b k : ℂ) * resolventC (zeroRC {b} H) z k i) := by
  have h := resolventC_sub_zeroRC_single hH hz b b i hib
  rw [resolventC_zeroRC_apply_of_mem hH hz (Finset.mem_singleton_self b) i] at h
  simp only [Ne.symm hib, ite_false, sub_zero] at h
  rw [resolventC_symm hH hz i b, h]

/-! ### Entries of the row `b` against functions independent of the row `b` -/

private lemma eg_integrable_sq {N : ℕ} {L : EntryLaws N} {C0 : ℝ} (hL : L.IsGenWigner C0)
    (a c : Fin N) : Integrable (fun ω => (symOfEntries ω a c) ^ 2) L.law := by
  have hm := measurable_symOfEntries_at (N := N) a c
  have hi : Integrable (fun x : ℝ => x ^ 2) (L.law.map (fun ω => symOfEntries ω a c)) := by
    rw [fa_map_sym hL.isProb a c]
    exact fa_entryLaw_sq_int hL a c
  exact (integrable_map_measure (by fun_prop) hm.aemeasurable).1 hi

private lemma eg_integrable_entry {N : ℕ} {L : EntryLaws N} {C0 : ℝ} (hL : L.IsGenWigner C0)
    (a c : Fin N) : Integrable (fun ω => symOfEntries ω a c) L.law := by
  have := isProbabilityMeasure_law hL.isProb
  exact ((memLp_two_iff_integrable_sq (measurable_symOfEntries_at a c).aestronglyMeasurable).2
    (eg_integrable_sq hL a c)).integrable (by norm_num)

private lemma eg_integrable_entry_mul {N : ℕ} {L : EntryLaws N} {C0 : ℝ} (hL : L.IsGenWigner C0)
    (a c a' c' : Fin N) :
    Integrable (fun ω => symOfEntries ω a c * symOfEntries ω a' c') L.law := by
  refine Integrable.mono' ((eg_integrable_sq hL a c).add (eg_integrable_sq hL a' c'))
    ((measurable_symOfEntries_at a c).mul (measurable_symOfEntries_at a' c')).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul, Pi.add_apply]
  nlinarith [sq_nonneg (|symOfEntries ω a c| - |symOfEntries ω a' c'|), sq_abs (symOfEntries ω a c),
    sq_abs (symOfEntries ω a' c')]

private lemma eg_rowIndep_mul {N : ℕ} {T : Finset (Fin N)} {f g : Entries N → ℂ}
    (hf : RowIndep T f) (hg : RowIndep T g) : RowIndep T (fun ω => f ω * g ω) := by
  intro ω
  simp only [hf ω, hg ω]

/-- `E[Y h_bk] = 0` for `Y` bounded and independent of the row `b`. -/
private lemma eg_integral_mul_entry {N : ℕ} {L : EntryLaws N} {C0 : ℝ} (hL : L.IsGenWigner C0)
    {b : Fin N} {Y : Entries N → ℂ} (hY : RowIndep {b} Y) (hYm : Measurable Y) {K : ℝ}
    (hYK : ∀ ω, ‖Y ω‖ ≤ K) (k : Fin N) :
    ∫ ω, Y ω * (symOfEntries ω b k : ℂ) ∂L.law = 0 := by
  have := isProbabilityMeasure_law hL.isProb
  have hint : Integrable (fun ω => Y ω * (symOfEntries ω b k : ℂ)) L.law :=
    (eg_integrable_entry hL b k).ofReal.bdd_mul hYm.aestronglyMeasurable (ae_of_all _ hYK)
  rw [← integral_rowsExp hL.isProb {b} hint]
  have h1 : L.rowsExp {b} (fun ω => Y ω * (symOfEntries ω b k : ℂ)) =
      Y * L.rowsExp {b} (fun ω => (symOfEntries ω b k : ℂ)) :=
    rowsExp_mul_of_rowIndep L (X := fun ω => (symOfEntries ω b k : ℂ)) hY
  have h2 : ∀ ω, L.rowsExp {b} (fun ω => (symOfEntries ω b k : ℂ)) ω = 0 := by
    intro ω
    simp only [rowsExp, symOfEntries_rowsMix_left_of_mem {b} (Finset.mem_singleton_self b)]
    rw [integral_complex_ofReal, fa_mean_sym hL b k, Complex.ofReal_zero]
  rw [h1]
  simp [h2]

/-- `E[Y h_bk h_bl] = δ_kl N⁻¹ E Y` for `k ≠ b` and `Y` bounded and independent of the row `b`. -/
private lemma eg_integral_mul_entry_mul {N : ℕ} {L : EntryLaws N} {C0 : ℝ}
    (hL : L.IsGenWigner C0) {b : Fin N} {Y : Entries N → ℂ} (hY : RowIndep {b} Y)
    (hYm : Measurable Y) {K : ℝ} (hYK : ∀ ω, ‖Y ω‖ ≤ K) {k : Fin N} (hk : k ≠ b) (l : Fin N) :
    ∫ ω, Y ω * ((symOfEntries ω b k * symOfEntries ω b l : ℝ) : ℂ) ∂L.law =
      (∫ ω, Y ω ∂L.law) * ((if k = l then (N : ℝ)⁻¹ else 0 : ℝ) : ℂ) := by
  have := isProbabilityMeasure_law hL.isProb
  have hint : Integrable (fun ω => Y ω * ((symOfEntries ω b k * symOfEntries ω b l : ℝ) : ℂ))
      L.law :=
    (eg_integrable_entry_mul hL b k b l).ofReal.bdd_mul hYm.aestronglyMeasurable
      (ae_of_all _ hYK)
  rw [← integral_rowsExp hL.isProb {b} hint]
  have h1 : L.rowsExp {b} (fun ω => Y ω * ((symOfEntries ω b k * symOfEntries ω b l : ℝ) : ℂ)) =
      Y * L.rowsExp {b} (fun ω => ((symOfEntries ω b k * symOfEntries ω b l : ℝ) : ℂ)) :=
    rowsExp_mul_of_rowIndep L
      (X := fun ω => ((symOfEntries ω b k * symOfEntries ω b l : ℝ) : ℂ)) hY
  have h2 : ∀ ω, L.rowsExp {b} (fun ω => ((symOfEntries ω b k * symOfEntries ω b l : ℝ) : ℂ)) ω =
      ((if k = l then (N : ℝ)⁻¹ else 0 : ℝ) : ℂ) := by
    intro ω
    simp only [rowsExp, symOfEntries_rowsMix_left_of_mem {b} (Finset.mem_singleton_self b)]
    rw [integral_complex_ofReal, fa_integral_mul_sym hL b k l hk]
  rw [h1]
  simp only [Pi.mul_apply, h2]
  exact integral_mul_const _ _


private lemma eg_norm_mul_le {x y : ℂ} {K K' : ℝ} (hx : ‖x‖ ≤ K') (hy : ‖y‖ ≤ K) :
    ‖x * y‖ ≤ K' * K := by
  rw [norm_mul]
  exact mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx)

/-- `E[X Σ_k h_bk a_k] = 0` for `X` and the `a_k` bounded and independent of the row `b`
((6.97) at `f = 0`). -/
private lemma eg_integral_mul_linear {N : ℕ} {L : EntryLaws N} {C0 : ℝ} (hL : L.IsGenWigner C0)
    {b : Fin N} {a : Fin N → Entries N → ℂ} (ha : ∀ k, RowIndep {b} (a k))
    (ham : ∀ k, Measurable (a k)) {K : ℝ} (haK : ∀ k ω, ‖a k ω‖ ≤ K)
    {X : Entries N → ℂ} (hX : RowIndep {b} X) (hXm : Measurable X) {K' : ℝ}
    (hXK : ∀ ω, ‖X ω‖ ≤ K') :
    Integrable (fun ω => X ω * ∑ k, (symOfEntries ω b k : ℂ) * a k ω) L.law ∧
      ∫ ω, X ω * ∑ k, (symOfEntries ω b k : ℂ) * a k ω ∂L.law = 0 := by
  have := isProbabilityMeasure_law hL.isProb
  have e : ∀ ω, X ω * ∑ k, (symOfEntries ω b k : ℂ) * a k ω =
      ∑ k, (X ω * a k ω) * (symOfEntries ω b k : ℂ) := by
    intro ω
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hm : ∀ k, Measurable (fun ω => X ω * a k ω) := fun k => hXm.mul (ham k)
  have hint : ∀ k, Integrable (fun ω => X ω * a k ω * (symOfEntries ω b k : ℂ)) L.law :=
    fun k => (eg_integrable_entry hL b k).ofReal.bdd_mul (hm k).aestronglyMeasurable
      (ae_of_all _ fun ω => eg_norm_mul_le (hXK ω) (haK k ω))
  simp_rw [e]
  refine ⟨integrable_finsetSum _ fun k _ => hint k, ?_⟩
  rw [integral_finsetSum _ fun k _ => hint k]
  exact Finset.sum_eq_zero fun k _ => eg_integral_mul_entry hL (eg_rowIndep_mul hX (ha k))
    (hm k) (fun ω => eg_norm_mul_le (hXK ω) (haK k ω)) k

private lemma eg_ofReal_norm_sq (x : ℂ) : ((‖x‖ ^ 2 : ℝ) : ℂ) = x * (starRingEnd ℂ) x := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- `E|Σ_k h_bk a_k|² = N⁻¹ Σ_k E|a_k|²` for coefficients `a_k` bounded and independent of the
row `b`, with `a_b = 0` (the second-moment form of the large deviation step after (6.97)). -/
private lemma eg_integral_norm_sq_linear {N : ℕ} {L : EntryLaws N} {C0 : ℝ}
    (hL : L.IsGenWigner C0) {b : Fin N} {a : Fin N → Entries N → ℂ} (ha : ∀ k, RowIndep {b} (a k))
    (ham : ∀ k, Measurable (a k)) {K : ℝ} (haK : ∀ k ω, ‖a k ω‖ ≤ K) (hab : ∀ ω, a b ω = 0) :
    Integrable (fun ω => ‖∑ k, (symOfEntries ω b k : ℂ) * a k ω‖ ^ 2) L.law ∧
      ∫ ω, ‖∑ k, (symOfEntries ω b k : ℂ) * a k ω‖ ^ 2 ∂L.law =
        (N : ℝ)⁻¹ * ∑ k, ∫ ω, ‖a k ω‖ ^ 2 ∂L.law := by
  have := isProbabilityMeasure_law hL.isProb
  have hexp : ∀ ω, ((‖∑ k, (symOfEntries ω b k : ℂ) * a k ω‖ ^ 2 : ℝ) : ℂ) =
      ∑ k, ∑ l, (a k ω * (starRingEnd ℂ) (a l ω)) *
        ((symOfEntries ω b k * symOfEntries ω b l : ℝ) : ℂ) := by
    intro ω
    rw [eg_ofReal_norm_sq, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  have hYm : ∀ k l, Measurable (fun ω => a k ω * (starRingEnd ℂ) (a l ω)) := fun k l =>
    (ham k).mul (Complex.continuous_conj.measurable.comp (ham l))
  have hYK : ∀ k l ω, ‖a k ω * (starRingEnd ℂ) (a l ω)‖ ≤ K * K := fun k l ω =>
    eg_norm_mul_le (haK k ω) (by rw [Complex.norm_conj]; exact haK l ω)
  have hint : ∀ k l, Integrable (fun ω => (a k ω * (starRingEnd ℂ) (a l ω)) *
      ((symOfEntries ω b k * symOfEntries ω b l : ℝ) : ℂ)) L.law := fun k l =>
    (eg_integrable_entry_mul hL b k b l).ofReal.bdd_mul (hYm k l).aestronglyMeasurable
      (ae_of_all _ (hYK k l))
  have hterm : ∀ k l, ∫ ω, (a k ω * (starRingEnd ℂ) (a l ω)) *
      ((symOfEntries ω b k * symOfEntries ω b l : ℝ) : ℂ) ∂L.law =
      (∫ ω, a k ω * (starRingEnd ℂ) (a l ω) ∂L.law) *
        ((if k = l then (N : ℝ)⁻¹ else 0 : ℝ) : ℂ) := by
    intro k l
    by_cases hk : k = b
    · subst hk
      simp [hab]
    · exact eg_integral_mul_entry_mul hL (eg_rowIndep_mul (ha k) (fun ω => by
        simp only [ha l ω])) (hYm k l) (hYK k l) hk l
  have hC : Integrable (fun ω => ((‖∑ k, (symOfEntries ω b k : ℂ) * a k ω‖ ^ 2 : ℝ) : ℂ))
      L.law := by
    simp_rw [hexp]
    exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l
  refine ⟨?_, ?_⟩
  · refine (hC.norm).congr (ae_of_all _ fun ω => ?_)
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  · have h1 : ((∫ ω, ‖∑ k, (symOfEntries ω b k : ℂ) * a k ω‖ ^ 2 ∂L.law : ℝ) : ℂ) =
        ∑ k, ((∫ ω, ‖a k ω‖ ^ 2 ∂L.law : ℝ) : ℂ) * (((N : ℝ)⁻¹ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      simp_rw [hexp]
      rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_finsetSum _ fun l _ => hint k l]
      simp_rw [hterm]
      rw [Finset.sum_eq_single k (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
      simp only [ite_true]
      congr 1
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (ae_of_all _ fun ω => (eg_ofReal_norm_sq _).symm)
    have h2 : ((∫ ω, ‖∑ k, (symOfEntries ω b k : ℂ) * a k ω‖ ^ 2 ∂L.law : ℝ) : ℂ) =
        (((N : ℝ)⁻¹ * ∑ k, ∫ ω, ‖a k ω‖ ^ 2 ∂L.law : ℝ) : ℂ) := by
      rw [h1]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    exact_mod_cast h2


/-! ### Deterministic bounds -/

/-- An integrable `f` bounded by `δ ≥ 0` off `T` and by `M` everywhere has `E f ≤ δ + M μ(T)`. -/
private lemma eg_integral_le_of_event {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Integrable f μ) {T : Set α} {δ M : ℝ}
    (hδ : 0 ≤ δ) (hgood : ∀ ω, ω ∉ T → f ω ≤ δ) (hbad : ∀ ω, f ω ≤ M) :
    ∫ ω, f ω ∂μ ≤ δ + M * (μ T).toReal := by
  set T' := toMeasurable μ T with hT'
  have hmeas : MeasurableSet T' := measurableSet_toMeasurable μ T
  have hpt : ∀ ω, f ω ≤ δ + M * T'.indicator 1 ω := by
    intro ω
    by_cases h : ω ∈ T'
    · simp only [Set.indicator_of_mem h, Pi.one_apply, mul_one]
      linarith [hbad ω]
    · have : ω ∉ T := fun hT => h (subset_toMeasurable μ T hT)
      simp only [Set.indicator_of_notMem h, mul_zero, add_zero]
      exact hgood ω this
  have h1 : Integrable (T'.indicator (1 : α → ℝ)) μ := (integrable_const (1 : ℝ)).indicator hmeas
  calc ∫ ω, f ω ∂μ ≤ ∫ ω, (δ + M * T'.indicator (1 : α → ℝ) ω) ∂μ :=
        integral_mono hf ((integrable_const δ).add (h1.const_mul M)) hpt
    _ = δ + M * (μ T).toReal := by
        rw [integral_add (integrable_const δ) (h1.const_mul M),
          integral_const, integral_const_mul, integral_indicator_one hmeas]
        simp [measureReal_def, hT', measure_toMeasurable]

/-- (6.91): if `|G_kl - δ_kl m| ≤ P` for all `k, l`, with `1/5 ≤ |m| ≤ 1` and `P ≤ 1/10`, then
`|G^{(b)}_kl - G_kl| ≤ 10 P²` for `k, l ≠ b`, `|G^{(b)}_kl| ≤ 2P` for `k ≠ l`, and
`|G^{(b)}_kk| ≤ 2` for `k ≠ b`. -/
private lemma eg_minor_bounds {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) {m : ℂ} (hm1 : ‖m‖ ≤ 1) (hm5 : 1 / 5 ≤ ‖m‖) {P : ℝ} (hP0 : 0 ≤ P)
    (hP : P ≤ 1 / 10) (hG : ∀ k l, ‖resolventC H z k l - (if k = l then m else 0)‖ ≤ P)
    (b : Fin N) :
    (∀ k l, k ≠ b → l ≠ b →
      ‖resolventC (zeroRC {b} H) z k l - resolventC H z k l‖ ≤ 10 * P ^ 2) ∧
    (∀ k l, k ≠ l → ‖resolventC (zeroRC {b} H) z k l‖ ≤ 2 * P) ∧
    (∀ k, k ≠ b → ‖resolventC (zeroRC {b} H) z k k‖ ≤ 2) := by
  have hoff : ∀ k l, k ≠ l → ‖resolventC H z k l‖ ≤ P := fun k l h => by
    simpa [h] using hG k l
  have hdiag : ∀ k, ‖resolventC H z k k - m‖ ≤ P := fun k => by simpa using hG k k
  have hbb : 1 / 10 ≤ ‖resolventC H z b b‖ := by
    have h := norm_sub_norm_le m (m - resolventC H z b b)
    rw [sub_sub_cancel, norm_sub_rev] at h
    linarith [hdiag b]
  have hdd : ∀ k, ‖resolventC H z k k‖ ≤ 1 + P := fun k => by
    have h := norm_le_insert' (resolventC H z k k) m
    linarith [hdiag k]
  have h1 : ∀ k l, k ≠ b → l ≠ b →
      ‖resolventC (zeroRC {b} H) z k l - resolventC H z k l‖ ≤ 10 * P ^ 2 := by
    intro k l hk hl
    have e := resolventC_eq_minor_add hH hz hk hl
    have e2 : resolventC (zeroRC {b} H) z k l - resolventC H z k l =
        -(resolventC H z k b * resolventC H z b l / resolventC H z b b) := by
      rw [e]; ring
    rw [e2, norm_neg, norm_div, norm_mul]
    have hpos : 0 < ‖resolventC H z b b‖ := by linarith
    rw [div_le_iff₀ hpos]
    have a1 := hoff k b hk
    have a2 := hoff b l (Ne.symm hl)
    calc ‖resolventC H z k b‖ * ‖resolventC H z b l‖ ≤ P * P :=
          mul_le_mul a1 a2 (norm_nonneg _) hP0
      _ ≤ 10 * P ^ 2 * ‖resolventC H z b b‖ := by nlinarith
  have hzero : ∀ k l, k ≠ l → (k = b ∨ l = b) → resolventC (zeroRC {b} H) z k l = 0 := by
    intro k l hkl h
    rcases h with rfl | rfl
    · rw [resolventC_zeroRC_apply_of_mem hH hz (Finset.mem_singleton_self k) l]
      simp [hkl]
    · rw [resolventC_symm (zeroRC_isHermitian hH {l}) hz k l,
        resolventC_zeroRC_apply_of_mem hH hz (Finset.mem_singleton_self l) k]
      simp [Ne.symm hkl]
  refine ⟨h1, fun k l hkl => ?_, fun k hk => ?_⟩
  · by_cases h : k = b ∨ l = b
    · rw [hzero k l hkl h, norm_zero]; linarith
    · push Not at h
      have a := h1 k l h.1 h.2
      have a2 := norm_le_insert' (resolventC (zeroRC {b} H) z k l) (resolventC H z k l)
      have := hoff k l hkl
      nlinarith
  · have a := h1 k k hk hk
    have a2 := norm_le_insert' (resolventC (zeroRC {b} H) z k k) (resolventC H z k k)
    have := hdd k
    nlinarith


/-- The off-diagonal Ward sums of `G` and `G^{(b)}` under the hypotheses of `eg_minor_bounds`
((6.92)): `Σ_{k≠l} |G_kl|² ≤ N²P²`, `Σ_{k≠l} |G^{(b)}_kl|² ≤ 4N²P²`, and their difference is at
most `32 N² P³` when `NP ≥ 1`. -/
private lemma eg_offSum_bounds {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) {m : ℂ} (hm1 : ‖m‖ ≤ 1) (hm5 : 1 / 5 ≤ ‖m‖) {P : ℝ} (hP0 : 0 ≤ P)
    (hP : P ≤ 1 / 10) (hNP : 1 ≤ N * P)
    (hG : ∀ k l, ‖resolventC H z k l - (if k = l then m else 0)‖ ≤ P) (b : Fin N) :
    (∑ k, ∑ l, if k = l then (0 : ℝ) else ‖resolventC H z k l‖ ^ 2) ≤ (N : ℝ) ^ 2 * P ^ 2 ∧
    (∑ k, ∑ l, if k = l then (0 : ℝ) else ‖resolventC (zeroRC {b} H) z k l‖ ^ 2) ≤
      4 * (N : ℝ) ^ 2 * P ^ 2 ∧
    |(∑ k, ∑ l, if k = l then (0 : ℝ) else ‖resolventC H z k l‖ ^ 2) -
        ∑ k, ∑ l, if k = l then (0 : ℝ) else ‖resolventC (zeroRC {b} H) z k l‖ ^ 2| ≤
      32 * (N : ℝ) ^ 2 * P ^ 3 := by
  obtain ⟨h1, h2, -⟩ := eg_minor_bounds hH hz hm1 hm5 hP0 hP hG b
  have hoff : ∀ k l, k ≠ l → ‖resolventC H z k l‖ ≤ P := fun k l h => by
    simpa [h] using hG k l
  have hcard : ∀ c : ℝ, ∑ _k : Fin N, ∑ _l : Fin N, c = (N : ℝ) ^ 2 * c := fun c => by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  refine ⟨?_, ?_, ?_⟩
  · calc _ ≤ ∑ _k : Fin N, ∑ _l : Fin N, P ^ 2 :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => by
            split_ifs with h
            · positivity
            · exact pow_le_pow_left₀ (norm_nonneg _) (hoff k l h) 2
      _ = _ := hcard _
  · calc _ ≤ ∑ _k : Fin N, ∑ _l : Fin N, 4 * P ^ 2 :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => by
            split_ifs with h
            · positivity
            · have := pow_le_pow_left₀ (norm_nonneg _) (h2 k l h) 2
              nlinarith
      _ = _ := by rw [hcard]; ring
  · rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    have hterm : ∀ k l, |(if k = l then (0 : ℝ) else ‖resolventC H z k l‖ ^ 2) -
        (if k = l then (0 : ℝ) else ‖resolventC (zeroRC {b} H) z k l‖ ^ 2)| ≤
        30 * P ^ 3 + P ^ 2 * ((if k = b then 1 else 0) + (if l = b then 1 else 0)) := by
      intro k l
      have hb0 : 0 ≤ P ^ 2 * ((if k = b then (1 : ℝ) else 0) + (if l = b then 1 else 0)) := by
        apply mul_nonneg (by positivity); split_ifs <;> norm_num
      by_cases hkl : k = l
      · simp only [hkl, ite_true, sub_self, abs_zero]; positivity
      simp only [hkl, ite_false]
      by_cases hb : k = b ∨ l = b
      · have hz0 : resolventC (zeroRC {b} H) z k l = 0 := by
          rcases hb with rfl | rfl
          · rw [resolventC_zeroRC_apply_of_mem hH hz (Finset.mem_singleton_self k) l]
            simp [hkl]
          · rw [resolventC_symm (zeroRC_isHermitian hH {l}) hz k l,
              resolventC_zeroRC_apply_of_mem hH hz (Finset.mem_singleton_self l) k]
            simp [Ne.symm hkl]
        rw [hz0, norm_zero]
        have hP2 : ‖resolventC H z k l‖ ^ 2 ≤ P ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hoff k l hkl) 2
        have hge : P ^ 2 ≤ P ^ 2 * ((if k = b then (1 : ℝ) else 0) + (if l = b then 1 else 0)) := by
          rcases hb with rfl | rfl
          · simp only [ite_true]
            have : (0 : ℝ) ≤ if l = k then 1 else 0 := ite_nonneg zero_le_one le_rfl
            nlinarith [sq_nonneg P]
          · simp only [ite_true]
            have : (0 : ℝ) ≤ if k = l then 1 else 0 := ite_nonneg zero_le_one le_rfl
            nlinarith [sq_nonneg P]
        rw [abs_of_nonneg (by simp)]
        nlinarith [pow_nonneg hP0 3]
      · push Not at hb
        have a := h1 k l hb.1 hb.2
        have a1 := hoff k l hkl
        have a2 := h2 k l hkl
        have e : ‖resolventC H z k l‖ ^ 2 - (‖resolventC (zeroRC {b} H) z k l‖ ^ 2 - 0) =
            (‖resolventC H z k l‖ - ‖resolventC (zeroRC {b} H) z k l‖) *
              (‖resolventC H z k l‖ + ‖resolventC (zeroRC {b} H) z k l‖) := by ring
        have hd : |‖resolventC H z k l‖ - ‖resolventC (zeroRC {b} H) z k l‖| ≤ 10 * P ^ 2 := by
          refine (abs_norm_sub_norm_le _ _).trans ?_
          rw [norm_sub_rev]; exact a
        have hs : 0 ≤ ‖resolventC H z k l‖ + ‖resolventC (zeroRC {b} H) z k l‖ := by positivity
        calc _ = |(‖resolventC H z k l‖ - ‖resolventC (zeroRC {b} H) z k l‖) *
              (‖resolventC H z k l‖ + ‖resolventC (zeroRC {b} H) z k l‖)| := by
              rw [← e]; simp
          _ ≤ 10 * P ^ 2 * (3 * P) := by
              rw [abs_mul, abs_of_nonneg hs]
              exact mul_le_mul hd (by linarith) hs (by positivity)
          _ ≤ _ := by nlinarith
    calc _ ≤ ∑ k : Fin N, ∑ l : Fin N, |(if k = l then (0 : ℝ) else ‖resolventC H z k l‖ ^ 2) -
          (if k = l then (0 : ℝ) else ‖resolventC (zeroRC {b} H) z k l‖ ^ 2)| :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ k : Fin N, ∑ l : Fin N,
          (30 * P ^ 3 + P ^ 2 * ((if k = b then 1 else 0) + (if l = b then 1 else 0))) :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hterm k l
      _ = 30 * (N : ℝ) ^ 2 * P ^ 3 + 2 * N * P ^ 2 := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
            ite_true]
          ring
      _ ≤ _ := by
          nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (sq_nonneg P))
            (sub_nonneg.2 hNP)]


/-- (6.93)–(6.94): on the good event, `F′(x_R) R_bb R_dj conj(R_ij) - m F′(x^{(b)}) R^{(b)}_dj
conj(R^{(b)}_ij)` is at most `2P² |F′(x_R) - F′(x^{(b)})| + 31 B P³` with `|F′(x^{(b)})| ≤ B`. -/
private lemma eg_diff_good {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) {m : ℂ} (hm1 : ‖m‖ ≤ 1) (hm5 : 1 / 5 ≤ ‖m‖) {P : ℝ} (hP0 : 0 ≤ P)
    (hP : P ≤ 1 / 10) (hG : ∀ k l, ‖resolventC H z k l - (if k = l then m else 0)‖ ≤ P)
    {b d i j : Fin N} (hdb : d ≠ b) (hij : i ≠ j) (hib : i ≠ b) (hjb : j ≠ b) (hjd : j ≠ d)
    {u v B δ : ℝ} (hv : |v| ≤ B) (huv : |u - v| ≤ δ) :
    ‖(u : ℂ) * resolventC H z b b * resolventC H z d j * (starRingEnd ℂ) (resolventC H z i j) -
        m * ((v : ℂ) * resolventC (zeroRC {b} H) z d j *
          (starRingEnd ℂ) (resolventC (zeroRC {b} H) z i j))‖ ≤
      2 * P ^ 2 * δ + 31 * B * P ^ 3 := by
  obtain ⟨h1, h2, -⟩ := eg_minor_bounds hH hz hm1 hm5 hP0 hP hG b
  have hoff : ∀ k l, k ≠ l → ‖resolventC H z k l‖ ≤ P := fun k l h => by
    simpa [h] using hG k l
  have hbb : ‖resolventC H z b b‖ ≤ 2 := by
    have h := norm_le_insert' (resolventC H z b b) m
    have := hG b b
    simp only [ite_true] at this
    linarith
  have hbm : ‖resolventC H z b b - m‖ ≤ P := by simpa using hG b b
  set Gbb := resolventC H z b b
  set Gdj := resolventC H z d j
  set Gij := resolventC H z i j
  set Mdj := resolventC (zeroRC {b} H) z d j
  set Mij := resolventC (zeroRC {b} H) z i j
  have a1 : ‖Gdj‖ ≤ P := hoff d j (Ne.symm hjd)
  have a2 : ‖Gij‖ ≤ P := hoff i j hij
  have a3 : ‖Mdj - Gdj‖ ≤ 10 * P ^ 2 := h1 d j hdb hjb
  have a4 : ‖Mij - Gij‖ ≤ 10 * P ^ 2 := h1 i j hib hjb
  have a5 : ‖Mdj‖ ≤ 2 * P := h2 d j (Ne.symm hjd)
  have hB : 0 ≤ B := (abs_nonneg _).trans hv
  have hδ : 0 ≤ δ := (abs_nonneg _).trans huv
  have e : (u : ℂ) * Gbb * Gdj * (starRingEnd ℂ) Gij - m * ((v : ℂ) * Mdj * (starRingEnd ℂ) Mij) =
      ((u - v : ℝ) : ℂ) * Gbb * Gdj * (starRingEnd ℂ) Gij +
        (v : ℂ) * (Gbb - m) * Gdj * (starRingEnd ℂ) Gij +
        (v : ℂ) * m * ((Gdj - Mdj) * (starRingEnd ℂ) Gij +
          Mdj * (starRingEnd ℂ) (Gij - Mij)) := by
    rw [map_sub]; push_cast; ring
  rw [e]
  have t1 : ‖((u - v : ℝ) : ℂ) * Gbb * Gdj * (starRingEnd ℂ) Gij‖ ≤ δ * 2 * P * P := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
    gcongr
  have t2 : ‖(v : ℂ) * (Gbb - m) * Gdj * (starRingEnd ℂ) Gij‖ ≤ B * P * P * P := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
    gcongr
  have t3 : ‖(Gdj - Mdj) * (starRingEnd ℂ) Gij + Mdj * (starRingEnd ℂ) (Gij - Mij)‖ ≤
      10 * P ^ 2 * P + 2 * P * (10 * P ^ 2) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_conj, norm_sub_rev]
      exact mul_le_mul a3 a2 (norm_nonneg _) (by positivity)
    · rw [norm_mul, Complex.norm_conj, norm_sub_rev]
      exact mul_le_mul a5 a4 (norm_nonneg _) (by positivity)
  have t4 : ‖(v : ℂ) * m * ((Gdj - Mdj) * (starRingEnd ℂ) Gij +
      Mdj * (starRingEnd ℂ) (Gij - Mij))‖ ≤ B * 1 * (10 * P ^ 2 * P + 2 * P * (10 * P ^ 2)) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
  calc _ ≤ _ := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add t1 t2)) t4)
    _ = 2 * P ^ 2 * δ + 31 * B * P ^ 3 := by ring

/-- The deterministic bound of the same difference: at most `2 Mf η⁻³` for `|F′| ≤ Mf`,
`η ≤ 1`, `|m| ≤ 1`. -/
private lemma eg_diff_bad {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (hz1 : z.im ≤ 1) {m : ℂ} (hm1 : ‖m‖ ≤ 1) (b d i j : Fin N)
    {u v Mf : ℝ} (hu : |u| ≤ Mf) (hv : |v| ≤ Mf) :
    ‖(u : ℂ) * resolventC H z b b * resolventC H z d j * (starRingEnd ℂ) (resolventC H z i j) -
        m * ((v : ℂ) * resolventC (zeroRC {b} H) z d j *
          (starRingEnd ℂ) (resolventC (zeroRC {b} H) z i j))‖ ≤ 2 * Mf / z.im ^ 3 := by
  have hM : 0 ≤ Mf := (abs_nonneg _).trans hu
  have hG : ∀ k l, ‖resolventC H z k l‖ ≤ 1 / z.im := fun k l => norm_resolventC_apply_le hH hz k l
  have hG' : ∀ k l, ‖resolventC (zeroRC {b} H) z k l‖ ≤ 1 / z.im := fun k l =>
    norm_resolventC_apply_le (zeroRC_isHermitian hH {b}) hz k l
  have hη : 1 ≤ 1 / z.im := by rw [le_div_iff₀ hz]; linarith
  have hη0 : 0 ≤ 1 / z.im := by positivity
  have t1 : ‖(u : ℂ) * resolventC H z b b * resolventC H z d j *
      (starRingEnd ℂ) (resolventC H z i j)‖ ≤ Mf * (1 / z.im) * (1 / z.im) * (1 / z.im) := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
    gcongr <;> exact hG _ _
  have t2 : ‖m * ((v : ℂ) * resolventC (zeroRC {b} H) z d j *
      (starRingEnd ℂ) (resolventC (zeroRC {b} H) z i j))‖ ≤
      1 * (Mf * (1 / z.im) * (1 / z.im)) := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
    gcongr <;> exact hG' _ _
  have e : 2 * Mf / z.im ^ 3 = 2 * (Mf * (1 / z.im) * (1 / z.im) * (1 / z.im)) := by
    field_simp
  rw [e]
  have : Mf * (1 / z.im) * (1 / z.im) ≤ Mf * (1 / z.im) * (1 / z.im) * (1 / z.im) :=
    le_mul_of_one_le_right (by positivity) hη
  refine (norm_sub_le _ _).trans ?_
  linarith


open private measurable_zeroEntry from WEdgeNS.Comparison.Telescope

private lemma eg_amgm {x y s : ℝ} (hs : 0 < s) : x * y ≤ x ^ 2 / (2 * s) + s * y ^ 2 / 2 := by
  rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (x - s * y), sq_nonneg s, mul_pos hs hs]

/-- (6.87) at one point `z` for a functional `φ` of the matrix, with the good event `Ω` on which
`|R_kl - δ_kl m| ≤ P`: the expectation is at most `E|D|²/(2P²) + P² E|L|²/2`, where
`R_ib = -R_bb L`, `L = Σ_k h_bk R^{(b)}_ki`, and `D` is the difference of `eg_diff_good`. -/
private lemma eg_core {N : ℕ} {L : EntryLaws N} {C0 : ℝ} (hL : L.IsGenWigner C0)
    {p : OffDiag N} {b d i j : Fin N} (hbd : (b = p.1.1 ∧ d = p.1.2) ∨ (b = p.1.2 ∧ d = p.1.1))
    (hij : i ≠ j) (hib : i ≠ b) (hjb : j ≠ b) (hjd : j ≠ d)
    {F : ℝ → ℝ} (hF4 : ContDiff ℝ 4 F) {z : ℂ} (hz : 0 < z.im) (hz1 : z.im ≤ 1)
    {m : ℂ} (hm1 : ‖m‖ ≤ 1) (hm5 : 1 / 5 ≤ ‖m‖) {P : ℝ} (hP0 : 0 < P) (hP : P ≤ 1 / 10)
    (hNP : 4 / (N : ℝ) ≤ P ^ 2)
    {φ : Matrix (Fin N) (Fin N) ℝ → ℝ} (hφc : Continuous fun ω : Entries N => φ (symOfEntries ω))
    {Mf : ℝ} (hMf : ∀ ω : Entries N, |iteratedDeriv 1 F (φ (symOfEntries ω))| ≤ Mf)
    {Ω : Set (Entries N)}
    (hΩ : ∀ ω ∈ Ω, ∀ k l, ‖resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) z k l -
      (if k = l then m else 0)‖ ≤ P)
    {B δ : ℝ}
    (hφΩ : ∀ ω ∈ Ω, |iteratedDeriv 1 F (φ (zeroRC {b} (symOfEntries ω)))| ≤ B ∧
      |iteratedDeriv 1 F (φ (symOfEntries (zeroEntry (Sum.inr p) ω))) -
        iteratedDeriv 1 F (φ (zeroRC {b} (symOfEntries ω)))| ≤ δ) :
    ‖∫ ω, ((iteratedDeriv 1 F (φ (symOfEntries (zeroEntry (Sum.inr p) ω))) : ℝ) : ℂ) *
        resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) z i b *
        resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) z d j *
        (starRingEnd ℂ) (resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) z i j) ∂L.law‖ ≤
      ((2 * P ^ 2 * δ + 31 * B * P ^ 3) ^ 2 + (2 * Mf / z.im ^ 3) ^ 2 * (L.law Ωᶜ).toReal) /
          (2 * P ^ 2) +
        P ^ 2 * (5 * P ^ 2 + (L.law Ωᶜ).toReal / z.im ^ 2) / 2 := by
  have hprob := isProbabilityMeasure_law hL.isProb
  have hN : 0 < N := Fin.pos i
  have hdb : d ≠ b := by
    rcases hbd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [p.2.ne', p.2.ne]
  have hb : b = p.1.1 ∨ b = p.1.2 := by
    rcases hbd with ⟨h, -⟩ | ⟨h, -⟩
    exacts [Or.inl h, Or.inr h]
  have hMf0 : 0 ≤ Mf := (abs_nonneg _).trans (hMf 0)
  have hη0 : 0 ≤ 1 / z.im := by positivity
  have hF1c : Continuous (iteratedDeriv 1 F) := hF4.continuous_iteratedDeriv 1 (by norm_num)
  -- measurability
  have hmR : ∀ k l, Measurable fun ω => resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) z k l :=
    fun k l => (continuous_resolventC_symOfEntries hz.ne' k l).measurable.comp
      (measurable_zeroEntry _)
  have hmRb : ∀ k l,
      Measurable fun ω : Entries N => resolventC (zeroRC {b} (symOfEntries ω)) z k l :=
    fun k l => (continuous_resolventC_zeroRC_symOfEntries {b} hz.ne' k l).measurable
  have hxb : ∀ ω, φ (zeroRC {b} (symOfEntries ω)) = φ (symOfEntries (zeroEntries {b} ω)) :=
    fun ω => by rw [symOfEntries_zeroEntries]
  have hmu : Measurable fun ω => ((iteratedDeriv 1 F (φ (symOfEntries (zeroEntry (Sum.inr p) ω)))
      : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (hF1c.measurable.comp (hφc.measurable.comp
      (measurable_zeroEntry _)))
  have hmv :
      Measurable fun ω => ((iteratedDeriv 1 F (φ (zeroRC {b} (symOfEntries ω))) : ℝ) : ℂ) := by
    simp_rw [hxb]
    exact Complex.measurable_ofReal.comp (hF1c.measurable.comp (hφc.measurable.comp
      (continuous_zeroEntries_entries {b}).measurable))
  have hu : ∀ ω, |iteratedDeriv 1 F (φ (symOfEntries (zeroEntry (Sum.inr p) ω)))| ≤ Mf :=
    fun ω => hMf _
  have hv : ∀ ω, |iteratedDeriv 1 F (φ (zeroRC {b} (symOfEntries ω)))| ≤ Mf :=
    fun ω => by rw [hxb]; exact hMf _
  -- row-independence
  have hiRb : ∀ k l,
      RowIndep {b} fun ω : Entries N => resolventC (zeroRC {b} (symOfEntries ω)) z k l :=
    fun k l => rowIndep_resolventC_zeroRC subset_rfl z k l
  have hiv :
      RowIndep {b} fun ω => ((iteratedDeriv 1 F (φ (zeroRC {b} (symOfEntries ω))) : ℝ) : ℂ) := by
    intro ω
    simp only
    rw [symOfEntries_zeroEntries, zeroRC_zeroRC, Finset.union_self]
  -- the coefficients `a_k` and the linear form `L`
  set a : Fin N → Entries N → ℂ := fun k ω =>
    if k = d then 0 else resolventC (zeroRC {b} (symOfEntries ω)) z k i with ha
  have hia : ∀ k, RowIndep {b} (a k) := by
    intro k ω
    simp only [ha]
    split_ifs
    · rfl
    · exact hiRb k i ω
  have hma : ∀ k, Measurable (a k) := by
    intro k
    simp only [ha]
    split_ifs
    · exact measurable_const
    · exact hmRb k i
  have haK : ∀ k ω, ‖a k ω‖ ≤ 1 / z.im := by
    intro k ω
    simp only [ha]
    split_ifs
    · simpa using hη0
    · exact norm_resolventC_apply_le (zeroRC_isHermitian (symOfEntries_isHermitian ω) {b}) hz k i
  have hab : ∀ ω, a b ω = 0 := by
    intro ω
    simp only [ha, hdb.symm, ite_false]
    rw [resolventC_zeroRC_apply_of_mem (symOfEntries_isHermitian ω) hz
      (Finset.mem_singleton_self b) i]
    simp [Ne.symm hib]
  -- the identity `R_ib = -R_bb L`
  have hschur : ∀ ω, resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) z i b =
      -(resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) z b b *
        ∑ k, (symOfEntries ω b k : ℂ) * a k ω) := by
    intro ω
    rw [eg_schur (symOfEntries_isHermitian _) hz hib, eg_zeroRC_zeroEntry hb ω]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eg_zeroEntry_row hbd ω k]
    simp only [ha]
    split_ifs <;> simp
  -- the factors `X`, `D` and the identity `Z + m X L = -D L`
  set Lf : Entries N → ℂ := fun ω => ∑ k, (symOfEntries ω b k : ℂ) * a k ω with hLf
  set X : Entries N → ℂ := fun ω =>
    ((iteratedDeriv 1 F (φ (zeroRC {b} (symOfEntries ω))) : ℝ) : ℂ) *
      resolventC (zeroRC {b} (symOfEntries ω)) z d j *
      (starRingEnd ℂ) (resolventC (zeroRC {b} (symOfEntries ω)) z i j) with hX
  set D : Entries N → ℂ := fun ω =>
    ((iteratedDeriv 1 F (φ (symOfEntries (zeroEntry (Sum.inr p) ω))) : ℝ) : ℂ) *
      resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) z b b *
      resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) z d j *
      (starRingEnd ℂ) (resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) z i j) - m * X ω
    with hD
  have hiX : RowIndep {b} X :=
    eg_rowIndep_mul (eg_rowIndep_mul hiv (hiRb d j)) (fun ω => by simp only [hiRb i j ω])
  have hmX : Measurable X :=
    (hmv.mul (hmRb d j)).mul (Complex.continuous_conj.measurable.comp (hmRb i j))
  have hXK : ∀ ω, ‖X ω‖ ≤ Mf * (1 / z.im) * (1 / z.im) := by
    intro ω
    have hH := zeroRC_isHermitian (symOfEntries_isHermitian ω) {b}
    simp only [hX, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
    gcongr
    exacts [hv ω, norm_resolventC_apply_le hH hz d j, norm_resolventC_apply_le hH hz i j]
  obtain ⟨hXL_int, hXL⟩ := eg_integral_mul_linear hL hia hma haK hiX hmX hXK
  have hmD : Measurable D := by
    refine (((hmu.mul (hmR b b)).mul (hmR d j)).mul
      (Complex.continuous_conj.measurable.comp (hmR i j))).sub (measurable_const.mul hmX)
  have hDK : ∀ ω, ‖D ω‖ ≤ 2 * Mf / z.im ^ 3 := by
    intro ω
    have h := eg_diff_bad (symOfEntries_isHermitian (zeroEntry (Sum.inr p) ω)) hz hz1 hm1 b d i j
      (hu ω) (hv ω)
    rw [eg_zeroRC_zeroEntry hb ω] at h
    exact h
  have hDgood : ∀ ω ∈ Ω, ‖D ω‖ ≤ 2 * P ^ 2 * δ + 31 * B * P ^ 3 := by
    intro ω hω
    have h := eg_diff_good (symOfEntries_isHermitian (zeroEntry (Sum.inr p) ω)) hz hm1 hm5
      hP0.le hP (hΩ ω hω) hdb hij hib hjb hjd (hφΩ ω hω).1 (hφΩ ω hω).2
    rw [eg_zeroRC_zeroEntry hb ω] at h
    exact h
  have hid : ∀ ω, ((iteratedDeriv 1 F (φ (symOfEntries (zeroEntry (Sum.inr p) ω))) : ℝ) : ℂ) *
        resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) z i b *
        resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) z d j *
        (starRingEnd ℂ) (resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) z i j) +
        m * (X ω * Lf ω) = -(D ω * Lf ω) := by
    intro ω
    rw [hschur ω]
    simp only [hD, hLf]
    ring
  -- `E Z = -E[D L]`
  have hZm : Measurable fun ω =>
      ((iteratedDeriv 1 F (φ (symOfEntries (zeroEntry (Sum.inr p) ω))) : ℝ) : ℂ) *
        resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) z i b *
        resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) z d j *
        (starRingEnd ℂ) (resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) z i j) :=
    ((hmu.mul (hmR i b)).mul (hmR d j)).mul (Complex.continuous_conj.measurable.comp (hmR i j))
  have hZ_int : Integrable (fun ω =>
      ((iteratedDeriv 1 F (φ (symOfEntries (zeroEntry (Sum.inr p) ω))) : ℝ) : ℂ) *
        resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) z i b *
        resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) z d j *
        (starRingEnd ℂ) (resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) z i j)) L.law := by
    refine Integrable.of_bound hZm.aestronglyMeasurable
      (Mf * (1 / z.im) * (1 / z.im) * (1 / z.im)) (ae_of_all _ fun ω => ?_)
    have hH := symOfEntries_isHermitian (zeroEntry (Sum.inr p) ω)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
    gcongr
    exacts [hu ω, norm_resolventC_apply_le hH hz i b, norm_resolventC_apply_le hH hz d j,
      norm_resolventC_apply_le hH hz i j]
  have hint_eq : ∫ ω, ((iteratedDeriv 1 F (φ (symOfEntries (zeroEntry (Sum.inr p) ω))) : ℝ) : ℂ) *
        resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) z i b *
        resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) z d j *
        (starRingEnd ℂ) (resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) z i j) ∂L.law =
      ∫ ω, -(D ω * Lf ω) ∂L.law := by
    have h1 := integral_add hZ_int (hXL_int.const_mul m)
    rw [integral_const_mul, hXL, mul_zero, add_zero] at h1
    rw [← h1]
    exact integral_congr_ae (ae_of_all _ hid)
  -- `|E[D L]| ≤ E|D|²/(2P²) + P² E|L|²/2`
  have hL2 := eg_integral_norm_sq_linear hL hia hma haK hab
  have hD2_int : Integrable (fun ω => ‖D ω‖ ^ 2) L.law :=
    Integrable.of_bound (hmD.norm.pow_const 2).aestronglyMeasurable ((2 * Mf / z.im ^ 3) ^ 2)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hDK ω) 2)
  have hP2 : 0 < P ^ 2 := by positivity
  have hmain : ‖∫ ω, -(D ω * Lf ω) ∂L.law‖ ≤
      (∫ ω, ‖D ω‖ ^ 2 ∂L.law) / (2 * P ^ 2) + P ^ 2 * (∫ ω, ‖Lf ω‖ ^ 2 ∂L.law) / 2 := by
    calc _ ≤ ∫ ω, ‖-(D ω * Lf ω)‖ ∂L.law := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, (‖D ω‖ ^ 2 / (2 * P ^ 2) + P ^ 2 * ‖Lf ω‖ ^ 2 / 2) ∂L.law := by
          refine integral_mono_of_nonneg (ae_of_all _ fun ω => norm_nonneg _)
            ((hD2_int.div_const _).add ((hL2.1.const_mul (P ^ 2)).div_const 2))
            (ae_of_all _ fun ω => ?_)
          simp only [norm_neg, norm_mul]
          exact eg_amgm hP2
      _ = _ := by
          rw [integral_add (hD2_int.div_const _) ((hL2.1.const_mul _).div_const _), integral_div,
            integral_div, integral_const_mul]
  -- the two second moments
  have hD2 : ∫ ω, ‖D ω‖ ^ 2 ∂L.law ≤ (2 * P ^ 2 * δ + 31 * B * P ^ 3) ^ 2 +
      (2 * Mf / z.im ^ 3) ^ 2 * (L.law Ωᶜ).toReal :=
    eg_integral_le_of_event hD2_int (by positivity)
      (fun ω hω => pow_le_pow_left₀ (norm_nonneg _) (hDgood ω (by simpa using hω)) 2)
      (fun ω => pow_le_pow_left₀ (norm_nonneg _) (hDK ω) 2)
  have hak_int : ∀ k, Integrable (fun ω => ‖a k ω‖ ^ 2) L.law := fun k =>
    Integrable.of_bound ((hma k).norm.pow_const 2).aestronglyMeasurable ((1 / z.im) ^ 2)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (haK k ω) 2)
  have hsum : ∫ ω, ∑ k, ‖a k ω‖ ^ 2 ∂L.law ≤
      (N * (4 * P ^ 2) + 4) + N * (1 / z.im) ^ 2 * (L.law Ωᶜ).toReal := by
    refine eg_integral_le_of_event (integrable_finsetSum _ fun k _ => hak_int k) (by positivity)
      (fun ω hω => ?_) (fun ω => ?_)
    · have hω' : ω ∈ Ω := by simpa using hω
      obtain ⟨-, h2, h3⟩ := eg_minor_bounds (symOfEntries_isHermitian (zeroEntry (Sum.inr p) ω))
        hz hm1 hm5 hP0.le hP (hΩ ω hω') b
      rw [eg_zeroRC_zeroEntry hb ω] at h2 h3
      calc ∑ k, ‖a k ω‖ ^ 2 ≤ ∑ k : Fin N, (4 * P ^ 2 + if k = i then 4 else 0) :=
            Finset.sum_le_sum fun k _ => by
              simp only [ha]
              split_ifs with hkd hki hki
              · simp only [norm_zero]; nlinarith [sq_nonneg P]
              · simp only [norm_zero]; nlinarith [sq_nonneg P]
              · subst hki
                have := pow_le_pow_left₀ (norm_nonneg _) (h3 k hib) 2
                nlinarith
              · have := pow_le_pow_left₀ (norm_nonneg _) (h2 k i hki) 2
                nlinarith
        _ = N * (4 * P ^ 2) + 4 := by
            simp [Finset.sum_add_distrib, Finset.sum_ite_eq']
    · calc ∑ k, ‖a k ω‖ ^ 2 ≤ ∑ _k : Fin N, (1 / z.im) ^ 2 :=
            Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (haK k ω) 2
        _ = N * (1 / z.im) ^ 2 := by simp
  have hL2b : ∫ ω, ‖Lf ω‖ ^ 2 ∂L.law ≤ 5 * P ^ 2 + (L.law Ωᶜ).toReal / z.im ^ 2 := by
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have e : ∫ ω, ‖Lf ω‖ ^ 2 ∂L.law = (N : ℝ)⁻¹ * ∫ ω, ∑ k, ‖a k ω‖ ^ 2 ∂L.law := by
      rw [integral_finsetSum _ fun k _ => hak_int k]
      exact hL2.2
    rw [e]
    calc (N : ℝ)⁻¹ * ∫ ω, ∑ k, ‖a k ω‖ ^ 2 ∂L.law ≤
        (N : ℝ)⁻¹ * ((N * (4 * P ^ 2) + 4) + N * (1 / z.im) ^ 2 * (L.law Ωᶜ).toReal) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 4 / N + 4 * P ^ 2 + (L.law Ωᶜ).toReal / z.im ^ 2 := by
          field_simp
          ring
      _ ≤ _ := by linarith
  rw [hint_eq]
  refine hmain.trans (add_le_add ?_ ?_)
  · exact div_le_div_of_nonneg_right hD2 (by positivity)
  · gcongr


/-! ### The two functionals on the good event -/

open private ward_continuous_b ward_continuous_b' ward_continuous_y ward_rpow_mul_exp_le
  ward_offsum_nonneg ward_eta_int_le from WEdgeNS.EdgeUniv.WardReduction

/-- `1/5 ≤ |m_sc(z)| ≤ 1` for `|Re z| ≤ 3`, `0 < Im z ≤ 1` ((2.10)). -/
private lemma eg_msc_bounds {z : ℂ} (hz : 0 < z.im) (hz1 : z.im ≤ 1) (hre : |z.re| ≤ 3) :
    ‖msc z‖ ≤ 1 ∧ 1 / 5 ≤ ‖msc z‖ := by
  obtain ⟨h1, h2⟩ := norm_msc_eq_inv_and_lt_one hz
  refine ⟨h2.le, ?_⟩
  have hpos : 0 < ‖msc z + z‖ := by
    have := im_msc_pos hz
    have h := Complex.abs_im_le_norm (msc z + z)
    rw [Complex.add_im, abs_of_pos (by linarith)] at h
    linarith
  have hle : ‖msc z + z‖ ≤ 5 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    have := norm_add_le (msc z) z
    rw [abs_of_pos hz] at *
    linarith
  rw [h1, ← one_div]
  exact div_le_div_of_nonneg_left (by norm_num) hpos hle

/-- (6.92) for `x_R = η² Σ_{k≠l} |R_kl|²` at `E + iη` on the good event. -/
private lemma eg_offWard_good {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {η P : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hP0 : 0 ≤ P) (hP : P ≤ 1 / 10) (hNP : 1 ≤ N * P)
    {E : ℝ} (hE : |E| ≤ 3)
    (hG : ∀ k l, ‖resolventC H ⟨E, η⟩ k l - (if k = l then msc ⟨E, η⟩ else 0)‖ ≤ P)
    (b : Fin N) :
    |offWard H ⟨E, η⟩| ≤ η ^ 2 * ((N : ℝ) ^ 2 * P ^ 2) ∧
      |offWard (zeroRC {b} H) ⟨E, η⟩| ≤ η ^ 2 * (4 * (N : ℝ) ^ 2 * P ^ 2) ∧
      |offWard H ⟨E, η⟩ - offWard (zeroRC {b} H) ⟨E, η⟩| ≤ η ^ 2 * (32 * (N : ℝ) ^ 2 * P ^ 3) := by
  obtain ⟨hm1, hm5⟩ := eg_msc_bounds (z := ⟨E, η⟩) hη hη1 hE
  obtain ⟨s1, s2, s3⟩ := eg_offSum_bounds hH (z := ⟨E, η⟩) hη hm1 hm5 hP0 hP hNP hG b
  have n1 := ward_offsum_nonneg H ⟨E, η⟩
  have n2 := ward_offsum_nonneg (zeroRC {b} H) ⟨E, η⟩
  have e1 : offWard H ⟨E, η⟩ = η ^ 2 *
      ∑ k, ∑ l, if k = l then (0 : ℝ) else ‖resolventC H ⟨E, η⟩ k l‖ ^ 2 := rfl
  have e2 : offWard (zeroRC {b} H) ⟨E, η⟩ = η ^ 2 *
      ∑ k, ∑ l, if k = l then (0 : ℝ) else ‖resolventC (zeroRC {b} H) ⟨E, η⟩ k l‖ ^ 2 := rfl
  have hη2 : 0 ≤ η ^ 2 := sq_nonneg η
  rw [e1, e2, ← mul_sub, abs_mul, abs_mul, abs_mul, abs_of_nonneg hη2, abs_of_nonneg n1,
    abs_of_nonneg n2]
  exact ⟨mul_le_mul_of_nonneg_left s1 hη2, mul_le_mul_of_nonneg_left s2 hη2,
    mul_le_mul_of_nonneg_left s3 hη2⟩

/-- (6.92) for `x_R = η ∫_{E₁}^{E₂} Σ_{k≠l} |R_kl(y + iη)|² dy` on the good event. -/
private lemma eg_offWardInt_good {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {η P w : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hP0 : 0 ≤ P) (hP : P ≤ 1 / 10) (hNP : 1 ≤ N * P)
    (hw : w ≤ 1) {b : Fin N}
    (hc1 : Continuous fun y : ℝ =>
      ∑ k, ∑ l, if k = l then (0 : ℝ) else ‖resolventC H ⟨y, η⟩ k l‖ ^ 2)
    (hc2 : Continuous fun y : ℝ =>
      ∑ k, ∑ l, if k = l then (0 : ℝ) else ‖resolventC (zeroRC {b} H) ⟨y, η⟩ k l‖ ^ 2)
    (hG : ∀ E : ℝ, |E - 2| ≤ w → ∀ k l,
      ‖resolventC H ⟨E, η⟩ k l - (if k = l then msc ⟨E, η⟩ else 0)‖ ≤ P)
    {E₁ E₂ : ℝ} (h1 : |E₁ - 2| ≤ w) (h2 : |E₂ - 2| ≤ w) :
    |offWardInt H η E₁ E₂| ≤ η * ((N : ℝ) ^ 2 * P ^ 2 * (2 * w)) ∧
      |offWardInt (zeroRC {b} H) η E₁ E₂| ≤ η * (4 * (N : ℝ) ^ 2 * P ^ 2 * (2 * w)) ∧
      |offWardInt H η E₁ E₂ - offWardInt (zeroRC {b} H) η E₁ E₂| ≤
        η * (32 * (N : ℝ) ^ 2 * P ^ 3 * (2 * w)) := by
  have a1 := abs_le.1 h1
  have a2 := abs_le.1 h2
  have hΔ : |E₂ - E₁| ≤ 2 * w := abs_le.2 ⟨by linarith, by linarith⟩
  have hy : ∀ y ∈ Set.uIoc E₁ E₂, |y - 2| ≤ w := by
    intro y hy
    rcases Set.mem_uIcc.1 (Set.uIoc_subset_uIcc hy) with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩ <;>
      exact abs_le.2 ⟨by linarith, by linarith⟩
  have hbd : ∀ y ∈ Set.uIoc E₁ E₂, _ := fun y hy' => by
    have hy3 : |y| ≤ 3 := by
      have := abs_le.1 (hy y hy')
      exact abs_le.2 ⟨by linarith, by linarith⟩
    obtain ⟨hm1, hm5⟩ := eg_msc_bounds (z := ⟨y, η⟩) hη hη1 hy3
    exact eg_offSum_bounds hH (z := ⟨y, η⟩) hη hm1 hm5 hP0 hP hNP (hG y (hy y hy')) b
  have e3 : offWardInt H η E₁ E₂ - offWardInt (zeroRC {b} H) η E₁ E₂ = η * ∫ y in E₁..E₂,
      ((∑ k, ∑ l, if k = l then (0 : ℝ) else ‖resolventC H ⟨y, η⟩ k l‖ ^ 2) -
        ∑ k, ∑ l, if k = l then (0 : ℝ) else ‖resolventC (zeroRC {b} H) ⟨y, η⟩ k l‖ ^ 2) := by
    rw [intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
      mul_sub]
    rfl
  have hfin : ∀ K : ℝ, 0 ≤ K → η * (K * |E₂ - E₁|) ≤ η * (K * (2 * w)) := fun K hK =>
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΔ hK) hη.le
  refine ⟨(ward_eta_int_le hη fun y hy' => ?_).trans (hfin _ (by positivity)),
    (ward_eta_int_le hη fun y hy' => ?_).trans (hfin _ (by positivity)), ?_⟩
  · rw [abs_of_nonneg (ward_offsum_nonneg _ _)]; exact (hbd y hy').1
  · rw [abs_of_nonneg (ward_offsum_nonneg _ _)]; exact (hbd y hy').2.1
  · rw [e3]
    exact (ward_eta_int_le hη fun y hy' => (hbd y hy').2.2).trans (hfin _ (by positivity))

/-! ### Bookkeeping of the powers of `N` -/

/-- Mean value inequality for `F′`: `|F′ y - F′ x| ≤ B |y - x|` for `|x|, |y| ≤ R` when
`|F″| ≤ B` on `[-R, R]`. -/
private lemma eg_deriv_sub_le {F : ℝ → ℝ} (hF : ContDiff ℝ 4 F) {R B : ℝ}
    (hB : ∀ ζ : ℝ, |ζ| ≤ R → |iteratedDeriv 2 F ζ| ≤ B) {x y : ℝ} (hx : |x| ≤ R)
    (hy : |y| ≤ R) : |iteratedDeriv 1 F y - iteratedDeriv 1 F x| ≤ B * |y - x| := by
  have hd : Differentiable ℝ (iteratedDeriv 1 F) :=
    hF.differentiable_iteratedDeriv 1 (by norm_num)
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := iteratedDeriv 1 F)
    (s := Set.Icc (-R) R) (C := B) (x := x) (y := y) (fun x _ => hd.differentiableAt)
    (fun x hx => by
      rw [← iteratedDeriv_succ]
      exact hB x (abs_le.2 hx)) (convex_Icc _ _) (abs_le.1 hx) (abs_le.1 hy)
  simpa [Real.norm_eq_abs] using this

/-- The powers of `N` in terms of `a = N^{1/3}` and `t = N^ε`. -/
private lemma eg_rpow_params {N : ℕ} (hN : 1 ≤ N) (ε : ℝ) :
    (N : ℝ) = ((N : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 ∧
    (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) = 1 / (((N : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 * (N : ℝ) ^ ε) ∧
    (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) = (N : ℝ) ^ ε / ((N : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 ∧
    (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) = ((N : ℝ) ^ ε) ^ 3 / (N : ℝ) ^ ((1 : ℝ) / 3) ∧
    (N : ℝ) ^ ((1 : ℝ) / 3 - 3 * ε) = (N : ℝ) ^ ((1 : ℝ) / 3) / ((N : ℝ) ^ ε) ^ 3 ∧
    (N : ℝ) ^ (7 * ε) = ((N : ℝ) ^ ε) ^ 7 := by
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow : ∀ (u : ℝ) (k : ℕ), ((N : ℝ) ^ u) ^ k = (N : ℝ) ^ (u * k) := fun u k => by
    rw [← Real.rpow_mul_natCast hn0.le]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpow]; norm_num
  · rw [hpow, one_div, ← Real.rpow_add hn0, ← Real.rpow_neg hn0.le]
    congr 1; push_cast; ring
  · rw [hpow, ← Real.rpow_sub hn0]
    congr 1; push_cast; ring
  · rw [hpow, ← Real.rpow_sub hn0]
    congr 1; push_cast; ring
  · rw [hpow, ← Real.rpow_sub hn0]
    congr 1; push_cast; ring
  · rw [hpow]; congr 1; push_cast; ring

/-- The normalisation of the conclusion: `N^{-4/3+(14 CF+27)ε} = (N^{(7CF+1)ε})² t^{25} / a⁴`. -/
private lemma eg_rpow_target {N : ℕ} (hN : 1 ≤ N) {CF : ℝ} (hCF : 0 ≤ CF) (ε : ℝ) :
    (N : ℝ) ^ (-(4 : ℝ) / 3 + (14 * |CF| + 27) * ε) =
      ((N : ℝ) ^ ((7 * CF + 1) * ε)) ^ 2 * ((N : ℝ) ^ ε) ^ 25 / ((N : ℝ) ^ ((1 : ℝ) / 3)) ^ 4 := by
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_of_nonneg hCF, ← Real.rpow_mul_natCast hn0.le, ← Real.rpow_mul_natCast hn0.le,
    ← Real.rpow_mul_natCast hn0.le, ← Real.rpow_add hn0, ← Real.rpow_sub hn0]
  congr 1
  push_cast
  ring

/-- The bad event is beaten by `exp(-c φ)`: `(2 Mf² + 1) N⁶ P(Ωᶜ) ≤ 1` with
`Mf = CF (1 + 2N³)^CF`. -/
private lemma eg_bad_le {CF c Cb : ℝ} (hCF : 0 ≤ CF) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ pr : ℝ, pr ≤ (N : ℝ) ^ Cb * Real.exp (-c * phi N ^ (1 : ℝ)) →
      (2 * (CF * (1 + 2 * (N : ℝ) ^ 3) ^ CF) ^ 2 + 1) * (N : ℝ) ^ 6 * pr ≤ 1 := by
  filter_upwards [ward_rpow_mul_exp_le c (6 * CF + 7 + Cb) hc, eventually_ge_atTop 1,
    eventually_ge_atTop ⌈2 * CF ^ 2 * 9 ^ CF + 1⌉₊] with N hN hN1 hNK pr hpr
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < N := by linarith
  have hK : 2 * CF ^ 2 * 9 ^ CF + 1 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNK)
  rw [Real.rpow_one] at hpr
  set e := Real.exp (-c * phi N) with he_def
  have he : 0 ≤ e := (Real.exp_pos _).le
  have h3 : 1 + 2 * (N : ℝ) ^ 3 ≤ 3 * (N : ℝ) ^ 3 := by
    nlinarith [pow_le_pow_left₀ zero_le_one hn1 3]
  have hrp : (1 + 2 * (N : ℝ) ^ 3) ^ CF ≤ 3 ^ CF * (N : ℝ) ^ (3 * CF) := by
    calc (1 + 2 * (N : ℝ) ^ 3) ^ CF ≤ (3 * (N : ℝ) ^ 3) ^ CF :=
          Real.rpow_le_rpow (by positivity) h3 hCF
      _ = 3 ^ CF * ((N : ℝ) ^ 3) ^ CF := Real.mul_rpow (by norm_num) (by positivity)
      _ = 3 ^ CF * (N : ℝ) ^ (3 * CF) := by
          rw [← Real.rpow_natCast (N : ℝ) 3, ← Real.rpow_mul hn0.le]
          norm_num
  have hMf0 : 0 ≤ CF * (1 + 2 * (N : ℝ) ^ 3) ^ CF := by positivity
  have hMf : CF * (1 + 2 * (N : ℝ) ^ 3) ^ CF ≤ CF * 3 ^ CF * (N : ℝ) ^ (3 * CF) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hrp hCF
  have h9 : ((3 : ℝ) ^ CF) ^ 2 = 9 ^ CF := by
    rw [sq, ← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have hN6 : ((N : ℝ) ^ (3 * CF)) ^ 2 = (N : ℝ) ^ (6 * CF) := by
    rw [← Real.rpow_mul_natCast hn0.le]; congr 1; push_cast; ring
  have hNC : 1 ≤ (N : ℝ) ^ (6 * CF) := Real.one_le_rpow hn1 (by positivity)
  have hM2 : 2 * (CF * (1 + 2 * (N : ℝ) ^ 3) ^ CF) ^ 2 + 1 ≤
      (2 * CF ^ 2 * 9 ^ CF + 1) * (N : ℝ) ^ (6 * CF) := by
    have := pow_le_pow_left₀ hMf0 hMf 2
    have e2 : (CF * 3 ^ CF * (N : ℝ) ^ (3 * CF)) ^ 2 = CF ^ 2 * 9 ^ CF * (N : ℝ) ^ (6 * CF) := by
      rw [mul_pow, mul_pow, h9, hN6]
    nlinarith
  have hfin : (N : ℝ) * (N : ℝ) ^ (6 * CF) * (N : ℝ) ^ 6 * ((N : ℝ) ^ Cb * e) ≤ 1 := by
    have : (N : ℝ) * (N : ℝ) ^ (6 * CF) * (N : ℝ) ^ 6 * (N : ℝ) ^ Cb =
        (N : ℝ) ^ (6 * CF + 7 + Cb) := by
      rw [Real.rpow_add hn0, Real.rpow_add hn0, show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      ring
    calc _ = (N : ℝ) * (N : ℝ) ^ (6 * CF) * (N : ℝ) ^ 6 * (N : ℝ) ^ Cb * e := by ring
      _ = _ := by rw [this]
      _ ≤ 1 := hN
  have hcoef : 0 ≤ (2 * (CF * (1 + 2 * (N : ℝ) ^ 3) ^ CF) ^ 2 + 1) * (N : ℝ) ^ 6 := by positivity
  calc _ ≤ (2 * (CF * (1 + 2 * (N : ℝ) ^ 3) ^ CF) ^ 2 + 1) * (N : ℝ) ^ 6 *
        ((N : ℝ) ^ Cb * e) := mul_le_mul_of_nonneg_left hpr hcoef
    _ ≤ (N : ℝ) * (N : ℝ) ^ (6 * CF) * (N : ℝ) ^ 6 * ((N : ℝ) ^ Cb * e) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
          (by positivity)
        nlinarith
    _ ≤ 1 := hfin


/-- The final bookkeeping with `P = t³/a`, `η = 1/(a²t)`, `N = a³`, `δ = 64 B t⁹/a`: the bound of
the core estimate is at most `B² t^{25} / a⁴`. -/
private lemma eg_final_arith {a t B Mf pr : ℝ} (ha : 1 ≤ a) (ht : 12644 ≤ t) (hta : t ≤ a)
    (hB : 1 ≤ B) (hpr : 0 ≤ pr) (hbad : (2 * Mf ^ 2 + 1) * (a ^ 3) ^ 6 * pr ≤ 1) :
    ((2 * (t ^ 3 / a) ^ 2 * (B * (64 * t ^ 9 / a)) + 31 * B * (t ^ 3 / a) ^ 3) ^ 2 +
        (2 * Mf / (1 / (a ^ 2 * t)) ^ 3) ^ 2 * pr) / (2 * (t ^ 3 / a) ^ 2) +
      (t ^ 3 / a) ^ 2 * (5 * (t ^ 3 / a) ^ 2 + pr / (1 / (a ^ 2 * t)) ^ 2) / 2 ≤
    B ^ 2 * t ^ 25 / a ^ 4 := by
  have ha0 : 0 < a := by linarith
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have e : ((2 * (t ^ 3 / a) ^ 2 * (B * (64 * t ^ 9 / a)) + 31 * B * (t ^ 3 / a) ^ 3) ^ 2 +
        (2 * Mf / (1 / (a ^ 2 * t)) ^ 3) ^ 2 * pr) / (2 * (t ^ 3 / a) ^ 2) +
      (t ^ 3 / a) ^ 2 * (5 * (t ^ 3 / a) ^ 2 + pr / (1 / (a ^ 2 * t)) ^ 2) / 2 =
      (B ^ 2 * t ^ 12 * (128 * t ^ 6 + 31) ^ 2 / 2 + 2 * (Mf ^ 2 * (a ^ 3) ^ 6 * pr) +
        5 * t ^ 12 / 2 + t ^ 8 * a ^ 6 * pr / 2) / a ^ 4 := by
    field_simp
    ring
  rw [e]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have ht6 : 1 ≤ t ^ 6 := one_le_pow₀ ht1
  have h1 : (128 * t ^ 6 + 31) ^ 2 ≤ (159 * t ^ 6) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h2 : B ^ 2 * t ^ 12 * (128 * t ^ 6 + 31) ^ 2 ≤ 25281 * (B ^ 2 * t ^ 24) := by
    calc _ ≤ B ^ 2 * t ^ 12 * (159 * t ^ 6) ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  have h3 : t ^ 8 * a ^ 6 * pr ≤ (a ^ 3) ^ 6 * pr := by
    refine mul_le_mul_of_nonneg_right ?_ hpr
    calc t ^ 8 * a ^ 6 ≤ a ^ 8 * a ^ 6 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht0.le hta 8) (by positivity)
      _ = a ^ 14 := by ring
      _ ≤ a ^ 18 := pow_le_pow_right₀ ha (by norm_num)
      _ = (a ^ 3) ^ 6 := by ring
  have hB2 : 1 ≤ B ^ 2 := one_le_pow₀ hB
  have ht24 : 1 ≤ t ^ 24 := one_le_pow₀ ht1
  have h4 : t ^ 12 ≤ B ^ 2 * t ^ 24 := by
    calc t ^ 12 ≤ t ^ 24 := pow_le_pow_right₀ ht1 (by norm_num)
      _ ≤ B ^ 2 * t ^ 24 := le_mul_of_one_le_left (by positivity) hB2
  have h5 : 1 ≤ B ^ 2 * t ^ 24 := one_le_mul_of_one_le_of_one_le hB2 ht24
  have h6 : 12644 * (B ^ 2 * t ^ 24) ≤ B ^ 2 * t ^ 25 := by
    have : B ^ 2 * t ^ 25 = t * (B ^ 2 * t ^ 24) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right ht (by positivity)
  have hb : 2 * (Mf ^ 2 * (a ^ 3) ^ 6 * pr) + (a ^ 3) ^ 6 * pr ≤ 1 := by
    have : (2 * Mf ^ 2 + 1) * (a ^ 3) ^ 6 * pr = 2 * (Mf ^ 2 * (a ^ 3) ^ 6 * pr) +
      (a ^ 3) ^ 6 * pr := by ring
    linarith
  have h7 : 0 ≤ (a ^ 3) ^ 6 * pr := by positivity
  linarith


/-- The good-event sizes of the two functionals in terms of `a = N^{1/3}`, `t = N^ε`. -/
private lemma eg_sizes {a t n η P w : ℝ} (ha : 1 ≤ a) (ht : 8 ≤ t) (hn : n = a ^ 3)
    (hη : η = 1 / (a ^ 2 * t)) (hP : P = t ^ 3 / a) (hw : w = t / a ^ 2) :
    η ^ 2 * (n ^ 2 * P ^ 2) ≤ t ^ 7 ∧ η ^ 2 * (4 * n ^ 2 * P ^ 2) ≤ t ^ 7 ∧
    η ^ 2 * (32 * n ^ 2 * P ^ 3) ≤ 64 * t ^ 9 / a ∧
    η * (n ^ 2 * P ^ 2 * (2 * w)) ≤ t ^ 7 ∧ η * (4 * n ^ 2 * P ^ 2 * (2 * w)) ≤ t ^ 7 ∧
    η * (32 * n ^ 2 * P ^ 3 * (2 * w)) ≤ 64 * t ^ 9 / a := by
  have ha0 : 0 < a := by linarith
  have ht0 : 0 < t := by linarith
  subst hn hη hP hw
  have e1 : (1 / (a ^ 2 * t)) ^ 2 * ((a ^ 3) ^ 2 * (t ^ 3 / a) ^ 2) = t ^ 4 := by
    field_simp
  have e2 : (1 / (a ^ 2 * t)) ^ 2 * (32 * (a ^ 3) ^ 2 * (t ^ 3 / a) ^ 3) = 32 * t ^ 7 / a := by
    field_simp
  have e3 : 1 / (a ^ 2 * t) * ((a ^ 3) ^ 2 * (t ^ 3 / a) ^ 2 * (2 * (t / a ^ 2))) = 2 * t ^ 6 := by
    field_simp
  have e4 : 1 / (a ^ 2 * t) * (32 * (a ^ 3) ^ 2 * (t ^ 3 / a) ^ 3 * (2 * (t / a ^ 2))) =
      64 * t ^ 9 / a := by
    field_simp; ring
  have t43 : 8 * t ^ 4 ≤ t ^ 7 := by
    have : t ^ 7 = t ^ 3 * t ^ 4 := by ring
    rw [this]
    have : 8 ≤ t ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) ht 3]
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have t6 : 8 * t ^ 6 ≤ t ^ 7 := by
    have : t ^ 7 = t * t ^ 6 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right ht (by positivity)
  have t79 : 32 * t ^ 7 / a ≤ 64 * t ^ 9 / a := by
    refine div_le_div_of_nonneg_right ?_ ha0.le
    have : t ^ 9 = t ^ 2 * t ^ 7 := by ring
    rw [this]
    nlinarith [pow_pos ht0 7, pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) ht 2]
  have ht4 : 0 ≤ t ^ 4 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1]; linarith
  · have : (1 / (a ^ 2 * t)) ^ 2 * (4 * (a ^ 3) ^ 2 * (t ^ 3 / a) ^ 2) = 4 * t ^ 4 := by
      rw [← e1]; ring
    rw [this]; linarith
  · rw [e2]; exact t79
  · rw [e3]; nlinarith [pow_pos ht0 6]
  · have : 1 / (a ^ 2 * t) * (4 * (a ^ 3) ^ 2 * (t ^ 3 / a) ^ 2 * (2 * (t / a ^ 2))) =
        8 * t ^ 6 := by rw [show (8 : ℝ) * t ^ 6 = 4 * (2 * t ^ 6) by ring, ← e3]; ring
    rw [this]; exact t6
  · rw [e4]

/-- Deterministic size of the off-diagonal Ward sum: `Σ_{k≠l} |G_kl|² ≤ N² η⁻²`. -/
private lemma eg_offSum_le_det {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {η : ℝ} (hη : 0 < η) (y : ℝ) :
    (∑ k, ∑ l, if k = l then (0 : ℝ) else ‖resolventC H ⟨y, η⟩ k l‖ ^ 2) ≤
      (N : ℝ) ^ 2 * (1 / η) ^ 2 := by
  calc _ ≤ ∑ _k : Fin N, ∑ _l : Fin N, (1 / η) ^ 2 :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => by
          split_ifs
          · positivity
          · exact pow_le_pow_left₀ (norm_nonneg _)
              (norm_resolventC_apply_le hH (z := ⟨y, η⟩) hη k l) 2
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring


/-! ### (6.87) at one point -/

/-- (6.87) at one point `y ∈ I_ε` for a functional `φ` of the matrix with the good-event sizes
of `eg_sizes`, once the powers of `N` satisfy the listed lower bounds. -/
private lemma eg_point {N : ℕ} {L : EntryLaws N} {C0 : ℝ} (hL : L.IsGenWigner C0)
    {CF ε : ℝ} (hCF : 0 ≤ CF) (hε : 0 < ε) (hN1 : 1 ≤ N)
    (ht : 12644 ≤ (N : ℝ) ^ ε) (hta : (N : ℝ) ^ ε ≤ (N : ℝ) ^ ((1 : ℝ) / 3))
    (h10 : 10 ≤ (N : ℝ) ^ ((1 : ℝ) / 3 - 3 * ε)) (h4 : 4 ≤ (N : ℝ) ^ ((1 : ℝ) / 3))
    {p : OffDiag N} {b d i j : Fin N} (hbd : (b = p.1.1 ∧ d = p.1.2) ∨ (b = p.1.2 ∧ d = p.1.1))
    (hij : i ≠ j) (hib : i ≠ b) (hjb : j ≠ b) (hjd : j ≠ d)
    {F : ℝ → ℝ} (hF4 : ContDiff ℝ 4 F)
    (hF : ∀ n ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF)
    (hF7 : ∀ ζ : ℝ, |ζ| ≤ (N : ℝ) ^ (7 * ε) → ∀ n ∈ Finset.Icc 1 4,
      |iteratedDeriv n F ζ| ≤ (N : ℝ) ^ ((7 * CF + 1) * ε))
    {y : ℝ} (hy : |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε))
    {Ω : Set (Entries N)}
    (hΩ : ∀ ω ∈ Ω, ∀ k l, ‖resolventC (symOfEntries (zeroEntry (Sum.inr p) ω))
        ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l -
      (if k = l then msc ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ else 0)‖ ≤
        (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε))
    (hpr : (2 * (CF * (1 + 2 * (N : ℝ) ^ 3) ^ CF) ^ 2 + 1) * (N : ℝ) ^ 6 *
      (L.law Ωᶜ).toReal ≤ 1)
    {φ : Matrix (Fin N) (Fin N) ℝ → ℝ} (hφc : Continuous fun ω : Entries N => φ (symOfEntries ω))
    (hφb : ∀ ω : Entries N, |φ (symOfEntries ω)| ≤ 2 * (N : ℝ) ^ 3)
    (hφΩ : ∀ ω ∈ Ω, |φ (symOfEntries (zeroEntry (Sum.inr p) ω))| ≤ (N : ℝ) ^ (7 * ε) ∧
      |φ (zeroRC {b} (symOfEntries ω))| ≤ (N : ℝ) ^ (7 * ε) ∧
      |φ (symOfEntries (zeroEntry (Sum.inr p) ω)) - φ (zeroRC {b} (symOfEntries ω))| ≤
        64 * ((N : ℝ) ^ ε) ^ 9 / (N : ℝ) ^ ((1 : ℝ) / 3)) :
    ‖∫ ω, ((iteratedDeriv 1 F (φ (symOfEntries (zeroEntry (Sum.inr p) ω))) : ℝ) : ℂ) *
        resolventC (symOfEntries (zeroEntry (Sum.inr p) ω))
          ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i b *
        resolventC (symOfEntries (zeroEntry (Sum.inr p) ω))
          ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ d j *
        (starRingEnd ℂ) (resolventC (symOfEntries (zeroEntry (Sum.inr p) ω))
          ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i j) ∂L.law‖ ≤
      (N : ℝ) ^ (-(4 : ℝ) / 3 + (14 * |CF| + 27) * ε) := by
  obtain ⟨hNa, hηa, hwa, hPa, h13, h7⟩ := eg_rpow_params hN1 ε
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have ha1 : 1 ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by linarith
  have ha0 : 0 < (N : ℝ) ^ ((1 : ℝ) / 3) := by linarith
  have ht1 : 1 ≤ (N : ℝ) ^ ε := by linarith
  have ht0 : 0 < (N : ℝ) ^ ε := by linarith
  have hP0 : 0 < (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) := Real.rpow_pos_of_pos hn0 _
  have hP : (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) ≤ 1 / 10 := by
    rw [h13, le_div_iff₀ (by positivity)] at h10
    rw [hPa, div_le_iff₀ ha0]
    linarith
  have hNP : 4 / (N : ℝ) ≤ ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 2 := by
    rw [hPa, div_pow, div_le_div_iff₀ hn0 (by positivity)]
    have h1 : 1 ≤ (((N : ℝ) ^ ε) ^ 3) ^ 2 := one_le_pow₀ (one_le_pow₀ ht1)
    have h2 : 4 * ((N : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 ≤ ((N : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg ((N : ℝ) ^ ((1 : ℝ) / 3))) (sub_nonneg.2 h4)]
    calc 4 * ((N : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 ≤ ((N : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := h2
      _ = N := hNa.symm
      _ ≤ _ := le_mul_of_one_le_left hn0.le h1
  have hη0 : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) := Real.rpow_pos_of_pos hn0 _
  have hη1 : (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) ≤ 1 := by
    rw [hηa, div_le_one (by positivity)]
    nlinarith [one_le_pow₀ (n := 2) ha1]
  have hw1 : (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) ≤ 1 := by
    rw [hwa, div_le_one (by positivity)]
    nlinarith
  have hy3 : |y| ≤ 3 := by
    obtain ⟨h1, h2⟩ := abs_le.1 hy
    exact abs_le.2 ⟨by linarith, by linarith⟩
  obtain ⟨hm1, hm5⟩ := eg_msc_bounds (z := ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩) hη0 hη1 hy3
  have hMf : ∀ ω : Entries N,
      |iteratedDeriv 1 F (φ (symOfEntries ω))| ≤ CF * (1 + 2 * (N : ℝ) ^ 3) ^ CF :=
    fun ω => abs_iteratedDeriv_le_of_abs_le hF (hφb ω) 1 (by simp)
  have hB1 : 1 ≤ (N : ℝ) ^ ((7 * CF + 1) * ε) :=
    Real.one_le_rpow (by exact_mod_cast hN1) (by positivity)
  have hφΩ' : ∀ ω ∈ Ω, |iteratedDeriv 1 F (φ (zeroRC {b} (symOfEntries ω)))| ≤
        (N : ℝ) ^ ((7 * CF + 1) * ε) ∧
      |iteratedDeriv 1 F (φ (symOfEntries (zeroEntry (Sum.inr p) ω))) -
        iteratedDeriv 1 F (φ (zeroRC {b} (symOfEntries ω)))| ≤
        (N : ℝ) ^ ((7 * CF + 1) * ε) * (64 * ((N : ℝ) ^ ε) ^ 9 / (N : ℝ) ^ ((1 : ℝ) / 3)) := by
    intro ω hω
    obtain ⟨h1, h2, h3⟩ := hφΩ ω hω
    refine ⟨hF7 _ h2 1 (by simp), ?_⟩
    refine (eg_deriv_sub_le hF4 (fun ζ hζ => hF7 ζ hζ 2 (by simp)) h2 h1).trans ?_
    exact mul_le_mul_of_nonneg_left h3 (by linarith)
  have hcore := eg_core hL hbd hij hib hjb hjd hF4 (z := ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩)
    hη0 hη1 hm1 hm5 hP0 hP hNP hφc hMf hΩ hφΩ'
  have hbad : (2 * (CF * (1 + 2 * (N : ℝ) ^ 3) ^ CF) ^ 2 + 1) *
      (((N : ℝ) ^ ((1 : ℝ) / 3)) ^ 3) ^ 6 * (L.law Ωᶜ).toReal ≤ 1 := by
    rw [← hNa]; exact hpr
  refine hcore.trans ?_
  dsimp only
  rw [hPa, hηa, eg_rpow_target hN1 hCF ε]
  exact eg_final_arith ha1 ht hta hB1 ENNReal.toReal_nonneg hbad


/-- The deterministic sizes of the two functionals: at most `2N³`. -/
private lemma eg_big {a t n η w Δ : ℝ} (ha : 1 ≤ a) (ht : 1 ≤ t) (hta : t ≤ a) (hn : n = a ^ 3)
    (hη : η = 1 / (a ^ 2 * t)) (hw : w = t / a ^ 2) (hΔ : |Δ| ≤ 2 * w) :
    η * (n ^ 2 * (1 / η) ^ 2 * |Δ|) ≤ 2 * n ^ 3 ∧ η ^ 2 * (n ^ 2 * (1 / η) ^ 2) ≤ 2 * n ^ 3 := by
  have ha0 : 0 < a := by linarith
  have ht0 : 0 < t := by linarith
  subst hn hη hw
  constructor
  · calc 1 / (a ^ 2 * t) * ((a ^ 3) ^ 2 * (1 / (1 / (a ^ 2 * t))) ^ 2 * |Δ|) ≤
        1 / (a ^ 2 * t) * ((a ^ 3) ^ 2 * (1 / (1 / (a ^ 2 * t))) ^ 2 * (2 * (t / a ^ 2))) := by
          gcongr
      _ = 2 * a ^ 6 * t ^ 2 := by field_simp
      _ ≤ 2 * a ^ 6 * a ^ 3 := by
          have h1 : t ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ ht0.le hta 2
          have h2 : a ^ 2 ≤ a ^ 3 := pow_le_pow_right₀ ha (by norm_num)
          gcongr
          linarith
      _ = 2 * (a ^ 3) ^ 3 := by ring
  · have e : (1 / (a ^ 2 * t)) ^ 2 * ((a ^ 3) ^ 2 * (1 / (1 / (a ^ 2 * t))) ^ 2) = (a ^ 3) ^ 2 := by
      field_simp
    rw [e]
    have : 1 ≤ a ^ 3 := one_le_pow₀ ha
    nlinarith [pow_pos ha0 3]

/-! ### [16] Lemma 6.8 at `f = 0` -/

/-- [16] Lemma 6.8, (6.87) at `f = 0`: for the off-diagonal entry `e = (b, d)` (either order) and
`i, j, b, d` distinct, `|E F′(x_R) R_ib R_dj conj(R_ij)(y + iη)| ≤ N^{-4/3+Cε}` (`= N^{Cε} p^{-4}`,
`p⁻¹ = N^{-1/3+3ε}`), uniformly in `y ∈ I_ε`, for every `H_γ` and both functionals `x_R`; `C`
depends only on `CF`. -/
theorem expectation_gain_largeQ {CF C0 φs : ℝ} (hC0 : 0 ≤ C0) (hφs : 1 / 3 < φs)
    (hφs' : φs ≤ 1 / 2) :
    ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < 1 / 10 → ∃ N0 : ℕ, ∀ N ≥ N0,
      ∀ L : EntryLaws N, (∃ Lv γ, LargeQClass C0 φs N Lv ∧ L = interp (lexPos N) γ Lv (goeLaws N)) →
      ∀ p : OffDiag N, ∀ b d i j : Fin N, ((b = p.1.1 ∧ d = p.1.2) ∨ (b = p.1.2 ∧ d = p.1.1)) →
      i ≠ j → i ≠ b → i ≠ d → j ≠ b → j ≠ d →
      ∀ F : ℝ → ℝ, ContDiff ℝ 4 F →
        (∀ n ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF) →
      ∀ y : ℝ, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
        (∀ E₁ E₂ : ℝ, |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          ‖∫ ω, ((iteratedDeriv 1 F (offWardInt (symOfEntries (zeroEntry (Sum.inr p) ω))
                ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂) : ℝ) : ℂ) *
              resolventC (symOfEntries (zeroEntry (Sum.inr p) ω))
                ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i b *
              resolventC (symOfEntries (zeroEntry (Sum.inr p) ω))
                ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ d j *
              (starRingEnd ℂ) (resolventC (symOfEntries (zeroEntry (Sum.inr p) ω))
                ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i j) ∂L.law‖ ≤
            (N : ℝ) ^ (-(4 : ℝ) / 3 + C * ε)) ∧
        (∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          ‖∫ ω, ((iteratedDeriv 1 F (offWard (symOfEntries (zeroEntry (Sum.inr p) ω))
                ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩) : ℝ) : ℂ) *
              resolventC (symOfEntries (zeroEntry (Sum.inr p) ω))
                ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i b *
              resolventC (symOfEntries (zeroEntry (Sum.inr p) ω))
                ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ d j *
              (starRingEnd ℂ) (resolventC (symOfEntries (zeroEntry (Sum.inr p) ω))
                ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i j) ∂L.law‖ ≤
            (N : ℝ) ^ (-(4 : ℝ) / 3 + C * ε)) := by
  refine ⟨14 * |CF| + 27, by positivity, fun ε hε hε' => ?_⟩
  by_cases hCF : 0 ≤ CF
  swap
  · refine ⟨0, fun N _ L _ p b d i j _ _ _ _ _ _ F _ hF => ?_⟩
    exfalso
    have h1 := hF 1 (by simp) 0
    exact hCF (by simpa using (abs_nonneg _).trans h1)
  obtain ⟨c, hc, Cb, -, N1, hN1⟩ := (apriori_largeQInterp_event hC0 hφs hφs' ε hε hε').inter
    (entryVal_le_largeQInterp hC0 hφs hφs' ε hε hε')
  obtain ⟨N2, hN2⟩ := norm_resolventC_zeroEntry_sub_le hφs hφs' ε hε hε'
  obtain ⟨N3, hN3⟩ := abs_iteratedDeriv_le_rpow_eps (CF := CF) (a := 7) (by norm_num) hε
  obtain ⟨N4, hN4⟩ := eventually_atTop.1 <|
    (eventually_ge_atTop 1).and <|
    (((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 12644).and <|
    (((tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 / 3 - 3 * ε)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 10).and <|
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 4).and <|
    eg_bad_le (Cb := Cb) hCF hc
  refine ⟨max N1 (max N2 (max N3 N4)),
    fun N hN L hL p b d i j hbd hij hib _ hjb hjd F hF4 hF y hy => ?_⟩
  have hNN1 : N1 ≤ N := le_trans (le_max_left _ _) hN
  have hNN2 : N2 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNN3 : N3 ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNN4 : N4 ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  obtain ⟨hN1', ht, h10, h4, hbad⟩ := hN4 N hNN4
  replace ht : 12644 ≤ (N : ℝ) ^ ε := ht
  replace h10 : 10 ≤ (N : ℝ) ^ ((1 : ℝ) / 3 - 3 * ε) := h10
  replace h4 : 4 ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := h4
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1'
  have hn0 : (0 : ℝ) < N := by linarith
  have hta : (N : ℝ) ^ ε ≤ (N : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have ha1 : 1 ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by linarith
  have ht1 : 1 ≤ (N : ℝ) ^ ε := by linarith
  obtain ⟨hNa, hηa, hwa, hPa, h13, h7⟩ := eg_rpow_params hN1' ε
  obtain ⟨Lv, γ, hv, rfl⟩ := hL
  have hGW : (interp (lexPos N) γ Lv (goeLaws N)).IsGenWigner (max C0 1) :=
    interp_isGenWigner hv.1 (goeLaws_isGenWigner N)
  -- the good event `Ω` of (6.55) and its probability
  have hpr0 : ((interp (lexPos N) γ Lv (goeLaws N)).law
      (swapEvent N ε φs (Sum.inr p))ᶜ).toReal ≤
      (N : ℝ) ^ Cb * Real.exp (-c * phi N ^ (1 : ℝ)) := by
    have hsub : (swapEvent N ε φs (Sum.inr p))ᶜ ⊆ (aprioriEvent N ε ∩
        {ω | ∀ e : Fin N ⊕ OffDiag N, |entryVal e ω| ≤ (N : ℝ) ^ (ε - φs)})ᶜ :=
      Set.compl_subset_compl.2 fun ω hω => ⟨hω.1, hω.2 _⟩
    exact ENNReal.toReal_le_of_le_ofReal (by positivity)
      ((measure_mono hsub).trans (hN1 N hNN1 _ ⟨Lv, γ, hv, rfl⟩))
  have hpr := hbad ((interp (lexPos N) γ Lv (goeLaws N)).law
    (swapEvent N ε φs (Sum.inr p))ᶜ).toReal (by rw [Real.rpow_natCast]; exact hpr0)
  have hΩ : ∀ ω ∈ swapEvent N ε φs (Sum.inr p), ∀ E : ℝ,
      |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) → ∀ k l,
      ‖resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l -
        (if k = l then msc ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ else 0)‖ ≤
        (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) :=
    fun ω hω => hN2 N hNN2 ω (Sum.inr p) hω.1 hω.2
  have hF7 := fun ζ hζ => hN3 N hNN3 F hF ζ hζ
  -- the sizes
  have hsz := eg_sizes ha1 (by linarith) hNa hηa hPa hwa
  rw [← h7] at hsz
  have hη0 : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) := Real.rpow_pos_of_pos hn0 _
  have hη1 : (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) ≤ 1 := by
    rw [hηa, div_le_one (by positivity)]
    nlinarith [one_le_pow₀ (n := 2) ha1]
  have hw1 : (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) ≤ 1 := by
    rw [hwa, div_le_one (by positivity)]
    nlinarith
  have hP0 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) := (Real.rpow_pos_of_pos hn0 _).le
  have hP : (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) ≤ 1 / 10 := by
    rw [h13, le_div_iff₀ (by positivity)] at h10
    rw [hPa, div_le_iff₀ (by linarith)]
    linarith
  have hNP : 1 ≤ (N : ℝ) * (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) := by
    have e : (N : ℝ) * (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) =
        ((N : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 * ((N : ℝ) ^ ε) ^ 3 := by
      rw [hPa]
      nth_rewrite 1 [hNa]
      field_simp
    rw [e]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ ha1) (one_le_pow₀ ht1)
  have hb : b = p.1.1 ∨ b = p.1.2 := by
    rcases hbd with ⟨h, -⟩ | ⟨h, -⟩
    exacts [Or.inl h, Or.inr h]
  have hc2 : ∀ ω : Entries N, Continuous fun y : ℝ => ∑ k, ∑ l, if k = l then (0 : ℝ) else
      ‖resolventC (zeroRC {b} (symOfEntries (zeroEntry (Sum.inr p) ω)))
        ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l‖ ^ 2 := by
    intro ω
    rw [eg_zeroRC_zeroEntry hb ω, ← symOfEntries_zeroEntries]
    exact (ward_continuous_y hη0 (zeroEntries {b} ω)).2
  refine ⟨fun E₁ E₂ h1 h2 => ?_, fun E hE => ?_⟩
  · have hΔ : |E₂ - E₁| ≤ 2 * (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) := by
      have a1 := abs_le.1 h1
      have a2 := abs_le.1 h2
      exact abs_le.2 ⟨by linarith, by linarith⟩
    refine eg_point hGW hCF hε hN1' ht hta h10 h4 hbd hij hib hjb hjd hF4 hF hF7 hy
      (fun ω hω => hΩ ω hω y hy) hpr
      (φ := fun H => offWardInt H ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂)
      (ward_continuous_b' hη0 E₁ E₂) (fun ω => ?_) (fun ω hω => ?_)
    · refine (ward_eta_int_le hη0 (K := (N : ℝ) ^ 2 * (1 / (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) ^ 2)
        fun y _ => ?_).trans (eg_big ha1 ht1 hta hNa hηa hwa hΔ).1
      rw [abs_of_nonneg (ward_offsum_nonneg _ _)]
      exact eg_offSum_le_det (symOfEntries_isHermitian ω) hη0 y
    · obtain ⟨g1, g2, g3⟩ := eg_offWardInt_good (symOfEntries_isHermitian (zeroEntry (Sum.inr p) ω))
        hη0 hη1 hP0 hP hNP hw1 (b := b) (ward_continuous_y hη0 (zeroEntry (Sum.inr p) ω)).2
        (hc2 ω) (hΩ ω hω) h1 h2
      rw [eg_zeroRC_zeroEntry hb ω] at g2 g3
      exact ⟨g1.trans hsz.2.2.2.1, g2.trans hsz.2.2.2.2.1, g3.trans hsz.2.2.2.2.2⟩
  · refine eg_point hGW hCF hε hN1' ht hta h10 h4 hbd hij hib hjb hjd hF4 hF hF7 hy
      (fun ω hω => hΩ ω hω y hy) hpr (φ := fun H => offWard H ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩)
      (ward_continuous_b hη0 E) (fun ω => ?_) (fun ω hω => ?_)
    · have e : offWard (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ =
          ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) ^ 2 * ∑ k, ∑ l, if k = l then (0 : ℝ) else
            ‖resolventC (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l‖ ^ 2 := rfl
      change |offWard (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩| ≤ 2 * (N : ℝ) ^ 3
      rw [e, abs_of_nonneg (mul_nonneg (sq_nonneg _) (ward_offsum_nonneg _ _))]
      exact (mul_le_mul_of_nonneg_left (eg_offSum_le_det (symOfEntries_isHermitian ω) hη0 E)
        (sq_nonneg _)).trans
          (eg_big ha1 ht1 hta hNa hηa hwa (Δ := 0) (by rw [abs_zero]; positivity)).2
    · have hE3 : |E| ≤ 3 := by
        obtain ⟨a1, a2⟩ := abs_le.1 hE
        exact abs_le.2 ⟨by linarith, by linarith⟩
      obtain ⟨g1, g2, g3⟩ := eg_offWard_good (symOfEntries_isHermitian (zeroEntry (Sum.inr p) ω))
        hη0 hη1 hP0 hP hNP hE3 (hΩ ω hω E hE) b
      rw [eg_zeroRC_zeroEntry hb ω] at g2 g3
      exact ⟨g1.trans hsz.1, g2.trans hsz.2.1, g3.trans hsz.2.2.1⟩

/-! ### Checks -/

-- The entry law of Lemma 3.5 at `N = 1024` with diagonal values `±1/16, 0, 0` (variance `2/N`)
-- and off-diagonal values `±1/32` (variance `1/N`), in `LargeQClass 1 (2/5) 1024`.
open private lawA lawA_isGenWigner lawA_supp from WEdgeNS.EdgeUniv.LargeQClass

/-- Every hypothesis of `expectation_gain_largeQ` holds at one point: `N = 1024`, `C0 = 1`,
`φs = 2/5`, `ε = 1/15` (the window `I_ε` is `|E - 2| ≤ 1/64`), `L = H_γ` with `γ = 5000` between
the law above and the GOE (both entry types occur), `F = K(·/π)` for the edge cutoff `K`,
`E₁ = 2 - 1/100 < E₂ = 2 + 1/100`, `E = y = 2`, `e = (0, 1)`, `(b, d, i, j) = (0, 1, 2, 3)`. -/
example : ∃ CF : ℝ, 0 < CF ∧ (0 : ℝ) ≤ 1 ∧ (1 / 3 : ℝ) < 2 / 5 ∧ (2 / 5 : ℝ) ≤ 1 / 2 ∧
    (0 : ℝ) < 1 / 15 ∧ (1 / 15 : ℝ) < 1 / 10 ∧
    (∃ Lv γ, LargeQClass 1 (2 / 5) 1024 Lv ∧
      interp (lexPos 1024) 5000 lawA (goeLaws 1024) = interp (lexPos 1024) γ Lv (goeLaws 1024)) ∧
    ContDiff ℝ 4 (fun x => edgeCutoff (x / Real.pi)) ∧
    (∀ n ∈ Finset.Icc 1 4, ∀ x : ℝ,
      |iteratedDeriv n (fun x => edgeCutoff (x / Real.pi)) x| ≤ CF * (1 + |x|) ^ CF) ∧
    |(2 - 1 / 100 : ℝ) - 2| ≤ ((1024 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) ∧
    |(2 + 1 / 100 : ℝ) - 2| ≤ ((1024 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) ∧
    (2 - 1 / 100 : ℝ) < 2 + 1 / 100 ∧
    |(2 : ℝ) - 2| ≤ ((1024 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) ∧
    (((0 : Fin 1024) = (⟨(0, 1), by decide⟩ : OffDiag 1024).1.1 ∧
        (1 : Fin 1024) = (⟨(0, 1), by decide⟩ : OffDiag 1024).1.2) ∨
      ((0 : Fin 1024) = (⟨(0, 1), by decide⟩ : OffDiag 1024).1.2 ∧
        (1 : Fin 1024) = (⟨(0, 1), by decide⟩ : OffDiag 1024).1.1)) ∧
    (2 : Fin 1024) ≠ 3 ∧ (2 : Fin 1024) ≠ 0 ∧ (2 : Fin 1024) ≠ 1 ∧ (3 : Fin 1024) ≠ 0 ∧
    (3 : Fin 1024) ≠ 1 := by
  obtain ⟨CF, hCF, h⟩ := edgeCutoff_deriv_le
  refine ⟨CF, hCF, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    ⟨lawA, 5000, ⟨lawA_isGenWigner, lawA_supp⟩, rfl⟩,
    (edgeCutoff_props.1 4).comp (contDiff_id.div_const _), h, ?_, ?_, by norm_num, ?_,
    Or.inl ⟨rfl, rfl⟩, by decide, by decide, by decide, by decide, by decide⟩ <;>
  · rw [rpow_1024_window]; norm_num [abs_of_nonneg, abs_of_nonpos]

#print axioms expectation_gain_largeQ

end WEdgeNS
