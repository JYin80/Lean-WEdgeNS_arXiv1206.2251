import WEdgeNS.LocalLaw.Weak
import WEdgeNS.LocalLaw.Decoupling
import WEdgeNS.LocalLaw.Graded

/-!
# Fluctuation averaging
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

open private ctlIdx ctl_symOfEntries_symm ctl_symOfEntries_eq_coord ctlIdx_off
  from WEdgeNS.LocalLaw.Control
open private sc_one_le_phi sc_phi_pos sc_rpow_mono sc_sq_add3_le
  from WEdgeNS.LocalLaw.SelfConsistent

/-! ### The entries of one row as independent random variables -/

section Row

variable {N : ℕ}

private lemma fa_idx_row_inj (i : Fin N) : Function.Injective fun k : Fin N => ctlIdx i k := by
  intro k k' h
  simp only at h
  unfold ctlIdx at h
  split_ifs at h <;> simp_all [Fin.ext_iff]

/-- The entries `h_{ik}`, `k = 1, …, N`, of the row `i` are independent. -/
private lemma fa_iIndep_row {L : EntryLaws N} (hL : L.IsProb) (i : Fin N) :
    iIndepFun (fun k (ω : Entries N) => symOfEntries ω i k) L.law := by
  have h := (EntryLaws.iIndepFun_entryCoord hL).precomp (fa_idx_row_inj i)
  convert h using 2 with k
  funext ω
  exact ctl_symOfEntries_eq_coord ω _ _

private lemma fa_map_off {L : EntryLaws N} (hL : L.IsProb) (p : OffDiag N) :
    L.law.map (fun ω : Entries N => ω.2 p) = L.off p := by
  have := hL.diag
  have := hL.off
  have h1 : MeasurePreserving (fun ω : Entries N => ω.2) L.law (Measure.pi L.off) :=
    measurePreserving_snd
  exact ((measurePreserving_eval L.off p).comp h1).map_eq

private lemma fa_map_diag {L : EntryLaws N} (hL : L.IsProb) (i : Fin N) :
    L.law.map (fun ω : Entries N => ω.1 i) = L.diag i := by
  have := hL.diag
  have := hL.off
  have h1 : MeasurePreserving (fun ω : Entries N => ω.1) L.law (Measure.pi L.diag) :=
    measurePreserving_fst
  exact ((measurePreserving_eval L.diag i).comp h1).map_eq

/-- The law of the entry `h_{ab}`. -/
private def faEntryLaw (L : EntryLaws N) (a b : Fin N) : Measure ℝ :=
  Sum.elim L.diag L.off (ctlIdx a b)

private lemma fa_map_sym {L : EntryLaws N} (hL : L.IsProb) (a b : Fin N) :
    L.law.map (fun ω : Entries N => symOfEntries ω a b) = faEntryLaw L a b := by
  have e : (fun ω : Entries N => symOfEntries ω a b) =
      fun ω => EntryLaws.entryCoord (ctlIdx a b) ω :=
    funext fun ω => ctl_symOfEntries_eq_coord ω a b
  rw [e]
  unfold faEntryLaw
  rcases ctlIdx a b with i | p
  · exact fa_map_diag hL i
  · exact fa_map_off hL p

private lemma fa_entryLaw_prob {L : EntryLaws N} (hL : L.IsProb) (a b : Fin N) :
    IsProbabilityMeasure (faEntryLaw L a b) := by
  unfold faEntryLaw
  rcases ctlIdx a b with i | p
  · exact hL.diag i
  · exact hL.off p

private lemma fa_integral_sym {L : EntryLaws N} (hL : L.IsProb) (a b : Fin N) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (faEntryLaw L a b)) :
    ∫ ω, f (symOfEntries ω a b) ∂L.law = ∫ x, f x ∂(faEntryLaw L a b) := by
  have h := integral_map (μ := L.law) (measurable_symOfEntries_at a b).aemeasurable (f := f)
    (by rw [fa_map_sym hL a b]; exact hf)
  rw [fa_map_sym hL a b] at h
  exact h.symm

private lemma fa_entryLaw_tail {L : EntryLaws N} {q : ℝ} (hq : L.BoundedSupportAS q)
    (a b : Fin N) : faEntryLaw L a b {x | q⁻¹ < |x|} = 0 := by
  unfold faEntryLaw
  rcases ctlIdx a b with i | p
  · exact hq.1 i
  · exact hq.2 p

private lemma fa_entryLaw_ae_le {L : EntryLaws N} {q : ℝ} (hq : L.BoundedSupportAS q)
    (a b : Fin N) : ∀ᵐ x ∂(faEntryLaw L a b), |x| ≤ q⁻¹ := by
  rw [ae_iff]
  simpa [not_le] using fa_entryLaw_tail hq a b

private lemma fa_ae_sym_le {L : EntryLaws N} (hL : L.IsProb) {q : ℝ} (hq : L.BoundedSupportAS q)
    (a b : Fin N) : ∀ᵐ ω ∂L.law, |symOfEntries ω a b| ≤ q⁻¹ := by
  have hA : MeasurableSet {x : ℝ | q⁻¹ < |x|} := measurableSet_lt measurable_const measurable_abs
  rw [ae_iff]
  have : {ω : Entries N | ¬ |symOfEntries ω a b| ≤ q⁻¹} =
      (fun ω : Entries N => symOfEntries ω a b) ⁻¹' {x : ℝ | q⁻¹ < |x|} := by
    ext ω
    simp
  rw [this, ← Measure.map_apply (measurable_symOfEntries_at a b) hA, fa_map_sym hL a b]
  exact fa_entryLaw_tail hq a b

/-- All entries are bounded by `q⁻¹` almost surely. -/
private lemma fa_ae_entries {L : EntryLaws N} (hL : L.IsProb) {q : ℝ}
    (hq : L.BoundedSupportAS q) : ∀ᵐ ω ∂L.law, ∀ a b : Fin N, |symOfEntries ω a b| ≤ q⁻¹ :=
  ae_all_iff.2 fun a => ae_all_iff.2 fun b => fa_ae_sym_le hL hq a b

private lemma fa_entryLaw_mean {L : EntryLaws N} {C0 : ℝ} (hL : L.IsGenWigner C0) (a b : Fin N) :
    ∫ x, x ∂(faEntryLaw L a b) = 0 := by
  unfold faEntryLaw
  rcases ctlIdx a b with i | p
  · exact hL.mean_diag i
  · exact hL.mean_off p

private lemma fa_entryLaw_sq_int {L : EntryLaws N} {C0 : ℝ} (hL : L.IsGenWigner C0)
    (a b : Fin N) : Integrable (fun x : ℝ => x ^ 2) (faEntryLaw L a b) := by
  unfold faEntryLaw
  rcases ctlIdx a b with i | p
  · exact hL.sq_int_diag i
  · exact hL.sq_int_off p

private lemma fa_entryLaw_var_le {L : EntryLaws N} {C0 : ℝ} (hL : L.IsGenWigner C0)
    (a b : Fin N) : ∫ x, x ^ 2 ∂(faEntryLaw L a b) ≤ (1 + C0) / N := by
  unfold faEntryLaw
  rcases ctlIdx a b with i | p
  · have h := hL.var_diag i
    have h1 := (abs_le.mp h).2
    simp only [Sum.elim_inl]
    rw [add_div]
    have : (N : ℝ)⁻¹ = 1 / N := by rw [one_div]
    rw [← this]
    have : C0 * (N : ℝ)⁻¹ = C0 / N := by rw [div_eq_mul_inv]
    linarith
  · simp only [Sum.elim_inr]
    rw [hL.var_off p, add_div, ← one_div]
    have hC0 : 0 ≤ C0 * (N : ℝ)⁻¹ := (abs_nonneg _).trans (hL.var_diag ⟨0, by
      rcases p with ⟨⟨x, y⟩, h⟩
      exact lt_of_le_of_lt (Nat.zero_le _) y.2⟩)
    have hN : 0 ≤ (N : ℝ)⁻¹ := by positivity
    have : 0 ≤ C0 / N := by
      rw [div_eq_mul_inv]
      exact hC0
    linarith

private lemma fa_entryLaw_var_off {L : EntryLaws N} {C0 : ℝ} (hL : L.IsGenWigner C0)
    {a b : Fin N} (hab : a ≠ b) : ∫ x, x ^ 2 ∂(faEntryLaw L a b) = (N : ℝ)⁻¹ := by
  obtain ⟨p, hp⟩ := ctlIdx_off hab
  unfold faEntryLaw
  rw [hp]
  exact hL.var_off p

private lemma fa_mean_sym {L : EntryLaws N} {C0 : ℝ} (hL : L.IsGenWigner C0) (a b : Fin N) :
    ∫ ω, symOfEntries ω a b ∂L.law = 0 := by
  have := fa_entryLaw_prob hL.isProb a b
  rw [fa_integral_sym hL.isProb a b (fun x => x) (by fun_prop)]
  exact fa_entryLaw_mean hL a b

private lemma fa_var_sym_le {L : EntryLaws N} {C0 : ℝ} (hL : L.IsGenWigner C0) (a b : Fin N) :
    ∫ ω, (symOfEntries ω a b) ^ 2 ∂L.law ≤ (1 + C0) / N := by
  rw [fa_integral_sym hL.isProb a b (fun x => x ^ 2) (by fun_prop)]
  exact fa_entryLaw_var_le hL a b

private lemma fa_var_sym_off {L : EntryLaws N} {C0 : ℝ} (hL : L.IsGenWigner C0) {a b : Fin N}
    (hab : a ≠ b) : ∫ ω, (symOfEntries ω a b) ^ 2 ∂L.law = (N : ℝ)⁻¹ := by
  rw [fa_integral_sym hL.isProb a b (fun x => x ^ 2) (by fun_prop)]
  exact fa_entryLaw_var_off hL hab

end Row

/-! ### The variables `Z_i^{[V]}` and the expansion (5.98) of their graded terms -/

section Graded

variable {N : ℕ}

/-- `Z_i^{[V]}` of (5.93) of [15], with the diagonal terms `k = l` of (5.80) included:
`Σ_{k,l ∉ iV} (h_{ik} h_{li} - δ_{kl} N⁻¹) G^{(iV)}_{kl}` for `i ∉ V`, and `0` for `i ∈ V`. -/
private def faZ (z : ℂ) (V : Finset (Fin N)) (i : Fin N) (ω : Entries N) : ℂ :=
  if i ∈ V then 0 else
    ∑ k, ∑ l, if k ∈ insert i V ∨ l ∈ insert i V then 0 else
      (((symOfEntries ω i k * symOfEntries ω l i : ℝ) : ℂ) -
        if k = l then ((N : ℝ)⁻¹ : ℂ) else 0) *
        resolventC (zeroRC (insert i V) (symOfEntries ω)) z k l

/-- `Z_i^{[∅]} = Z_i` of (3.15) of [15]. -/
private lemma fa_faZ_empty (z : ℂ) (i : Fin N) (ω : Entries N) :
    faZ z ∅ i ω = zFluct (symOfEntries ω) z i := by
  simp only [faZ, Finset.notMem_empty, ite_false, Finset.insert_empty, Finset.mem_singleton,
    zFluct]

/-- The coefficient `[G_{kl}]^{(Si) \ {k,l}, U \ {k,l}}` of (5.98) of [15]. -/
private def faCoef (z : ℂ) (S U : Finset (Fin N)) (i k l : Fin N)
    (H : Matrix (Fin N) (Fin N) ℝ) : ℂ :=
  if k = i ∨ l = i ∨ k ∈ S \ U ∨ l ∈ S \ U then 0 else
    gradedTerm (fun V => resolventC (zeroRC V H) z k l) ((insert i S) \ {k, l}) (U \ {k, l})

private lemma fa_gradedTerm_apply {β : Type*} (A : Finset (Fin N) → β → ℂ)
    (S U : Finset (Fin N)) (x : β) :
    gradedTerm A S U x = gradedTerm (fun V => A V x) S U := by
  simp only [gradedTerm, Finset.sum_apply, Pi.smul_apply]

private lemma fa_sum_powerset_ite (U : Finset (Fin N)) (k l : Fin N) (F : Finset (Fin N) → ℂ) :
    ∑ T ∈ U.powerset, (if k ∈ T ∨ l ∈ T then 0 else F T) =
      ∑ T ∈ (U \ {k, l}).powerset, F T := by
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext T
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff, Finset.mem_sdiff,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩ x hx
    refine ⟨h1 hx, ?_⟩
    rintro (rfl | rfl)
    · exact h2 (Or.inl hx)
    · exact h2 (Or.inr hx)
  · intro h
    refine ⟨fun x hx => (h hx).1, ?_⟩
    rintro (hk | hl)
    · exact (h hk).2 (Or.inl rfl)
    · exact (h hl).2 (Or.inr rfl)

/-- One term of (5.98) of [15]. -/
private lemma fa_graded_kl {S U : Finset (Fin N)} {i : Fin N} (hiS : i ∉ S) (hUS : U ⊆ S)
    (z : ℂ) (k l : Fin N) (c : ℂ) (ω : Entries N) :
    ∑ T ∈ U.powerset, ((-1 : ℤ) ^ T.card) •
      (if k ∈ insert i ((S \ U) ∪ T) ∨ l ∈ insert i ((S \ U) ∪ T) then 0 else
        c * resolventC (zeroRC (insert i ((S \ U) ∪ T)) (symOfEntries ω)) z k l) =
      c * faCoef z S U i k l (symOfEntries ω) := by
  unfold faCoef
  by_cases hbad : k = i ∨ l = i ∨ k ∈ S \ U ∨ l ∈ S \ U
  · simp only [hbad, ite_true, mul_zero]
    refine Finset.sum_eq_zero fun T _ => ?_
    have : k ∈ insert i ((S \ U) ∪ T) ∨ l ∈ insert i ((S \ U) ∪ T) := by
      rcases hbad with h | h | h | h
      · exact Or.inl (h ▸ Finset.mem_insert_self _ _)
      · exact Or.inr (h ▸ Finset.mem_insert_self _ _)
      · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
      · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
    simp only [this, ite_true, smul_zero]
  · simp only [hbad, ite_false]
    simp only [not_or] at hbad
    obtain ⟨hki, hli, hkS, hlS⟩ := hbad
    have hmem : ∀ T : Finset (Fin N), (k ∈ insert i ((S \ U) ∪ T) ∨ l ∈ insert i ((S \ U) ∪ T))
        ↔ (k ∈ T ∨ l ∈ T) := by
      intro T
      simp only [Finset.mem_insert, Finset.mem_union, hki, hli, hkS, hlS, false_or]
    simp only [hmem, smul_ite, smul_zero]
    rw [fa_sum_powerset_ite U k l, gradedTerm, Finset.mul_sum]
    have hset : ((insert i S) \ {k, l}) \ (U \ {k, l}) = insert i (S \ U) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr ⟨h1, fun hU => h3 ⟨hU, h2⟩⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · refine ⟨⟨Or.inl rfl, ?_⟩, fun h => ?_⟩
          · rintro (h | h)
            · exact hki h.symm
            · exact hli h.symm
          · exact hiS (hUS h.1)
        · refine ⟨⟨Or.inr h1, ?_⟩, fun h => h2 h.1⟩
          rintro (rfl | rfl)
          · exact hkS (Finset.mem_sdiff.mpr ⟨h1, h2⟩)
          · exact hlS (Finset.mem_sdiff.mpr ⟨h1, h2⟩)
    rw [hset]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.insert_union, mul_smul_comm]

/-- (5.98) of [15]: the graded term `Z_i^{S,U}` is a quadratic form in the row `i` with the
coefficients `faCoef`. -/
private lemma fa_graded_eq {S U : Finset (Fin N)} {i : Fin N} (hiS : i ∉ S) (hUS : U ⊆ S)
    (z : ℂ) (ω : Entries N) :
    gradedTerm (fun V => faZ z V i ω) S U = ∑ k, ∑ l,
      (((symOfEntries ω i k * symOfEntries ω l i : ℝ) : ℂ) -
        if k = l then ((N : ℝ)⁻¹ : ℂ) else 0) * faCoef z S U i k l (symOfEntries ω) := by
  unfold gradedTerm
  have hZ : ∀ T ∈ U.powerset, faZ z ((S \ U) ∪ T) i ω = ∑ k, ∑ l,
      if k ∈ insert i ((S \ U) ∪ T) ∨ l ∈ insert i ((S \ U) ∪ T) then 0 else
        (((symOfEntries ω i k * symOfEntries ω l i : ℝ) : ℂ) -
          if k = l then ((N : ℝ)⁻¹ : ℂ) else 0) *
          resolventC (zeroRC (insert i ((S \ U) ∪ T)) (symOfEntries ω)) z k l := by
    intro T hT
    have hi : i ∉ (S \ U) ∪ T := by
      simp only [Finset.mem_union, Finset.mem_sdiff, not_or, not_and_or]
      exact ⟨Or.inl hiS, fun h => hiS (hUS (Finset.mem_powerset.mp hT h))⟩
    simp only [faZ, hi, ite_false]
  rw [Finset.sum_congr rfl fun T hT => by
    change ((-1 : ℤ) ^ T.card) • faZ z ((S \ U) ∪ T) i ω = _
    rw [hZ T hT]]
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact fa_graded_kl hiS hUS z k l _ ω

/-- The coefficients of (5.98) are independent of the row `i` (`i ∈ A`, `i ∉ B` for
`[G_{kl}]^{A,B}`). -/
private lemma fa_coef_rowIndep {S U : Finset (Fin N)} {i : Fin N} (hiU : i ∉ U) (z : ℂ)
    (k l : Fin N) : RowIndep {i} (fun ω => faCoef z S U i k l (symOfEntries ω)) := by
  intro ω
  unfold faCoef
  by_cases h : k = i ∨ l = i ∨ k ∈ S \ U ∨ l ∈ S \ U
  · simp only [h, ite_true]
  · simp only [h, ite_false]
    have hk : k ≠ i := fun e => h (Or.inl e)
    have hl : l ≠ i := fun e => h (Or.inr (Or.inl e))
    have hsub : ({i} : Finset (Fin N)) ⊆ ((insert i S) \ {k, l}) \ (U \ {k, l}) := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, true_or, true_and,
        not_or, not_and, not_not]
      exact ⟨⟨Ne.symm hk, Ne.symm hl⟩, fun hU => absurd hU hiU⟩
    have := RowIndep.gradedTerm (A := fun V ω => resolventC (zeroRC V (symOfEntries ω)) z k l)
      (fun V hV => rowIndep_resolventC_zeroRC hV z k l) hsub ω
    simpa only [fa_gradedTerm_apply] using this

private lemma fa_coef_rowsMix {S U : Finset (Fin N)} {i : Fin N} (hiU : i ∉ U) (z : ℂ)
    (k l : Fin N) (ω ω' : Entries N) :
    faCoef z S U i k l (symOfEntries (rowsMix {i} ω ω')) = faCoef z S U i k l (symOfEntries ω) :=
  rowIndep_iff_rowsMix.mp (fa_coef_rowIndep hiU z k l) ω ω'

/-- After resampling the row `i`, the graded term is a quadratic form in the new row with the
old coefficients. -/
private lemma fa_graded_rowsMix {S U : Finset (Fin N)} {i : Fin N} (hiS : i ∉ S) (hUS : U ⊆ S)
    (z : ℂ) (ω ω' : Entries N) :
    gradedTerm (fun V => faZ z V i (rowsMix {i} ω ω')) S U = ∑ k, ∑ l,
      (((symOfEntries ω' i k * symOfEntries ω' i l : ℝ) : ℂ) -
        if k = l then ((N : ℝ)⁻¹ : ℂ) else 0) * faCoef z S U i k l (symOfEntries ω) := by
  rw [fa_graded_eq hiS hUS]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [fa_coef_rowsMix (fun h => hiS (hUS h)), ctl_symOfEntries_symm (rowsMix {i} ω ω') l i,
    symOfEntries_rowsMix_left_of_mem {i} (Finset.mem_singleton_self i),
    symOfEntries_rowsMix_left_of_mem {i} (Finset.mem_singleton_self i)]

end Graded

/-! ### Continuity and crude bounds -/

section Regularity

variable {N : ℕ}

private lemma fa_continuous_faZ {z : ℂ} (hz : z.im ≠ 0) (V : Finset (Fin N)) (i : Fin N) :
    Continuous (faZ z V i) := by
  unfold faZ
  by_cases hi : i ∈ V
  · simp only [hi, ite_true]
    exact continuous_const
  · simp only [hi, ite_false]
    refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_
    by_cases h : k ∈ insert i V ∨ l ∈ insert i V
    · simp only [h, ite_true]
      exact continuous_const
    · simp only [h, ite_false]
      exact ((Complex.continuous_ofReal.comp ((continuous_symOfEntries_at i k).mul
        (continuous_symOfEntries_at l i))).sub continuous_const).mul
          (continuous_resolventC_zeroRC_symOfEntries _ hz k l)

private lemma fa_continuous_graded {z : ℂ} (hz : z.im ≠ 0) (S U : Finset (Fin N)) (i : Fin N) :
    Continuous (gradedTerm (fun V => faZ z V i) S U) := by
  have e : gradedTerm (fun V => faZ z V i) S U =
      fun ω => gradedTerm (fun V => faZ z V i ω) S U :=
    funext fun ω => fa_gradedTerm_apply _ S U ω
  rw [e]
  unfold gradedTerm
  exact continuous_finsetSum _ fun T _ => (fa_continuous_faZ hz _ i).const_smul _

private lemma fa_norm_faZ_le {z : ℂ} (hz : 0 < z.im) (V : Finset (Fin N)) (i : Fin N)
    {ω : Entries N} {q : ℝ} (hω : ∀ a b : Fin N, |symOfEntries ω a b| ≤ q⁻¹) :
    ‖faZ z V i ω‖ ≤ (N : ℝ) ^ 2 * (((q⁻¹) ^ 2 + (N : ℝ)⁻¹) * (1 / z.im)) := by
  unfold faZ
  have hterm : ∀ k l : Fin N, ‖(if k ∈ insert i V ∨ l ∈ insert i V then 0 else
      (((symOfEntries ω i k * symOfEntries ω l i : ℝ) : ℂ) -
        if k = l then ((N : ℝ)⁻¹ : ℂ) else 0) *
        resolventC (zeroRC (insert i V) (symOfEntries ω)) z k l)‖ ≤
      ((q⁻¹) ^ 2 + (N : ℝ)⁻¹) * (1 / z.im) := by
    intro k l
    have hpos : 0 ≤ ((q⁻¹) ^ 2 + (N : ℝ)⁻¹) * (1 / z.im) := by positivity
    by_cases h : k ∈ insert i V ∨ l ∈ insert i V
    · rw [ite_eq_left h, norm_zero]; exact hpos
    · rw [ite_eq_right h, norm_mul]
      refine mul_le_mul ?_ (norm_resolventC_apply_le (zeroRC_isHermitian
        (symOfEntries_isHermitian ω) _) hz k l) (norm_nonneg _) (by positivity)
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, sq]
        exact mul_le_mul (hω i k) (hω l i) (abs_nonneg _) ((abs_nonneg _).trans (hω i k))
      · by_cases hkl : k = l
        · rw [ite_eq_left hkl]
          simp
        · rw [ite_eq_right hkl, norm_zero]; positivity
  split_ifs
  · rw [norm_zero]; positivity
  · refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖∑ l, (if k ∈ insert i V ∨ l ∈ insert i V then 0 else
          (((symOfEntries ω i k * symOfEntries ω l i : ℝ) : ℂ) -
            if k = l then ((N : ℝ)⁻¹ : ℂ) else 0) *
            resolventC (zeroRC (insert i V) (symOfEntries ω)) z k l)‖
        ≤ ∑ _k : Fin N, ∑ _l : Fin N, ((q⁻¹) ^ 2 + (N : ℝ)⁻¹) * (1 / z.im) :=
          Finset.sum_le_sum fun k _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun l _ => hterm k l)
      _ = (N : ℝ) ^ 2 * (((q⁻¹) ^ 2 + (N : ℝ)⁻¹) * (1 / z.im)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring

private lemma fa_norm_graded_le {z : ℂ} (S U : Finset (Fin N)) (i : Fin N) (ω : Entries N)
    {M : ℝ} (hM : ∀ V, ‖faZ z V i ω‖ ≤ M) :
    ‖gradedTerm (fun V => faZ z V i) S U ω‖ ≤ 2 ^ U.card * M := by
  rw [fa_gradedTerm_apply]
  unfold gradedTerm
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ T ∈ U.powerset, ‖((-1 : ℤ) ^ T.card) • faZ z ((S \ U) ∪ T) i ω‖ ≤ M := by
    intro T _
    rw [zsmul_eq_mul, norm_mul]
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, norm_pow, norm_neg, norm_one, one_pow,
      one_mul]
    exact hM _
  refine (Finset.sum_le_sum h).trans ?_
  rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
  push_cast
  rfl

end Regularity

/-! ### Deterministic bounds on the coefficients (Lemmas 5.7 and 5.11 of [15]) -/

section CoefBounds

/-- The coefficients of (5.98) for a matrix with `Λ_o ≤ o`, `Λ_d ≤ d` and `(|S| + 1)(o + d)`
small: (5.72)–(5.73) of [15] with `w ≥ C u o`, `u = |U| + 1`, and `|G^{(T)}_{kk}| ≤ 2`. -/
private lemma fa_coef_bounds : ∃ c1 > 0, ∃ Cg > 0, ∀ {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ},
    H.IsHermitian → ∀ {z : ℂ}, |z.re| ≤ 5 → 0 < z.im → z.im ≤ 10 →
    ∀ (o d w : ℝ) (S U : Finset (Fin N)) (i : Fin N), 0 ≤ o → 0 ≤ d →
    (∀ a b, a ≠ b → ‖resolventC H z a b‖ ≤ o) → (∀ a, ‖resolventC H z a a - msc z‖ ≤ d) →
    ((S.card : ℝ) + 1) * (o + d) ≤ c1 → i ∉ S → U ⊆ S →
    Cg * (U.card + 1) * o ≤ w → w ≤ 1 →
    (∀ k l, k ∈ U → l ∈ U → ‖faCoef z S U i k l H‖ ≤ 2 * w ^ (U.card - 1)) ∧
    (∀ k l, k ≠ l → ¬ (k ∈ U ∧ l ∈ U) → ‖faCoef z S U i k l H‖ ≤ w ^ U.card ∧
      ‖faCoef z S U i k l H‖ ^ 2 ≤ w ^ (2 * (U.card + 1)) +
        ((if k ∈ U then 1 else 0) + (if l ∈ U then 1 else 0)) * w ^ (2 * U.card)) ∧
    (∀ k, k ∉ U → ‖faCoef z S U i k k H‖ ≤ 2 * w ^ U.card) := by
  obtain ⟨c1r, hc1r, Cr, hCr, hR⟩ := resolventC_zeroRC_sub_le
  obtain ⟨c1g, hc1g, Cg, hCg, hG⟩ := norm_gradedTerm_resolventC_le
  have hCr0 : 0 < Cr := by linarith
  refine ⟨min (min c1r c1g) Cr⁻¹, lt_min (lt_min hc1r hc1g) (by positivity), Cg, hCg, ?_⟩
  intro N H hH z hre hz hz10 o d w S U i ho hd hoff hdiag hcard hiS hUS hw hw1
  have hod0 : 0 ≤ o + d := by linarith
  have hS1 : ∀ T : Finset (Fin N), T.card ≤ S.card + 1 → (T.card : ℝ) * (o + d) ≤
      min (min c1r c1g) Cr⁻¹ := by
    intro T hT
    have : (T.card : ℝ) ≤ S.card + 1 := by exact_mod_cast hT
    exact le_trans (mul_le_mul_of_nonneg_right this hod0) hcard
  have hod1 : o + d ≤ min (min c1r c1g) Cr⁻¹ := by
    have h0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    have h1 : (1 : ℝ) ≤ S.card + 1 := by linarith
    calc o + d = 1 * (o + d) := (one_mul _).symm
      _ ≤ ((S.card : ℝ) + 1) * (o + d) := mul_le_mul_of_nonneg_right h1 hod0
      _ ≤ _ := hcard
  have hw0 : 0 ≤ w := le_trans (by positivity) hw
  have hcardS'' : ∀ k l : Fin N, ((insert i S) \ {k, l}).card ≤ S.card + 1 :=
    fun k l => (Finset.card_le_card Finset.sdiff_subset).trans (Finset.card_insert_le _ _)
  -- the graded bound
  have hgr : ∀ k l, k ≠ i → l ≠ i → (U \ {k, l}).Nonempty ∨ k ≠ l →
      ‖gradedTerm (fun V => resolventC (zeroRC V H) z k l) ((insert i S) \ {k, l})
        (U \ {k, l})‖ ≤ w ^ ((U \ {k, l}).card + 1) := by
    intro k l hk hl hne
    have hk' : k ∉ (insert i S) \ {k, l} := by simp
    have hl' : l ∉ (insert i S) \ {k, l} := by simp
    have hsub : U \ {k, l} ⊆ (insert i S) \ {k, l} :=
      Finset.sdiff_subset_sdiff (hUS.trans (Finset.subset_insert _ _)) le_rfl
    have h := hG hH hre hz hz10 o d _ _ ho hoff hdiag (hod1.trans ((min_le_left _ _).trans
      (min_le_right _ _))) ((hS1 _ (hcardS'' k l)).trans ((min_le_left _ _).trans
      (min_le_right _ _))) hsub k l hk' hl' hne
    refine h.trans (pow_le_pow_left₀ (by positivity) (le_trans ?_ hw) _)
    have : ((U \ {k, l}).card : ℝ) ≤ U.card := by
      exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    gcongr
  -- the diagonal of a minor is bounded by `2`
  have hdg : ∀ k : Fin N, k ≠ i → ‖resolventC (zeroRC ((insert i S) \ {k}) H) z k k‖ ≤ 2 := by
    intro k hk
    have hk' : k ∉ (insert i S) \ {k} := by simp
    have hc : ((insert i S) \ {k}).card ≤ S.card + 1 :=
      (Finset.card_le_card Finset.sdiff_subset).trans (Finset.card_insert_le _ _)
    have h := (hR hH hre hz hz10 o d _ ho hoff hdiag (hod1.trans ((min_le_left _ _).trans
      (min_le_left _ _))) ((hS1 _ hc).trans ((min_le_left _ _).trans (min_le_left _ _)))
      k k hk' hk').1
    simp only [ite_true] at h
    have h2 : Cr * (d + o) ≤ 1 := by
      have : d + o ≤ Cr⁻¹ := by linarith [hod1.trans (min_le_right _ _)]
      calc Cr * (d + o) ≤ Cr * Cr⁻¹ := mul_le_mul_of_nonneg_left this hCr0.le
        _ = 1 := mul_inv_cancel₀ hCr0.ne'
    have hm := (norm_msc_eq_inv_and_lt_one hz).2
    calc ‖resolventC (zeroRC ((insert i S) \ {k}) H) z k k‖
        ≤ ‖resolventC (zeroRC ((insert i S) \ {k}) H) z k k - msc z‖ + ‖msc z‖ := by
          have := norm_add_le (resolventC (zeroRC ((insert i S) \ {k}) H) z k k - msc z) (msc z)
          simpa using this
      _ ≤ 2 := by linarith
  have hiU : i ∉ U := fun h => hiS (hUS h)
  refine ⟨?_, ?_, ?_⟩
  · -- both indices in `U`
    intro k l hk hl
    have hki : k ≠ i := fun e => hiU (e ▸ hk)
    have hli : l ≠ i := fun e => hiU (e ▸ hl)
    have hkS : k ∉ S \ U := fun h => (Finset.mem_sdiff.mp h).2 hk
    have hlS : l ∉ S \ U := fun h => (Finset.mem_sdiff.mp h).2 hl
    have hnz : ¬ (k = i ∨ l = i ∨ k ∈ S \ U ∨ l ∈ S \ U) := by tauto
    unfold faCoef
    simp only [hnz, ite_false]
    rcases (U \ {k, l}).eq_empty_or_nonempty with he | hne
    · by_cases hkl : k = l
      · subst hkl
        have hU1 : U.card - 1 = 0 := by
          have hsub : U ⊆ {k, k} := Finset.sdiff_eq_empty_iff_subset.mp he
          have : U.card ≤ 1 := by
            have := Finset.card_le_card hsub
            simpa using this
          omega
        rw [hU1, pow_zero, mul_one, he, gradedTerm_empty]
        have e : ({k, k} : Finset (Fin N)) = {k} := by simp
        rw [e]
        exact hdg k hki
      · have h := hgr k l hki hli (Or.inr hkl)
        have hp0 := pow_nonneg hw0 (U.card - 1)
        refine h.trans (le_trans (pow_le_pow_of_le_one hw0 hw1 ?_) (by linarith))
        have := Finset.card_le_card_sdiff_add_card (s := U) (t := {k, l})
        have h2 := Finset.card_le_two (a := k) (b := l)
        omega
    · have h := hgr k l hki hli (Or.inl hne)
      have hp0 := pow_nonneg hw0 (U.card - 1)
      refine h.trans (le_trans (pow_le_pow_of_le_one hw0 hw1 ?_) (by linarith))
      have := Finset.card_le_card_sdiff_add_card (s := U) (t := {k, l})
      have h2 := Finset.card_le_two (a := k) (b := l)
      omega
  · -- off the diagonal, not both in `U`
    intro k l hkl hnot
    unfold faCoef
    by_cases hz0 : k = i ∨ l = i ∨ k ∈ S \ U ∨ l ∈ S \ U
    · simp only [hz0, ite_true, norm_zero]
      refine ⟨pow_nonneg hw0 _, ?_⟩
      have : 0 ≤ ((if k ∈ U then (1 : ℝ) else 0) + (if l ∈ U then 1 else 0)) := by
        split_ifs <;> norm_num
      have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [h0]
      positivity
    · simp only [hz0, ite_false]
      have hki : k ≠ i := fun e => hz0 (Or.inl e)
      have hli : l ≠ i := fun e => hz0 (Or.inr (Or.inl e))
      have h := hgr k l hki hli (Or.inr hkl)
      have hcard2 : U.card ≤ (U \ {k, l}).card + 1 := by
        have hinter : (U ∩ {k, l}).card ≤ 1 := by
          by_contra hc
          have h2 : 2 ≤ (U ∩ {k, l}).card := by omega
          have hsub : U ∩ {k, l} ⊆ {k, l} := Finset.inter_subset_right
          have heq : U ∩ {k, l} = {k, l} := Finset.eq_of_subset_of_card_le hsub
            (by rw [Finset.card_pair hkl]; exact h2)
          have hk : k ∈ U ∩ {k, l} := by rw [heq]; simp
          have hl : l ∈ U ∩ {k, l} := by rw [heq]; simp
          exact hnot ⟨(Finset.mem_inter.mp hk).1, (Finset.mem_inter.mp hl).1⟩
        have := Finset.card_sdiff_add_card_inter U {k, l}
        omega
      refine ⟨h.trans (pow_le_pow_of_le_one hw0 hw1 hcard2), ?_⟩
      have hsq : ‖gradedTerm (fun V => resolventC (zeroRC V H) z k l) (insert i S \ {k, l})
          (U \ {k, l})‖ ^ 2 ≤ w ^ (2 * ((U \ {k, l}).card + 1)) := by
        rw [show 2 * ((U \ {k, l}).card + 1) = ((U \ {k, l}).card + 1) * 2 by ring, pow_mul]
        exact pow_le_pow_left₀ (norm_nonneg _) h 2
      have hexp : w ^ (2 * ((U \ {k, l}).card + 1)) ≤ w ^ (2 * U.card) :=
        pow_le_pow_of_le_one hw0 hw1 (by omega)
      have hp1 := pow_nonneg hw0 (2 * (U.card + 1))
      by_cases hkU : k ∈ U
      · have hlU : l ∉ U := fun h => hnot ⟨hkU, h⟩
        simp only [hkU, hlU, ite_true, ite_false, add_zero, one_mul]
        linarith
      · by_cases hlU : l ∈ U
        · simp only [hkU, hlU, ite_true, ite_false, zero_add, one_mul]
          linarith
        · simp only [hkU, hlU, ite_false, add_zero, zero_mul]
          have he : U \ {k, l} = U := by
            refine Finset.sdiff_eq_self_of_disjoint ?_
            rw [Finset.disjoint_right]
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hkU
            · exact hlU
          rw [he] at hsq ⊢
          exact hsq
  · -- the diagonal outside `U`
    intro k hkU
    unfold faCoef
    by_cases hz0 : k = i ∨ k = i ∨ k ∈ S \ U ∨ k ∈ S \ U
    · simp only [hz0, ite_true, norm_zero]
      positivity
    · simp only [hz0, ite_false]
      have hki : k ≠ i := fun e => hz0 (Or.inl e)
      have he : U \ {k, k} = U := by
        refine Finset.sdiff_eq_self_of_disjoint ?_
        rw [Finset.disjoint_right]
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton, or_self] at hx
        rw [hx]
        exact hkU
      rw [he]
      rcases U.eq_empty_or_nonempty with hU0 | hUne
      · subst hU0
        rw [gradedTerm_empty]
        have e : ({k, k} : Finset (Fin N)) = {k} := by simp
        rw [e]
        simpa using hdg k hki
      · have h := hgr k k hki hki (Or.inl (by rw [he]; exact hUne))
        rw [he] at h
        refine h.trans ?_
        have h1 : w ^ (U.card + 1) ≤ w ^ U.card :=
          pow_le_pow_of_le_one hw0 hw1 (Nat.le_add_right U.card 1)
        have h2 := pow_nonneg hw0 U.card
        linarith

end CoefBounds

/-! ### The Hilbert–Schmidt norm of a minor (Ward identity and (3.31) of [15]) -/

section HS

/-- `N⁻² Σ_{k,l ∉ T} |G^{(T)}_{kl}|² ≤ (Im m_sc + Λ + C |T| (Im m_sc + Λ_d + Λ_o)/(Nη))/(Nη)`,
from the Ward identity (3.27) and (3.31) of [15]. -/
private lemma fa_hs_bound : ∃ c1 > 0, ∃ CH > 0, ∀ {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ},
    H.IsHermitian → ∀ {z : ℂ}, |z.re| ≤ 5 → 0 < z.im → z.im ≤ 10 →
    ∀ (o d g : ℝ) (T : Finset (Fin N)), 0 ≤ o → 0 ≤ d →
    (∀ a b, a ≠ b → ‖resolventC H z a b‖ ≤ o) → (∀ a, ‖resolventC H z a a - msc z‖ ≤ d) →
    ‖stieltjesM H z - msc z‖ ≤ g → ((T.card : ℝ) + 1) * (o + d) ≤ c1 →
    ∑ k ∈ Tᶜ, ∑ l, ‖resolventC (zeroRC T H) z k l‖ ^ 2 ≤
      N / z.im * ((msc z).im + g + CH * T.card * ((msc z).im + d + o) / (N * z.im)) := by
  obtain ⟨c1r, hc1r, Cr, hCr, hR⟩ := resolventC_zeroRC_sub_le
  have hCr0 : 0 < Cr := by linarith
  refine ⟨c1r, hc1r, Cr * Cr, by positivity, ?_⟩
  intro N H hH z hre hz hz10 o d g T ho hd hoff hdiag hg hcard
  have hod0 : 0 ≤ o + d := by linarith
  have him := im_msc_pos hz
  set B : ℝ := Cr * ((msc z).im + Cr * (d + o)) / (N * z.im) with hBdef
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    have : Tᶜ = ∅ := Finset.eq_empty_of_isEmpty _
    rw [this, Finset.sum_empty]
    simp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hB0 : 0 ≤ B := by positivity
  have hcardT : ∀ V : Finset (Fin N), V.card ≤ T.card → (V.card : ℝ) * (o + d) ≤ c1r := by
    intro V hV
    have h1 : (V.card : ℝ) ≤ T.card + 1 := by
      have : (V.card : ℝ) ≤ T.card := by exact_mod_cast hV
      linarith
    exact (mul_le_mul_of_nonneg_right h1 hod0).trans hcard
  have hod1 : o + d ≤ c1r := by
    have h0 : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
    nlinarith
  -- the chain of minors
  have hchain : ∀ V : Finset (Fin N), V.card ≤ T.card →
      ‖minorM V H z - stieltjesM H z‖ ≤ V.card * B := by
    intro V
    induction V using Finset.induction_on with
    | empty => intro _; simp [minorM_empty]
    | insert a V haV ih =>
      intro hc
      rw [Finset.card_insert_of_notMem haV] at hc
      have ih' := ih (by omega)
      have hstep := (norm_minorM_insert_sub_le hH haV hz).1
      have hRV := hR hH hre hz hz10 o d V ho hoff hdiag hod1 (hcardT V (by omega)) a a haV haV
      simp only [ite_true] at hRV
      obtain ⟨hR1, hR2⟩ := hRV
      set G := resolventC (zeroRC V H) z a a with hGdef
      have hGpos : 0 < ‖G‖ := lt_of_lt_of_le (by positivity) hR2
      have hImG : G.im ≤ (msc z).im + Cr * (d + o) := by
        have h1 : G.im - (msc z).im ≤ ‖G - msc z‖ := by
          rw [← Complex.sub_im]
          exact (le_abs_self _).trans (Complex.abs_im_le_norm _)
        linarith
      have hstep' : G.im / (N * z.im * ‖G‖) ≤ B := by
        rw [hBdef]
        rcases le_or_gt G.im 0 with hneg | hpos
        · have : G.im / (N * z.im * ‖G‖) ≤ 0 :=
            div_nonpos_of_nonpos_of_nonneg hneg (by positivity)
          linarith
        · rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : G.im ≤ Cr * ‖G‖ * G.im := by
            have : 1 ≤ Cr * ‖G‖ := by
              have := mul_le_mul_of_nonneg_left hR2 hCr0.le
              rwa [mul_inv_cancel₀ hCr0.ne'] at this
            nlinarith
          have h2 : Cr * ‖G‖ * G.im ≤ Cr * ‖G‖ * ((msc z).im + Cr * (d + o)) :=
            mul_le_mul_of_nonneg_left hImG (by positivity)
          nlinarith [mul_pos hNr hz]
      rw [Finset.card_insert_of_notMem haV]
      calc ‖minorM (insert a V) H z - stieltjesM H z‖
          ≤ ‖minorM (insert a V) H z - minorM V H z‖ + ‖minorM V H z - stieltjesM H z‖ := by
            have := norm_add_le (minorM (insert a V) H z - minorM V H z)
              (minorM V H z - stieltjesM H z)
            simpa using this
        _ ≤ B + V.card * B := add_le_add (hstep.trans hstep') ih'
        _ = ((V.card + 1 : ℕ) : ℝ) * B := by push_cast; ring
  -- Ward identity
  have hward : ∑ k ∈ Tᶜ, ∑ l, ‖resolventC (zeroRC T H) z k l‖ ^ 2 =
      (N * minorM T H z).im / z.im := by
    have h1 : ∀ k, ∑ l, ‖resolventC (zeroRC T H) z k l‖ ^ 2 =
        (resolventC (zeroRC T H) z k k).im / z.im :=
      fun k => sum_norm_sq_resolventC_zeroRC hH T hz k
    simp only [h1]
    rw [← Finset.sum_div]
    congr 1
    unfold minorM
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hNpos.ne'), one_mul, Complex.im_sum]
  rw [hward]
  have hm : (minorM T H z).im ≤ (msc z).im + g + T.card * B := by
    have h1 := hchain T le_rfl
    have h2 : (minorM T H z).im - (stieltjesM H z).im ≤ ‖minorM T H z - stieltjesM H z‖ := by
      rw [← Complex.sub_im]
      exact (le_abs_self _).trans (Complex.abs_im_le_norm _)
    have h3 : (stieltjesM H z).im - (msc z).im ≤ ‖stieltjesM H z - msc z‖ := by
      rw [← Complex.sub_im]
      exact (le_abs_self _).trans (Complex.abs_im_le_norm _)
    linarith
  have hNim : (N * minorM T H z).im = N * (minorM T H z).im := by
    rw [Complex.mul_im]
    simp
  rw [hNim, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hz]
  refine mul_le_mul_of_nonneg_left (hm.trans ?_) hNr.le
  have : (T.card : ℝ) * B ≤ Cr * Cr * T.card * ((msc z).im + d + o) / (N * z.im) := by
    rw [hBdef]
    have hT0 : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
    rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
    have : Cr * ((msc z).im + Cr * (d + o)) ≤ Cr * Cr * ((msc z).im + d + o) := by
      have h1 : Cr ≤ Cr * Cr := by nlinarith
      have h2 := mul_le_mul_of_nonneg_right h1 him.le
      nlinarith
    nlinarith
  linarith

end HS

/-! ### Moments of the quadratic forms in one row (Appendix A of [15]) -/

section RowMoments

variable {N : ℕ} {L : EntryLaws N}

private lemma fa_sq_le_of_abs_le {x q : ℝ} (h : |x| ≤ q⁻¹) : x ^ 2 ≤ (q⁻¹) ^ 2 := by
  calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    _ ≤ (q⁻¹) ^ 2 := by gcongr

/-- Under (2.6), `N⁻¹ ≤ q⁻²`. -/
private lemma fa_inv_le {C0 q : ℝ} (hL : L.IsGenWigner C0) (hq : L.BoundedSupportAS q)
    (hN : 2 ≤ N) : (N : ℝ)⁻¹ ≤ (q⁻¹) ^ 2 := by
  have hp : ∃ p : OffDiag N, True :=
    ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.lt_def]⟩, trivial⟩
  obtain ⟨p, -⟩ := hp
  have := hL.isProb.off p
  have hb : ∀ᵐ x ∂(L.off p), |x| ≤ q⁻¹ := by
    rw [ae_iff]
    simpa [not_le] using hq.2 p
  have hae : ∀ᵐ x ∂(L.off p), x ^ 2 ≤ (q⁻¹) ^ 2 := by
    filter_upwards [hb] with x hx
    exact fa_sq_le_of_abs_le hx
  calc (N : ℝ)⁻¹ = ∫ x, x ^ 2 ∂(L.off p) := (hL.var_off p).symm
    _ ≤ ∫ _x, (q⁻¹) ^ 2 ∂(L.off p) :=
        integral_mono_ae (hL.sq_int_off p) (integrable_const _) hae
    _ = (q⁻¹) ^ 2 := by simp

/-- The centred squares `h_{ik}² - E h_{ik}²` of the row `i`. -/
private def faSq (L : EntryLaws N) (i k : Fin N) (ω : Entries N) : ℝ :=
  (symOfEntries ω i k) ^ 2 - ∫ ω', (symOfEntries ω' i k) ^ 2 ∂L.law

private lemma fa_integrable_pow_sym {L : EntryLaws N} (hL : L.IsProb) {q : ℝ}
    (hq : L.BoundedSupportAS q) (a b : Fin N) (n : ℕ) :
    Integrable (fun ω : Entries N => (symOfEntries ω a b) ^ n) L.law := by
  have := isProbabilityMeasure_law hL
  refine Integrable.of_bound ((measurable_symOfEntries_at a b).pow_const n).aestronglyMeasurable
    ((q⁻¹) ^ n) ?_
  filter_upwards [fa_ae_sym_le hL hq a b] with ω hω
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) hω n

private lemma fa_sq_mean_bounds {C0 : ℝ} (hL : L.IsGenWigner C0) {q : ℝ}
    (hq : L.BoundedSupportAS q) (a b : Fin N) :
    0 ≤ ∫ ω, (symOfEntries ω a b) ^ 2 ∂L.law ∧
      ∫ ω, (symOfEntries ω a b) ^ 2 ∂L.law ≤ (q⁻¹) ^ 2 := by
  have := isProbabilityMeasure_law hL.isProb
  refine ⟨integral_nonneg fun ω => sq_nonneg _, ?_⟩
  calc ∫ ω, (symOfEntries ω a b) ^ 2 ∂L.law ≤ ∫ _ω, (q⁻¹) ^ 2 ∂L.law :=
        integral_mono_ae (fa_integrable_pow_sym hL.isProb hq a b 2) (integrable_const _)
          (by filter_upwards [fa_ae_sym_le hL.isProb hq a b] with ω hω
              exact fa_sq_le_of_abs_le hω)
    _ = (q⁻¹) ^ 2 := by simp

private lemma fa_faSq_facts {C0 : ℝ} (hL : L.IsGenWigner C0) {q : ℝ}
    (hq : L.BoundedSupportAS q) (i : Fin N) :
    iIndepFun (fun k => faSq L i k) L.law ∧ (∀ k, Measurable (faSq L i k)) ∧
    (∀ k, ∫ ω, faSq L i k ω ∂L.law = 0) ∧ (∀ k, ∀ᵐ ω ∂L.law, |faSq L i k ω| ≤ (q ^ 2)⁻¹) ∧
    (∀ k, ∫ ω, faSq L i k ω ^ 2 ∂L.law ≤ (1 + C0) / N * (q⁻¹) ^ 2) := by
  have hP := isProbabilityMeasure_law hL.isProb
  refine ⟨?_, fun k => ((measurable_symOfEntries_at i k).pow_const 2).sub_const _, fun k => ?_,
    fun k => ?_, fun k => ?_⟩
  · have h := (fa_iIndep_row hL.isProb i).comp
      (fun k x => x ^ 2 - ∫ ω', (symOfEntries ω' i k) ^ 2 ∂L.law)
      (fun k => (measurable_id.pow_const 2).sub_const _)
    convert h using 1
    funext k
    rfl
  · unfold faSq
    rw [integral_sub (fa_integrable_pow_sym hL.isProb hq i k 2) (integrable_const _)]
    simp
  · obtain ⟨hm0, hm1⟩ := fa_sq_mean_bounds hL hq i k
    filter_upwards [fa_ae_sym_le hL.isProb hq i k] with ω hω
    have h1 := fa_sq_le_of_abs_le hω
    have h2 : 0 ≤ (symOfEntries ω i k) ^ 2 := sq_nonneg _
    have e : (q ^ 2)⁻¹ = (q⁻¹) ^ 2 := by rw [inv_pow]
    rw [e]
    unfold faSq
    rw [abs_le]
    constructor <;> linarith
  · set m := ∫ ω', (symOfEntries ω' i k) ^ 2 ∂L.law with hm
    have hi2 := fa_integrable_pow_sym hL.isProb hq i k 2
    have hi4 := fa_integrable_pow_sym hL.isProb hq i k 4
    have e : ∀ ω, faSq L i k ω ^ 2 =
        (symOfEntries ω i k) ^ 4 - 2 * m * (symOfEntries ω i k) ^ 2 + m ^ 2 := by
      intro ω
      unfold faSq
      ring
    simp only [e]
    have hsub : Integrable (fun ω : Entries N =>
        (symOfEntries ω i k) ^ 4 - 2 * m * (symOfEntries ω i k) ^ 2) L.law :=
      hi4.sub (hi2.const_mul _)
    rw [integral_add (f := fun ω : Entries N =>
        (symOfEntries ω i k) ^ 4 - 2 * m * (symOfEntries ω i k) ^ 2) (g := fun _ => m ^ 2)
        hsub (integrable_const _),
      integral_sub (f := fun ω : Entries N => (symOfEntries ω i k) ^ 4)
        (g := fun ω : Entries N => 2 * m * (symOfEntries ω i k) ^ 2) hi4 (hi2.const_mul _),
      integral_const_mul, ← hm]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have h4 : ∫ ω, (symOfEntries ω i k) ^ 4 ∂L.law ≤ (q⁻¹) ^ 2 * m := by
      rw [hm, ← integral_const_mul]
      refine integral_mono_ae hi4 (hi2.const_mul _) ?_
      filter_upwards [fa_ae_sym_le hL.isProb hq i k] with ω hω
      have h1 := fa_sq_le_of_abs_le hω
      have : (symOfEntries ω i k) ^ 4 = (symOfEntries ω i k) ^ 2 * (symOfEntries ω i k) ^ 2 := by
        ring
      rw [this]
      exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    have hmv : m ≤ (1 + C0) / N := fa_var_sym_le hL i k
    have hq2 : 0 ≤ (q⁻¹) ^ 2 := sq_nonneg _
    have hm0 : 0 ≤ m := (fa_sq_mean_bounds hL hq i k).1
    nlinarith [mul_le_mul_of_nonneg_left hmv hq2]

private lemma fa_integrable_pow_of_ae {f : Entries N → ℂ} (hL : L.IsProb) (hf : Measurable f)
    {M : ℝ} (hM : ∀ᵐ ω ∂L.law, ‖f ω‖ ≤ M) (n : ℕ) :
    Integrable (fun ω => ‖f ω‖ ^ n) L.law := by
  have := isProbabilityMeasure_law hL
  refine Integrable.of_bound (hf.norm.pow_const n).aestronglyMeasurable (M ^ n) ?_
  filter_upwards [hM] with ω hω
  rw [Real.norm_eq_abs, abs_pow, abs_norm]
  exact pow_le_pow_left₀ (norm_nonneg _) hω n

private lemma fa_pow_three_le (x y w : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hw : 0 ≤ w) (n : ℕ) :
    (x + y + w) ^ n ≤ 3 ^ n * (x ^ n + y ^ n + w ^ n) := by
  set M := max (max x y) w with hM
  have hxM : x ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hyM : y ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hwM : w ≤ M := le_max_right _ _
  have h1 : (x + y + w) ^ n ≤ (3 * M) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
  have h2 : M ^ n ≤ x ^ n + y ^ n + w ^ n := by
    have hx' := pow_nonneg hx n
    have hy' := pow_nonneg hy n
    have hw' := pow_nonneg hw n
    rcases max_choice (max x y) w with h | h <;> rw [hM, h]
    · rcases max_choice x y with h' | h' <;> rw [h'] <;> linarith
    · linarith
  rw [mul_pow] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))

/-- The `2p`-th moment of `Σ_{k,l} (h_{ik} h_{il} - δ_{kl} N⁻¹) B_{kl}` with deterministic
coefficients vanishing in the row and column `i`: the terms with `k, l ∈ U` are bounded almost
surely, the other off-diagonal terms by (A.4) and the diagonal terms by (A.2) of [15]. -/
private lemma fa_moment_split (C0 : ℝ) (hC0 : 0 ≤ C0) : ∃ C1 > 0, ∃ C2 > 0, ∀ {N : ℕ}
    {L : EntryLaws N} {q : ℝ}, L.IsGenWigner C0 → L.BoundedSupportAS q → 1 ≤ q → 2 ≤ N →
    ∀ (i : Fin N) (U : Finset (Fin N)) (B Bq : Fin N → Fin N → ℂ) (A : Fin N → ℂ) (Mu : ℝ),
    (∀ k, B i k = 0) → (∀ k, B k i = 0) → (∀ k l, k ∈ U → l ∈ U → ‖B k l‖ ≤ Mu) →
    (∀ k l, Bq k l = if k ∈ U ∧ l ∈ U then 0 else B k l) →
    (∀ k, A k = if k ∈ U then 0 else B k k) → ∀ p : ℕ, 1 ≤ p →
    ∫ ω, ‖∑ k, ∑ l, (((symOfEntries ω i k * symOfEntries ω i l : ℝ) : ℂ) -
        if k = l then ((N : ℝ)⁻¹ : ℂ) else 0) * B k l‖ ^ (2 * p) ∂L.law ≤
      3 ^ (2 * p) * (((U.card : ℝ) ^ 2 * (q⁻¹) ^ 2 * Mu) ^ (2 * p) +
        (C2 * p) ^ (4 * p) * ((⨆ k, ⨆ l, if k = l then 0 else ‖Bq k l‖) / q +
          Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∑ k, ∑ l, if k = l then 0 else ‖Bq k l‖ ^ 2)) ^ (2 * p) +
        (C1 * p) ^ (2 * p) * ((⨆ k, ‖A k‖) / q ^ 2 +
          Real.sqrt ((1 + C0) / N * (q⁻¹) ^ 2 * ∑ k, ‖A k‖ ^ 2)) ^ (2 * p)) := by
  obtain ⟨C1, hC1, hlin⟩ := moment_linear_le
  obtain ⟨C2, hC2, hquad⟩ := moment_quadratic_le (1 + C0) (by linarith)
  refine ⟨C1, hC1, C2, hC2, ?_⟩
  intro N L q hL hq hq1 hN i U B Bq A Mu hBi hBi' hBU hBq hA p hp
  have hP := isProbabilityMeasure_law hL.isProb
  have hq0 : 0 < q := by linarith
  set a : Fin N → Entries N → ℝ := fun k ω => symOfEntries ω i k with hadef
  have ha_meas : ∀ k, Measurable (a k) := fun k => measurable_symOfEntries_at i k
  obtain ⟨hSind, hSmeas, hSmean, hSbd, hSvar⟩ := fa_faSq_facts hL hq i
  have hNinv := fa_inv_le hL hq hN
  -- the three pieces
  set W1 : Entries N → ℂ := fun ω => ∑ k, ∑ l, if k ∈ U ∧ l ∈ U then
    (((a k ω * a l ω : ℝ) : ℂ) - if k = l then ((N : ℝ)⁻¹ : ℂ) else 0) * B k l else 0 with hW1
  set Q2 : Entries N → ℂ := fun ω => ∑ k, ∑ l,
    (if k = l then 0 else Bq k l * (a k ω : ℂ) * (a l ω : ℂ)) with hQ2
  set D2 : Entries N → ℂ := fun ω => ∑ k, A k * (faSq L i k ω : ℂ) with hD2
  have hsplit : ∀ ω, (∑ k, ∑ l, (((symOfEntries ω i k * symOfEntries ω i l : ℝ) : ℂ) -
      if k = l then ((N : ℝ)⁻¹ : ℂ) else 0) * B k l) = W1 ω + Q2 ω + D2 ω := by
    intro ω
    have hD2' : D2 ω = ∑ k, ∑ l, if k = l then A k * (faSq L i k ω : ℂ) else 0 := by
      rw [hD2]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_ite_eq]
      simp
    rw [hD2', hW1, hQ2]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    by_cases hU : k ∈ U ∧ l ∈ U
    · have hA0 : k = l → A k = 0 := fun _ => by rw [hA k, ite_eq_left hU.1]
      rw [ite_eq_left hU, hBq k l, ite_eq_left hU]
      by_cases hkl : k = l
      · rw [ite_eq_left hkl, ite_eq_left hkl, hA0 hkl]
        simp [hadef]
      · simp [hkl, hadef]
    · rw [ite_eq_right hU, hBq k l, ite_eq_right hU]
      by_cases hkl : k = l
      · subst hkl
        have hkU : k ∉ U := fun h => hU ⟨h, h⟩
        rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl, hA k, ite_eq_right hkU]
        by_cases hki : k = i
        · subst hki
          rw [hBi]
          simp
        · have hm : ∫ ω', (symOfEntries ω' i k) ^ 2 ∂L.law = (N : ℝ)⁻¹ :=
            fa_var_sym_off hL (Ne.symm hki)
          simp only [faSq, hm]
          push_cast
          ring
      · rw [ite_eq_right hkl, ite_eq_right hkl, ite_eq_right hkl]
        simp only [hadef]
        push_cast
        ring
  -- measurability
  have hmW1 : Measurable W1 := by
    refine Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_
    by_cases h : k ∈ U ∧ l ∈ U
    · simp only [h, and_self, ite_true]
      exact ((Complex.measurable_ofReal.comp ((ha_meas k).mul (ha_meas l))).sub_const _).mul_const _
    · simp only [h, ite_false]
      exact measurable_const
  have hmQ2 : Measurable Q2 := by
    refine Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_
    split_ifs
    · exact measurable_const
    · exact ((Complex.measurable_ofReal.comp (ha_meas k)).const_mul _).mul
        (Complex.measurable_ofReal.comp (ha_meas l))
  have hmD2 : Measurable D2 :=
    Finset.measurable_sum _ fun k _ => (Complex.measurable_ofReal.comp (hSmeas k)).const_mul _
  -- almost sure bounds
  have hae := fa_ae_entries hL.isProb hq
  have hcoef : ∀ ω, (∀ a b : Fin N, |symOfEntries ω a b| ≤ q⁻¹) → ∀ k l,
      ‖(((a k ω * a l ω : ℝ) : ℂ) - if k = l then ((N : ℝ)⁻¹ : ℂ) else 0)‖ ≤ (q⁻¹) ^ 2 := by
    intro ω hω k l
    by_cases hkl : k = l
    · subst hkl
      rw [ite_eq_left rfl]
      have e : (((a k ω * a k ω : ℝ) : ℂ) - ((N : ℝ)⁻¹ : ℂ)) =
          ((a k ω * a k ω - (N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; ring
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
      have h1 : a k ω * a k ω ≤ (q⁻¹) ^ 2 := by
        rw [← sq]; exact fa_sq_le_of_abs_le (hω i k)
      have h2 : 0 ≤ a k ω * a k ω := mul_self_nonneg _
      have h3 : 0 ≤ (N : ℝ)⁻¹ := by positivity
      constructor <;> linarith
    · rw [ite_eq_right hkl, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_mul, sq]
      exact mul_le_mul (hω i k) (hω i l) (abs_nonneg _) (by positivity)
  have hW1b : ∀ᵐ ω ∂L.law, ‖W1 ω‖ ≤ (U.card : ℝ) ^ 2 * (q⁻¹) ^ 2 * Mu := by
    filter_upwards [hae] with ω hω
    rw [hW1]
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ k, ‖∑ l, (if k ∈ U ∧ l ∈ U then
        (((a k ω * a l ω : ℝ) : ℂ) - if k = l then ((N : ℝ)⁻¹ : ℂ) else 0) * B k l else 0)‖ ≤
        if k ∈ U then (U.card : ℝ) * ((q⁻¹) ^ 2 * Mu) else 0 := by
      intro k
      refine (norm_sum_le _ _).trans ?_
      by_cases hk : k ∈ U
      · rw [ite_eq_left hk]
        have h2 : ∀ l, ‖(if k ∈ U ∧ l ∈ U then
            (((a k ω * a l ω : ℝ) : ℂ) - if k = l then ((N : ℝ)⁻¹ : ℂ) else 0) * B k l else 0)‖ ≤
            if l ∈ U then (q⁻¹) ^ 2 * Mu else 0 := by
          intro l
          by_cases hl : l ∈ U
          · rw [ite_eq_left ⟨hk, hl⟩, ite_eq_left hl, norm_mul]
            exact mul_le_mul (hcoef ω hω k l) (hBU k l hk hl) (norm_nonneg _) (by positivity)
          · rw [ite_eq_right (fun h => hl h.2), ite_eq_right hl, norm_zero]
        refine (Finset.sum_le_sum fun l _ => h2 l).trans (le_of_eq ?_)
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      · simp [hk]
    refine (Finset.sum_le_sum fun k _ => h1 k).trans (le_of_eq ?_)
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    ring
  have hQ2b : ∀ᵐ ω ∂L.law, ‖Q2 ω‖ ≤ ∑ k, ∑ l, ‖Bq k l‖ * (q⁻¹ * q⁻¹) := by
    filter_upwards [hae] with ω hω
    rw [hQ2]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun l _ => ?_))
    split_ifs
    · rw [norm_zero]; positivity
    · rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hω i k) (hω i l) (abs_nonneg _)
        (by positivity)) (norm_nonneg _)
  have hD2b : ∀ᵐ ω ∂L.law, ‖D2 ω‖ ≤ ∑ k, ‖A k‖ * (q ^ 2)⁻¹ := by
    filter_upwards [ae_all_iff.2 hSbd] with ω hω
    rw [hD2]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hω k) (norm_nonneg _)
  have hiW := fa_integrable_pow_of_ae hL.isProb hmW1 hW1b (2 * p)
  have hiQ := fa_integrable_pow_of_ae hL.isProb hmQ2 hQ2b (2 * p)
  have hiD := fa_integrable_pow_of_ae hL.isProb hmD2 hD2b (2 * p)
  -- the moments of the pieces
  have hmomW : ∫ ω, ‖W1 ω‖ ^ (2 * p) ∂L.law ≤ ((U.card : ℝ) ^ 2 * (q⁻¹) ^ 2 * Mu) ^ (2 * p) := by
    calc ∫ ω, ‖W1 ω‖ ^ (2 * p) ∂L.law
        ≤ ∫ _ω, ((U.card : ℝ) ^ 2 * (q⁻¹) ^ 2 * Mu) ^ (2 * p) ∂L.law :=
          integral_mono_ae hiW (integrable_const _) (by
            filter_upwards [hW1b] with ω hω
            exact pow_le_pow_left₀ (norm_nonneg _) hω _)
      _ = _ := by simp
  have hmomQ := hquad L.law N N a (fa_iIndep_row hL.isProb i) ha_meas
    (fun k => fa_mean_sym hL i k) q hq0 hq1 le_rfl (fun k => fa_ae_sym_le hL.isProb hq i k)
    (fun k => fa_var_sym_le hL i k) Bq p hp
  have hmomD := hlin L.law N (faSq L i) hSind hSmeas hSmean (q ^ 2) ((1 + C0) / N * (q⁻¹) ^ 2)
    (by positivity) hSbd hSvar A p hp
  -- assembling
  have hpt : ∀ ω, ‖∑ k, ∑ l, (((symOfEntries ω i k * symOfEntries ω i l : ℝ) : ℂ) -
      if k = l then ((N : ℝ)⁻¹ : ℂ) else 0) * B k l‖ ^ (2 * p) ≤
      3 ^ (2 * p) * (‖W1 ω‖ ^ (2 * p) + ‖Q2 ω‖ ^ (2 * p) + ‖D2 ω‖ ^ (2 * p)) := by
    intro ω
    rw [hsplit ω]
    have h1 : ‖W1 ω + Q2 ω + D2 ω‖ ≤ ‖W1 ω‖ + ‖Q2 ω‖ + ‖D2 ω‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 _).trans
      (fa_pow_three_le _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) _)
  calc ∫ ω, ‖∑ k, ∑ l, (((symOfEntries ω i k * symOfEntries ω i l : ℝ) : ℂ) -
        if k = l then ((N : ℝ)⁻¹ : ℂ) else 0) * B k l‖ ^ (2 * p) ∂L.law
      ≤ ∫ ω, 3 ^ (2 * p) * (‖W1 ω‖ ^ (2 * p) + ‖Q2 ω‖ ^ (2 * p) + ‖D2 ω‖ ^ (2 * p)) ∂L.law :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => by positivity)
          (((hiW.add hiQ).add hiD).const_mul _) (ae_of_all _ hpt)
    _ = 3 ^ (2 * p) * (∫ ω, ‖W1 ω‖ ^ (2 * p) ∂L.law + ∫ ω, ‖Q2 ω‖ ^ (2 * p) ∂L.law +
          ∫ ω, ‖D2 ω‖ ^ (2 * p) ∂L.law) := by
        rw [integral_const_mul, integral_add (f := fun ω => ‖W1 ω‖ ^ (2 * p) + ‖Q2 ω‖ ^ (2 * p))
          (g := fun ω => ‖D2 ω‖ ^ (2 * p)) (hiW.add hiQ) hiD, integral_add hiW hiQ]
    _ ≤ _ := by
        gcongr

end RowMoments

/-! ### Conditioning on the entries outside one row -/

section Conditioning

variable {N : ℕ} {L : EntryLaws N}

/-- `E X = E E_i X` for real `X` (Fubini over the row `i` and the other entries). -/
private lemma fa_integral_rowsMix (hL : L.IsProb) (T : Finset (Fin N)) {g : Entries N → ℝ}
    (hg : Integrable g L.law) :
    ∫ ω, g ω ∂L.law = ∫ ω, (∫ ω', g (rowsMix T ω ω') ∂L.law) ∂L.law := by
  have h := EntryLaws.integral_rowsExp hL T (X := fun ω => (g ω : ℂ)) hg.ofReal
  simp only [EntryLaws.rowsExp, integral_complex_ofReal] at h
  exact_mod_cast h.symm

/-- If the conditional `p`-th moment of `F` given the entries outside the row `i` is at most
`R` on `[Ξ]_i`, then `E 1(Ξ) |F|^p ≤ R`. -/
private lemma fa_lintegral_sat_le (hL : L.IsProb) (i : Fin N) {Ξ : Set (Entries N)}
    (hsat : MeasurableSet (rowSat {i} Ξ)) {F : Entries N → ℂ} (hF : Measurable F) {M : ℝ}
    (hM : ∀ᵐ ω ∂L.law, ‖F ω‖ ≤ M) (p : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hcond : ∀ ω ∈ rowSat {i} Ξ, ∫ ω', ‖F (rowsMix {i} ω ω')‖ ^ p ∂L.law ≤ R) :
    ∫⁻ ω in Ξ, ‖F ω‖ₑ ^ p ∂L.law ≤ ENNReal.ofReal R := by
  have hP := isProbabilityMeasure_law hL
  set g : Entries N → ℝ := (rowSat {i} Ξ).indicator (fun ω => ‖F ω‖ ^ p) with hgdef
  have hgm : Measurable g := (hF.norm.pow_const p).indicator hsat
  have hgi : Integrable g L.law := by
    refine Integrable.of_bound hgm.aestronglyMeasurable (M ^ p) ?_
    filter_upwards [hM] with ω hω
    rw [hgdef]
    by_cases h : ω ∈ rowSat {i} Ξ
    · rw [Set.indicator_of_mem h, Real.norm_eq_abs, abs_pow, abs_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) hω p
    · rw [Set.indicator_of_notMem h, norm_zero]
      exact pow_nonneg ((norm_nonneg _).trans hω) p
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => Set.indicator_nonneg (fun _ _ => by positivity) ω
  have h1 : ∫⁻ ω in Ξ, ‖F ω‖ₑ ^ p ∂L.law ≤ ∫⁻ ω, ENNReal.ofReal (g ω) ∂L.law := by
    calc ∫⁻ ω in Ξ, ‖F ω‖ₑ ^ p ∂L.law ≤ ∫⁻ ω in rowSat {i} Ξ, ‖F ω‖ₑ ^ p ∂L.law :=
          lintegral_mono_set (subset_rowSat {i} Ξ)
      _ = ∫⁻ ω, (rowSat {i} Ξ).indicator (fun ω => ‖F ω‖ₑ ^ p) ω ∂L.law :=
          (lintegral_indicator hsat _).symm
      _ = ∫⁻ ω, ENNReal.ofReal (g ω) ∂L.law := by
          refine lintegral_congr fun ω => ?_
          rw [hgdef]
          by_cases h : ω ∈ rowSat {i} Ξ
          · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, ENNReal.ofReal_pow (norm_nonneg _),
              ofReal_norm]
          · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, ENNReal.ofReal_zero]
  have h2 : ∫⁻ ω, ENNReal.ofReal (g ω) ∂L.law = ENNReal.ofReal (∫ ω, g ω ∂L.law) :=
    (ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hg0)).symm
  have hmem : ∀ ω ω', (rowsMix {i} ω ω' ∈ rowSat {i} Ξ) = (ω ∈ rowSat {i} Ξ) :=
    fun ω ω' => rowIndep_iff_rowsMix.mp (rowIndep_mem_rowSat {i} Ξ) ω ω'
  have h3 : ∫ ω, g ω ∂L.law ≤ R := by
    rw [fa_integral_rowsMix hL {i} hgi]
    calc ∫ ω, (∫ ω', g (rowsMix {i} ω ω') ∂L.law) ∂L.law ≤ ∫ _ω, R ∂L.law := by
          refine integral_mono_of_nonneg (ae_of_all _ fun ω => integral_nonneg fun ω' => hg0 _)
            (integrable_const _) (ae_of_all _ fun ω => ?_)
          by_cases h : ω ∈ rowSat {i} Ξ
          · have e : ∀ ω', g (rowsMix {i} ω ω') = ‖F (rowsMix {i} ω ω')‖ ^ p := by
              intro ω'
              rw [hgdef, Set.indicator_of_mem (by rw [hmem]; exact h)]
            simp only [e]
            exact hcond ω h
          · have e : ∀ ω', g (rowsMix {i} ω ω') = 0 := by
              intro ω'
              rw [hgdef, Set.indicator_of_notMem (by rw [hmem]; exact h)]
            simp only [e, integral_zero]
            exact hR
      _ = R := by simp
  calc ∫⁻ ω in Ξ, ‖F ω‖ₑ ^ p ∂L.law ≤ ∫⁻ ω, ENNReal.ofReal (g ω) ∂L.law := h1
    _ = ENNReal.ofReal (∫ ω, g ω ∂L.law) := h2
    _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal h3

end Conditioning

/-! ### Assumption (i) of Theorem 5.6 for `Z_i^{[U]}` -/

section HypI

variable {N : ℕ} {L : EntryLaws N}

private lemma fa_faZ_rowIndep (z : ℂ) {U : Finset (Fin N)} {i : Fin N} (hi : i ∉ U) :
    RowIndep U (faZ z U i) := by
  intro ω
  unfold faZ
  simp only [hi, ite_false]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  by_cases h : k ∈ insert i U ∨ l ∈ insert i U
  · simp only [h, ite_true]
  · simp only [h, ite_false]
    have hk : k ∉ U := fun hk => h (Or.inl (Finset.mem_insert_of_mem hk))
    have hl : l ∉ U := fun hl => h (Or.inr (Finset.mem_insert_of_mem hl))
    have h1 : symOfEntries (zeroEntries U ω) i k = symOfEntries ω i k :=
      rowIndep_symOfEntries_apply hi hk ω
    have h2 : symOfEntries (zeroEntries U ω) l i = symOfEntries ω l i :=
      rowIndep_symOfEntries_apply hl hi ω
    have h3 : resolventC (zeroRC (insert i U) (symOfEntries (zeroEntries U ω))) z k l =
        resolventC (zeroRC (insert i U) (symOfEntries ω)) z k l :=
      rowIndep_resolventC_zeroRC (Finset.subset_insert i U) z k l ω
    rw [h1, h2, h3]

private lemma fa_integral_mul_sym {C0 : ℝ} (hL : L.IsGenWigner C0) (i k l : Fin N)
    (hk : k ≠ i) :
    ∫ ω, symOfEntries ω i k * symOfEntries ω i l ∂L.law = if k = l then (N : ℝ)⁻¹ else 0 := by
  by_cases hkl : k = l
  · subst hkl
    rw [ite_eq_left rfl, ← fa_var_sym_off hL (Ne.symm hk)]
    congr 1
    funext ω
    ring
  · rw [ite_eq_right hkl]
    have hind := (fa_iIndep_row hL.isProb i).indepFun hkl
    have h := IndepFun.integral_mul_eq_mul_integral hind
      (measurable_symOfEntries_at i k).aestronglyMeasurable
      (measurable_symOfEntries_at i l).aestronglyMeasurable
    simp only [Pi.mul_apply] at h
    rw [h, fa_mean_sym hL i k, zero_mul]

/-- Assumption (i) of Theorem 5.6 of [15] for `Z_i^{[U]}`: integrability, independence of the
rows `U` and `E_i Z_i^{[U]} = 0`. -/
private lemma fa_hyp_i {C0 : ℝ} (hL : L.IsGenWigner C0) {q : ℝ} (hq : L.BoundedSupportAS q)
    {z : ℂ} (hz : 0 < z.im) (U : Finset (Fin N)) (i : Fin N) (hi : i ∉ U) :
    Integrable (faZ z U i) L.law ∧ RowIndep U (faZ z U i) ∧
      ∀ᵐ ω ∂L.law, L.rowsExp {i} (faZ z U i) ω = 0 := by
  have hP := isProbabilityMeasure_law hL.isProb
  refine ⟨?_, fa_faZ_rowIndep z hi, ae_of_all _ fun ω => ?_⟩
  · refine Integrable.of_bound (fa_continuous_faZ hz.ne' U i).aestronglyMeasurable
      ((N : ℝ) ^ 2 * (((q⁻¹) ^ 2 + (N : ℝ)⁻¹) * (1 / z.im))) ?_
    filter_upwards [fa_ae_entries hL.isProb hq] with ω hω
    exact fa_norm_faZ_le hz U i hω
  · unfold EntryLaws.rowsExp
    have hG : ∀ k l ω', resolventC (zeroRC (insert i U) (symOfEntries (rowsMix {i} ω ω'))) z k l =
        resolventC (zeroRC (insert i U) (symOfEntries ω)) z k l := fun k l ω' =>
      rowIndep_iff_rowsMix.mp (rowIndep_resolventC_zeroRC (T := {i})
        (by simp) z k l) ω ω'
    have hint : ∀ k l, Integrable (fun ω' : Entries N =>
        symOfEntries ω' i k * symOfEntries ω' i l) L.law := by
      intro k l
      refine Integrable.of_bound ((measurable_symOfEntries_at i k).mul
        (measurable_symOfEntries_at i l)).aestronglyMeasurable (q⁻¹ * q⁻¹) ?_
      filter_upwards [fa_ae_entries hL.isProb hq] with ω' hω'
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hω' i k) (hω' i l) (abs_nonneg _) ((abs_nonneg _).trans (hω' i k))
    have e : ∀ ω', faZ z U i (rowsMix {i} ω ω') = ∑ k, ∑ l,
        if k ∈ insert i U ∨ l ∈ insert i U then 0 else
          (((symOfEntries ω' i k * symOfEntries ω' i l : ℝ) : ℂ) -
            if k = l then ((N : ℝ)⁻¹ : ℂ) else 0) *
            resolventC (zeroRC (insert i U) (symOfEntries ω)) z k l := by
      intro ω'
      unfold faZ
      simp only [hi, ite_false]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      by_cases h : k ∈ insert i U ∨ l ∈ insert i U
      · simp only [h, ite_true]
      · simp only [h, ite_false]
        rw [hG, ctl_symOfEntries_symm _ l i,
          symOfEntries_rowsMix_left_of_mem {i} (Finset.mem_singleton_self i),
          symOfEntries_rowsMix_left_of_mem {i} (Finset.mem_singleton_self i)]
    simp only [e]
    have hint2 : ∀ k l, Integrable (fun ω' : Entries N =>
        if k ∈ insert i U ∨ l ∈ insert i U then (0 : ℂ) else
          (((symOfEntries ω' i k * symOfEntries ω' i l : ℝ) : ℂ) -
            if k = l then ((N : ℝ)⁻¹ : ℂ) else 0) *
            resolventC (zeroRC (insert i U) (symOfEntries ω)) z k l) L.law := by
      intro k l
      by_cases h : k ∈ insert i U ∨ l ∈ insert i U
      · simp only [h, ite_true]
        exact integrable_const _
      · simp only [h, ite_false]
        exact (((hint k l).ofReal).sub (integrable_const _)).mul_const _
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint2 k l]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => hint2 k l]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h : k ∈ insert i U ∨ l ∈ insert i U
    · simp only [h, ite_true, integral_zero]
    · simp only [h, ite_false]
      have hki : k ≠ i := fun e => h (Or.inl (e ▸ Finset.mem_insert_self i U))
      rw [integral_mul_const, integral_sub (hint k l).ofReal (integrable_const _),
        integral_complex_ofReal, fa_integral_mul_sym hL i k l hki]
      by_cases hkl : k = l
      · simp [hkl]
      · simp [hkl]

/-- The crude bound `|Z_i^{[V]}| ≤ 2 N³` when all entries are at most `q⁻¹ ≤ 1` and `Nη ≥ 1`. -/
private lemma fa_norm_faZ_le' {z : ℂ} (hz : 0 < z.im) (hNz : 1 ≤ (N : ℝ) * z.im) {q : ℝ}
    (hq1 : 1 ≤ q) (V : Finset (Fin N)) (i : Fin N) {ω : Entries N}
    (hω : ∀ a b : Fin N, |symOfEntries ω a b| ≤ q⁻¹) : ‖faZ z V i ω‖ ≤ 2 * (N : ℝ) ^ 3 := by
  have hN : (0 : ℝ) < N := by
    by_contra h
    have : (N : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg N)
    rw [this, zero_mul] at hNz
    linarith
  have hN1 : (1 : ℝ) ≤ N := by
    have : (1 : ℕ) ≤ N := by exact_mod_cast hN
    exact_mod_cast this
  refine (fa_norm_faZ_le hz V i hω).trans ?_
  have h1 : (q⁻¹) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hq1)
  have h2 : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
  have h3 : 1 / z.im ≤ N := by
    rw [div_le_iff₀ hz]
    linarith
  have h4 : ((q⁻¹) ^ 2 + (N : ℝ)⁻¹) * (1 / z.im) ≤ 2 * N :=
    mul_le_mul (by linarith) h3 (by positivity) (by norm_num)
  calc (N : ℝ) ^ 2 * (((q⁻¹) ^ 2 + (N : ℝ)⁻¹) * (1 / z.im)) ≤ (N : ℝ) ^ 2 * (2 * N) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = 2 * (N : ℝ) ^ 3 := by ring

/-- (5.10) and (5.9) (at `r = 2`) of [15] for `Z_i^{[V]}`. -/
private lemma fa_hyp_59_510 {L : EntryLaws N} (hL : L.IsProb) {q : ℝ}
    (hq : L.BoundedSupportAS q) (hq1 : 1 ≤ q) {z : ℂ} (hz : 0 < z.im)
    (hNz : 1 ≤ (N : ℝ) * z.im) (hN4 : 4 ≤ N) (Ξ : Set (Entries N))
    (hΞ : ∀ ω ∈ Ξ, ∀ a b : Fin N, |symOfEntries ω a b| ≤ q⁻¹) (Y : ℝ) (hY : 1 ≤ Y) (p : ℕ)
    (hp : 2 ≤ p) :
    (∀ S U i, U ⊆ S → i ∉ S → S.card ≤ p →
      ∫⁻ ω in rowSat {i} Ξ, ‖gradedTerm (fun V => faZ z V i) S U ω‖ₑ ^ 2 ∂L.law ≤
        ENNReal.ofReal ((N : ℝ) ^ ((8 : ℝ) * p))) ∧
    (∀ U i, i ∉ U → ∀ ω ∈ Ξ, ‖faZ z U i ω‖ ≤ Y * (N : ℝ) ^ (4 : ℝ)) := by
  have hP := isProbabilityMeasure_law hL
  have hN : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  refine ⟨fun S U i hUS hiS hS => ?_, fun U i _ ω hω => ?_⟩
  · have hb : ∀ᵐ ω ∂L.law, ‖gradedTerm (fun V => faZ z V i) S U ω‖ₑ ^ 2 ≤
        ENNReal.ofReal ((N : ℝ) ^ ((8 : ℝ) * p)) := by
      filter_upwards [fa_ae_entries hL hq] with ω hω
      have h1 := fa_norm_graded_le S U i ω (fun V => fa_norm_faZ_le' hz hNz hq1 V i hω)
      have hU : U.card ≤ p := (Finset.card_le_card hUS).trans hS
      have h4 : (2 : ℝ) ^ U.card ≤ (N : ℝ) ^ p := by
        calc (2 : ℝ) ^ U.card ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hU
          _ ≤ (N : ℝ) ^ p := pow_le_pow_left₀ (by norm_num) (by linarith) p
      have h2 : ‖gradedTerm (fun V => faZ z V i) S U ω‖ ≤ (N : ℝ) ^ (p + 4) := by
        refine h1.trans ?_
        calc (2 : ℝ) ^ U.card * (2 * (N : ℝ) ^ 3) ≤ (N : ℝ) ^ p * (N * (N : ℝ) ^ 3) := by
              gcongr
              linarith
          _ = (N : ℝ) ^ (p + 4) := by ring
      have h3 : ‖gradedTerm (fun V => faZ z V i) S U ω‖ ^ 2 ≤ (N : ℝ) ^ ((8 : ℝ) * p) := by
        have e : (N : ℝ) ^ ((8 : ℝ) * p) = (N : ℝ) ^ (8 * p) := by
          rw [← Real.rpow_natCast]
          push_cast
          ring_nf
        rw [e]
        calc ‖gradedTerm (fun V => faZ z V i) S U ω‖ ^ 2 ≤ ((N : ℝ) ^ (p + 4)) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h2 2
          _ = (N : ℝ) ^ (2 * p + 8) := by ring
          _ ≤ (N : ℝ) ^ (8 * p) := pow_le_pow_right₀ hN1 (by omega)
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal h3
    calc ∫⁻ ω in rowSat {i} Ξ, ‖gradedTerm (fun V => faZ z V i) S U ω‖ₑ ^ 2 ∂L.law
        ≤ ∫⁻ ω, ‖gradedTerm (fun V => faZ z V i) S U ω‖ₑ ^ 2 ∂L.law := setLIntegral_le_lintegral _ _
      _ ≤ ∫⁻ _ω, ENNReal.ofReal ((N : ℝ) ^ ((8 : ℝ) * p)) ∂L.law := lintegral_mono_ae hb
      _ = ENNReal.ofReal ((N : ℝ) ^ ((8 : ℝ) * p)) := by simp
  · have h1 := fa_norm_faZ_le' hz hNz hq1 U i (hΞ ω hω)
    have e : (N : ℝ) ^ (4 : ℝ) = (N : ℝ) ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast]; norm_num
    rw [e]
    calc ‖faZ z U i ω‖ ≤ 2 * (N : ℝ) ^ 3 := h1
      _ ≤ 1 * (N : ℝ) ^ 4 := by nlinarith [pow_pos hN0 3]
      _ ≤ Y * (N : ℝ) ^ 4 := mul_le_mul_of_nonneg_right hY (by positivity)

end HypI

/-! ### The brackets of the moment bounds on `Ξ` ((5.102)–(5.105) of [15]) -/

section Brackets

private lemma fa_iSup_le_of {N : ℕ} {f : Fin N → ℝ} {b : ℝ} (hb : 0 ≤ b) (h : ∀ k, f k ≤ b) :
    (⨆ k, f k) ≤ b :=
  Real.iSup_le h hb

/-- `E^{n+1}`-domination used in (5.102)–(5.105). -/
private lemma fa_dom {x Dg C' u K : ℝ} (n : ℕ) (hx : 0 ≤ x) (hu : 0 ≤ u) (hDg : 0 ≤ Dg)
    (hDC : Dg ≤ C') (hK : 0 ≤ K) (hKC : K ≤ C' * u) :
    (Dg * u * x) ^ n * x * K ≤ (C' * x * u) ^ (n + 1) := by
  have h1 : (Dg * u * x) ^ n ≤ (C' * x * u) ^ n :=
    pow_le_pow_left₀ (by positivity) (by nlinarith [mul_nonneg hu hx]) n
  have h2 : x * K ≤ C' * x * u := by nlinarith
  calc (Dg * u * x) ^ n * x * K = (Dg * u * x) ^ n * (x * K) := by ring
    _ ≤ (C' * x * u) ^ n * (C' * x * u) :=
        mul_le_mul h1 h2 (by positivity) (pow_nonneg (by nlinarith [mul_nonneg hu hx]) n)
    _ = (C' * x * u) ^ (n + 1) := by ring

/-- The bracket of (5.102). -/
private lemma fa_T1 (c : ℕ) {q X w Dg C' : ℝ} (hq0 : 0 < q) (hqX : q⁻¹ ≤ X) (hX : 0 ≤ X)
    (hw0 : 0 ≤ w) (hwX : w ≤ Dg * ((c : ℝ) + 1) * X) (hDg : 0 ≤ Dg) (hC'Dg : Dg ≤ C')
    (hC'4 : 4 ≤ C') :
    (c : ℝ) ^ 2 * (q⁻¹) ^ 2 * (2 * w ^ (c - 1)) ≤ (C' * X * ((c : ℝ) + 1)) ^ (c + 1) := by
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · subst h0
    simp only [CharP.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_mul, zero_add, pow_one]
    nlinarith
  · obtain ⟨n, rfl⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    push_cast
    set uR : ℝ := (n : ℝ) + 1 + 1 with huR
    have hu0 : 0 ≤ uR := by positivity
    have hqX2 : (q⁻¹) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by positivity) hqX 2
    have hwX' : w ≤ Dg * uR * X := by
      rw [huR]; push_cast at hwX; linarith
    have h7 := mul_le_mul_of_nonneg_right hC'Dg (mul_nonneg hu0 hX)
    have h8 : Dg * uR * X ≤ C' * X * uR := by nlinarith
    have h3 : w ^ n ≤ (C' * X * uR) ^ n := pow_le_pow_left₀ hw0 (hwX'.trans h8) n
    have h4 : 2 * (((n : ℝ) + 1) ^ 2 * X ^ 2) ≤ (C' * X * uR) ^ 2 := by
      have e : (C' * X * uR) ^ 2 = C' ^ 2 * (uR ^ 2 * X ^ 2) := by ring
      rw [e]
      have h5 : ((n : ℝ) + 1) ^ 2 ≤ uR ^ 2 := by
        rw [huR]
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith
      have h6 : (2 : ℝ) ≤ C' ^ 2 := by nlinarith
      calc 2 * (((n : ℝ) + 1) ^ 2 * X ^ 2) ≤ C' ^ 2 * (((n : ℝ) + 1) ^ 2 * X ^ 2) :=
            mul_le_mul_of_nonneg_right h6 (by positivity)
        _ ≤ C' ^ 2 * (uR ^ 2 * X ^ 2) := by gcongr
    calc ((n : ℝ) + 1) ^ 2 * (q⁻¹) ^ 2 * (2 * w ^ n) ≤
          ((n : ℝ) + 1) ^ 2 * X ^ 2 * (2 * (C' * X * uR) ^ n) := by gcongr
      _ = 2 * (((n : ℝ) + 1) ^ 2 * X ^ 2) * (C' * X * uR) ^ n := by ring
      _ ≤ (C' * X * uR) ^ 2 * (C' * X * uR) ^ n := by gcongr
      _ = (C' * X * uR) ^ (n + 1 + 1) := by ring

/-- The Hilbert–Schmidt term of (5.103)–(5.104) for `U ≠ ∅`. -/
private lemma fa_sigma_ne {N : ℕ} (hN : 0 < N) (U : Finset (Fin N)) (F : Fin N → Fin N → ℝ)
    {w Cm X : ℝ} (hw0 : 0 ≤ w) (hCmX : 0 ≤ Cm * X)
    (hF : ∀ k l, F k l ≤ w ^ (2 * (U.card + 1)) +
      ((if k ∈ U then 1 else 0) + (if l ∈ U then 1 else 0)) * w ^ (2 * U.card))
    (hNX : (N : ℝ)⁻¹ ≤ (Cm * X) ^ 2) :
    Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∑ k, ∑ l, F k l) ≤
      w ^ (U.card + 1) + 2 * ((U.card : ℝ) + 1) * (Cm * X) * w ^ U.card := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.sqrt_le_left (by positivity)]
  set A := w ^ (2 * (U.card + 1)) with hA
  set B := w ^ (2 * U.card) with hB
  have hsum : (∑ k, ∑ l, F k l) ≤ ∑ k : Fin N, ∑ l : Fin N,
      (A + ((if k ∈ U then 1 else 0) + (if l ∈ U then 1 else 0)) * B) :=
    Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hF k l
  have hc : (∑ k : Fin N, (if k ∈ U then (1 : ℝ) else 0)) = U.card := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcount : (∑ k : Fin N, ∑ l : Fin N,
      (A + ((if k ∈ U then 1 else 0) + (if l ∈ U then 1 else 0)) * B)) =
      (N : ℝ) ^ 2 * A + 2 * N * U.card * B := by
    have e1 : ∀ k : Fin N, (∑ l : Fin N,
        (A + ((if k ∈ U then 1 else 0) + (if l ∈ U then 1 else 0)) * B)) =
        N * A + (N * (if k ∈ U then 1 else 0) + U.card) * B := by
      intro k
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_add_distrib, hc]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [e1]
    calc (∑ k : Fin N, ((N : ℝ) * A + ((N : ℝ) * (if k ∈ U then 1 else 0) + U.card) * B)) =
          ∑ k : Fin N, ((N : ℝ) * A + U.card * B) + N * B * ∑ k : Fin N,
            (if k ∈ U then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = (N : ℝ) ^ 2 * A + 2 * N * U.card * B := by
          rw [hc]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  rw [hcount] at hsum
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  calc ((N : ℝ) ^ 2)⁻¹ * (∑ k, ∑ l, F k l) ≤ ((N : ℝ) ^ 2)⁻¹ * ((N : ℝ) ^ 2 * A +
        2 * N * U.card * B) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = A + 2 * U.card * (N : ℝ)⁻¹ * B := by field_simp
    _ ≤ A + 2 * U.card * (Cm * X) ^ 2 * B := by gcongr
    _ ≤ (w ^ (U.card + 1) + 2 * ((U.card : ℝ) + 1) * (Cm * X) * w ^ U.card) ^ 2 := by
        have e1 : A = (w ^ (U.card + 1)) ^ 2 := by rw [hA]; ring
        have e2 : B = (w ^ U.card) ^ 2 := by rw [hB]; ring
        rw [e1, e2]
        have hU0 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
        have h5 : 2 * (U.card : ℝ) ≤ (2 * ((U.card : ℝ) + 1)) ^ 2 := by nlinarith
        have h6 : 0 ≤ w ^ (U.card + 1) * (2 * ((U.card : ℝ) + 1) * (Cm * X) * w ^ U.card) := by
          positivity
        nlinarith [mul_le_mul_of_nonneg_right h5
          (by positivity : (0 : ℝ) ≤ (Cm * X) ^ 2 * (w ^ U.card) ^ 2)]

/-- For `U = ∅` the coefficients are the entries of `G^{(Si)}` off the rows `Si`. -/
private lemma fa_sum_coef_empty_le {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ)
    (S : Finset (Fin N)) (i : Fin N) :
    (∑ k, ∑ l, if k = l then (0 : ℝ) else
      ‖(if k ∈ (∅ : Finset (Fin N)) ∧ l ∈ (∅ : Finset (Fin N)) then 0 else
        faCoef z S ∅ i k l H)‖ ^ 2) ≤
      ∑ k ∈ (insert i S)ᶜ, ∑ l, ‖resolventC (zeroRC (insert i S) H) z k l‖ ^ 2 := by
  set T := insert i S with hT
  have hterm : ∀ k l, (if k = l then (0 : ℝ) else
      ‖(if k ∈ (∅ : Finset (Fin N)) ∧ l ∈ (∅ : Finset (Fin N)) then 0 else
        faCoef z S ∅ i k l H)‖ ^ 2) ≤
      if k ∈ T then 0 else ‖resolventC (zeroRC T H) z k l‖ ^ 2 := by
    intro k l
    simp only [Finset.notMem_empty, and_false, ite_false]
    by_cases hkl : k = l
    · rw [ite_eq_left hkl]
      split_ifs <;> first | exact le_rfl | positivity
    · rw [ite_eq_right hkl]
      unfold faCoef
      by_cases hz0 : k = i ∨ l = i ∨ k ∈ S \ ∅ ∨ l ∈ S \ ∅
      · rw [ite_eq_left hz0, norm_zero, sq, zero_mul]
        split_ifs <;> first | exact le_rfl | positivity
      · rw [ite_eq_right hz0, Finset.empty_sdiff, gradedTerm_empty]
        have hkT : k ∉ T := by
          rw [hT, Finset.mem_insert]
          rintro (h | h)
          · exact hz0 (Or.inl h)
          · exact hz0 (Or.inr (Or.inr (Or.inl (by simpa using h))))
        have hlT : l ∉ T := by
          rw [hT, Finset.mem_insert]
          rintro (h | h)
          · exact hz0 (Or.inr (Or.inl h))
          · exact hz0 (Or.inr (Or.inr (Or.inr (by simpa using h))))
        have e : insert i S \ {k, l} = T := by
          rw [hT]
          refine Finset.sdiff_eq_self_of_disjoint ?_
          rw [Finset.disjoint_right]
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hkT
          · exact hlT
        rw [e, ite_eq_right hkT]
  calc _ ≤ ∑ k, ∑ l, (if k ∈ T then (0 : ℝ) else ‖resolventC (zeroRC T H) z k l‖ ^ 2) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hterm k l
    _ = ∑ k ∈ Tᶜ, ∑ l, ‖resolventC (zeroRC T H) z k l‖ ^ 2 := by
        rw [← Finset.sum_subset (Finset.subset_univ Tᶜ)]
        · refine Finset.sum_congr rfl fun k hk => ?_
          have hkT : k ∉ T := Finset.mem_compl.mp hk
          simp only [hkT, ite_false]
        · intro k _ hk
          have hkT : k ∈ T := by simpa using hk
          simp only [hkT, ite_true, Finset.sum_const_zero]

/-- Elementary inequalities for `C' = 4 (1 + C_m + C_σ + s) D_g`. -/
private lemma fa_aux_C {Dg Cm Cσ s u : ℝ} (hDg : 1 ≤ Dg) (hCm : 0 ≤ Cm) (hCσ : 0 ≤ Cσ)
    (hs : 0 ≤ s) (hu : 1 ≤ u) :
    Dg ≤ 4 * (1 + Cm + Cσ + s) * Dg ∧ 4 ≤ 4 * (1 + Cm + Cσ + s) * Dg ∧
    1 + Dg * u + 2 * u * Cm ≤ 4 * (1 + Cm + Cσ + s) * Dg * u ∧
    2 * (1 + s) ≤ 4 * (1 + Cm + Cσ + s) * Dg * u ∧ 1 + Cσ ≤ 4 * (1 + Cm + Cσ + s) * Dg := by
  have h1 : 1 ≤ 1 + Cm + Cσ + s := by linarith
  have hDu : 1 ≤ Dg * u := one_le_mul_of_one_le_of_one_le hDg hu
  have hA : Dg ≤ 4 * (1 + Cm + Cσ + s) * Dg := by nlinarith
  have hB : 4 ≤ 4 * (1 + Cm + Cσ + s) * Dg := by nlinarith
  have e : 4 * (1 + Cm + Cσ + s) * Dg * u = 4 * (Dg * u) + 4 * Cm * (Dg * u) +
      4 * Cσ * (Dg * u) + 4 * s * (Dg * u) := by ring
  have hu' : u ≤ Dg * u := by nlinarith
  refine ⟨hA, hB, ?_, ?_, ?_⟩
  · rw [e]
    have : 2 * u * Cm ≤ 4 * Cm * (Dg * u) := by nlinarith
    nlinarith [mul_nonneg hCσ (by linarith : (0 : ℝ) ≤ Dg * u),
      mul_nonneg hs (by linarith : (0 : ℝ) ≤ Dg * u)]
  · rw [e]
    have : 2 * s ≤ 4 * s * (Dg * u) := by nlinarith
    nlinarith [mul_nonneg hCσ (by linarith : (0 : ℝ) ≤ Dg * u),
      mul_nonneg hCm (by linarith : (0 : ℝ) ≤ Dg * u)]
  · nlinarith

/-- The bracket of (5.103)–(5.105) for `U ≠ ∅`. -/
private lemma fa_T2_ne {N : ℕ} (hN : 0 < N) (U : Finset (Fin N)) (B : Fin N → Fin N → ℂ)
    {w X q Dg Cm C' : ℝ} (hw0 : 0 ≤ w) (hX : 0 ≤ X) (hq0 : 0 < q) (hqX : q⁻¹ ≤ X)
    (hDg : 1 ≤ Dg) (hCm : 0 ≤ Cm) (hwX : w ≤ Dg * ((U.card : ℝ) + 1) * X) (hC'Dg : Dg ≤ C')
    (hK : 1 + Dg * ((U.card : ℝ) + 1) + 2 * ((U.card : ℝ) + 1) * Cm ≤ C' * ((U.card : ℝ) + 1))
    (hNX : (N : ℝ)⁻¹ ≤ (Cm * X) ^ 2)
    (hb : ∀ k l, k ≠ l → ¬ (k ∈ U ∧ l ∈ U) → ‖B k l‖ ≤ w ^ U.card ∧
      ‖B k l‖ ^ 2 ≤ w ^ (2 * (U.card + 1)) +
        ((if k ∈ U then 1 else 0) + (if l ∈ U then 1 else 0)) * w ^ (2 * U.card)) :
    (⨆ k, ⨆ l, if k = l then 0 else ‖(if k ∈ U ∧ l ∈ U then 0 else B k l)‖) / q +
      Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∑ k, ∑ l, if k = l then 0 else
        ‖(if k ∈ U ∧ l ∈ U then 0 else B k l)‖ ^ 2) ≤
      (C' * X * ((U.card : ℝ) + 1)) ^ (U.card + 1) := by
  set uR : ℝ := (U.card : ℝ) + 1 with huR
  have hu0 : 0 ≤ uR := by positivity
  have hβ : (⨆ k, ⨆ l, if k = l then (0 : ℝ) else ‖(if k ∈ U ∧ l ∈ U then 0 else B k l)‖) ≤
      w ^ U.card := by
    refine fa_iSup_le_of (pow_nonneg hw0 _) fun k =>
      fa_iSup_le_of (pow_nonneg hw0 _) fun l => ?_
    by_cases hkl : k = l
    · rw [ite_eq_left hkl]; exact pow_nonneg hw0 _
    · rw [ite_eq_right hkl]
      by_cases hU : k ∈ U ∧ l ∈ U
      · rw [ite_eq_left hU, norm_zero]; exact pow_nonneg hw0 _
      · rw [ite_eq_right hU]; exact (hb k l hkl hU).1
  have h1 : (⨆ k, ⨆ l, if k = l then (0 : ℝ) else ‖(if k ∈ U ∧ l ∈ U then 0 else B k l)‖) / q ≤
      w ^ U.card * X := by
    rw [div_le_iff₀ hq0]
    calc _ ≤ w ^ U.card := hβ
      _ = w ^ U.card * (q⁻¹ * q) := by rw [inv_mul_cancel₀ hq0.ne', mul_one]
      _ ≤ w ^ U.card * (X * q) := by gcongr
      _ = w ^ U.card * X * q := by ring
  have hF : ∀ k l, (if k = l then (0 : ℝ) else ‖(if k ∈ U ∧ l ∈ U then 0 else B k l)‖ ^ 2) ≤
      w ^ (2 * (U.card + 1)) +
        ((if k ∈ U then 1 else 0) + (if l ∈ U then 1 else 0)) * w ^ (2 * U.card) := by
    intro k l
    have h0 : 0 ≤ ((if k ∈ U then (1 : ℝ) else 0) + (if l ∈ U then 1 else 0)) := by
      split_ifs <;> norm_num
    have hR0 : 0 ≤ w ^ (2 * (U.card + 1)) + ((if k ∈ U then (1 : ℝ) else 0) +
        (if l ∈ U then 1 else 0)) * w ^ (2 * U.card) := by positivity
    by_cases hkl : k = l
    · rw [ite_eq_left hkl]; exact hR0
    · rw [ite_eq_right hkl]
      by_cases hU : k ∈ U ∧ l ∈ U
      · rw [ite_eq_left hU, norm_zero, sq, zero_mul]; exact hR0
      · rw [ite_eq_right hU]; exact (hb k l hkl hU).2
  have hσ := fa_sigma_ne hN U _ hw0 (by positivity) hF hNX
  have h5 : X + w + 2 * uR * Cm * X ≤ X * (1 + Dg * uR + 2 * uR * Cm) := by nlinarith
  calc _ ≤ w ^ U.card * X + (w ^ (U.card + 1) + 2 * uR * (Cm * X) * w ^ U.card) :=
        add_le_add h1 hσ
    _ = w ^ U.card * (X + w + 2 * uR * Cm * X) := by ring
    _ ≤ (Dg * uR * X) ^ U.card * (X * (1 + Dg * uR + 2 * uR * Cm)) :=
        mul_le_mul (pow_le_pow_left₀ hw0 hwX _) h5 (by positivity) (pow_nonneg (by positivity) _)
    _ = (Dg * uR * X) ^ U.card * X * (1 + Dg * uR + 2 * uR * Cm) := by ring
    _ ≤ (C' * X * uR) ^ (U.card + 1) :=
        fa_dom U.card hX hu0 (by linarith) hC'Dg (by positivity) hK

/-- The bracket of (A.2) for the diagonal terms. -/
private lemma fa_T3 {N : ℕ} (hN : 0 < N) (U : Finset (Fin N)) (A : Fin N → ℂ)
    {w X q Dg C' C0 : ℝ} (hw0 : 0 ≤ w) (hX : 0 ≤ X) (hq1 : 1 ≤ q) (hqX : q⁻¹ ≤ X)
    (hDg : 1 ≤ Dg) (hC0 : 0 ≤ C0) (hwX : w ≤ Dg * ((U.card : ℝ) + 1) * X) (hC'Dg : Dg ≤ C')
    (hK : 2 * (1 + Real.sqrt (1 + C0)) ≤ C' * ((U.card : ℝ) + 1))
    (hA : ∀ k, ‖A k‖ ≤ 2 * w ^ U.card) :
    (⨆ k, ‖A k‖) / q ^ 2 + Real.sqrt ((1 + C0) / N * (q⁻¹) ^ 2 * ∑ k, ‖A k‖ ^ 2) ≤
      (C' * X * ((U.card : ℝ) + 1)) ^ (U.card + 1) := by
  set uR : ℝ := (U.card : ℝ) + 1 with huR
  have hu0 : 0 ≤ uR := by positivity
  have hq0 : 0 < q := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq0 : 0 ≤ Real.sqrt (1 + C0) := Real.sqrt_nonneg _
  have hMa : (⨆ k, ‖A k‖) ≤ 2 * w ^ U.card := fa_iSup_le_of (by positivity) hA
  have hs : Real.sqrt ((1 + C0) / N * (q⁻¹) ^ 2 * ∑ k, ‖A k‖ ^ 2) ≤
      2 * Real.sqrt (1 + C0) * q⁻¹ * w ^ U.card := by
    rw [Real.sqrt_le_left (by positivity)]
    have hsum : (∑ k, ‖A k‖ ^ 2) ≤ N * (2 * w ^ U.card) ^ 2 := by
      calc _ ≤ ∑ _k : Fin N, (2 * w ^ U.card) ^ 2 :=
            Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hA k) 2
        _ = N * (2 * w ^ U.card) ^ 2 := by simp
    have e : (2 * Real.sqrt (1 + C0) * q⁻¹ * w ^ U.card) ^ 2 =
        (1 + C0) / N * (q⁻¹) ^ 2 * (N * (2 * w ^ U.card) ^ 2) := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by linarith)]
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have h1 : (⨆ k, ‖A k‖) / q ^ 2 ≤ 2 * w ^ U.card * q⁻¹ := by
    rw [div_le_iff₀ (by positivity)]
    have hq2 : q ≤ q ^ 2 := by nlinarith
    calc _ ≤ 2 * w ^ U.card := hMa
      _ = 2 * w ^ U.card * q⁻¹ * q := by field_simp
      _ ≤ 2 * w ^ U.card * q⁻¹ * q ^ 2 := by gcongr
  calc _ ≤ 2 * w ^ U.card * q⁻¹ + 2 * Real.sqrt (1 + C0) * q⁻¹ * w ^ U.card := add_le_add h1 hs
    _ = w ^ U.card * q⁻¹ * (2 * (1 + Real.sqrt (1 + C0))) := by ring
    _ ≤ (Dg * uR * X) ^ U.card * X * (2 * (1 + Real.sqrt (1 + C0))) := by
        have := pow_le_pow_left₀ hw0 hwX U.card
        gcongr
    _ ≤ (C' * X * uR) ^ (U.card + 1) :=
        fa_dom U.card hX hu0 (by linarith) hC'Dg (by positivity) hK

/-- The three brackets of `fa_moment_split` for the coefficients of (5.98) at a matrix with the
bounds that define `Ξ`, with `C' = 4 (1 + C_m + C_σ + (1 + C0)^{1/2}) D_g`. -/
private lemma fa_brackets (C0 : ℝ) (hC0 : 0 ≤ C0) : ∃ c1 > 0, ∃ Cg > 0, ∃ CH > 0,
    ∀ {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}, H.IsHermitian → ∀ {z : ℂ}, |z.re| ≤ 5 →
    0 < z.im → z.im ≤ 10 → ∀ (o d g X q Dg Cm Cσ : ℝ) (P : ℕ) (S U : Finset (Fin N))
    (i : Fin N),
    (∀ a b, a ≠ b → ‖resolventC H z a b‖ ≤ o) → (∀ a, ‖resolventC H z a a - msc z‖ ≤ d) →
    ‖stieltjesM H z - msc z‖ ≤ g → 0 < N →
    0 ≤ o → 0 ≤ d → 0 ≤ X → 1 ≤ q → 1 ≤ Dg → 0 ≤ Cm → 0 ≤ Cσ →
    ((P : ℝ) + 2) * (o + d) ≤ c1 → Cg * ((P : ℝ) + 1) * o ≤ 1 →
    Cg * o ≤ Dg * X → q⁻¹ ≤ X → (N : ℝ)⁻¹ ≤ (Cm * X) ^ 2 →
    ((msc z).im + g + CH * ((P : ℝ) + 1) * ((msc z).im + d + o) / (N * z.im)) / (N * z.im) ≤
      (Cσ * X) ^ 2 →
    i ∉ S → U ⊆ S → S.card ≤ P →
    (∀ k l, k ∈ U → l ∈ U →
      ‖faCoef z S U i k l H‖ ≤ 2 * (Cg * ((U.card : ℝ) + 1) * o) ^ (U.card - 1)) ∧
    (U.card : ℝ) ^ 2 * (q⁻¹) ^ 2 * (2 * (Cg * ((U.card : ℝ) + 1) * o) ^ (U.card - 1)) ≤
      (4 * (1 + Cm + Cσ + Real.sqrt (1 + C0)) * Dg * X * (U.card + 1)) ^ (U.card + 1) ∧
    (⨆ k, ⨆ l, if k = l then 0 else
        ‖(if k ∈ U ∧ l ∈ U then 0 else faCoef z S U i k l H)‖) / q +
      Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∑ k, ∑ l, if k = l then 0 else
        ‖(if k ∈ U ∧ l ∈ U then 0 else faCoef z S U i k l H)‖ ^ 2) ≤
      (4 * (1 + Cm + Cσ + Real.sqrt (1 + C0)) * Dg * X * (U.card + 1)) ^ (U.card + 1) ∧
    (⨆ k, ‖(if k ∈ U then 0 else faCoef z S U i k k H)‖) / q ^ 2 +
      Real.sqrt ((1 + C0) / N * (q⁻¹) ^ 2 *
        ∑ k, ‖(if k ∈ U then 0 else faCoef z S U i k k H)‖ ^ 2) ≤
      (4 * (1 + Cm + Cσ + Real.sqrt (1 + C0)) * Dg * X * (U.card + 1)) ^ (U.card + 1) := by
  obtain ⟨c1c, hc1c, Cg, hCg, hcoef⟩ := fa_coef_bounds
  obtain ⟨c1h, hc1h, CH, hCH, hhs⟩ := fa_hs_bound
  refine ⟨min c1c c1h, lt_min hc1c hc1h, Cg, hCg, CH, hCH, ?_⟩
  intro N H hH z hre hz hz10 o d g X q Dg Cm Cσ P S U i hoff hdiag hg hN ho hd hX hq1 hDg hCm hCσ
    hc1 hCgP hCgo hqX hNX hHS hiS hUS hSP
  set C' := 4 * (1 + Cm + Cσ + Real.sqrt (1 + C0)) * Dg with hC'
  set w := Cg * ((U.card : ℝ) + 1) * o with hwdef
  have hq0 : 0 < q := by linarith
  have hod : 0 ≤ o + d := by linarith
  have hSP' : (S.card : ℝ) ≤ P := by exact_mod_cast hSP
  have hUP : (U.card : ℝ) ≤ P := by
    have : U.card ≤ P := (Finset.card_le_card hUS).trans hSP
    exact_mod_cast this
  have hScard : ((S.card : ℝ) + 1) * (o + d) ≤ c1c := by
    have h1 : ((S.card : ℝ) + 1) * (o + d) ≤ ((P : ℝ) + 2) * (o + d) :=
      mul_le_mul_of_nonneg_right (by linarith) hod
    exact h1.trans (hc1.trans (min_le_left _ _))
  have hw1 : w ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left (show (U.card : ℝ) + 1 ≤ P + 1 by linarith) hCg.le
    have h2 := mul_le_mul_of_nonneg_right h1 ho
    exact h2.trans hCgP
  obtain ⟨b1, b2, b3⟩ := hcoef hH hre hz hz10 o d w S U i ho hd hoff hdiag hScard hiS hUS le_rfl
    hw1
  have hU0 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
  have hw0 : 0 ≤ w := by positivity
  have hwX : w ≤ Dg * ((U.card : ℝ) + 1) * X := by
    have e : w = ((U.card : ℝ) + 1) * (Cg * o) := by rw [hwdef]; ring
    rw [e]
    calc ((U.card : ℝ) + 1) * (Cg * o) ≤ ((U.card : ℝ) + 1) * (Dg * X) :=
          mul_le_mul_of_nonneg_left hCgo (by linarith)
      _ = Dg * ((U.card : ℝ) + 1) * X := by ring
  have hsq0 : 0 ≤ Real.sqrt (1 + C0) := Real.sqrt_nonneg _
  obtain ⟨hC'Dg, hC'4, hK2, hK3, hK1⟩ := fa_aux_C (u := (U.card : ℝ) + 1) hDg hCm hCσ hsq0
    (by linarith)
  refine ⟨b1, fa_T1 U.card hq0 hqX hX hw0 hwX (by linarith) hC'Dg hC'4, ?_, ?_⟩
  · rcases U.eq_empty_or_nonempty with hUe | hUne
    · -- `U = ∅`: Ward identity
      subst hUe
      have hσ : Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∑ k, ∑ l, if k = l then 0 else
          ‖(if k ∈ (∅ : Finset (Fin N)) ∧ l ∈ (∅ : Finset (Fin N)) then 0 else
            faCoef z S ∅ i k l H)‖ ^ 2) ≤ Cσ * X := by
        rw [Real.sqrt_le_left (by positivity)]
        refine le_trans ?_ hHS
        have hTc : ((insert i S).card : ℝ) ≤ P + 1 := by
          have h1 : (insert i S).card ≤ S.card + 1 := Finset.card_insert_le _ _
          have h2 : ((insert i S).card : ℝ) ≤ S.card + 1 := by exact_mod_cast h1
          linarith
        have hT1 : (((insert i S).card : ℝ) + 1) * (o + d) ≤ c1h :=
          (mul_le_mul_of_nonneg_right (by linarith) hod).trans (hc1.trans (min_le_right _ _))
        have hW := hhs hH hre hz hz10 o d g (insert i S) ho hd hoff hdiag hg hT1
        have hsum := (fa_sum_coef_empty_le H z S i).trans hW
        have hNr : (0 : ℝ) < N := by exact_mod_cast hN
        have hNN : ((N : ℝ) ^ 2)⁻¹ * (N / z.im) = 1 / (N * z.im) := by
          field_simp
        have him := im_msc_pos hz
        calc ((N : ℝ) ^ 2)⁻¹ * (∑ k, ∑ l, if k = l then (0 : ℝ) else
              ‖(if k ∈ (∅ : Finset (Fin N)) ∧ l ∈ (∅ : Finset (Fin N)) then 0 else
                faCoef z S ∅ i k l H)‖ ^ 2)
            ≤ ((N : ℝ) ^ 2)⁻¹ * (N / z.im * ((msc z).im + g + CH * (insert i S).card *
                ((msc z).im + d + o) / (N * z.im))) :=
              mul_le_mul_of_nonneg_left hsum (by positivity)
          _ = ((msc z).im + g + CH * (insert i S).card * ((msc z).im + d + o) / (N * z.im)) /
                (N * z.im) := by rw [← mul_assoc, hNN]; ring
          _ ≤ ((msc z).im + g + CH * ((P : ℝ) + 1) * ((msc z).im + d + o) / (N * z.im)) /
                (N * z.im) := by gcongr
      have hβ : (⨆ k, ⨆ l, if k = l then (0 : ℝ) else
          ‖(if k ∈ (∅ : Finset (Fin N)) ∧ l ∈ (∅ : Finset (Fin N)) then 0 else
            faCoef z S ∅ i k l H)‖) ≤ 1 := by
        refine fa_iSup_le_of zero_le_one fun k => fa_iSup_le_of zero_le_one fun l => ?_
        by_cases hkl : k = l
        · rw [ite_eq_left hkl]; exact zero_le_one
        · rw [ite_eq_right hkl]
          simp only [Finset.notMem_empty, and_false, ite_false]
          have := (b2 k l hkl (by simp)).1
          simpa using this
      have h1 : (⨆ k, ⨆ l, if k = l then (0 : ℝ) else
          ‖(if k ∈ (∅ : Finset (Fin N)) ∧ l ∈ (∅ : Finset (Fin N)) then 0 else
            faCoef z S ∅ i k l H)‖) / q ≤ X := by
        rw [div_le_iff₀ hq0]
        calc _ ≤ (1 : ℝ) := hβ
          _ = q⁻¹ * q := (inv_mul_cancel₀ hq0.ne').symm
          _ ≤ X * q := mul_le_mul_of_nonneg_right hqX hq0.le
      have e1 : ((Finset.card (∅ : Finset (Fin N)) : ℝ) + 1) = 1 := by simp
      rw [e1, Finset.card_empty, zero_add, pow_one, mul_one]
      calc _ ≤ X + Cσ * X := add_le_add h1 hσ
        _ = (1 + Cσ) * X := by ring
        _ ≤ C' * X := mul_le_mul_of_nonneg_right hK1 hX
    · exact fa_T2_ne hN U _ hw0 hX hq0 hqX hDg hCm hwX hC'Dg hK2 hNX
        (fun k l hkl hU => b2 k l hkl hU)
  · refine fa_T3 hN U _ hw0 hX hq1 hqX hDg hC0 hwX hC'Dg hK3 fun k => ?_
    by_cases hk : k ∈ U
    · rw [ite_eq_left hk, norm_zero]; positivity
    · rw [ite_eq_right hk]; exact b3 k hk

end Brackets


/-! ### Assumption (5.6) of Theorem 5.6 ((5.96) of [15] at `r = p`) -/

section HypMoment

private lemma fa_pow_combine {T1 T2 T3 V a b : ℝ} (n : ℕ) (hn : 1 ≤ n) (h1 : 0 ≤ T1)
    (h2 : 0 ≤ T2) (h3 : 0 ≤ T3) (hb : 0 ≤ b) (hT1 : T1 ≤ V) (hT2 : a ^ 2 * T2 ≤ V)
    (hT3 : b * T3 ≤ V) :
    3 ^ (2 * n) * (T1 ^ (2 * n) + a ^ (4 * n) * T2 ^ (2 * n) + b ^ (2 * n) * T3 ^ (2 * n)) ≤
      (9 * V) ^ (2 * n) := by
  have hV : 0 ≤ V := h1.trans hT1
  have e2 : a ^ (4 * n) * T2 ^ (2 * n) = (a ^ 2 * T2) ^ (2 * n) := by
    rw [mul_pow, ← pow_mul]; ring_nf
  have e3 : b ^ (2 * n) * T3 ^ (2 * n) = (b * T3) ^ (2 * n) := by rw [mul_pow]
  rw [e2, e3]
  have k1 : T1 ^ (2 * n) ≤ V ^ (2 * n) := pow_le_pow_left₀ h1 hT1 _
  have k2 : (a ^ 2 * T2) ^ (2 * n) ≤ V ^ (2 * n) := pow_le_pow_left₀ (by positivity) hT2 _
  have k3 : (b * T3) ^ (2 * n) ≤ V ^ (2 * n) := pow_le_pow_left₀ (by positivity) hT3 _
  have k4 : (3 : ℝ) ^ (2 * n) * 3 ≤ 9 ^ (2 * n) := by
    have : (9 : ℝ) ^ (2 * n) = 3 ^ (2 * n) * 3 ^ (2 * n) := by
      rw [← mul_pow]; norm_num
    rw [this]
    have : (3 : ℝ) ≤ 3 ^ (2 * n) := by
      calc (3 : ℝ) = 3 ^ 1 := (pow_one 3).symm
        _ ≤ 3 ^ (2 * n) := pow_le_pow_right₀ (by norm_num) (by omega)
    gcongr
  calc 3 ^ (2 * n) * (T1 ^ (2 * n) + (a ^ 2 * T2) ^ (2 * n) + (b * T3) ^ (2 * n))
      ≤ 3 ^ (2 * n) * (3 * V ^ (2 * n)) := by gcongr; linarith
    _ = (3 ^ (2 * n) * 3) * V ^ (2 * n) := by ring
    _ ≤ 9 ^ (2 * n) * V ^ (2 * n) := by gcongr
    _ = (9 * V) ^ (2 * n) := by rw [mul_pow]

/-- (5.96) of [15] at `r = p`, i.e. the hypothesis (5.6) of Theorem 5.6, for `Z_i^{[V]}` on an
event `Ξ` where `Λ_o ≤ o`, `Λ_d ≤ d` and `Λ ≤ g`. -/
private lemma fa_hyp_moment (C0 : ℝ) (hC0 : 0 ≤ C0) : ∃ c1 > 0, ∃ Cg > 0, ∃ CH > 0, ∃ C1 > 0,
    ∃ C2 > 0, ∀ {N : ℕ} {L : EntryLaws N} {q : ℝ} {z : ℂ} (Ξ : Set (Entries N))
    (o d g X Y Dg Cm Cσ : ℝ) (p' : ℕ),
    L.IsGenWigner C0 → L.BoundedSupportAS q → 1 ≤ q → 2 ≤ N →
    |z.re| ≤ 5 → 0 < z.im → z.im ≤ 10 → (∀ i, MeasurableSet (rowSat {i} Ξ)) →
    (∀ ω ∈ Ξ, (∀ a b, a ≠ b → ‖resolventC (symOfEntries ω) z a b‖ ≤ o) ∧
      (∀ a, ‖resolventC (symOfEntries ω) z a a - msc z‖ ≤ d) ∧
      ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ g) →
    0 ≤ o → 0 ≤ d → 0 ≤ X → 1 ≤ Dg → 0 ≤ Cm → 0 ≤ Cσ → 1 ≤ Y → 1 ≤ p' →
    (((2 * p' : ℕ) : ℝ) + 2) * (o + d) ≤ c1 → Cg * (((2 * p' : ℕ) : ℝ) + 1) * o ≤ 1 →
    Cg * o ≤ Dg * X → q⁻¹ ≤ X → (N : ℝ)⁻¹ ≤ (Cm * X) ^ 2 →
    ((msc z).im + g + CH * (((2 * p' : ℕ) : ℝ) + 1) * ((msc z).im + d + o) / (N * z.im)) /
      (N * z.im) ≤ (Cσ * X) ^ 2 →
    (C2 * p') ^ 2 ≤ Y → C1 * p' ≤ Y →
    ∀ S U i, U ⊆ S → i ∉ S → S.card ≤ 2 * p' →
      ∫⁻ ω in Ξ, ‖gradedTerm (fun V => faZ z V i) S U ω‖ₑ ^ (2 * p') ∂L.law ≤
        ENNReal.ofReal ((Y * (36 * (1 + Cm + Cσ + Real.sqrt (1 + C0)) * Dg * X *
          (U.card + 1)) ^ (U.card + 1)) ^ (2 * p')) := by
  obtain ⟨c1, hc1, Cg, hCg, CH, hCH, hbr⟩ := fa_brackets C0 hC0
  obtain ⟨C1, hC1, C2, hC2, hms⟩ := fa_moment_split C0 hC0
  refine ⟨c1, hc1, Cg, hCg, CH, hCH, C1, hC1, C2, hC2, ?_⟩
  intro N L q z Ξ o d g X Y Dg Cm Cσ p' hL hq hq1 hN hre hz hz10 hsat hΞ ho hd hX hDg hCm hCσ
    hY hp' hc1' hCgP hCgo hqX hNX hHS hC2Y hC1Y S U i hUS hiS hS
  have hP := isProbabilityMeasure_law hL.isProb
  have hNpos : 0 < N := by omega
  have hq0 : 0 < q := by linarith
  set C' := 4 * (1 + Cm + Cσ + Real.sqrt (1 + C0)) * Dg with hC'
  set E := (C' * X * ((U.card : ℝ) + 1)) ^ (U.card + 1) with hE
  set V := Y * E with hV
  have hE0 : 0 ≤ E := by
    have : 0 ≤ C' := by rw [hC']; positivity
    positivity
  have hEV : E ≤ V := by rw [hV]; nlinarith
  have hiU : i ∉ U := fun h => hiS (hUS h)
  -- the coefficients at a point of `Ξ`
  have hcond : ∀ ω ∈ rowSat {i} Ξ, ∫ ω', ‖gradedTerm (fun V => faZ z V i) S U
      (rowsMix {i} ω ω')‖ ^ (2 * p') ∂L.law ≤ (9 * V) ^ (2 * p') := by
    intro ω hω
    obtain ⟨ω₀, hω₀, heq⟩ := hω
    have hB : ∀ k l, faCoef z S U i k l (symOfEntries ω) =
        faCoef z S U i k l (symOfEntries ω₀) := by
      intro k l
      have h1 := fa_coef_rowIndep (S := S) hiU z k l ω
      have h2 := fa_coef_rowIndep (S := S) hiU z k l ω₀
      simp only at h1 h2
      rw [← h1, ← heq, h2]
    set B : Fin N → Fin N → ℂ := fun k l => faCoef z S U i k l (symOfEntries ω₀) with hBdef
    have hF : ∀ ω', gradedTerm (fun V => faZ z V i) S U (rowsMix {i} ω ω') = ∑ k, ∑ l,
        (((symOfEntries ω' i k * symOfEntries ω' i l : ℝ) : ℂ) -
          if k = l then ((N : ℝ)⁻¹ : ℂ) else 0) * B k l := by
      intro ω'
      rw [fa_gradedTerm_apply, fa_graded_rowsMix hiS hUS]
      simp only [hB, hBdef]
    simp only [hF]
    obtain ⟨hoff, hdiag, hg⟩ := hΞ ω₀ hω₀
    obtain ⟨b1, hT1, hT2, hT3⟩ := hbr (symOfEntries_isHermitian ω₀) hre hz hz10 o d g X q Dg
      Cm Cσ (2 * p') S U i hoff hdiag hg hNpos ho hd hX hq1 hDg hCm hCσ hc1' hCgP hCgo hqX hNX
      hHS hiS hUS hS
    have hm := hms hL hq hq1 hN i U B (fun k l => if k ∈ U ∧ l ∈ U then 0 else B k l)
      (fun k => if k ∈ U then 0 else B k k)
      (2 * (Cg * ((U.card : ℝ) + 1) * o) ^ (U.card - 1))
      (fun k => by simp [hBdef, faCoef]) (fun k => by simp [hBdef, faCoef]) b1
      (fun _ _ => rfl) (fun _ => rfl) p' hp'
    refine hm.trans ?_
    have hT1' : 0 ≤ (U.card : ℝ) ^ 2 * (q⁻¹) ^ 2 *
        (2 * (Cg * ((U.card : ℝ) + 1) * o) ^ (U.card - 1)) := by positivity
    have hT2' : 0 ≤ (⨆ k, ⨆ l, if k = l then (0 : ℝ) else
        ‖(if k ∈ U ∧ l ∈ U then 0 else B k l)‖) / q +
        Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∑ k, ∑ l, if k = l then 0 else
          ‖(if k ∈ U ∧ l ∈ U then 0 else B k l)‖ ^ 2) := by
      have : 0 ≤ (⨆ k, ⨆ l, if k = l then (0 : ℝ) else
          ‖(if k ∈ U ∧ l ∈ U then 0 else B k l)‖) :=
        Real.iSup_nonneg fun k => Real.iSup_nonneg fun l => by split_ifs <;> positivity
      positivity
    have hT3' : 0 ≤ (⨆ k, ‖(if k ∈ U then 0 else B k k)‖) / q ^ 2 +
        Real.sqrt ((1 + C0) / N * (q⁻¹) ^ 2 * ∑ k, ‖(if k ∈ U then 0 else B k k)‖ ^ 2) := by
      have : 0 ≤ (⨆ k, ‖(if k ∈ U then 0 else B k k)‖) := Real.iSup_nonneg fun k => norm_nonneg _
      positivity
    refine fa_pow_combine p' hp' hT1' hT2' hT3' (by positivity) (hT1.trans hEV) ?_ ?_
    · exact (mul_le_mul_of_nonneg_left hT2 (by positivity)).trans
        (by rw [hV]; exact mul_le_mul_of_nonneg_right hC2Y hE0)
    · exact (mul_le_mul_of_nonneg_left hT3 (by positivity)).trans
        (by rw [hV]; exact mul_le_mul_of_nonneg_right hC1Y hE0)
  -- the almost sure bound
  have hMb : ∀ᵐ ω ∂L.law, ‖gradedTerm (fun V => faZ z V i) S U ω‖ ≤
      2 ^ U.card * ((N : ℝ) ^ 2 * (((q⁻¹) ^ 2 + (N : ℝ)⁻¹) * (1 / z.im))) := by
    filter_upwards [fa_ae_entries hL.isProb hq] with ω hω
    exact fa_norm_graded_le S U i ω fun V => fa_norm_faZ_le hz V i hω
  have hV0 : 0 ≤ V := hE0.trans hEV
  refine (fa_lintegral_sat_le hL.isProb i (hsat i) (fa_continuous_graded hz.ne' S U i).measurable
    hMb (2 * p') (by positivity) hcond).trans (ENNReal.ofReal_le_ofReal ?_)
  refine pow_le_pow_left₀ (by positivity) ?_ _
  -- `9 V ≤ Y (9 C' X u)^u`
  have e : 36 * (1 + Cm + Cσ + Real.sqrt (1 + C0)) * Dg * X * ((U.card : ℝ) + 1) =
      9 * (C' * X * ((U.card : ℝ) + 1)) := by rw [hC']; ring
  rw [e, mul_pow, hV, hE]
  have h9 : (9 : ℝ) ≤ 9 ^ (U.card + 1) := by
    calc (9 : ℝ) = 9 ^ 1 := (pow_one 9).symm
      _ ≤ 9 ^ (U.card + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hY0 : 0 ≤ Y := by linarith
  calc 9 * (Y * (C' * X * ((U.card : ℝ) + 1)) ^ (U.card + 1)) =
      Y * (9 * (C' * X * ((U.card : ℝ) + 1)) ^ (U.card + 1)) := by ring
    _ ≤ Y * (9 ^ (U.card + 1) * (C' * X * ((U.card : ℝ) + 1)) ^ (U.card + 1)) := by
        gcongr
    _ = Y * (9 ^ (U.card + 1) * (C' * X * ((U.card : ℝ) + 1)) ^ (U.card + 1)) := rfl

end HypMoment

/-! ### Arithmetic of `φ` -/

section PhiArith

private lemma fa_rpow_pos {N : ℕ} (hN : 3 ≤ N) (a : ℝ) : 0 < phi N ^ a :=
  Real.rpow_pos_of_pos (sc_phi_pos hN) a

private lemma fa_rpow_add {N : ℕ} (hN : 3 ≤ N) (a b : ℝ) :
    phi N ^ (a + b) = phi N ^ a * phi N ^ b :=
  Real.rpow_add (sc_phi_pos hN) a b

private lemma fa_rpow_natMul {N : ℕ} (hN : 3 ≤ N) (a : ℝ) (n : ℕ) :
    phi N ^ ((n : ℝ) * a) = (phi N ^ a) ^ n := by
  rw [mul_comm, Real.rpow_mul (sc_phi_pos hN).le, Real.rpow_natCast]

/-- `φ^a` outgrows every polynomial in `log N`. -/
private lemma fa_eventually_phi {a : ℝ} (ha : 0 < a) (B : ℝ) (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, 3 ≤ N ∧ B * (Real.log N + 1) ^ k ≤ phi N ^ a := by
  have hloglog : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  set L0 := Real.log (|B| * 2 ^ k + 1) with hL0
  filter_upwards [eventually_ge_atTop 3,
    hloglog.eventually_ge_atTop (max 1 ((|L0| + k) / a))] with N hN hu
  refine ⟨hN, ?_⟩
  set u := Real.log (Real.log N) with hu_def
  have hN1 : (1 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlogpos : 0 < Real.log N := Real.log_pos hN1
  have hlog : Real.log N = Real.exp u := (Real.exp_log hlogpos).symm
  have hu1 : 1 ≤ u := le_trans (le_max_left _ _) hu
  have hua : |L0| + k ≤ u * a := by
    have := le_trans (le_max_right _ _) hu
    rwa [div_le_iff₀ ha] at this
  have hlog1 : 1 ≤ Real.log N := by
    rw [hlog]
    exact Real.one_le_exp (by linarith)
  have hexpL : Real.exp L0 = |B| * 2 ^ k + 1 := Real.exp_log (by positivity)
  rw [phi_eq_exp hN, ← Real.exp_mul]
  calc B * (Real.log N + 1) ^ k ≤ |B| * (2 * Real.log N) ^ k := by
        have h1 : (Real.log N + 1) ^ k ≤ (2 * Real.log N) ^ k :=
          pow_le_pow_left₀ (by linarith) (by linarith) k
        calc B * (Real.log N + 1) ^ k ≤ |B| * (Real.log N + 1) ^ k :=
              mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)
          _ ≤ |B| * (2 * Real.log N) ^ k := mul_le_mul_of_nonneg_left h1 (abs_nonneg B)
    _ = |B| * 2 ^ k * Real.exp (k * u) := by
        rw [mul_pow, hlog, ← Real.exp_nat_mul]; ring
    _ ≤ (|B| * 2 ^ k + 1) * Real.exp (k * u) := by
        gcongr; linarith
    _ = Real.exp (L0 + k * u) := by rw [Real.exp_add, hexpL]
    _ ≤ Real.exp (u ^ 2 * a) := by
        apply Real.exp_le_exp.mpr
        have h1 : u ^ 2 * a = u * (u * a) := by ring
        rw [h1]
        have h2 : u * (|L0| + k) ≤ u * (u * a) := mul_le_mul_of_nonneg_left hua (by linarith)
        have h3 : L0 ≤ |L0| := le_abs_self L0
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith [abs_nonneg L0]

private lemma fa_eventually_log (B : ℝ) : ∀ᶠ N : ℕ in atTop, B ≤ Real.log N :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop B

private lemma fa_small {N : ℕ} (hN : 3 ≤ N) {C a b : ℝ} (hC : 0 ≤ C) (hab : a ≤ b - 1)
    (hφ : 16 * C ≤ phi N) : C * phi N ^ a ≤ phi N ^ b / 16 := by
  have h1 : phi N ^ a ≤ phi N ^ (b - 1) := sc_rpow_mono hN hab
  have h2 : phi N ^ (b - 1) = phi N ^ b / phi N := by
    rw [Real.rpow_sub (sc_phi_pos hN), Real.rpow_one]
  have hφ0 := sc_phi_pos hN
  have hb0 := fa_rpow_pos hN b
  calc C * phi N ^ a ≤ C * (phi N ^ b / phi N) := by rw [← h2]; gcongr
    _ ≤ phi N ^ b / 16 := by
        rw [mul_div_assoc', div_le_div_iff₀ hφ0 (by norm_num)]
        nlinarith

private lemma fa_inv_rpow_le {N : ℕ} (hN : 3 ≤ N) {x K r : ℝ} (hx : phi N ^ K ≤ x)
    (hr : 0 ≤ r) : (x ^ r)⁻¹ ≤ phi N ^ (-(K * r)) := by
  have hK0 := fa_rpow_pos hN K
  have hx0 : 0 < x := lt_of_lt_of_le hK0 hx
  have h1 : (phi N ^ K) ^ r ≤ x ^ r := Real.rpow_le_rpow hK0.le hx hr
  rw [← Real.rpow_mul (sc_phi_pos hN).le] at h1
  rw [Real.rpow_neg (sc_phi_pos hN).le]
  exact inv_anti₀ (fa_rpow_pos hN _) h1

private lemma fa_inv_le_rpow {N : ℕ} (hN : 3 ≤ N) {x K : ℝ} (hx : phi N ^ K ≤ x) :
    x⁻¹ ≤ phi N ^ (-K) := by
  have h := fa_inv_rpow_le hN hx zero_le_one
  rwa [Real.rpow_one, mul_one] at h

private lemma fa_inv_sqrt_le {N : ℕ} (hN : 3 ≤ N) {x K : ℝ} (hx : phi N ^ K ≤ x) :
    (Real.sqrt x)⁻¹ ≤ phi N ^ (-(K / 2)) := by
  have hx0 : 0 ≤ x := (fa_rpow_pos hN K).le.trans hx
  have h := fa_inv_rpow_le hN hx (r := 1 / 2) (by norm_num)
  rw [← Real.sqrt_eq_rpow] at h
  convert h using 2
  ring

/-- `|m_sc| ≥ 1/16` on `|E| ≤ 5`, `0 < η ≤ 10`. -/
private lemma fa_msc_lower {z : ℂ} (hre : |z.re| ≤ 5) (him : 0 < z.im) (hle : z.im ≤ 10) :
    1 / 16 ≤ ‖msc z‖ := by
  obtain ⟨h1, -⟩ := norm_msc_eq_inv_and_lt_one him
  have hz : ‖z‖ ≤ 15 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos him] at this
    linarith
  have hm1 := (norm_msc_eq_inv_and_lt_one him).2
  have hsum : ‖msc z + z‖ ≤ 16 := (norm_add_le _ _).trans (by linarith)
  have hpos : 0 < ‖msc z + z‖ := by
    have hm0 : 0 < ‖msc z‖ := norm_pos_iff.mpr fun h => by
      have := im_msc_pos him
      rw [h] at this
      simp at this
    rw [h1] at hm0
    exact inv_pos.mp hm0
  rw [h1, one_div]
  exact inv_anti₀ hpos hsum

/-- `Im m_sc ≥ η/256` on `|E| ≤ 5`, `0 < η ≤ 10` (from `Im m_sc = (η + Im m_sc)|m_sc|²`). -/
private lemma fa_im_msc_ge {z : ℂ} (hre : |z.re| ≤ 5) (him : 0 < z.im) (hle : z.im ≤ 10) :
    z.im / 256 ≤ (msc z).im := by
  have hm := msc_add_inv_eq_zero him
  have hl := fa_msc_lower hre him hle
  have hpos := im_msc_pos him
  set m := msc z with hmdef
  have hw : z + m ≠ 0 := by
    intro h
    rw [h, _root_.inv_zero, add_zero] at hm
    rw [hm] at hpos
    simp at hpos
  have hm' : m = -(z + m)⁻¹ := by linear_combination hm
  have hnorm : ‖m‖ = ‖z + m‖⁻¹ := by
    conv_lhs => rw [hm']
    rw [norm_neg, norm_inv]
  have hns : Complex.normSq (z + m) = ‖z + m‖ ^ 2 := Complex.normSq_eq_norm_sq _
  have hwpos : 0 < ‖z + m‖ := norm_pos_iff.mpr hw
  have him' : m.im = (z.im + m.im) * ‖m‖ ^ 2 := by
    have h1 : m.im = (z + m).im / Complex.normSq (z + m) := by
      conv_lhs => rw [hm']
      rw [Complex.neg_im, Complex.inv_im]
      ring
    calc m.im = (z + m).im / Complex.normSq (z + m) := h1
      _ = (z.im + m.im) * ‖m‖ ^ 2 := by
          rw [hns, hnorm, Complex.add_im, inv_pow, div_eq_mul_inv]
  have h2 : (1 / 16 : ℝ) ^ 2 ≤ ‖m‖ ^ 2 := pow_le_pow_left₀ (by norm_num) hl 2
  rw [him']
  nlinarith

end PhiArith

/-! ### The event `Ω_s(z)` by continuity in `η` -/

section Chain

variable {N : ℕ}

/-- `max_i |G_ii - m|`. -/
private def faMdev (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : ℝ :=
  ⨆ i, ‖resolventC H z i i - stieltjesM H z‖

private lemma fa_stieltjesM_eq (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    stieltjesM H z = (N : ℂ)⁻¹ * ∑ j, resolventC H z j j := by
  simp [stieltjesM, Matrix.trace]

private lemma fa_norm_stieltjesM_sub_le {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    ‖stieltjesM H z - stieltjesM H w‖ ≤ ‖z - w‖ / (z.im * w.im) := by
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0
    have e : ∀ x : ℂ, stieltjesM H x = 0 := fun x => by simp [stieltjesM]
    rw [e, e, sub_zero, norm_zero]
    positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [fa_stieltjesM_eq, fa_stieltjesM_eq, ← mul_sub, ← Finset.sum_sub_distrib, norm_mul,
    norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ j, (resolventC H z j j - resolventC H w j j)‖
      ≤ (N : ℝ)⁻¹ * ∑ _j : Fin N, ‖z - w‖ / (z.im * w.im) := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
          norm_resolventC_apply_sub_le hH hz hw j j)
    _ = ‖z - w‖ / (z.im * w.im) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ hNr.ne', one_mul]

private lemma fa_le_mdev (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (i : Fin N) :
    ‖resolventC H z i i - stieltjesM H z‖ ≤ faMdev H z :=
  le_ciSup (f := fun i => ‖resolventC H z i i - stieltjesM H z‖) (Set.finite_range _).bddAbove i

private lemma fa_mdev_le (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    faMdev H z ≤ lamD H z + lamAvg H z := by
  refine Real.iSup_le (fun i => ?_) (by
    have h1 : 0 ≤ lamD H z := Real.iSup_nonneg fun _ => norm_nonneg _
    have h2 : 0 ≤ lamAvg H z := norm_nonneg _
    linarith)
  have h1 : ‖resolventC H z i i - msc z‖ ≤ lamD H z :=
    le_ciSup (f := fun i => ‖resolventC H z i i - msc z‖) (Set.finite_range _).bddAbove i
  calc ‖resolventC H z i i - stieltjesM H z‖
      ≤ ‖resolventC H z i i - msc z‖ + ‖stieltjesM H z - msc z‖ := by
        have := norm_sub_le (resolventC H z i i - msc z) (stieltjesM H z - msc z)
        simpa using this
    _ ≤ lamD H z + lamAvg H z := add_le_add h1 le_rfl

private lemma fa_lamD_le (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    lamD H z ≤ faMdev H z + lamAvg H z := by
  refine Real.iSup_le (fun i => ?_) (by
    rcases isEmpty_or_nonempty (Fin N) with h | ⟨⟨i⟩⟩
    · have : faMdev H z = 0 := by simp [faMdev]
      rw [this]
      have h2 : 0 ≤ lamAvg H z := norm_nonneg _
      linarith
    · have h1 := (norm_nonneg _).trans (fa_le_mdev H z i)
      have h2 : 0 ≤ lamAvg H z := norm_nonneg _
      linarith)
  calc ‖resolventC H z i i - msc z‖
      ≤ ‖resolventC H z i i - stieltjesM H z‖ + ‖stieltjesM H z - msc z‖ := by
        have := norm_add_le (resolventC H z i i - stieltjesM H z) (stieltjesM H z - msc z)
        simpa using this
    _ ≤ faMdev H z + lamAvg H z := add_le_add (fa_le_mdev H z i) le_rfl

private lemma fa_mdev_lip {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    faMdev H w ≤ faMdev H z + 2 * (‖z - w‖ / (z.im * w.im)) := by
  have hb : 0 ≤ ‖z - w‖ / (z.im * w.im) := by positivity
  refine Real.iSup_le (fun i => ?_) (by
    rcases isEmpty_or_nonempty (Fin N) with h | ⟨⟨i⟩⟩
    · have : faMdev H z = 0 := by simp [faMdev]
      rw [this]; linarith
    · have := (norm_nonneg _).trans (fa_le_mdev H z i)
      linarith)
  have h1 := norm_resolventC_apply_sub_le hH hz hw i i
  have h2 := fa_norm_stieltjesM_sub_le hH hz hw
  calc ‖resolventC H w i i - stieltjesM H w‖
      ≤ ‖resolventC H z i i - stieltjesM H z‖ + ‖resolventC H z i i - resolventC H w i i‖ +
          ‖stieltjesM H z - stieltjesM H w‖ := by
        have e : resolventC H w i i - stieltjesM H w = (resolventC H z i i - stieltjesM H z) -
            (resolventC H z i i - resolventC H w i i) + (stieltjesM H z - stieltjesM H w) := by
          ring
        rw [e]
        refine (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ faMdev H z + 2 * (‖z - w‖ / (z.im * w.im)) := by
        linarith [fa_le_mdev H z i]

/-- The continuity argument for `Ω_s(z) = {Λ_d + Λ_o ≤ s⁻¹}` along a vertical chain of
points `w_0, …, w_B = z` (as in the proof of Lemma 3.18 of [15]). -/
private lemma fa_chain_det {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    (w : ℕ → ℂ) (B : ℕ) {η δ s ε ε0 ε1 : ℝ} (hη : 0 < η)
    (him : ∀ b ≤ B, η ≤ (w b).im) (hstep : ∀ b < B, ‖w b - w (b + 1)‖ ≤ δ)
    (hweak : ∀ b ≤ B, lamO H (w b) ≤ ε ∧ lamAvg H (w b) ≤ ε)
    (hinit : lamD H (w 0) ≤ ε0)
    (hdiag : ∀ b ≤ B, lamD H (w b) + lamO H (w b) ≤ s⁻¹ → faMdev H (w b) ≤ ε1)
    (h1 : ε0 + ε ≤ s⁻¹ / 2) (h2 : ε1 + 2 * (δ / (η * η)) ≤ s⁻¹ / 2) (h3 : 2 * ε ≤ s⁻¹ / 2) :
    ∀ b ≤ B, lamD H (w b) + lamO H (w b) ≤ s⁻¹ := by
  have hP : ∀ b ≤ B, faMdev H (w b) ≤ s⁻¹ / 2 := by
    intro b
    induction b with
    | zero =>
      intro _
      exact (fa_mdev_le H (w 0)).trans (by linarith [(hweak 0 (Nat.zero_le _)).2])
    | succ n ih =>
      intro hn
      have hn' : n ≤ B := by omega
      have hP := ih hn'
      have hΩ : lamD H (w n) + lamO H (w n) ≤ s⁻¹ := by
        have := fa_lamD_le H (w n)
        linarith [(hweak n hn').1, (hweak n hn').2]
      have hd := hdiag n hn' hΩ
      have hzn : 0 < (w n).im := lt_of_lt_of_le hη (him n hn')
      have hzn1 : 0 < (w (n + 1)).im := lt_of_lt_of_le hη (him (n + 1) hn)
      have hl := fa_mdev_lip hH hzn hzn1
      have hq : ‖w n - w (n + 1)‖ / ((w n).im * (w (n + 1)).im) ≤ δ / (η * η) := by
        have hδ : 0 ≤ δ := (norm_nonneg _).trans (hstep n (by omega))
        calc ‖w n - w (n + 1)‖ / ((w n).im * (w (n + 1)).im) ≤ δ / ((w n).im * (w (n + 1)).im) :=
              div_le_div_of_nonneg_right (hstep n (by omega)) (by positivity)
          _ ≤ δ / (η * η) := div_le_div_of_nonneg_left hδ (by positivity)
              (mul_le_mul (him n hn') (him (n + 1) hn) hη.le hzn.le)
      linarith
  intro b hb
  have := fa_lamD_le H (w b)
  linarith [hP b hb, (hweak b hb).1, (hweak b hb).2]

/-- The vertical chain from `Re z + 10 i` down to `z` with steps `N⁻⁸`. -/
private def faPt (N : ℕ) (z : ℂ) (b : ℕ) : ℂ :=
  ⟨z.re, max z.im (10 - (b : ℝ) / (N : ℝ) ^ 8)⟩

private lemma fa_exp_three : (13 : ℝ) ≤ Real.exp 3 := by
  have h2 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have h3 := Real.exp_one_gt_d9
  rw [h2]
  have h4 : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h3.le 3
  have h5 : (13 : ℝ) ≤ (2.7182818283 : ℝ) ^ 3 := by norm_num
  linarith

/-- The union bound over the `10 N⁸ + 1` points of the chain and two further events. -/
private lemma fa_chain_union {N : ℕ} (hN : 3 ≤ N) {c' s : ℝ} (hc' : 0 < c')
    (hs : 32 / c' * (Real.log N + 1) ≤ s) :
    ((10 * N ^ 8 + 1 : ℕ) : ℝ) * Real.exp (-c' * s) + Real.exp (-c' * s) +
      Real.exp (-c' * s) ≤ Real.exp (-(c' / 2) * s) := by
  have hN0 : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hcs : 3 + 8 * Real.log N ≤ c' / 2 * s := by
    have h1 := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ c' / 2)
    have h2 : c' / 2 * (32 / c' * (Real.log N + 1)) = 16 * (Real.log N + 1) := by
      field_simp
      ring
    rw [h2] at h1
    linarith
  have hB3 : ((10 * N ^ 8 + 1 : ℕ) : ℝ) + 2 ≤ Real.exp (3 + 8 * Real.log N) := by
    rw [Real.exp_add, show 8 * Real.log N = ((8 : ℕ) : ℝ) * Real.log N by norm_num,
      Real.exp_nat_mul, Real.exp_log hN0]
    have hN1 : (1 : ℝ) ≤ (N : ℝ) ^ 8 := one_le_pow₀ (by
      have : (3 : ℝ) ≤ N := by exact_mod_cast hN
      linarith)
    push_cast
    have h13 := mul_le_mul_of_nonneg_right fa_exp_three (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 8)
    linarith
  calc ((10 * N ^ 8 + 1 : ℕ) : ℝ) * Real.exp (-c' * s) + Real.exp (-c' * s) +
        Real.exp (-c' * s) = (((10 * N ^ 8 + 1 : ℕ) : ℝ) + 2) * Real.exp (-c' * s) := by ring
    _ ≤ Real.exp (3 + 8 * Real.log N) * Real.exp (-c' * s) := by gcongr
    _ = Real.exp (3 + 8 * Real.log N + -c' * s) := by rw [← Real.exp_add]
    _ ≤ Real.exp (-(c' / 2) * s) := Real.exp_le_exp.mpr (by linarith)

/-- The event `Ω(z) = {Λ_d + Λ_o ≤ s⁻¹}` of (3.25) of [15] at a level `s` has probability at
least `1 - e^{-cs}`, uniformly in `s ∈ [φ^ζ, φ^{ζ+3}]` and `z ∈ S(K)`: the continuity argument in
`η` of the proof of Lemma 3.18 of [15], started from Lemma 3.16 and propagated by (3.36). -/
theorem fluctAvg_omega_level {ζ C0 : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) :
    ∃ K > 0, ∃ c > 0, ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (L : EntryLaws N) (q s : ℝ) (z : ℂ),
      L.IsGenWigner C0 → L.BoundedSupportAS q → phi N ^ K ≤ q → z ∈ specDomain N K →
      phi N ^ ζ ≤ s → s ≤ phi N ^ (ζ + 3) →
      L.law {ω | ¬ (lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹)} ≤
        ENNReal.ofReal (Real.exp (-c * s)) := by
  obtain ⟨Kd, hKd, Cd, hCd, cd, hcd, Nd, hD⟩ := norm_resolventC_diag_sub_le_on_omega hζ hC0
  obtain ⟨Kw, hKw, Cw, hCw, cw, hcw, Nw, hW⟩ := weakLocalLaw (ζ := ζ + 3) (by linarith) hC0
  obtain ⟨Ki, hKi, Ci, hCi, ci, hci, Ni, hI⟩ := initial_large_eta (ζ := ζ + 3) (by linarith) hC0
  set c' := min (min cd cw) ci with hc'
  have hc'0 : 0 < c' := lt_min (lt_min hcd hcw) hci
  set K := max (max Kd Kw) (max (Ki : ℝ) (7 * (ζ + 3) + 3)) with hK
  have hKd' : Kd ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hKw' : Kw ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have hKi' : (Ki : ℝ) ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hK7 : 7 * (ζ + 3) + 3 ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 ((fa_eventually_phi (a := ζ) hζ (32 / c') 1).and
    ((fa_eventually_phi (a := 1) one_pos (16 * (Cw + Ci + 2 * Cd)) 0).and
    ((phi_rpow_le_rpow (6 * (ζ + 3) + 2) one_pos).and
    ((phi_rpow_le_rpow (ζ + 3) one_pos).and (eventually_ge_atTop 2)))))
  refine ⟨K, by linarith, c' / 2, by positivity, max N1 (max Nd (max Nw Ni)), ?_⟩
  intro N hN L q s z hL hq hqK hz hs1 hs2
  obtain ⟨⟨hN3, hlogφ⟩, ⟨-, hφ⟩, hNφ1, hNφ2, hN2⟩ := hN1 N (le_trans (le_max_left _ _) hN)
  have hNd : Nd ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNw : Nw ≤ N :=
    le_trans (le_trans (le_max_left _ _) ((le_max_right _ _).trans (le_max_right _ _))) hN
  have hNi : Ni ≤ N :=
    le_trans (le_trans (le_max_right _ _) ((le_max_right _ _).trans (le_max_right _ _))) hN
  simp only [pow_zero, mul_one, Real.rpow_one] at hφ hNφ1 hNφ2
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hN0 : (0 : ℝ) < N := by linarith
  have hφ0 := sc_phi_pos hN3
  obtain ⟨hzre, hzK, hz10⟩ := hz
  have hηK : phi N ^ K < N * z.im := by
    rwa [div_lt_iff₀ hN0, mul_comm] at hzK
  have hq0 : 0 < q := lt_of_lt_of_le (fa_rpow_pos hN3 K) hqK
  have hη0 : 0 < z.im := pos_of_mul_pos_right (lt_trans (fa_rpow_pos hN3 K) hηK) hN0.le
  have hs0 : 0 < s := lt_of_lt_of_le (fa_rpow_pos hN3 ζ) hs1
  set m0 : ℝ := phi N ^ (-(ζ + 3)) with hm0
  have hm0s : m0 ≤ s⁻¹ := by
    rw [hm0, Real.rpow_neg hφ0.le]
    exact inv_anti₀ hs0 hs2
  have hm0pos : 0 < m0 := fa_rpow_pos hN3 _
  -- the chain
  set B : ℕ := 10 * N ^ 8 with hB
  set w : ℕ → ℂ := faPt N z with hw
  have hN8 : (0 : ℝ) < (N : ℝ) ^ 8 := by positivity
  have hwre : ∀ b, (w b).re = z.re := fun b => rfl
  have hwim : ∀ b, (w b).im = max z.im (10 - (b : ℝ) / (N : ℝ) ^ 8) := fun b => rfl
  have him : ∀ b ≤ B, z.im ≤ (w b).im := fun b _ => by rw [hwim]; exact le_max_left _ _
  have hw10 : ∀ b, (w b).im ≤ 10 := by
    intro b
    rw [hwim]
    refine max_le hz10 ?_
    have : 0 ≤ (b : ℝ) / (N : ℝ) ^ 8 := by positivity
    linarith
  have hwS : ∀ b, w b ∈ specDomain N K := fun b =>
    ⟨by rw [hwre]; exact hzre, lt_of_lt_of_le hzK (by rw [hwim]; exact le_max_left _ _), hw10 b⟩
  have hSmono : ∀ {K' : ℝ}, K' ≤ K → ∀ b, w b ∈ specDomain N K' := by
    intro K' hK' b
    obtain ⟨h1, h2, h3⟩ := hwS b
    exact ⟨h1, lt_of_le_of_lt (div_le_div_of_nonneg_right (sc_rpow_mono hN3 hK') hN0.le) h2, h3⟩
  have hw0 : w 0 = ⟨z.re, 10⟩ := by
    refine Complex.ext rfl ?_
    change max z.im (10 - ((0 : ℕ) : ℝ) / (N : ℝ) ^ 8) = 10
    simp [hz10]
  have hwB : w B = z := by
    refine Complex.ext rfl ?_
    change max z.im (10 - ((10 * N ^ 8 : ℕ) : ℝ) / (N : ℝ) ^ 8) = z.im
    push_cast
    rw [mul_div_assoc, div_self hN8.ne', mul_one, sub_self]
    exact max_eq_left hη0.le
  have hstep : ∀ b < B, ‖w b - w (b + 1)‖ ≤ 1 / (N : ℝ) ^ 8 := by
    intro b _
    have e : w b - w (b + 1) = ((((w b).im - (w (b + 1)).im : ℝ) : ℂ) * Complex.I) := by
      refine Complex.ext ?_ ?_ <;> simp [hwre]
    rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, hwim, hwim,
      max_comm z.im, max_comm z.im]
    refine (abs_max_sub_max_le_abs _ _ _).trans (le_of_eq ?_)
    push_cast
    rw [show 10 - (b : ℝ) / (N : ℝ) ^ 8 - (10 - ((b : ℝ) + 1) / (N : ℝ) ^ 8) = 1 / (N : ℝ) ^ 8 by
      field_simp; ring]
    exact abs_of_pos (by positivity)
  -- numerical bounds
  have hφC : ∀ {C : ℝ}, 0 ≤ C → C ≤ Cw + Ci + 2 * Cd → ∀ {a : ℝ}, a ≤ -(ζ + 3) - 1 →
      C * phi N ^ a ≤ m0 / 16 := by
    intro C hC0' hC a ha
    exact fa_small hN3 hC0' ha (by linarith)
  have hqinv : q⁻¹ ≤ phi N ^ (-K) := fa_inv_le_rpow hN3 hqK
  have hNη : ∀ b, phi N ^ K ≤ N * (w b).im := fun b =>
    hηK.le.trans (by rw [hwim]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) hN0.le)
  have hCw0 : 0 ≤ Cw := hCw.le
  have hCi0 : 0 ≤ Ci := hCi.le
  have hCd0 : 0 ≤ Cd := hCd.le
  have nb1 : ∀ b, Cw * (1 / q + phi N ^ (2 * (ζ + 3)) / Real.sqrt (N * (w b).im)) ≤ m0 / 8 := by
    intro b
    have h1 := fa_inv_sqrt_le hN3 (hNη b)
    have e1 : Cw * (1 / q + phi N ^ (2 * (ζ + 3)) / Real.sqrt (N * (w b).im)) =
        Cw * q⁻¹ + Cw * (phi N ^ (2 * (ζ + 3)) * (Real.sqrt (N * (w b).im))⁻¹) := by ring
    rw [e1]
    have h2 : Cw * q⁻¹ ≤ m0 / 16 :=
      (mul_le_mul_of_nonneg_left hqinv hCw0).trans (hφC hCw0 (by linarith) (by linarith))
    have h3 : Cw * (phi N ^ (2 * (ζ + 3)) * (Real.sqrt (N * (w b).im))⁻¹) ≤ m0 / 16 := by
      calc _ ≤ Cw * (phi N ^ (2 * (ζ + 3)) * phi N ^ (-(K / 2))) := by gcongr
        _ = Cw * phi N ^ (2 * (ζ + 3) + -(K / 2)) := by rw [fa_rpow_add hN3]
        _ ≤ m0 / 16 := hφC hCw0 (by linarith) (by linarith)
    linarith
  have nb2 : ∀ b, Cw * (phi N ^ (ζ + 3) / Real.sqrt q +
      phi N ^ (4 * (ζ + 3) / 3) / (N * (w b).im) ^ ((1 : ℝ) / 3)) ≤ m0 / 8 := by
    intro b
    have h1 := fa_inv_sqrt_le hN3 hqK
    have h1' := fa_inv_rpow_le hN3 (hNη b) (r := 1 / 3) (by norm_num)
    have e1 : Cw * (phi N ^ (ζ + 3) / Real.sqrt q +
        phi N ^ (4 * (ζ + 3) / 3) / (N * (w b).im) ^ ((1 : ℝ) / 3)) =
        Cw * (phi N ^ (ζ + 3) * (Real.sqrt q)⁻¹) +
          Cw * (phi N ^ (4 * (ζ + 3) / 3) * ((N * (w b).im) ^ ((1 : ℝ) / 3))⁻¹) := by ring
    rw [e1]
    have h2 : Cw * (phi N ^ (ζ + 3) * (Real.sqrt q)⁻¹) ≤ m0 / 16 := by
      calc _ ≤ Cw * (phi N ^ (ζ + 3) * phi N ^ (-(K / 2))) := by gcongr
        _ = Cw * phi N ^ ((ζ + 3) + -(K / 2)) := by rw [← fa_rpow_add hN3]
        _ ≤ m0 / 16 := hφC hCw0 (by linarith) (by linarith)
    have h3 : Cw * (phi N ^ (4 * (ζ + 3) / 3) * ((N * (w b).im) ^ ((1 : ℝ) / 3))⁻¹) ≤
        m0 / 16 := by
      calc _ ≤ Cw * (phi N ^ (4 * (ζ + 3) / 3) * phi N ^ (-(K * (1 / 3)))) := by gcongr
        _ = Cw * phi N ^ (4 * (ζ + 3) / 3 + -(K * (1 / 3))) := by rw [fa_rpow_add hN3]
        _ ≤ m0 / 16 := hφC hCw0 (by linarith) (by linarith)
    linarith
  have nb3 : Ci * (phi N ^ (ζ + 3) / q + phi N ^ (2 * (ζ + 3)) / Real.sqrt N) ≤ m0 / 8 := by
    have h1 := fa_inv_sqrt_le hN3 hNφ1
    have e1 : Ci * (phi N ^ (ζ + 3) / q + phi N ^ (2 * (ζ + 3)) / Real.sqrt N) =
        Ci * (phi N ^ (ζ + 3) * q⁻¹) + Ci * (phi N ^ (2 * (ζ + 3)) * (Real.sqrt N)⁻¹) := by ring
    rw [e1]
    have h2 : Ci * (phi N ^ (ζ + 3) * q⁻¹) ≤ m0 / 16 := by
      calc _ ≤ Ci * (phi N ^ (ζ + 3) * phi N ^ (-K)) := by gcongr
        _ = Ci * phi N ^ ((ζ + 3) + -K) := by rw [← fa_rpow_add hN3]
        _ ≤ m0 / 16 := hφC hCi0 (by linarith) (by linarith)
    have h3 : Ci * (phi N ^ (2 * (ζ + 3)) * (Real.sqrt N)⁻¹) ≤ m0 / 16 := by
      calc _ ≤ Ci * (phi N ^ (2 * (ζ + 3)) * phi N ^ (-((6 * (ζ + 3) + 2) / 2))) := by gcongr
        _ = Ci * phi N ^ (2 * (ζ + 3) + -((6 * (ζ + 3) + 2) / 2)) := by rw [fa_rpow_add hN3]
        _ ≤ m0 / 16 := hφC hCi0 (by linarith) (by linarith)
    linarith
  have nb4 : ∀ Ψ : ℝ, 0 ≤ Ψ → Ψ ≤ 2 * phi N ^ (-(K / 2)) →
      Cd * (s / q + s ^ 2 * Ψ) ≤ m0 / 8 := by
    intro Ψ hΨ0 hΨ
    have hsφ : s ^ 2 ≤ phi N ^ (2 * (ζ + 3)) := by
      have : phi N ^ (2 * (ζ + 3)) = (phi N ^ (ζ + 3)) ^ 2 := by
        rw [← fa_rpow_natMul hN3]; norm_num
      rw [this]
      exact pow_le_pow_left₀ hs0.le hs2 2
    have h2 : Cd * (s / q) ≤ m0 / 16 := by
      calc Cd * (s / q) = Cd * (s * q⁻¹) := by ring
        _ ≤ Cd * (phi N ^ (ζ + 3) * phi N ^ (-K)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hs2 hqinv (inv_nonneg.2 hq0.le)
              (fa_rpow_pos hN3 _).le) hCd0
        _ = Cd * phi N ^ ((ζ + 3) + -K) := by rw [← fa_rpow_add hN3]
        _ ≤ m0 / 16 := hφC hCd0 (by linarith) (by linarith)
    have h3 : Cd * (s ^ 2 * Ψ) ≤ m0 / 16 := by
      calc Cd * (s ^ 2 * Ψ) ≤ Cd * (phi N ^ (2 * (ζ + 3)) * (2 * phi N ^ (-(K / 2)))) := by
            gcongr
        _ = (2 * Cd) * phi N ^ (2 * (ζ + 3) + -(K / 2)) := by rw [fa_rpow_add hN3]; ring
        _ ≤ m0 / 16 := hφC (by positivity) (by linarith) (by linarith)
    have e : Cd * (s / q + s ^ 2 * Ψ) = Cd * (s / q) + Cd * (s ^ 2 * Ψ) := by ring
    linarith
  have hm01 : m0 ≤ 1 := by
    rw [hm0]
    exact Real.rpow_le_one_of_one_le_of_nonpos (sc_one_le_phi hN3) (by linarith)
  have hηN : 1 / (N : ℝ) ≤ z.im := by
    have h1 : (1 : ℝ) ≤ phi N ^ K := Real.one_le_rpow (sc_one_le_phi hN3) (by linarith)
    rw [div_le_iff₀ hN0]
    linarith
  have hlip : 2 * ((1 / (N : ℝ) ^ 8) / (z.im * z.im)) ≤ m0 / 4 := by
    have h1 : (1 / (N : ℝ) ^ 8) / (z.im * z.im) ≤ (1 / (N : ℝ) ^ 8) / (1 / N * (1 / N)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul hηN hηN (by positivity) hη0.le)
    have h2 : (1 / (N : ℝ) ^ 8) / (1 / N * (1 / N)) = 1 / (N : ℝ) ^ 6 := by
      field_simp
    have h3 : (N : ℝ)⁻¹ ≤ m0 := by
      rw [hm0, Real.rpow_neg hφ0.le]
      exact inv_anti₀ (fa_rpow_pos hN3 _) hNφ2
    have h4 : 8 / (N : ℝ) ^ 6 ≤ (N : ℝ)⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      have : (8 : ℝ) ≤ (N : ℝ) ^ 5 := by
        calc (8 : ℝ) ≤ 3 ^ 5 := by norm_num
          _ ≤ (N : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hNr 5
      calc (8 : ℝ) ≤ (N : ℝ) ^ 5 := this
        _ = (N : ℝ)⁻¹ * (N : ℝ) ^ 6 := by field_simp
    rw [h2] at h1
    have : 2 * (1 / (N : ℝ) ^ 6) = (8 / (N : ℝ) ^ 6) / 4 := by ring
    linarith
  -- the exceptional events
  set Bw : Set (Entries N) := {ω | ∃ z' ∈ specDomain N Kw,
      Cw * (1 / q + phi N ^ (2 * (ζ + 3)) / Real.sqrt (N * z'.im)) < lamO (symOfEntries ω) z' ∨
      Cw * (phi N ^ (ζ + 3) / Real.sqrt q + phi N ^ (4 * (ζ + 3) / 3) /
        (N * z'.im) ^ ((1 : ℝ) / 3)) < lamAvg (symOfEntries ω) z'} with hBw
  set Bi : Set (Entries N) := {ω | Ci * (phi N ^ (ζ + 3) / q + phi N ^ (2 * (ζ + 3)) /
      Real.sqrt N) < lamD (symOfEntries ω) (w 0) + lamO (symOfEntries ω) (w 0)} with hBi
  set Bd : ℕ → Set (Entries N) := fun b => {ω | lamD (symOfEntries ω) (w b) +
      lamO (symOfEntries ω) (w b) ≤ s⁻¹ ∧
      Cd * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) (w b)) <
        ⨆ i, ‖resolventC (symOfEntries ω) (w b) i i - stieltjesM (symOfEntries ω) (w b)‖}
    with hBd
  have hsub : {ω | ¬ (lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹)} ⊆
      Bw ∪ Bi ∪ ⋃ b ∈ Finset.range (B + 1), Bd b := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hcon
    obtain ⟨⟨hnw, hni⟩, hnd⟩ := hcon
    apply hω
    have hH := symOfEntries_isHermitian ω
    have hweak : ∀ b ≤ B, lamO (symOfEntries ω) (w b) ≤ m0 / 8 ∧
        lamAvg (symOfEntries ω) (w b) ≤ m0 / 8 := by
      intro b _
      have h : ¬ (Cw * (1 / q + phi N ^ (2 * (ζ + 3)) / Real.sqrt (N * (w b).im)) <
          lamO (symOfEntries ω) (w b) ∨
          Cw * (phi N ^ (ζ + 3) / Real.sqrt q + phi N ^ (4 * (ζ + 3) / 3) /
            (N * (w b).im) ^ ((1 : ℝ) / 3)) < lamAvg (symOfEntries ω) (w b)) :=
        fun hh => hnw ⟨w b, hSmono hKw' b, hh⟩
      rw [not_or, not_lt, not_lt] at h
      exact ⟨h.1.trans (nb1 b), h.2.trans (nb2 b)⟩
    have hinit : lamD (symOfEntries ω) (w 0) ≤ m0 / 8 := by
      have h : ¬ (Ci * (phi N ^ (ζ + 3) / q + phi N ^ (2 * (ζ + 3)) / Real.sqrt N) <
          lamD (symOfEntries ω) (w 0) + lamO (symOfEntries ω) (w 0)) := hni
      rw [not_lt] at h
      have hO : 0 ≤ lamO (symOfEntries ω) (w 0) :=
        Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => by split_ifs <;> positivity
      linarith
    have hdiag : ∀ b ≤ B, lamD (symOfEntries ω) (w b) + lamO (symOfEntries ω) (w b) ≤ s⁻¹ →
        faMdev (symOfEntries ω) (w b) ≤ m0 / 8 := by
      intro b hb hΩ
      have h : ¬ (lamD (symOfEntries ω) (w b) + lamO (symOfEntries ω) (w b) ≤ s⁻¹ ∧
          Cd * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) (w b)) <
            ⨆ i, ‖resolventC (symOfEntries ω) (w b) i i - stieltjesM (symOfEntries ω) (w b)‖) :=
        hnd b (Finset.mem_range.mpr (by omega))
      rw [not_and, not_lt] at h
      refine (h hΩ).trans (nb4 _ (Real.sqrt_nonneg _) ?_)
      have hwb : 0 < (w b).im := lt_of_lt_of_le hη0 (him b hb)
      have hA := (hweak b hb).2
      have hm1 : (msc (w b)).im ≤ 1 :=
        ((Complex.im_le_norm _).trans (norm_msc_eq_inv_and_lt_one hwb).2.le)
      have hNb : 0 < (N : ℝ) * (w b).im := by positivity
      unfold psiCtrl
      calc Real.sqrt ((lamAvg (symOfEntries ω) (w b) + (msc (w b)).im) / (N * (w b).im))
          ≤ Real.sqrt (2 * (N * (w b).im)⁻¹) := by
            apply Real.sqrt_le_sqrt
            rw [div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = Real.sqrt 2 * (Real.sqrt (N * (w b).im))⁻¹ := by
            rw [Real.sqrt_mul (by norm_num), Real.sqrt_inv]
        _ ≤ 2 * phi N ^ (-(K / 2)) := by
            have h2 : Real.sqrt 2 ≤ 2 := by
              rw [Real.sqrt_le_left (by norm_num)]; norm_num
            exact mul_le_mul h2 (fa_inv_sqrt_le hN3 (hNη b)) (by positivity) (by norm_num)
    have hchain := fa_chain_det hH w B hη0 him hstep hweak hinit hdiag
      (by linarith) (by linarith) (by linarith)
    have := hchain B le_rfl
    rwa [hwB] at this
  -- probabilities
  have hPw : L.law Bw ≤ ENNReal.ofReal (Real.exp (-cw * phi N ^ (ζ + 3))) :=
    hW N hNw L q hL hq ((sc_rpow_mono hN3 hKw').trans hqK)
  have hPi : L.law Bi ≤ ENNReal.ofReal (Real.exp (-ci * phi N ^ (ζ + 3))) := by
    have hqi : phi N ^ Ki ≤ q := by
      have := (sc_rpow_mono hN3 hKi').trans hqK
      rwa [Real.rpow_natCast] at this
    have h0re : |(w 0).re| ≤ 5 := hzre
    have h0im : (w 0).im = 10 := by rw [hw0]
    exact hI N hNi L q (w 0) hL hq hqi h0re (by rw [h0im]; norm_num) (by rw [h0im])
  have hPd : ∀ b, L.law (Bd b) ≤ ENNReal.ofReal (Real.exp (-cd * s)) := fun b =>
    hD N hNd L q s (w b) hL hq ((sc_rpow_mono hN3 hKd').trans hqK) (hSmono hKd' b) hs1 hs2
  have hsM : s ≤ phi N ^ (ζ + 3) := hs2
  have he1 : Real.exp (-cw * phi N ^ (ζ + 3)) ≤ Real.exp (-c' * s) := by
    apply Real.exp_le_exp.mpr
    have h1 : c' ≤ cw := (min_le_left _ _).trans (min_le_right _ _)
    have := mul_le_mul h1 hsM hs0.le hcw.le
    linarith
  have he2 : Real.exp (-ci * phi N ^ (ζ + 3)) ≤ Real.exp (-c' * s) := by
    apply Real.exp_le_exp.mpr
    have h1 : c' ≤ ci := min_le_right _ _
    have := mul_le_mul h1 hsM hs0.le hci.le
    linarith
  have he3 : Real.exp (-cd * s) ≤ Real.exp (-c' * s) := by
    apply Real.exp_le_exp.mpr
    have h1 : c' ≤ cd := (min_le_left _ _).trans (min_le_left _ _)
    have := mul_le_mul_of_nonneg_right h1 hs0.le
    linarith
  have hfin := fa_chain_union hN3 hc'0 (s := s) (by
    have := hlogφ
    simp only [pow_one] at this
    linarith)
  calc L.law {ω | ¬ (lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹)}
      ≤ L.law (Bw ∪ Bi ∪ ⋃ b ∈ Finset.range (B + 1), Bd b) := measure_mono hsub
    _ ≤ L.law Bw + L.law Bi + ∑ b ∈ Finset.range (B + 1), L.law (Bd b) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _)
          (measure_biUnion_finset_le _ _))
    _ ≤ ENNReal.ofReal (Real.exp (-c' * s)) + ENNReal.ofReal (Real.exp (-c' * s)) +
          ∑ _b ∈ Finset.range (B + 1), ENNReal.ofReal (Real.exp (-c' * s)) :=
        add_le_add (add_le_add (hPw.trans (ENNReal.ofReal_le_ofReal he1))
          (hPi.trans (ENNReal.ofReal_le_ofReal he2)))
          (Finset.sum_le_sum fun b _ => (hPd b).trans (ENNReal.ofReal_le_ofReal he3))
    _ = ENNReal.ofReal (((B + 1 : ℕ) : ℝ) * Real.exp (-c' * s) + Real.exp (-c' * s) +
          Real.exp (-c' * s)) := by
        rw [Finset.sum_const, Finset.card_range, ← ENNReal.ofReal_nsmul, nsmul_eq_mul,
          ← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf
    _ ≤ ENNReal.ofReal (Real.exp (-(c' / 2) * s)) := ENNReal.ofReal_le_ofReal hfin

end Chain

/-! ### The event `Ξ` of §5.3 of [15] at a fixed `z` -/

section Xi

variable {N : ℕ}

/-- `Ξ` of §5.3 of [15] at the point `z`: bounded entries, (4.1) at `z`, and the bounds (5.78),
(5.79) on `Λ_o` and on `max_i |G_ii - m|`. -/
private def faXi (q : ℝ) (z : ℂ) (g o dM : ℝ) : Set (Entries N) :=
  {ω | (∀ a b : Fin N, |symOfEntries ω a b| ≤ q⁻¹) ∧ lamAvg (symOfEntries ω) z ≤ g ∧
    (∀ a b, a ≠ b → ‖resolventC (symOfEntries ω) z a b‖ ≤ o) ∧
    (∀ a, ‖resolventC (symOfEntries ω) z a a - stieltjesM (symOfEntries ω) z‖ ≤ dM)}

private lemma fa_continuous_stieltjesM {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun ω : Entries N => stieltjesM (symOfEntries ω) z := by
  have e : (fun ω : Entries N => stieltjesM (symOfEntries ω) z) =
      fun ω => (N : ℂ)⁻¹ * ∑ j, resolventC (symOfEntries ω) z j j :=
    funext fun ω => fa_stieltjesM_eq _ z
  rw [e]
  exact continuous_const.mul (continuous_finsetSum _ fun j _ =>
    continuous_resolventC_symOfEntries hz j j)

private lemma fa_isClosed_xi {z : ℂ} (hz : z.im ≠ 0) (q g o dM : ℝ) :
    IsClosed (faXi (N := N) q z g o dM) := by
  have h1 : IsClosed {ω : Entries N | ∀ a b : Fin N, |symOfEntries ω a b| ≤ q⁻¹} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_le (continuous_symOfEntries_at a b).abs continuous_const
  have h2 : IsClosed {ω : Entries N | lamAvg (symOfEntries ω) z ≤ g} :=
    isClosed_le ((fa_continuous_stieltjesM hz).sub continuous_const).norm continuous_const
  have h3 : IsClosed {ω : Entries N | ∀ a b, a ≠ b → ‖resolventC (symOfEntries ω) z a b‖ ≤ o} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ =>
      isClosed_le (continuous_resolventC_symOfEntries hz a b).norm continuous_const
  have h4 : IsClosed {ω : Entries N |
      ∀ a, ‖resolventC (symOfEntries ω) z a a - stieltjesM (symOfEntries ω) z‖ ≤ dM} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_le
      ((continuous_resolventC_symOfEntries hz a a).sub (fa_continuous_stieltjesM hz)).norm
      continuous_const
  have e : faXi (N := N) q z g o dM =
      {ω : Entries N | ∀ a b : Fin N, |symOfEntries ω a b| ≤ q⁻¹} ∩
      ({ω : Entries N | lamAvg (symOfEntries ω) z ≤ g} ∩
      ({ω : Entries N | ∀ a b, a ≠ b → ‖resolventC (symOfEntries ω) z a b‖ ≤ o} ∩
      {ω : Entries N |
        ∀ a, ‖resolventC (symOfEntries ω) z a a - stieltjesM (symOfEntries ω) z‖ ≤ dM})) := by
    ext ω
    simp [faXi]
  rw [e]
  exact h1.inter (h2.inter (h3.inter h4))

private lemma fa_le_lamO {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ} {a b : Fin N} (hab : a ≠ b) :
    ‖resolventC H z a b‖ ≤ lamO H z := by
  have h1 : ‖resolventC H z a b‖ ≤ ⨆ b', (if a = b' then 0 else ‖resolventC H z a b'‖) := by
    refine le_trans (le_of_eq ?_) (le_ciSup (f := fun b' =>
      if a = b' then (0 : ℝ) else ‖resolventC H z a b'‖) (Set.finite_range _).bddAbove b)
    simp [hab]
  exact h1.trans (le_ciSup (f := fun a' => ⨆ b', (if a' = b' then (0 : ℝ) else
    ‖resolventC H z a' b'‖)) (Set.finite_range _).bddAbove a)

/-- The complement of `Ξ` is covered by the exceptional events of (4.1), (3.32), (3.36) at the
level `s` and of `Ω_s(z)`. -/
private lemma fa_xi_compl {L : EntryLaws N} (hL : L.IsProb) {q : ℝ} (hq : L.BoundedSupportAS q)
    {z : ℂ} (hz : 0 < z.im) {s g Co Cd : ℝ} (hCo : 0 ≤ Co) (hCd : 0 ≤ Cd) {a1 a2 a3 a4 : ℝ}
    (h1 : L.law {ω | g < lamAvg (symOfEntries ω) z} ≤ ENNReal.ofReal a1)
    (h2 : L.law {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
      Co * (1 / q + s ^ 2 * psiCtrl (symOfEntries ω) z) < lamO (symOfEntries ω) z} ≤
        ENNReal.ofReal a2)
    (h3 : L.law {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
      Cd * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) <
        ⨆ i, ‖resolventC (symOfEntries ω) z i i - stieltjesM (symOfEntries ω) z‖} ≤
        ENNReal.ofReal a3)
    (h4 : L.law {ω | ¬ (lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹)} ≤
      ENNReal.ofReal a4) (ha : 0 ≤ a1 ∧ 0 ≤ a2 ∧ 0 ≤ a3 ∧ 0 ≤ a4) :
    L.law (faXi q z g (Co * (1 / q + s ^ 2 * Real.sqrt (((msc z).im + g) / (N * z.im))))
      (Cd * (s / q + s ^ 2 * Real.sqrt (((msc z).im + g) / (N * z.im)))))ᶜ ≤
      ENNReal.ofReal (a1 + a2 + a3 + a4) := by
  set ψ := Real.sqrt (((msc z).im + g) / (N * z.im)) with hψ
  set E0 : Set (Entries N) := {ω | ¬ ∀ a b : Fin N, |symOfEntries ω a b| ≤ q⁻¹}
  have hnull : L.law E0 = 0 := ae_iff.mp (fa_ae_entries hL hq)
  have hsub : (faXi q z g (Co * (1 / q + s ^ 2 * ψ)) (Cd * (s / q + s ^ 2 * ψ)))ᶜ ⊆
      E0 ∪ {ω | g < lamAvg (symOfEntries ω) z} ∪
      {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        Co * (1 / q + s ^ 2 * psiCtrl (symOfEntries ω) z) < lamO (symOfEntries ω) z} ∪
      {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        Cd * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) <
          ⨆ i, ‖resolventC (symOfEntries ω) z i i - stieltjesM (symOfEntries ω) z‖} ∪
      {ω | ¬ (lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹)} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, not_lt, not_and] at hcon
    obtain ⟨⟨⟨⟨hE0, hg⟩, hO⟩, hDd⟩, hΩ⟩ := hcon
    apply hω
    have hΨ : psiCtrl (symOfEntries ω) z ≤ ψ := by
      unfold psiCtrl
      rw [hψ]
      apply Real.sqrt_le_sqrt
      have hNz : 0 ≤ (N : ℝ) * z.im := by positivity
      exact div_le_div_of_nonneg_right (by linarith) hNz
    have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
    refine ⟨not_not.mp hE0, hg, fun a b hab => ?_, fun a => ?_⟩
    · refine (fa_le_lamO hab).trans ((hO hΩ).trans ?_)
      gcongr
    · refine (fa_le_mdev _ z a).trans ((hDd hΩ).trans ?_)
      gcongr
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
  calc _ ≤ _ := measure_mono hsub
    _ ≤ L.law E0 + L.law {ω | g < lamAvg (symOfEntries ω) z} +
        L.law {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
          Co * (1 / q + s ^ 2 * psiCtrl (symOfEntries ω) z) < lamO (symOfEntries ω) z} +
        L.law {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
          Cd * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) <
            ⨆ i, ‖resolventC (symOfEntries ω) z i i - stieltjesM (symOfEntries ω) z‖} +
        L.law {ω | ¬ (lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹)} :=
      (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add
        ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) le_rfl))
        le_rfl)
    _ ≤ 0 + ENNReal.ofReal a1 + ENNReal.ofReal a2 + ENNReal.ofReal a3 + ENNReal.ofReal a4 := by
        rw [hnull]
        gcongr
    _ = ENNReal.ofReal (a1 + a2 + a3 + a4) := by
        rw [zero_add, ENNReal.ofReal_add (by positivity) ha4,
          ENNReal.ofReal_add (by positivity) ha3, ENNReal.ofReal_add ha1 ha2]

end Xi

/-! ### Parameter inequalities in the proof of Lemma 4.1 -/

section Rows

/-- Powers of `s ≤ φ^{ζ+3}` against `φ^K` with `K ≥ 14(ζ+3) + 4`. -/
private lemma fa_atoms {N : ℕ} (hN : 3 ≤ N) {ζ K x s : ℝ} (hζ : 0 < ζ)
    (hK : 14 * (ζ + 3) + 4 ≤ K) (hx : phi N ^ K ≤ x) (hs0 : 0 < s)
    (hs2 : s ≤ phi N ^ (ζ + 3)) :
    s ^ 7 / x ≤ (phi N ^ (2 : ℝ))⁻¹ ∧ s ^ 7 * phi N ^ (-(K / 2)) ≤ (phi N ^ (2 : ℝ))⁻¹ ∧
      s ^ 3 ≤ x := by
  have hφ0 := sc_phi_pos hN
  have h7 : s ^ 7 ≤ phi N ^ ((7 : ℕ) * (ζ + 3)) := by
    rw [fa_rpow_natMul hN]
    exact pow_le_pow_left₀ hs0.le hs2 7
  have h3 : s ^ 3 ≤ phi N ^ ((3 : ℕ) * (ζ + 3)) := by
    rw [fa_rpow_natMul hN]
    exact pow_le_pow_left₀ hs0.le hs2 3
  have hinv := fa_inv_le_rpow hN hx
  have e2 : (phi N ^ (2 : ℝ))⁻¹ = phi N ^ (-2 : ℝ) := by rw [Real.rpow_neg hφ0.le]
  rw [e2]
  refine ⟨?_, ?_, ?_⟩
  · calc s ^ 7 / x = s ^ 7 * x⁻¹ := div_eq_mul_inv _ _
      _ ≤ phi N ^ ((7 : ℕ) * (ζ + 3)) * phi N ^ (-K) :=
          mul_le_mul h7 hinv (inv_nonneg.2 ((fa_rpow_pos hN K).le.trans hx))
            (fa_rpow_pos hN _).le
      _ = phi N ^ ((7 : ℕ) * (ζ + 3) + -K) := (fa_rpow_add hN _ _).symm
      _ ≤ phi N ^ (-2 : ℝ) := sc_rpow_mono hN (by push_cast; linarith)
  · calc s ^ 7 * phi N ^ (-(K / 2)) ≤ phi N ^ ((7 : ℕ) * (ζ + 3)) * phi N ^ (-(K / 2)) :=
          mul_le_mul_of_nonneg_right h7 (fa_rpow_pos hN _).le
      _ = phi N ^ ((7 : ℕ) * (ζ + 3) + -(K / 2)) := (fa_rpow_add hN _ _).symm
      _ ≤ phi N ^ (-2 : ℝ) := sc_rpow_mono hN (by push_cast; linarith)
  · exact h3.trans ((sc_rpow_mono hN (by push_cast; linarith)).trans hx)

/-- `ψ ≤ 2 φ^{-K/2}` when `Im m_sc + g ≤ 2` and `Nη ≥ φ^K`. -/
private lemma fa_psi_le {N : ℕ} (hN : 3 ≤ N) {K J x : ℝ} (hJ : J ≤ 2) (hx : phi N ^ K ≤ x) :
    Real.sqrt (J / x) ≤ 2 * phi N ^ (-(K / 2)) := by
  have hx0 : 0 < x := lt_of_lt_of_le (fa_rpow_pos hN K) hx
  calc Real.sqrt (J / x) ≤ Real.sqrt (2 * x⁻¹) := by
        apply Real.sqrt_le_sqrt
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hJ (inv_nonneg.2 hx0.le)
    _ = Real.sqrt 2 * (Real.sqrt x)⁻¹ := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_inv]
    _ ≤ 2 * phi N ^ (-(K / 2)) := by
        have h2 : Real.sqrt 2 ≤ 2 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        exact mul_le_mul h2 (fa_inv_sqrt_le hN hx) (by positivity) (by norm_num)

private lemma fa_aux_poly {A Lg : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ Lg) :
    A * Lg + 1 ≤ (A + 1) * (Lg + 1) ^ 2 := by
  nlinarith [mul_nonneg hA hL, mul_nonneg hA (mul_nonneg hL hL), mul_nonneg hL hL]

private lemma fa_log_six : Real.log 6 < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h7 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have h8 := Real.exp_one_gt_d9
  rw [h7]
  have h4 : (2.7182818283 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) h8.le 2
  have h5 : (6 : ℝ) < (2.7182818283 : ℝ) ^ 2 := by norm_num
  linarith

/-- `log N` against `(log N)^{3/2}`. -/
private lemma fa_ell_facts {Lg : ℝ} (hL : 2 ≤ Lg) :
    Lg ^ ((3 : ℝ) / 2) = Lg * Real.sqrt Lg ∧ Lg ≤ Lg ^ ((3 : ℝ) / 2) ∧
      Lg ^ ((3 : ℝ) / 2) ≤ (Lg + 1) ^ 2 ∧ 1 ≤ Real.sqrt Lg ∧ Real.sqrt Lg ≤ Lg := by
  have hℓ : Lg ^ ((3 : ℝ) / 2) = Lg * Real.sqrt Lg := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith),
      Real.rpow_one, Real.sqrt_eq_rpow]
  have hsqL : 1 ≤ Real.sqrt Lg := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hsqL' : Real.sqrt Lg ≤ Lg := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  refine ⟨hℓ, ?_, ?_, hsqL, hsqL'⟩
  · rw [hℓ]; nlinarith
  · rw [hℓ]; nlinarith

end Rows

/-! ### Lemma 4.1 at a level `s` -/

set_option maxHeartbeats 2000000 in -- one proof for all parameter inequalities of Lemma 4.1
/-- Lemma 4.1 of [15], (4.2), at a level `s ∈ [φ^ζ, φ^{ζ+3}]`, with the same `ν` in the input
and the output. -/
private lemma fa_level_main {ζ C0 : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) :
    ∃ K > 0, ∃ ν0 > 0, ∀ ν > 0, ν ≤ ν0 → ∀ A ≥ (0 : ℝ), ∃ N0 : ℕ, ∀ N ≥ N0,
      ∀ (L : EntryLaws N) (q s : ℝ) (D : Set ℂ) (γ : ℂ → ℝ),
      L.IsGenWigner C0 → L.BoundedSupportAS q → phi N ^ K ≤ q →
      phi N ^ ζ ≤ s → s ≤ phi N ^ (ζ + 3) → D ⊆ specDomain N K → (∀ z ∈ D, γ z ≤ s⁻¹) →
      L.law {ω | ∃ z ∈ D, γ z < lamAvg (symOfEntries ω) z} ≤
        ENNReal.ofReal ((N : ℝ) ^ A * Real.exp (-ν * s)) →
      ∀ z ∈ D, L.law {ω | s ^ 14 * (1 / q ^ 2 + 1 / (N * z.im) ^ 2 +
          s ^ 4 * ((msc z).im + γ z) / (N * z.im)) < ‖zAvg (symOfEntries ω) z‖} ≤
        ENNReal.ofReal (Real.exp (-ν * s / Real.log N ^ 2)) := by
  obtain ⟨Ko, hKo, Co, hCo, co, hco, No, hO⟩ := lamO_le_on_omega_level hζ hC0
  obtain ⟨Kd, hKd, Cd, hCd, cd, hcd, Nd, hDd⟩ := norm_resolventC_diag_sub_le_on_omega hζ hC0
  obtain ⟨KΩ, hKΩ, cΩ, hcΩ, NΩ, hΩ⟩ := fluctAvg_omega_level hζ hC0
  obtain ⟨c1, hc1, Cg, hCg, CH, hCH, C1, hC1, C2, hC2, hmom⟩ := fa_hyp_moment C0 hC0
  set cs := min (min co cd) cΩ with hcs
  have hcs0 : 0 < cs := lt_min (lt_min hco hcd) hcΩ
  set K := max (max Ko Kd) (max KΩ (40 * (ζ + 3) + 2)) with hK
  have hKo' : Ko ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hKd' : Kd ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have hKΩ' : KΩ ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hK40 : 40 * (ζ + 3) + 2 ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K, by linarith, cs / 4, by positivity, ?_⟩
  intro ν hν hνcs A hA
  set Dg := max 1 (Cg * Co) with hDg
  set Cσ := 1 + CH + 2 * CH * (Cd + Co) with hCσ
  set C6 := 36 * (1 + 16 + Cσ + Real.sqrt (1 + C0)) * Dg with hC6
  obtain ⟨Cdec, hCdec, Ndec, hdec⟩ := decoupling C6 8 4 (ν / 2) (by positivity)
  set Bζ := 3 * Cdec + 8 + 8 / c1 + 4 / cs + 4 / ν + C1 + 2 + 2 / ν * (A + 1) with hBζ
  set BL := 2 + 4 / c1 + C2 + 4 * ν ^ 2 with hBL
  set Bφ := 5 + 18 * (Co + Cd) / c1 + 6 * Cg * Co with hBφ
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 ((fa_eventually_phi (a := ζ) hζ Bζ 2).and
    ((fa_eventually_phi (a := 1) one_pos Bφ 0).and ((fa_eventually_log BL).and
    ((phi_rpow_le_rpow (ζ + 3) one_pos).and (eventually_ge_atTop 16)))))
  refine ⟨max N1 (max No (max Nd (max NΩ Ndec))), ?_⟩
  intro N hN L q s D γ hL hq hqK hs1 hs2 hDK hγ hin z hz
  obtain ⟨⟨hN3, hBζφ⟩, ⟨-, hBφφ⟩, hBLl, hNφ, hN16⟩ := hN1 N (le_trans (le_max_left _ _) hN)
  have hNo : No ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNd : Nd ≤ N :=
    le_trans (le_trans (le_max_left _ _) ((le_max_right _ _).trans (le_max_right _ _))) hN
  have hNΩ : NΩ ≤ N := le_trans (le_trans (le_max_left _ _) ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))) hN
  have hNdec : Ndec ≤ N := le_trans (le_trans (le_max_right _ _) ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))) hN
  simp only [pow_zero, mul_one, Real.rpow_one] at hBφφ hNφ
  -- basic facts
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hN0 : (0 : ℝ) < N := by linarith
  have hφ0 := sc_phi_pos hN3
  have hφ1 := sc_one_le_phi hN3
  obtain ⟨hzre, hzK, hz10⟩ := hDK hz
  have hηK : phi N ^ K < N * z.im := by rwa [div_lt_iff₀ hN0, mul_comm] at hzK
  have hη0 : 0 < z.im := pos_of_mul_pos_right (lt_trans (fa_rpow_pos hN3 K) hηK) hN0.le
  have hq0 : 0 < q := lt_of_lt_of_le (fa_rpow_pos hN3 K) hqK
  have hK1 : (1 : ℝ) ≤ phi N ^ K := Real.one_le_rpow hφ1 (by linarith)
  have hq1 : 1 ≤ q := hK1.trans hqK
  have hNη1 : 1 ≤ (N : ℝ) * z.im := hK1.trans hηK.le
  have hs0 : 0 < s := lt_of_lt_of_le (fa_rpow_pos hN3 ζ) hs1
  have hs1' : 1 ≤ s := (Real.one_le_rpow hφ1 hζ.le).trans hs1
  set Lg := Real.log N with hLg
  have hL2 : 2 ≤ Lg := by
    have : (0 : ℝ) ≤ 4 / c1 + C2 + 4 * ν ^ 2 := by positivity
    linarith
  have hLφ : Lg ≤ phi N := log_le_phi hN16
  set ℓ := Lg ^ ((3 : ℝ) / 2) with hℓdef
  obtain ⟨hℓ, hℓL, hℓsq, hsqL, hsqL'⟩ := fa_ell_facts hL2
  have hℓ0 : 0 < ℓ := by linarith
  have hsB : Bζ * (Lg + 1) ^ 2 ≤ s := hBζφ.trans hs1
  have hLp1 : 1 ≤ (Lg + 1) ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (show (1 : ℝ) ≤ Lg + 1 by linarith) 2
    simpa using this
  -- consequences of `s ≥ Bζ (log N + 1)²`
  have hpos1 : 0 < 8 / c1 := by positivity
  have hpos2 : 0 < 4 / cs := by positivity
  have hpos3 : 0 < 4 / ν := by positivity
  have hpos4 : 0 ≤ 2 / ν * (A + 1) := by positivity
  have hpos5 : 0 ≤ 3 * Cdec + 8 := by positivity
  have hBζ1 : Bζ ≤ s := by
    have : Bζ ≤ Bζ * (Lg + 1) ^ 2 := le_mul_of_one_le_right (by positivity) hLp1
    linarith
  have hsc1 : 8 / c1 ≤ s := by linarith
  have hscs : 4 / cs ≤ s := by linarith
  have hsν : 4 / ν ≤ s := by linarith
  have hsC1 : C1 ≤ s := by linarith
  have hs2' : 2 ≤ s := by linarith
  have hsℓ : (3 * Cdec + 8) * ℓ ≤ s := by
    have h1 : (3 * Cdec + 8) * ℓ ≤ (3 * Cdec + 8) * (Lg + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left hℓsq hpos5
    have h2 : (3 * Cdec + 8) * (Lg + 1) ^ 2 ≤ Bζ * (Lg + 1) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hsA : 2 / ν * (A * Lg + 1) ≤ s := by
    have h1 := fa_aux_poly hA (by linarith : (0 : ℝ) ≤ Lg)
    have h2 : 2 / ν * (A * Lg + 1) ≤ 2 / ν * (A + 1) * (Lg + 1) ^ 2 := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 2 / ν * (A + 1) * (Lg + 1) ^ 2 ≤ Bζ * (Lg + 1) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  -- the exponential estimates
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hEA : (N : ℝ) ^ A * Real.exp (-ν * s) ≤ Real.exp (-(ν * s / 2)) / 2 := by
    rw [Real.rpow_def_of_pos hN0, ← Real.exp_add, ← hLg]
    have h1 : ν * (2 / ν * (A * Lg + 1)) = 2 * (A * Lg + 1) := by field_simp
    have h2 : ν * (2 / ν * (A * Lg + 1)) ≤ ν * s := mul_le_mul_of_nonneg_left hsA hν.le
    have h3 : Real.exp (-(ν * s / 2)) / 2 = Real.exp (-(ν * s / 2) - Real.log 2) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num)]
    rw [h3]
    apply Real.exp_le_exp.mpr
    linarith
  have hEC : Real.exp (-co * s) + Real.exp (-cd * s) + Real.exp (-cΩ * s) ≤
      Real.exp (-(ν * s / 2)) / 2 := by
    have hco' : cs ≤ co := (min_le_left _ _).trans (min_le_left _ _)
    have hcd' : cs ≤ cd := (min_le_left _ _).trans (min_le_right _ _)
    have hcΩ' : cs ≤ cΩ := min_le_right _ _
    have k1 : Real.exp (-co * s) ≤ Real.exp (-cs * s) := Real.exp_le_exp.mpr (by
      have := mul_le_mul_of_nonneg_right hco' hs0.le; linarith)
    have k2 : Real.exp (-cd * s) ≤ Real.exp (-cs * s) := Real.exp_le_exp.mpr (by
      have := mul_le_mul_of_nonneg_right hcd' hs0.le; linarith)
    have k3 : Real.exp (-cΩ * s) ≤ Real.exp (-cs * s) := Real.exp_le_exp.mpr (by
      have := mul_le_mul_of_nonneg_right hcΩ' hs0.le; linarith)
    have k4 : 3 * Real.exp (-cs * s) ≤ Real.exp (-(ν * s / 2)) / 2 := by
      have h6 := fa_log_six
      have h9 : cs * (4 / cs) = 4 := by field_simp
      have h10 : cs * (4 / cs) ≤ cs * s := mul_le_mul_of_nonneg_left hscs hcs0.le
      have h11 : ν * s ≤ cs / 4 * s := mul_le_mul_of_nonneg_right hνcs hs0.le
      have e : 3 * Real.exp (-cs * s) = Real.exp (Real.log 6 + -cs * s) / 2 := by
        rw [Real.exp_add, Real.exp_log (by norm_num)]; ring
      rw [e]
      gcongr
      linarith
    linarith
  have hEν : Real.exp (-(ν * s / 2)) ≤ Real.exp (-ν * s / Lg ^ 2) / 2 := by
    have hL4 : 4 ≤ Lg ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL2 2
      norm_num at this ⊢; linarith
    have h1 : ν * s / Lg ^ 2 ≤ ν * s / 4 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hL4
    have h2 : ν * (4 / ν) = 4 := by field_simp
    have h3 : ν * (4 / ν) ≤ ν * s := mul_le_mul_of_nonneg_left hsν hν.le
    have e : Real.exp (-ν * s / Lg ^ 2) / 2 = Real.exp (-ν * s / Lg ^ 2 - Real.log 2) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num)]
    rw [e]
    apply Real.exp_le_exp.mpr
    have : -ν * s / Lg ^ 2 = -(ν * s / Lg ^ 2) := by ring
    rw [this]
    linarith
  -- `γ(z) ≥ 0`
  set g := γ z with hgdef
  have hgs : g ≤ s⁻¹ := hγ z hz
  have hsubin : {ω : Entries N | g < lamAvg (symOfEntries ω) z} ⊆
      {ω | ∃ z ∈ D, γ z < lamAvg (symOfEntries ω) z} := fun ω hω => ⟨z, hz, hω⟩
  have hin' : L.law {ω | g < lamAvg (symOfEntries ω) z} ≤
      ENNReal.ofReal ((N : ℝ) ^ A * Real.exp (-ν * s)) := (measure_mono hsubin).trans hin
  have hP := isProbabilityMeasure_law hL.isProb
  have hg0 : 0 ≤ g := by
    by_contra hneg
    rw [not_le] at hneg
    have huniv : {ω : Entries N | g < lamAvg (symOfEntries ω) z} = Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact lt_of_lt_of_le hneg (norm_nonneg _)
    rw [huniv, measure_univ] at hin'
    have h1 : (N : ℝ) ^ A * Real.exp (-ν * s) < 1 := by
      have := Real.exp_le_one_iff.mpr (show -(ν * s / 2) ≤ 0 by
        have := mul_pos hν hs0; linarith)
      linarith
    have h2 := (ENNReal.one_le_ofReal).mp hin'
    linarith
  -- the parameters of Lemma 5.13
  set Im := (msc z).im with hIm
  have hIm0 : 0 < Im := im_msc_pos hη0
  have hIm1 : Im ≤ 1 := (Complex.im_le_norm _).trans (norm_msc_eq_inv_and_lt_one hη0).2.le
  have hIm256 : z.im / 256 ≤ Im := fa_im_msc_ge hzre hη0 hz10
  have hgs1 : g ≤ 1 := hgs.trans (inv_le_one_of_one_le₀ hs1')
  set J := Im + g with hJ
  have hJ2 : J ≤ 2 := by linarith
  have hJ0 : 0 ≤ J := by linarith
  set ψ := Real.sqrt (J / (N * z.im)) with hψ
  have hψ0 : 0 ≤ ψ := Real.sqrt_nonneg _
  have hψK : ψ ≤ 2 * phi N ^ (-(K / 2)) := fa_psi_le hN3 hJ2 hηK.le
  have hψsq : ψ ^ 2 = J / (N * z.im) := Real.sq_sqrt (by positivity)
  obtain ⟨a1, a2, a3⟩ := fa_atoms hN3 hζ (by linarith : 14 * (ζ + 3) + 4 ≤ K) hqK hs0 hs2
  obtain ⟨b1, -, b3⟩ := fa_atoms hN3 hζ (by linarith : 14 * (ζ + 3) + 4 ≤ K) hηK.le hs0 hs2
  set ε := (phi N ^ (2 : ℝ))⁻¹ with hε
  have hε0 : 0 < ε := inv_pos.mpr (fa_rpow_pos hN3 _)
  have hφ2 : phi N ≤ phi N ^ (2 : ℝ) := by
    have := sc_rpow_mono hN3 (show (1 : ℝ) ≤ 2 by norm_num)
    rwa [Real.rpow_one] at this
  have hεφ : ε * phi N ≤ 1 := by
    rw [hε, inv_mul_le_iff₀ (fa_rpow_pos hN3 _), mul_one]; exact hφ2
  have hs7ψ : s ^ 7 * ψ ≤ 2 * ε := by
    calc s ^ 7 * ψ ≤ s ^ 7 * (2 * phi N ^ (-(K / 2))) :=
          mul_le_mul_of_nonneg_left hψK (by positivity)
      _ = 2 * (s ^ 7 * phi N ^ (-(K / 2))) := by ring
      _ ≤ 2 * ε := by linarith
  have hspow : ∀ k : ℕ, k ≤ 7 → s ^ k ≤ s ^ 7 := fun k hk => pow_le_pow_right₀ hs1' hk
  have hsq7 : ∀ k : ℕ, k ≤ 7 → s ^ k / q ≤ ε := fun k hk =>
    (div_le_div_of_nonneg_right (hspow k hk) hq0.le).trans a1
  have hsη7 : ∀ k : ℕ, k ≤ 7 → s ^ k / (N * z.im) ≤ ε := fun k hk =>
    (div_le_div_of_nonneg_right (hspow k hk) (by positivity)).trans b1
  have hsψ7 : ∀ k : ℕ, k ≤ 7 → s ^ k * ψ ≤ 2 * ε := fun k hk =>
    (mul_le_mul_of_nonneg_right (hspow k hk) hψ0).trans hs7ψ
  set X := 1 / q + 1 / (N * z.im) + s ^ 2 * ψ with hX
  set Y := s ^ 2 with hY
  have hs2ψ : ψ ≤ s ^ 2 * ψ := le_mul_of_one_le_left hψ0 (one_le_pow₀ hs1')
  have hX0 : 0 ≤ X := by positivity
  have hqX : q⁻¹ ≤ X := by
    have : 0 ≤ 1 / (N * z.im) := by positivity
    rw [hX, one_div]; linarith [mul_nonneg (sq_nonneg s) hψ0]
  have hηX : 1 / (N * z.im) ≤ X := by
    have : 0 ≤ 1 / q := by positivity
    rw [hX]; linarith [mul_nonneg (sq_nonneg s) hψ0]
  have hψX : ψ ≤ X := by
    have h1 : 0 ≤ 1 / q := by positivity
    have h2 : 0 ≤ 1 / (N * z.im) := by positivity
    rw [hX]; linarith
  have hY1 : 1 ≤ Y := one_le_pow₀ hs1'
  set o := Co * (1 / q + s ^ 2 * ψ) with ho
  set dM := Cd * (s / q + s ^ 2 * ψ) with hdM
  set d := dM + g with hd
  have ho0 : 0 ≤ o := by positivity
  have hdM0 : 0 ≤ dM := by positivity
  have hd0 : 0 ≤ d := by positivity
  -- the moment `p`
  set p' := ⌊s / (2 * ℓ)⌋₊ with hp'
  set p := 2 * p' with hp
  have hsℓ2 : 1 ≤ s / (2 * ℓ) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : 2 * ℓ ≤ (3 * Cdec + 8) * ℓ :=
      mul_le_mul_of_nonneg_right (by linarith only [hCdec]) hℓ0.le
    linarith only [h1, hsℓ]
  have hp'le : (p' : ℝ) ≤ s / (2 * ℓ) := Nat.floor_le (by positivity)
  have hp'gt : s / (2 * ℓ) - 1 < p' := by
    have := Nat.lt_floor_add_one (s / (2 * ℓ)); linarith only [this]
  have hp'1 : 1 ≤ p' := Nat.le_floor (by exact_mod_cast hsℓ2)
  have hpR : (p : ℝ) = 2 * p' := by rw [hp]; push_cast; ring
  have hpℓ : (p : ℝ) ≤ s / ℓ := by
    rw [hpR]
    calc 2 * (p' : ℝ) ≤ 2 * (s / (2 * ℓ)) := by linarith only [hp'le]
      _ = s / ℓ := by field_simp
  have hsℓs : s / ℓ ≤ s / 2 :=
    div_le_div_of_nonneg_left hs0.le (by norm_num) (by linarith only [hℓL, hL2])
  have hps : (p : ℝ) ≤ s := by linarith only [hpℓ, hsℓs, hs0]
  have hp2 : 2 ≤ p := by rw [hp]; omega
  have hpN : p ≤ N := by
    have : (p : ℝ) ≤ N := hps.trans (hs2.trans hNφ)
    exact_mod_cast this
  have hℓp : ℓ * p ≤ s := by
    have := mul_le_mul_of_nonneg_left hpℓ hℓ0.le
    rwa [mul_div_cancel₀ _ hℓ0.ne'] at this
  -- (5.71) of [15] for the `p + 1` rows: `(|S| + 2)(Λ_o + Λ_d) ≤ c1`
  have hq_s : 1 / q ≤ s / q := div_le_div_of_nonneg_right hs1' hq0.le
  have hpp2 : ((2 * p' : ℕ) : ℝ) + 2 ≤ 3 * s := by
    have : ((2 * p' : ℕ) : ℝ) = p := by rw [hp]
    rw [this]; linarith only [hps, hs1']
  have hpp1 : ((2 * p' : ℕ) : ℝ) + 1 ≤ 2 * s := by
    have : ((2 * p' : ℕ) : ℝ) = p := by rw [hp]
    rw [this]; linarith only [hps, hs1']
  have hs2q : s * (s / q + s ^ 2 * ψ) ≤ 3 * ε := by
    have e : s * (s / q + s ^ 2 * ψ) = s ^ 2 / q + s ^ 3 * ψ := by ring
    rw [e]
    linarith only [hsq7 2 (by norm_num), hsψ7 3 (by norm_num)]
  have h_c1 : (((2 * p' : ℕ) : ℝ) + 2) * (o + d) ≤ c1 := by
    have hod : o + d ≤ (Co + Cd) * (s / q + s ^ 2 * ψ) + g := by
      rw [ho, hd, hdM]
      have := mul_le_mul_of_nonneg_left (show 1 / q + s ^ 2 * ψ ≤ s / q + s ^ 2 * ψ by
        linarith only [hq_s]) hCo.le
      linarith only [this]
    have hA1 : (((2 * p' : ℕ) : ℝ) + 2) * g ≤ c1 / 2 := by
      have hpg : (((2 * p' : ℕ) : ℝ) + 2) ≤ s / ℓ + 2 := by
        have : ((2 * p' : ℕ) : ℝ) = p := by rw [hp]
        rw [this]; linarith only [hpℓ]
      have h1 : (((2 * p' : ℕ) : ℝ) + 2) * g ≤ (s / ℓ + 2) * s⁻¹ :=
        mul_le_mul hpg hgs hg0 (by positivity)
      have h2 : (s / ℓ + 2) * s⁻¹ = 1 / ℓ + 2 / s := by field_simp
      have h3 : 1 / ℓ ≤ c1 / 4 := by
        rw [div_le_iff₀ hℓ0]
        have : 4 / c1 ≤ ℓ := by
          have : (0 : ℝ) ≤ C2 + 4 * ν ^ 2 := by positivity
          linarith only [hBLl, hℓL, this]
        have h5 : c1 / 4 * (4 / c1) = 1 := by field_simp
        nlinarith only [this, h5, hc1]
      have h4 : 2 / s ≤ c1 / 4 := by
        rw [div_le_iff₀ hs0]
        have h5 : c1 / 4 * (8 / c1) = 2 := by field_simp; ring
        nlinarith only [hsc1, h5, hc1]
      linarith only [h1, h2, h3, h4]
    have hA2 : (((2 * p' : ℕ) : ℝ) + 2) * ((Co + Cd) * (s / q + s ^ 2 * ψ)) ≤ c1 / 2 := by
      have h1 : (((2 * p' : ℕ) : ℝ) + 2) * ((Co + Cd) * (s / q + s ^ 2 * ψ)) ≤
          3 * s * ((Co + Cd) * (s / q + s ^ 2 * ψ)) :=
        mul_le_mul_of_nonneg_right hpp2 (by positivity)
      have h2 : 3 * s * ((Co + Cd) * (s / q + s ^ 2 * ψ)) =
          3 * (Co + Cd) * (s * (s / q + s ^ 2 * ψ)) := by ring
      have h3 : 3 * (Co + Cd) * (s * (s / q + s ^ 2 * ψ)) ≤ 3 * (Co + Cd) * (3 * ε) :=
        mul_le_mul_of_nonneg_left hs2q (by positivity)
      have h4 : 9 * (Co + Cd) * ε ≤ c1 / 2 := by
        have hφB : 18 * (Co + Cd) / c1 ≤ phi N := by
          have : (0 : ℝ) ≤ 6 * Cg * Co := by positivity
          linarith only [hBφφ, this]
        have h5 : 18 * (Co + Cd) ≤ c1 * phi N := by
          rw [div_le_iff₀ hc1] at hφB; linarith only [hφB]
        have h6 : (Co + Cd) * (ε * phi N) ≤ (Co + Cd) * 1 :=
          mul_le_mul_of_nonneg_left hεφ (by positivity)
        have h7 : 18 * (Co + Cd) * ε ≤ c1 * phi N * ε := mul_le_mul_of_nonneg_right h5 hε0.le
        have h8 : c1 * phi N * ε ≤ c1 := by
          have := mul_le_mul_of_nonneg_left hεφ hc1.le
          linarith only [this]
        linarith only [h7, h8]
      linarith only [h1, h2, h3, h4]
    calc (((2 * p' : ℕ) : ℝ) + 2) * (o + d) ≤ (((2 * p' : ℕ) : ℝ) + 2) *
          ((Co + Cd) * (s / q + s ^ 2 * ψ) + g) := mul_le_mul_of_nonneg_left hod (by positivity)
      _ = (((2 * p' : ℕ) : ℝ) + 2) * ((Co + Cd) * (s / q + s ^ 2 * ψ)) +
          (((2 * p' : ℕ) : ℝ) + 2) * g := by ring
      _ ≤ c1 := by linarith only [hA1, hA2]
  -- `C (|S| + 1) Λ_o ≤ 1` for (5.73)
  have h_Cg : Cg * (((2 * p' : ℕ) : ℝ) + 1) * o ≤ 1 := by
    have h1 : Cg * (((2 * p' : ℕ) : ℝ) + 1) * o ≤ Cg * (2 * s) * o :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpp1 hCg.le) ho0
    have h2 : Cg * (2 * s) * o ≤ 2 * Cg * Co * (s * (s / q + s ^ 2 * ψ)) := by
      have := mul_le_mul_of_nonneg_left (show 1 / q + s ^ 2 * ψ ≤ s / q + s ^ 2 * ψ by
        linarith only [hq_s]) (by positivity : (0 : ℝ) ≤ 2 * Cg * Co * s)
      rw [ho]
      nlinarith only [this]
    have h3 : 2 * Cg * Co * (s * (s / q + s ^ 2 * ψ)) ≤ 2 * Cg * Co * (3 * ε) :=
      mul_le_mul_of_nonneg_left hs2q (by positivity)
    have h4 : 6 * Cg * Co * ε ≤ 1 := by
      have hφB : 6 * Cg * Co ≤ phi N := by
        have : (0 : ℝ) ≤ 18 * (Co + Cd) / c1 := by positivity
        linarith only [hBφφ, this]
      have := mul_le_mul_of_nonneg_right hφB hε0.le
      linarith only [this, hεφ]
    linarith only [h1, h2, h3, h4]
  -- `C o ≤ D_g X`
  have hoX : o ≤ Co * X := by
    rw [ho]
    exact mul_le_mul_of_nonneg_left (by
      have : 0 ≤ 1 / (N * z.im) := by positivity
      rw [hX]; linarith only [this]) hCo.le
  have hDg1 : 1 ≤ Dg := le_max_left _ _
  have h_Dg : Cg * o ≤ Dg * X := by
    have h1 : Cg * o ≤ Cg * Co * X := by
      have := mul_le_mul_of_nonneg_left hoX hCg.le; linarith only [this]
    have h2 : Cg * Co * X ≤ Dg * X := mul_le_mul_of_nonneg_right (le_max_right _ _) hX0
    linarith only [h1, h2]
  -- `N⁻¹ ≤ (16 X)²`, from `Im m_sc ≥ η/256`
  have hNX : (N : ℝ)⁻¹ ≤ (16 * X) ^ 2 := by
    have h1 : (N : ℝ)⁻¹ / 256 ≤ ψ ^ 2 := by
      rw [hψsq]
      have h2 : (N : ℝ)⁻¹ / 256 = (z.im / 256) / (N * z.im) := by field_simp
      rw [h2]
      exact div_le_div_of_nonneg_right (by linarith only [hIm256, hg0]) (by positivity)
    have h3 : ψ ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hψ0 hψX 2
    nlinarith only [h1, h3]
  -- the Hilbert–Schmidt bound for `U = ∅`
  have hσ1 : 1 ≤ Cσ := by
    have : (0 : ℝ) ≤ CH + 2 * CH * (Cd + Co) := by positivity
    rw [hCσ]; linarith only [this]
  have hHS : ((msc z).im + g + CH * (((2 * p' : ℕ) : ℝ) + 1) * ((msc z).im + d + o) /
      (N * z.im)) / (N * z.im) ≤ (Cσ * X) ^ 2 := by
    have hNη0 : 0 < (N : ℝ) * z.im := by positivity
    have hsNη : s ≤ N * z.im := by
      have := (pow_le_pow_right₀ hs1' (show 1 ≤ 3 by norm_num)).trans b3
      simpa using this
    have hs2Nη : s ^ 2 ≤ N * z.im := (pow_le_pow_right₀ hs1' (by norm_num)).trans b3
    have hdo : (msc z).im + d + o ≤ J + (Cd + Co) * (s / q + s ^ 2 * ψ) := by
      rw [hd, hdM, ho, hJ]
      have := mul_le_mul_of_nonneg_left (show 1 / q + s ^ 2 * ψ ≤ s / q + s ^ 2 * ψ by
        linarith only [hq_s]) hCo.le
      linarith only [this]
    set W := N * z.im with hW
    have e1 : ((msc z).im + g + CH * (((2 * p' : ℕ) : ℝ) + 1) * ((msc z).im + d + o) / W) / W =
        J / W + CH * (((2 * p' : ℕ) : ℝ) + 1) * ((msc z).im + d + o) / W ^ 2 := by
      rw [hJ]; field_simp; ring
    rw [e1]
    have hpp1' : ((2 * p' : ℕ) : ℝ) + 1 ≤ s := by
      have : ((2 * p' : ℕ) : ℝ) = p := by rw [hp]
      rw [this]; linarith only [hpℓ, hsℓs, hs2']
    have k1 : CH * (((2 * p' : ℕ) : ℝ) + 1) * ((msc z).im + d + o) / W ^ 2 ≤
        CH * s * (J + (Cd + Co) * (s / q + s ^ 2 * ψ)) / W ^ 2 := by
      gcongr
    have k2 : CH * s * (J + (Cd + Co) * (s / q + s ^ 2 * ψ)) / W ^ 2 =
        CH * (s / W) * (J / W) + CH * (Cd + Co) * ((s ^ 2 / W) * (1 / q) * (1 / W) +
          (s ^ 2 / W) * (s / W) * ψ) := by
      field_simp
    have hsW : s / W ≤ 1 := (div_le_one hNη0).mpr hsNη
    have hs2W : s ^ 2 / W ≤ 1 := (div_le_one hNη0).mpr hs2Nη
    have hJW : J / W = ψ ^ 2 := hψsq.symm
    have k3 : CH * (s / W) * (J / W) ≤ CH * X ^ 2 := by
      rw [hJW]
      have : ψ ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hψ0 hψX 2
      have h0 : 0 ≤ s / W := by positivity
      calc CH * (s / W) * ψ ^ 2 ≤ CH * 1 * ψ ^ 2 := by gcongr
        _ ≤ CH * X ^ 2 := by rw [mul_one]; exact mul_le_mul_of_nonneg_left this hCH.le
    have k4 : (s ^ 2 / W) * (1 / q) * (1 / W) + (s ^ 2 / W) * (s / W) * ψ ≤ 2 * X ^ 2 := by
      have h1 : (s ^ 2 / W) * (1 / q) * (1 / W) ≤ X * X := by
        have h0 : 0 ≤ s ^ 2 / W := by positivity
        calc (s ^ 2 / W) * (1 / q) * (1 / W) ≤ 1 * (1 / q) * (1 / W) := by gcongr
          _ ≤ X * X := by
              rw [one_mul]
              exact mul_le_mul (by rw [one_div]; exact hqX) hηX (by positivity) hX0
      have h2 : (s ^ 2 / W) * (s / W) * ψ ≤ X * X := by
        have e : (s ^ 2 / W) * (s / W) * ψ = (s ^ 3 / W) * ((1 / W) * ψ) := by
          field_simp
        have h4 : s ^ 3 / W ≤ 1 := (div_le_one hNη0).mpr b3
        have h0 : 0 ≤ (1 / W) * ψ := by positivity
        rw [e]
        calc (s ^ 3 / W) * ((1 / W) * ψ) ≤ 1 * ((1 / W) * ψ) :=
              mul_le_mul_of_nonneg_right h4 h0
          _ = 1 / W * ψ := one_mul _
          _ ≤ X * X := mul_le_mul hηX hψX hψ0 hX0
      nlinarith only [h1, h2]
    have hψX2 : ψ ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hψ0 hψX 2
    have k5 : CH * (Cd + Co) * ((s ^ 2 / W) * (1 / q) * (1 / W) + (s ^ 2 / W) * (s / W) * ψ) ≤
        CH * (Cd + Co) * (2 * X ^ 2) := mul_le_mul_of_nonneg_left k4 (by positivity)
    have k6 : Cσ * X ^ 2 ≤ (Cσ * X) ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (by nlinarith only [hσ1]) (sq_nonneg X)
    have k7 : X ^ 2 + CH * X ^ 2 + CH * (Cd + Co) * (2 * X ^ 2) = Cσ * X ^ 2 := by
      rw [hCσ]; ring
    rw [hJW]
    linarith only [k1, k2, k3, k5, k6, k7, hψX2]
  -- (5.11)-type conditions on `p`
  have hC2Y : (C2 * p') ^ 2 ≤ Y := by
    have h1 : C2 * (p' : ℝ) ≤ s := by
      have h2 : C2 * (p' : ℝ) ≤ C2 * (s / (2 * ℓ)) := mul_le_mul_of_nonneg_left hp'le hC2.le
      have h3 : C2 * (s / (2 * ℓ)) ≤ s := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        have : C2 ≤ 2 * ℓ := by
          have : (0 : ℝ) ≤ 4 / c1 + 4 * ν ^ 2 := by positivity
          linarith only [hBLl, hℓL, this, hL2]
        nlinarith only [this, hs0]
      linarith only [h2, h3]
    rw [hY]
    exact pow_le_pow_left₀ (by positivity) h1 2
  have hC1Y : C1 * p' ≤ Y := by
    have h1 : (p' : ℝ) ≤ s := by
      have : (p' : ℝ) ≤ p := by rw [hpR]; linarith only [hp'le, hsℓ2]
      linarith only [this, hps]
    rw [hY, sq]
    exact mul_le_mul hsC1 h1 (Nat.cast_nonneg _) hs0.le
  -- (5.7): `X ≤ 1/(p⁵ log N)`
  have hX5 : X ≤ 1 / ((p : ℝ) ^ 5 * Real.log N) := by
    have hp0 : (0 : ℝ) < p := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      linarith only [this]
    have hden : 0 < (p : ℝ) ^ 5 * Lg := by positivity
    rw [← hLg, le_div_iff₀ hden]
    have h1 : X * ((p : ℝ) ^ 5 * Lg) ≤ X * (s ^ 5 * phi N) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_left₀ hp0.le hps 5) hLφ
        (by positivity) (by positivity)) hX0
    have h2 : X * (s ^ 5 * phi N) = (s ^ 5 / q + s ^ 5 / (N * z.im) + s ^ 7 * ψ) * phi N := by
      rw [hX]; field_simp; ring
    have h3 : (s ^ 5 / q + s ^ 5 / (N * z.im) + s ^ 7 * ψ) * phi N ≤ (4 * ε) * phi N := by
      refine mul_le_mul_of_nonneg_right ?_ hφ0.le
      linarith only [hsq7 5 (by norm_num), hsη7 5 (by norm_num), hs7ψ]
    have h4 : (4 * ε) * phi N ≤ 1 := by
      have h5 : 4 ≤ phi N := by
        have : (0 : ℝ) ≤ 18 * (Co + Cd) / c1 + 6 * Cg * Co := by positivity
        linarith only [hBφφ, this]
      have h8 : phi N * phi N = phi N ^ (2 : ℝ) := by
        rw [show phi N * phi N = phi N ^ (2 : ℕ) by ring, ← Real.rpow_natCast]
        norm_num
      have h9 : ε * phi N ^ (2 : ℝ) = 1 := by rw [hε]; field_simp
      calc (4 * ε) * phi N ≤ (phi N * ε) * phi N :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h5 hε0.le) hφ0.le
        _ = ε * (phi N * phi N) := by ring
        _ = 1 := by rw [h8, h9]
    linarith only [h1, h2, h3, h4]
  -- the threshold of (5.12) lies below the threshold of (4.2)
  have hthr : (p : ℝ) ^ 12 * Y * (X ^ 2 + (N : ℝ)⁻¹) ≤ s ^ 14 * (1 / q ^ 2 + 1 / (N * z.im) ^ 2 +
      s ^ 4 * ((msc z).im + γ z) / (N * z.im)) := by
    set B0 := 1 / q ^ 2 + 1 / (N * z.im) ^ 2 + s ^ 4 * ((msc z).im + γ z) / (N * z.im) with hB0
    have hNη0 : 0 < (N : ℝ) * z.im := by positivity
    have hs4 : 1 ≤ s ^ 4 := one_le_pow₀ hs1'
    have hJt : 0 ≤ s ^ 4 * J / (N * z.im) := by positivity
    have hX2 : X ^ 2 ≤ 3 * B0 := by
      have h1 := sc_sq_add3_le (1 / q) (1 / (N * z.im)) (s ^ 2 * ψ)
      have e : (s ^ 2 * ψ) ^ 2 = s ^ 4 * J / (N * z.im) := by
        rw [mul_pow, hψsq]; ring
      rw [e, div_pow, div_pow, one_pow] at h1
      rw [hB0]
      exact h1
    have hN1 : (N : ℝ)⁻¹ ≤ 256 * B0 := by
      have h1 : (N : ℝ)⁻¹ = 256 * ((z.im / 256) / (N * z.im)) := by field_simp
      have h2 : (z.im / 256) / (N * z.im) ≤ s ^ 4 * J / (N * z.im) := by
        apply div_le_div_of_nonneg_right _ hNη0.le
        nlinarith only [hIm256, hg0, hs4, hIm0]
      have h3 : s ^ 4 * J / (N * z.im) ≤ B0 := by
        rw [hB0]
        have : 0 ≤ 1 / q ^ 2 + 1 / (N * z.im) ^ 2 := by positivity
        linarith only [this]
      rw [h1]
      linarith only [h2, h3]
    have hB00 : 0 ≤ B0 := by rw [hB0]; positivity
    have hp12 : (p : ℝ) ^ 12 ≤ s ^ 12 / 4096 := by
      have hpL : (p : ℝ) ≤ s / Lg :=
        hpℓ.trans (div_le_div_of_nonneg_left hs0.le (by linarith only [hL2]) hℓL)
      have h1 : (p : ℝ) ^ 12 ≤ (s / Lg) ^ 12 := pow_le_pow_left₀ (Nat.cast_nonneg _) hpL 12
      have h2 : (2 : ℝ) ^ 12 ≤ Lg ^ 12 := pow_le_pow_left₀ (by norm_num) hL2 12
      rw [div_pow] at h1
      refine h1.trans ?_
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
      norm_num at h2 ⊢
      exact h2
    calc (p : ℝ) ^ 12 * Y * (X ^ 2 + (N : ℝ)⁻¹) ≤ s ^ 12 / 4096 * s ^ 2 * (259 * B0) := by
          rw [hY]
          refine mul_le_mul (mul_le_mul_of_nonneg_right hp12 (sq_nonneg s)) ?_ (by positivity)
            (by positivity)
          linarith only [hX2, hN1]
      _ ≤ s ^ 14 * B0 := by
          have : s ^ 12 / 4096 * s ^ 2 * (259 * B0) = (259 / 4096) * (s ^ 14 * B0) := by ring
          rw [this]
          have h0 : 0 ≤ s ^ 14 * B0 := by positivity
          linarith only [h0]
  -- the output (5.12) of Theorem 5.6
  have hout : (Cdec / p) ^ p ≤ Real.exp (-ν * s / Real.log N ^ 2) / 2 := by
    set t := s / ℓ with ht
    have hp0 : (0 : ℝ) < p := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      linarith only [this]
    have hpt : t - 2 < (p : ℝ) := by
      rw [hpR]
      have : 2 * (s / (2 * ℓ)) = t := by rw [ht]; field_simp
      linarith only [hp'gt, this]
    have ht8 : 3 * Cdec + 8 ≤ t := by
      rw [ht, le_div_iff₀ hℓ0]; exact hsℓ
    have hpe : Cdec * Real.exp 1 ≤ p := by
      have h1 := Real.exp_one_lt_d9
      have h2 : Cdec * Real.exp 1 ≤ Cdec * 3 :=
        mul_le_mul_of_nonneg_left (by linarith only [h1]) hCdec.le
      linarith only [h2, hpt, ht8]
    have hq1' : Cdec / p ≤ Real.exp (-1) := by
      rw [div_le_iff₀ hp0, Real.exp_neg]
      have := mul_le_mul_of_nonneg_right hpe (inv_nonneg.2 (Real.exp_pos 1).le)
      rwa [mul_assoc, mul_inv_cancel₀ (Real.exp_pos 1).ne', mul_one, mul_comm] at this
    have h1 : (Cdec / p) ^ p ≤ Real.exp (-1) ^ p :=
      pow_le_pow_left₀ (by positivity) hq1' p
    have h2 : Real.exp (-1) ^ p = Real.exp (-(p : ℝ)) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have hνs : ν * s / Lg ^ 2 ≤ t / 2 := by
      have hsq2 : 2 * ν ≤ Real.sqrt Lg := by
        rw [show 2 * ν = Real.sqrt ((2 * ν) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
        apply Real.sqrt_le_sqrt
        have : (0 : ℝ) ≤ 2 + 4 / c1 + C2 := by positivity
        nlinarith only [hBLl, this]
      have e : ν * s / Lg ^ 2 = ν * t / Real.sqrt Lg := by
        have hs0' : 0 < Real.sqrt Lg := by linarith only [hsqL]
        have : Lg ^ 2 = ℓ * Real.sqrt Lg := by
          have h5 : ℓ = Lg * Real.sqrt Lg := hℓ
          rw [h5, mul_assoc, Real.mul_self_sqrt (by linarith only [hL2])]; ring
        rw [this, ht]
        field_simp
      rw [e, div_le_div_iff₀ (by linarith only [hsqL]) (by norm_num)]
      have ht0 : 0 ≤ t := by positivity
      nlinarith only [hsq2, ht0]
    have h3 : Real.exp (-(p : ℝ)) ≤ Real.exp (-ν * s / Real.log N ^ 2) / 2 := by
      have e : Real.exp (-ν * s / Real.log N ^ 2) / 2 =
          Real.exp (-ν * s / Real.log N ^ 2 - Real.log 2) := by
        rw [Real.exp_sub, Real.exp_log (by norm_num)]
      rw [e]
      apply Real.exp_le_exp.mpr
      have : -ν * s / Real.log N ^ 2 = -(ν * s / Lg ^ 2) := by rw [← hLg]; ring
      rw [this]
      linarith only [hνs, hpt, ht8, hlog2, hCdec]
    calc (Cdec / p) ^ p ≤ Real.exp (-1) ^ p := h1
      _ = Real.exp (-(p : ℝ)) := h2
      _ ≤ _ := h3
  -- the event `Ξ`
  set Ξ : Set (Entries N) := faXi q z g o dM with hΞ
  have hΞc : IsClosed Ξ := fa_isClosed_xi hη0.ne' q g o dM
  have hsat : ∀ i, MeasurableSet (rowSat {i} Ξ) := fun i =>
    measurableSet_rowSat_of_isClosed {i} hΞc
  have hΞm : MeasurableSet Ξ := hΞc.measurableSet
  have hΞprop : ∀ ω ∈ Ξ, (∀ a b, a ≠ b → ‖resolventC (symOfEntries ω) z a b‖ ≤ o) ∧
      (∀ a, ‖resolventC (symOfEntries ω) z a a - msc z‖ ≤ d) ∧
      ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ g := by
    rintro ω ⟨-, hg', hoff, hdg⟩
    refine ⟨hoff, fun a => ?_, hg'⟩
    calc ‖resolventC (symOfEntries ω) z a a - msc z‖
        ≤ ‖resolventC (symOfEntries ω) z a a - stieltjesM (symOfEntries ω) z‖ +
          ‖stieltjesM (symOfEntries ω) z - msc z‖ := by
          have := norm_add_le (resolventC (symOfEntries ω) z a a - stieltjesM (symOfEntries ω) z)
            (stieltjesM (symOfEntries ω) z - msc z)
          simpa using this
      _ ≤ dM + g := add_le_add (hdg a) hg'
  have hΞent : ∀ ω ∈ Ξ, ∀ a b : Fin N, |symOfEntries ω a b| ≤ q⁻¹ := fun ω hω => hω.1
  -- the probability of `Ξᶜ`
  have hzS' : ∀ {K' : ℝ}, K' ≤ K → z ∈ specDomain N K' := by
    intro K' hK'
    exact ⟨hzre, lt_of_le_of_lt (div_le_div_of_nonneg_right (sc_rpow_mono hN3 hK') hN0.le) hzK,
      hz10⟩
  have hPO := hO N hNo L q s z hL hq ((sc_rpow_mono hN3 hKo').trans hqK) (hzS' hKo') hs1 hs2
  have hPD := hDd N hNd L q s z hL hq ((sc_rpow_mono hN3 hKd').trans hqK) (hzS' hKd') hs1 hs2
  have hPΩ := hΩ N hNΩ L q s z hL hq ((sc_rpow_mono hN3 hKΩ').trans hqK) (hzS' hKΩ') hs1 hs2
  have hXic := fa_xi_compl hL.isProb hq hη0 hCo.le hCd.le hin' hPO hPD hPΩ
    ⟨by positivity, (Real.exp_pos _).le, (Real.exp_pos _).le, (Real.exp_pos _).le⟩
  have hsum : (N : ℝ) ^ A * Real.exp (-ν * s) + Real.exp (-co * s) + Real.exp (-cd * s) +
      Real.exp (-cΩ * s) ≤ Real.exp (-(ν * s / 2)) := by linarith only [hEA, hEC]
  have hΞc_le : L.law Ξᶜ ≤ ENNReal.ofReal (Real.exp (-(ν * s / 2))) :=
    hXic.trans (ENNReal.ofReal_le_ofReal hsum)
  have hΞc_dec : L.law Ξᶜ ≤
      ENNReal.ofReal (Real.exp (-(ν / 2) * Real.log N ^ ((3 : ℝ) / 2) * p)) := by
    refine hΞc_le.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    have : (ν / 2) * (ℓ * p) ≤ (ν / 2) * s := mul_le_mul_of_nonneg_left hℓp (by positivity)
    have e : -(ν / 2) * Real.log N ^ ((3 : ℝ) / 2) * p = -((ν / 2) * (ℓ * p)) := by ring
    rw [e]
    linarith only [this]
  -- Theorem 5.6
  obtain ⟨h59, h510⟩ := fa_hyp_59_510 hL.isProb hq hq1 hη0 hNη1 (by omega) Ξ hΞent Y hY1 p hp2
  have hdecN := hdec N hNdec L (fun V i => faZ z V i) Ξ p X Y hL.isProb hΞm hsat
    (even_two_mul p') hp2 hpN hX0 hY1 hX5 (fun U i hi => fa_hyp_i hL hq hη0 U i hi)
    (fun S U i hUS hiS hS => hmom Ξ o d g X Y Dg 16 Cσ p' hL hq hq1 (by omega) hzre hη0 hz10
      hsat hΞprop ho0 hd0 hX0 hDg1 (by norm_num) (by linarith only [hσ1]) hY1 hp'1 h_c1 h_Cg
      h_Dg hqX hNX hHS hC2Y hC1Y S U i hUS hiS hS) h59 h510 hΞc_dec
  -- conclusion
  have hsubF : {ω | s ^ 14 * (1 / q ^ 2 + 1 / (N * z.im) ^ 2 +
      s ^ 4 * ((msc z).im + γ z) / (N * z.im)) < ‖zAvg (symOfEntries ω) z‖} ⊆
      Ξᶜ ∪ {ω | ω ∈ Ξ ∧ (p : ℝ) ^ 12 * Y * (X ^ 2 + (N : ℝ)⁻¹) ≤
        ‖(N : ℂ)⁻¹ * ∑ i, faZ z ∅ i ω‖} := by
    intro ω hω
    by_cases hξ : ω ∈ Ξ
    · refine Or.inr ⟨hξ, ?_⟩
      have e : zAvg (symOfEntries ω) z = (N : ℂ)⁻¹ * ∑ i, faZ z ∅ i ω := by
        simp only [zAvg, fa_faZ_empty]
      have h1 : s ^ 14 * (1 / q ^ 2 + 1 / (N * z.im) ^ 2 +
          s ^ 4 * ((msc z).im + γ z) / (N * z.im)) < ‖zAvg (symOfEntries ω) z‖ := hω
      rw [e] at h1
      exact hthr.trans h1.le
    · exact Or.inl hξ
  calc L.law {ω | s ^ 14 * (1 / q ^ 2 + 1 / (N * z.im) ^ 2 +
        s ^ 4 * ((msc z).im + γ z) / (N * z.im)) < ‖zAvg (symOfEntries ω) z‖}
      ≤ L.law Ξᶜ + L.law {ω | ω ∈ Ξ ∧ (p : ℝ) ^ 12 * Y * (X ^ 2 + (N : ℝ)⁻¹) ≤
        ‖(N : ℂ)⁻¹ * ∑ i, faZ z ∅ i ω‖} := (measure_mono hsubF).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (Real.exp (-(ν * s / 2))) + ENNReal.ofReal ((Cdec / p) ^ p) :=
        add_le_add hΞc_le hdecN
    _ = ENNReal.ofReal (Real.exp (-(ν * s / 2)) + (Cdec / p) ^ p) :=
        (ENNReal.ofReal_add (Real.exp_pos _).le (by positivity)).symm
    _ ≤ ENNReal.ofReal (Real.exp (-ν * s / Real.log N ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        linarith only [hEν, hout]

/-! ### The targets -/

/-- Lemma 4.1 of [15], (4.2), at a level `s ∈ [φ^ζ, φ^{ζ+3}]`: input `(ξ, ν)`, output
`(ξ - 2, ν)` with the same `ν`; a polynomial prefactor `N^A` is allowed in the input. -/
theorem fluctuation_averaging_level {ζ C0 : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) :
    ∃ K > 0, ∃ ν0 > 0, ∀ ν > 0, ν ≤ ν0 → ∀ A ≥ (0 : ℝ), ∃ N0 : ℕ, ∀ N ≥ N0,
      ∀ (L : EntryLaws N) (q s : ℝ) (D : Set ℂ) (γ : ℂ → ℝ),
      L.IsGenWigner C0 → L.BoundedSupportAS q → phi N ^ K ≤ q →
      phi N ^ ζ ≤ s → s ≤ phi N ^ (ζ + 3) → D ⊆ specDomain N K → (∀ z ∈ D, γ z ≤ s⁻¹) →
      L.law {ω | ∃ z ∈ D, γ z < lamAvg (symOfEntries ω) z} ≤
        ENNReal.ofReal ((N : ℝ) ^ A * Real.exp (-ν * s)) →
      ∀ z ∈ D, L.law {ω | s ^ 14 * (1 / q ^ 2 + 1 / (N * z.im) ^ 2 +
          s ^ 4 * ((msc z).im + γ z) / (N * z.im)) < ‖zAvg (symOfEntries ω) z‖} ≤
        ENNReal.ofReal (Real.exp (-ν * s / Real.log N ^ 2)) := by
  exact fa_level_main hζ hC0

/-- Fluctuation averaging (Lemma 4.1 of [15]) at each `z ∈ D`. -/
theorem fluctuation_averaging {ζ C0 : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) :
    ∃ K > 0, ∀ ch > 0, ∃ c > 0, ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (L : EntryLaws N) (q : ℝ) (D : Set ℂ)
      (γ : ℂ → ℝ), L.IsGenWigner C0 → L.BoundedSupportAS q → phi N ^ K ≤ q →
      D ⊆ specDomain N K → (∀ z ∈ D, γ z ≤ (phi N ^ ζ)⁻¹) →
      L.law {ω | ∃ z ∈ D, γ z < lamAvg (symOfEntries ω) z} ≤
        ENNReal.ofReal (Real.exp (-ch * phi N ^ ζ)) →
      ∀ z ∈ D, L.law {ω | phi N ^ (14 * ζ) * (1 / q ^ 2 + 1 / (N * z.im) ^ 2 +
          phi N ^ (4 * ζ) * ((msc z).im + γ z) / (N * z.im)) < ‖zAvg (symOfEntries ω) z‖} ≤
        ENNReal.ofReal (Real.exp (-c * phi N ^ ζ / Real.log N ^ 2)) := by
  obtain ⟨K, hK, ν0, hν0, h⟩ := fluctuation_averaging_level hζ hC0
  refine ⟨K, hK, fun ch hch => ?_⟩
  obtain ⟨N0, hN0⟩ := h (min ch ν0) (lt_min hch hν0) (min_le_right _ _) 0 le_rfl
  refine ⟨min ch ν0, lt_min hch hν0, max N0 3,
    fun N hN L q D γ hL hq hqK hD hγ hin z hz => ?_⟩
  have hN3 : 3 ≤ N := le_of_max_le_right hN
  have e14 : phi N ^ (14 * ζ) = (phi N ^ ζ) ^ 14 := by
    exact_mod_cast fa_rpow_natMul hN3 ζ 14
  have e4 : phi N ^ (4 * ζ) = (phi N ^ ζ) ^ 4 := by
    exact_mod_cast fa_rpow_natMul hN3 ζ 4
  rw [e14, e4]
  refine hN0 N (le_of_max_le_left hN) L q (phi N ^ ζ) D γ hL hq hqK le_rfl
    (sc_rpow_mono hN3 (by linarith)) hD hγ (hin.trans (ENNReal.ofReal_le_ofReal ?_)) z hz
  have hφ : 0 ≤ phi N ^ ζ := (fa_rpow_pos hN3 ζ).le
  rw [Real.rpow_zero, one_mul]
  exact Real.exp_le_exp.mpr (by nlinarith [min_le_left ch ν0])

/-! ### Compiled checks -/

/-- For the Rademacher laws, `q = N^{2/5}` and `z = i`: for every `K` and all large `N` the
class, threshold and domain hypotheses hold, and the event `{Λ(i) > φ^{-2}}` has probability at
most `e^{-c φ²}` (weak local law, Theorem 3.1 of [15], at the level `ζ = 2`). -/
private lemma fa_rad_input : ∃ c > (0 : ℝ), ∀ K : ℝ, ∀ᶠ N : ℕ in atTop,
    (radLaws N).IsGenWigner 1 ∧ (radLaws N).BoundedSupportAS ((N : ℝ) ^ (2 / 5 : ℝ)) ∧
    phi N ^ K ≤ (N : ℝ) ^ (2 / 5 : ℝ) ∧ ({Complex.I} : Set ℂ) ⊆ specDomain N K ∧
    (radLaws N).law {ω | ∃ z ∈ ({Complex.I} : Set ℂ),
      (phi N ^ (2 : ℝ))⁻¹ < lamAvg (symOfEntries ω) z} ≤
      ENNReal.ofReal (Real.exp (-c * phi N ^ (2 : ℝ))) := by
  obtain ⟨Kw, -, Cw, hCw, cw, hcw, Nw, hW⟩ := weakLocalLaw (ζ := 2) two_pos zero_le_one
  refine ⟨cw, hcw, fun K => ?_⟩
  have hdom : ∀ K' : ℝ, ∀ᶠ N : ℕ in atTop, Complex.I ∈ specDomain N K' := by
    intro K'
    filter_upwards [phi_rpow_le_rpow K' (by norm_num : (0 : ℝ) < 2 / 5), eventually_ge_atTop 32]
      with N h1 h2
    have hN : (32 : ℝ) ≤ N := by exact_mod_cast h2
    have hlt : (N : ℝ) ^ (2 / 5 : ℝ) < N := by
      calc (N : ℝ) ^ (2 / 5 : ℝ) < (N : ℝ) ^ (1 : ℝ) :=
            Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
        _ = N := Real.rpow_one _
    refine ⟨by simp, ?_, by simp⟩
    rw [Complex.I_im, div_lt_one (by linarith)]
    linarith
  filter_upwards [phi_rpow_le_rpow K (by norm_num : (0 : ℝ) < 2 / 5),
    phi_rpow_le_rpow Kw (by norm_num : (0 : ℝ) < 2 / 5), hdom K, hdom Kw,
    phi_rpow_le_rpow 6 (by norm_num : (0 : ℝ) < 1 / 5),
    fa_eventually_phi (a := 1) one_pos (2 * Cw) 0, eventually_ge_atTop (max Nw 32)]
    with N h1 h2 h3 h4 h5 h6 h7
  have hN32 : 32 ≤ N := le_of_max_le_right h7
  have hN : (32 : ℝ) ≤ N := by exact_mod_cast hN32
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨hN3, h6⟩ := h6
  simp only [pow_zero, mul_one, Real.rpow_one] at h6
  have hφ0 := sc_phi_pos hN3
  have hφ1 := sc_one_le_phi hN3
  refine ⟨radLaws_isGenWigner (by omega), radLaws_boundedSupportAS hN32, h1,
    fun z hz => by rw [Set.mem_singleton_iff.mp hz]; exact h3, ?_⟩
  -- the weak local law at `z = i`
  have hb : Cw * (phi N ^ (2 : ℝ) / Real.sqrt ((N : ℝ) ^ (2 / 5 : ℝ)) +
      phi N ^ (4 * 2 / 3 : ℝ) / ((N : ℝ) * Complex.I.im) ^ ((1 : ℝ) / 3)) ≤
      (phi N ^ (2 : ℝ))⁻¹ := by
    have hN15 : (N : ℝ) ^ (1 / 5 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hsq : Real.sqrt ((N : ℝ) ^ (2 / 5 : ℝ)) = (N : ℝ) ^ (1 / 5 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]; norm_num
    have hφ6 : 0 < phi N ^ (6 : ℝ) := fa_rpow_pos hN3 6
    have k1 : phi N ^ (2 : ℝ) / Real.sqrt ((N : ℝ) ^ (2 / 5 : ℝ)) ≤
        phi N ^ (2 : ℝ) / phi N ^ (6 : ℝ) := by
      rw [hsq]
      exact div_le_div_of_nonneg_left (fa_rpow_pos hN3 _).le hφ6 h5
    have k2 : phi N ^ (4 * 2 / 3 : ℝ) / ((N : ℝ) * Complex.I.im) ^ ((1 : ℝ) / 3) ≤
        phi N ^ (3 : ℝ) / phi N ^ (6 : ℝ) := by
      rw [Complex.I_im, mul_one]
      exact div_le_div₀ (fa_rpow_pos hN3 _).le (sc_rpow_mono hN3 (by norm_num)) hφ6
        (h5.trans hN15)
    have e6 : phi N ^ (6 : ℝ) = phi N ^ (2 : ℝ) * phi N ^ (2 : ℝ) * phi N ^ (2 : ℝ) := by
      rw [← Real.rpow_add hφ0, ← Real.rpow_add hφ0]; norm_num
    have e3 : phi N ^ (3 : ℝ) = phi N ^ (2 : ℝ) * phi N := by
      rw [← Real.rpow_add_one hφ0.ne']; norm_num
    have hp2 : 0 < phi N ^ (2 : ℝ) := fa_rpow_pos hN3 _
    have e1 : phi N ^ (2 : ℝ) / phi N ^ (6 : ℝ) = (phi N ^ (2 : ℝ))⁻¹ * (phi N ^ (2 : ℝ))⁻¹ := by
      rw [e6]; field_simp
    have e2 : phi N ^ (3 : ℝ) / phi N ^ (6 : ℝ) = (phi N ^ (2 : ℝ))⁻¹ * (phi N)⁻¹ := by
      rw [e6, e3]
      have : phi N ^ (2 : ℝ) = phi N * phi N := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.rpow_add hφ0, Real.rpow_one]
      rw [this]; field_simp
    have hinv2 : (phi N ^ (2 : ℝ))⁻¹ ≤ (phi N)⁻¹ := by
      apply inv_anti₀ hφ0
      have := sc_rpow_mono hN3 (show (1 : ℝ) ≤ 2 by norm_num)
      rwa [Real.rpow_one] at this
    have hCφ : Cw * (phi N)⁻¹ ≤ 1 / 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hφ0]; linarith
    have hP2 : 0 < (phi N ^ (2 : ℝ))⁻¹ := inv_pos.mpr (fa_rpow_pos hN3 _)
    calc Cw * (phi N ^ (2 : ℝ) / Real.sqrt ((N : ℝ) ^ (2 / 5 : ℝ)) +
          phi N ^ (4 * 2 / 3 : ℝ) / ((N : ℝ) * Complex.I.im) ^ ((1 : ℝ) / 3))
        ≤ Cw * ((phi N ^ (2 : ℝ))⁻¹ * (phi N)⁻¹ + (phi N ^ (2 : ℝ))⁻¹ * (phi N)⁻¹) := by
          rw [← e2]
          refine mul_le_mul_of_nonneg_left (add_le_add (k1.trans ?_) k2) hCw.le
          rw [e1, e2]
          exact mul_le_mul_of_nonneg_left hinv2 hP2.le
      _ = (phi N ^ (2 : ℝ))⁻¹ * (2 * (Cw * (phi N)⁻¹)) := by ring
      _ ≤ (phi N ^ (2 : ℝ))⁻¹ * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ hP2.le
          linarith
      _ = (phi N ^ (2 : ℝ))⁻¹ := mul_one _
  have hsub : {ω : Entries N | ∃ z ∈ ({Complex.I} : Set ℂ),
      (phi N ^ (2 : ℝ))⁻¹ < lamAvg (symOfEntries ω) z} ⊆
      {ω : Entries N | ∃ z ∈ specDomain N Kw,
        Cw * (1 / (N : ℝ) ^ (2 / 5 : ℝ) + phi N ^ (2 * (2 : ℝ)) / Real.sqrt (N * z.im)) <
          lamO (symOfEntries ω) z ∨
        Cw * (phi N ^ (2 : ℝ) / Real.sqrt ((N : ℝ) ^ (2 / 5 : ℝ)) +
          phi N ^ (4 * 2 / 3 : ℝ) / (N * z.im) ^ ((1 : ℝ) / 3)) < lamAvg (symOfEntries ω) z} := by
    rintro ω ⟨z, hz, hlt⟩
    rw [Set.mem_singleton_iff.mp hz] at hlt
    exact ⟨Complex.I, h4, Or.inr (lt_of_le_of_lt hb hlt)⟩
  exact (measure_mono hsub).trans (hW N (le_of_max_le_left h7) (radLaws N) _
    (radLaws_isGenWigner (by omega)) (radLaws_boundedSupportAS hN32) h2)

private lemma fa_one_lt_phi {N : ℕ} (hN : 3 ≤ N) : 1 < phi N := by
  rw [phi_eq_exp hN]
  apply Real.one_lt_exp_iff.mpr
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : 1 < Real.log N := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have h2 : 0 < Real.log (Real.log N) := Real.log_pos h1
  positivity

/-- `fluctuation_averaging_level` for the Rademacher laws with `ζ = 1`, `C0 = 1`, `q = N^{2/5}`,
the level `s = φ²` strictly inside `[φ, φ⁴]`, `D = {i}`, `γ ≡ φ^{-2}` and `A = 0`: for all large
`N` every hypothesis holds (the input bound by the weak local law) and the bound applies. -/
example : ∃ K > (0 : ℝ), ∃ ν > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
    (radLaws N).IsGenWigner 1 ∧ (radLaws N).BoundedSupportAS ((N : ℝ) ^ (2 / 5 : ℝ)) ∧
    phi N ^ K ≤ (N : ℝ) ^ (2 / 5 : ℝ) ∧
    phi N ^ (1 : ℝ) < phi N ^ (2 : ℝ) ∧ phi N ^ (2 : ℝ) < phi N ^ ((1 : ℝ) + 3) ∧
    ({Complex.I} : Set ℂ) ⊆ specDomain N K ∧
    (radLaws N).law {ω | ∃ z ∈ ({Complex.I} : Set ℂ),
      (phi N ^ (2 : ℝ))⁻¹ < lamAvg (symOfEntries ω) z} ≤
      ENNReal.ofReal ((N : ℝ) ^ (0 : ℝ) * Real.exp (-ν * phi N ^ (2 : ℝ))) ∧
    (radLaws N).law {ω | (phi N ^ (2 : ℝ)) ^ 14 * (1 / ((N : ℝ) ^ (2 / 5 : ℝ)) ^ 2 +
        1 / (N * Complex.I.im) ^ 2 + (phi N ^ (2 : ℝ)) ^ 4 * ((msc Complex.I).im +
          (phi N ^ (2 : ℝ))⁻¹) / (N * Complex.I.im)) < ‖zAvg (symOfEntries ω) Complex.I‖} ≤
      ENNReal.ofReal (Real.exp (-ν * phi N ^ (2 : ℝ) / Real.log N ^ 2)) := by
  obtain ⟨K, hK, ν0, hν0, h⟩ :=
    fluctuation_averaging_level (ζ := 1) (C0 := 1) one_pos zero_le_one
  obtain ⟨c, hc, hrad⟩ := fa_rad_input
  refine ⟨K, hK, min ν0 c, lt_min hν0 hc, ?_⟩
  obtain ⟨N0, hN0⟩ := h (min ν0 c) (lt_min hν0 hc) (min_le_left _ _) 0 le_rfl
  filter_upwards [hrad K, eventually_ge_atTop (max N0 3)] with N hi hN
  obtain ⟨h1, h2, h3, h4, h5⟩ := hi
  have hN3 : 3 ≤ N := le_of_max_le_right hN
  have hφ := fa_one_lt_phi hN3
  have hlt12 : phi N ^ (1 : ℝ) < phi N ^ (2 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hφ (by norm_num)
  have hlt24 : phi N ^ (2 : ℝ) < phi N ^ ((1 : ℝ) + 3) :=
    Real.rpow_lt_rpow_of_exponent_lt hφ (by norm_num)
  have hin : (radLaws N).law {ω | ∃ z ∈ ({Complex.I} : Set ℂ),
      (phi N ^ (2 : ℝ))⁻¹ < lamAvg (symOfEntries ω) z} ≤
      ENNReal.ofReal ((N : ℝ) ^ (0 : ℝ) * Real.exp (-min ν0 c * phi N ^ (2 : ℝ))) := by
    refine h5.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [Real.rpow_zero, one_mul]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (min_le_right ν0 c) (fa_rpow_pos hN3 (2 : ℝ)).le
    linarith
  exact ⟨h1, h2, h3, hlt12, hlt24, h4, hin,
    hN0 N (le_of_max_le_left hN) (radLaws N) _ _ {Complex.I} (fun _ => (phi N ^ (2 : ℝ))⁻¹)
      h1 h2 h3 hlt12.le hlt24.le h4 (fun _ _ => le_rfl) hin Complex.I rfl⟩

/-- `fluctuation_averaging` for the Rademacher laws with `ζ = 2`, `C0 = 1`, `q = N^{2/5}`,
`D = {i}`, `γ ≡ φ^{-2}` and `c_h` the rate of the weak local law at the level `2`: for all large
`N` every hypothesis holds and the bound applies. -/
example : ∃ K > (0 : ℝ), ∃ ch > (0 : ℝ), ∃ c > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
    (radLaws N).IsGenWigner 1 ∧ (radLaws N).BoundedSupportAS ((N : ℝ) ^ (2 / 5 : ℝ)) ∧
    phi N ^ K ≤ (N : ℝ) ^ (2 / 5 : ℝ) ∧ ({Complex.I} : Set ℂ) ⊆ specDomain N K ∧
    (radLaws N).law {ω | ∃ z ∈ ({Complex.I} : Set ℂ),
      (phi N ^ (2 : ℝ))⁻¹ < lamAvg (symOfEntries ω) z} ≤
      ENNReal.ofReal (Real.exp (-ch * phi N ^ (2 : ℝ))) ∧
    (radLaws N).law {ω | phi N ^ (14 * (2 : ℝ)) * (1 / ((N : ℝ) ^ (2 / 5 : ℝ)) ^ 2 +
        1 / (N * Complex.I.im) ^ 2 + phi N ^ (4 * (2 : ℝ)) * ((msc Complex.I).im +
          (phi N ^ (2 : ℝ))⁻¹) / (N * Complex.I.im)) < ‖zAvg (symOfEntries ω) Complex.I‖} ≤
      ENNReal.ofReal (Real.exp (-c * phi N ^ (2 : ℝ) / Real.log N ^ 2)) := by
  obtain ⟨K, hK, h⟩ := fluctuation_averaging (ζ := 2) (C0 := 1) two_pos zero_le_one
  obtain ⟨ch, hch, hrad⟩ := fa_rad_input
  obtain ⟨c, hc, N0, hN0⟩ := h ch hch
  refine ⟨K, hK, ch, hch, c, hc, ?_⟩
  filter_upwards [hrad K, eventually_ge_atTop N0] with N hi hN
  obtain ⟨h1, h2, h3, h4, h5⟩ := hi
  exact ⟨h1, h2, h3, h4, h5, hN0 N hN (radLaws N) _ {Complex.I} (fun _ => (phi N ^ (2 : ℝ))⁻¹)
    h1 h2 h3 h4 (fun _ _ => le_rfl) h5 Complex.I rfl⟩

/-- `fluctAvg_omega_level` for the Rademacher laws with `ζ = 1`, `C0 = 1`, `q = N^{2/5}`, `z = i`
and the level `s = φ²` strictly inside `[φ, φ⁴]`: for all large `N` the hypotheses hold and the
bound applies. -/
example : ∃ K > (0 : ℝ), ∃ c > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
    (radLaws N).IsGenWigner 1 ∧ (radLaws N).BoundedSupportAS ((N : ℝ) ^ (2 / 5 : ℝ)) ∧
    phi N ^ K ≤ (N : ℝ) ^ (2 / 5 : ℝ) ∧ Complex.I ∈ specDomain N K ∧
    phi N ^ (1 : ℝ) < phi N ^ (2 : ℝ) ∧ phi N ^ (2 : ℝ) < phi N ^ ((1 : ℝ) + 3) ∧
    (radLaws N).law {ω | ¬ (lamD (symOfEntries ω) Complex.I + lamO (symOfEntries ω) Complex.I ≤
      (phi N ^ (2 : ℝ))⁻¹)} ≤ ENNReal.ofReal (Real.exp (-c * phi N ^ (2 : ℝ))) := by
  obtain ⟨K, hK, c, hc, N0, h⟩ := fluctAvg_omega_level (ζ := 1) (C0 := 1) one_pos zero_le_one
  obtain ⟨_, -, hrad⟩ := fa_rad_input
  refine ⟨K, hK, c, hc, ?_⟩
  filter_upwards [hrad K, eventually_ge_atTop (max N0 3)] with N hi hN
  obtain ⟨h1, h2, h3, h4, -⟩ := hi
  have hN3 : 3 ≤ N := le_of_max_le_right hN
  have hφ := fa_one_lt_phi hN3
  have hlt12 : phi N ^ (1 : ℝ) < phi N ^ (2 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hφ (by norm_num)
  have hlt24 : phi N ^ (2 : ℝ) < phi N ^ ((1 : ℝ) + 3) :=
    Real.rpow_lt_rpow_of_exponent_lt hφ (by norm_num)
  have hI : Complex.I ∈ specDomain N K := h4 rfl
  exact ⟨h1, h2, h3, hI, hlt12, hlt24, h N (le_of_max_le_left hN) (radLaws N) _ _ _ h1 h2 h3 hI
    hlt12.le hlt24.le⟩

#print axioms fluctAvg_omega_level
#print axioms fluctuation_averaging_level
#print axioms fluctuation_averaging

end WEdgeNS
