import WEdgeNS.Probability.ProductSpace

/-!
# Lindeberg telescoping over the entries
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- The ordered pairs `(x, y)` with `(I_γ)_{xy} = 1` in (6.10), for the entry `e`. -/
def entryPairs {N : ℕ} : Fin N ⊕ OffDiag N → List (Fin N × Fin N)
  | Sum.inl a => [(a, a)]
  | Sum.inr p => [(p.1.1, p.1.2), (p.1.2, p.1.1)]

/-- The matrix `I_γ` of (6.10) for the entry `e`. -/
def entryMat {N : ℕ} (e : Fin N ⊕ OffDiag N) : Matrix (Fin N) (Fin N) ℝ :=
  fun k l => if (k, l) ∈ entryPairs e then 1 else 0

namespace EntryLaws

variable {N : ℕ}

/-- The law of the entry `e`. -/
def entry (L : EntryLaws N) (e : Fin N ⊕ OffDiag N) : Measure ℝ := Sum.elim L.diag L.off e

/-- `n_k = E(-h_e)^k` (6.61). -/
def entryMoment (L : EntryLaws N) (e : Fin N ⊕ OffDiag N) (k : ℕ) : ℝ :=
  ∫ x, (-x) ^ k ∂(L.entry e)

end EntryLaws

open EntryLaws

/-- Start of row `i` in the lexicographic order of the upper index pairs. -/
private def telRow (N i : ℕ) : ℕ := i * N - i * (i - 1) / 2

private lemma telRow_succ {N i : ℕ} (hi : i < N) : telRow N (i + 1) = telRow N i + (N - i) := by
  have h2 : (i + 1) * (i + 1 - 1) / 2 = i * (i - 1) / 2 + i := by
    rcases i with _ | i
    · simp
    · have : (i + 1 + 1) * (i + 1) = i * (i + 1) + 2 * (i + 1) := by ring
      simp only [Nat.add_sub_cancel]
      rw [this, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2), Nat.mul_comm (i + 1) i]
  have h3 : i * (i - 1) / 2 ≤ i * N := by
    calc i * (i - 1) / 2 ≤ i * (i - 1) := Nat.div_le_self _ _
      _ ≤ i * N := Nat.mul_le_mul_left _ (by omega)
  unfold telRow
  rw [h2]
  have : (i + 1) * N = i * N + N := by ring
  rw [this]
  have h4 : i ≤ N := hi.le
  have h5 : i * (i - 1) / 2 + i ≤ i * N + N := by omega
  omega

private lemma telRow_mono {N : ℕ} {i i' : ℕ} (h : i ≤ i') (hi' : i' ≤ N) :
    telRow N i ≤ telRow N i' := by
  induction i', h using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    rw [telRow_succ (by omega)]
    exact (ih (by omega)).trans (Nat.le_add_right _ _)

private lemma telRow_self (N : ℕ) : telRow N N = N * (N + 1) / 2 := by
  have h1 : 2 * (N * (N - 1) / 2) = N * (N - 1) :=
    Nat.mul_div_cancel' (Nat.even_mul_pred_self N).two_dvd
  have h2 : 2 * (N * (N + 1) / 2) = N * (N + 1) :=
    Nat.mul_div_cancel' (Nat.even_mul_succ_self N).two_dvd
  have h3 : N * (N - 1) + N = N * N := by
    rcases N with _ | n
    · simp
    · simp only [Nat.add_sub_cancel]; ring
  have h4 : N * (N + 1) = N * N + N := by ring
  unfold telRow
  omega

private lemma telPos_inl (N : ℕ) (j : Fin N) : lexPos N (Sum.inl j) = telRow N j + 0 + 1 := rfl

private lemma telPos_inr (N : ℕ) (p : OffDiag N) :
    lexPos N (Sum.inr p) = telRow N p.1.1 + (p.1.2.val - p.1.1.val) + 1 := rfl

/-- Range of `lexPos`. -/
theorem lexPos_mem_Icc (N : ℕ) (e : Fin N ⊕ OffDiag N) :
    1 ≤ lexPos N e ∧ lexPos N e ≤ N * (N + 1) / 2 := by
  rw [← telRow_self]
  rcases e with j | p
  · rw [telPos_inl]
    refine ⟨by omega, ?_⟩
    have h1 := telRow_succ j.2
    have h2 := telRow_mono (N := N) (show j.val + 1 ≤ N from j.2) le_rfl
    have := j.2
    omega
  · rw [telPos_inr]
    refine ⟨by omega, ?_⟩
    have h1 := telRow_succ p.1.1.2
    have h2 := telRow_mono (N := N) (show p.1.1.val + 1 ≤ N from p.1.1.2) le_rfl
    have := p.1.2.2
    omega

/-- `lexPos` is onto `[1, N(N+1)/2]`. -/
theorem lexPos_surj (N : ℕ) : ∀ γ ∈ Finset.Icc 1 (N * (N + 1) / 2), ∃ e, lexPos N e = γ := by
  intro γ hγ
  rw [Finset.mem_Icc, ← telRow_self] at hγ
  obtain ⟨hγ1, hγ2⟩ := hγ
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp [telRow] at hγ2; omega
    · exact h
  classical
  have hex : ∃ i, γ ≤ telRow N (i + 1) := ⟨N - 1, by rwa [Nat.sub_add_cancel hN]⟩
  set i := Nat.find hex with hi
  have hP : γ ≤ telRow N (i + 1) := Nat.find_spec hex
  have hiN : i < N := by
    have : i ≤ N - 1 := Nat.find_min' hex (by rwa [Nat.sub_add_cancel hN])
    omega
  have hlt : telRow N i < γ := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · rw [h0]; simp [telRow]; omega
    · have := Nat.find_min hex (show i - 1 < i by omega)
      rw [Nat.sub_add_cancel h0] at this
      omega
  have hsucc := telRow_succ hiN
  by_cases ha : γ = telRow N i + 1
  · exact ⟨Sum.inl ⟨i, hiN⟩, by rw [telPos_inl]; simp only; omega⟩
  · have hjN : i + (γ - telRow N i - 1) < N := by omega
    have hij : (⟨i, hiN⟩ : Fin N) < ⟨i + (γ - telRow N i - 1), hjN⟩ := by
      rw [Fin.lt_def]; simp only; omega
    refine ⟨Sum.inr ⟨(⟨i, hiN⟩, ⟨i + (γ - telRow N i - 1), hjN⟩), hij⟩, ?_⟩
    rw [telPos_inr]
    simp only
    omega

/-- `H_0 = H^w`. -/
theorem interp_lexPos_zero {N : ℕ} (Lv Lw : EntryLaws N) : interp (lexPos N) 0 Lv Lw = Lw := by
  have h1 : ∀ e, ¬ lexPos N e ≤ 0 := fun e => by
    rcases e with i | p <;> simp [lexPos]
  cases Lw
  simp only [interp, h1, ite_false]

/-- `H_{γmax} = H^v`. -/
theorem interp_lexPos_top {N : ℕ} (Lv Lw : EntryLaws N) :
    interp (lexPos N) (N * (N + 1) / 2) Lv Lw = Lv := by
  have h1 : ∀ e, lexPos N e ≤ N * (N + 1) / 2 := fun e => (lexPos_mem_Icc N e).2
  cases Lv
  simp only [interp, h1, ite_true]

private lemma sum_Icc_sub_succ (f : ℕ → ℂ) (n : ℕ) :
    ∑ γ ∈ Finset.Icc 1 n, (f γ - f (γ - 1)) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; simp

/-- The telescoping sum (6.4), (6.85) over the entries. -/
theorem sub_eq_sum_lexPos {N : ℕ} (f : ℕ → ℂ) :
    f (N * (N + 1) / 2) - f 0 = ∑ e : Fin N ⊕ OffDiag N, (f (lexPos N e) - f (lexPos N e - 1)) := by
  rw [← sum_Icc_sub_succ]
  symm
  refine Finset.sum_nbij (lexPos N) (fun e _ => Finset.mem_Icc.2 (lexPos_mem_Icc N e))
    (fun a _ b _ h => lexPos_injective N h) (fun γ hγ => ?_) (fun _ _ => rfl)
  obtain ⟨e, he⟩ := lexPos_surj N γ hγ
  exact ⟨e, Finset.mem_univ _, he⟩

/-- The entries with the coordinate `e` set to `0` (the matrix `Q` of (3.24)). -/
def zeroEntry {N : ℕ} : Fin N ⊕ OffDiag N → Entries N → Entries N
  | Sum.inl i, ω => (Function.update ω.1 i 0, ω.2)
  | Sum.inr p, ω => (ω.1, Function.update ω.2 p 0)

/-- The coordinate `e` of `ω` (`v_ab` of (3.23)). -/
def entryVal {N : ℕ} (e : Fin N ⊕ OffDiag N) (ω : Entries N) : ℝ := Sum.elim ω.1 ω.2 e

/-- (3.23)–(3.24): `H = Q + v_ab I_γ`. -/
theorem symOfEntries_eq_zeroEntry_add {N : ℕ} (e : Fin N ⊕ OffDiag N) (ω : Entries N) :
    symOfEntries ω = symOfEntries (zeroEntry e ω) + entryVal e ω • entryMat e := by
  ext k l
  rcases e with a | p
  · simp only [symOfEntries, zeroEntry, entryVal, entryMat, entryPairs, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, List.mem_singleton, Prod.mk.injEq, Sum.elim_inl]
    by_cases hkl : k = l
    · subst hkl
      by_cases hka : k = a
      · subst hka; simp
      · simp [hka]
    · have h0 : ¬ (k = a ∧ l = a) := fun h => hkl (h.1.trans h.2.symm)
      simp [hkl, h0]
  · obtain ⟨⟨a, b⟩, hab⟩ := p
    simp only [symOfEntries, zeroEntry, entryVal, entryMat, entryPairs, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq,
      Sum.elim_inr]
    by_cases hkl : k = l
    · subst hkl
      have : ¬ (k = a ∧ k = b) := fun h => absurd (h.1.symm.trans h.2) (ne_of_lt hab)
      have : ¬ (k = b ∧ k = a) := fun h => absurd (h.2.symm.trans h.1) (ne_of_lt hab)
      simp [*]
    · by_cases hlt : k < l
      · by_cases hq : k = a ∧ l = b
        · obtain ⟨rfl, rfl⟩ := hq; simp [hkl, hlt]
        · have : ¬ (k = b ∧ l = a) := fun h => by
            obtain ⟨rfl, rfl⟩ := h; exact absurd hab (not_lt.2 hlt.le)
          simp [hkl, hlt, hq, this]
      · have hgt : l < k := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hkl)
        by_cases hq : k = b ∧ l = a
        · obtain ⟨rfl, rfl⟩ := hq; simp [hkl, hlt]
        · have : ¬ (k = a ∧ l = b) := fun h => by
            obtain ⟨rfl, rfl⟩ := h; exact absurd hab (not_lt.2 hgt.le)
          have hne : (⟨(l, k), hgt⟩ : OffDiag N) ≠ ⟨(a, b), hab⟩ := fun h =>
            hq ⟨congrArg (fun x : OffDiag N => x.1.2) h, congrArg (fun x : OffDiag N => x.1.1) h⟩
          simp [hkl, hlt, hq, this, Function.update_of_ne hne]

private lemma measurable_update_zero {ι : Type*} [DecidableEq ι] (e : ι) :
    Measurable (fun x : ι → ℝ => Function.update x e (0 : ℝ)) := by
  refine measurable_pi_iff.2 fun j => ?_
  by_cases h : j = e
  · subst h; simp only [Function.update_self]; exact measurable_const
  · simp only [Function.update_of_ne h]; exact measurable_pi_apply j

private lemma measurable_zeroEntry {N : ℕ} (e : Fin N ⊕ OffDiag N) : Measurable (zeroEntry e) := by
  rcases e with i | p
  · exact ((measurable_update_zero i).comp measurable_fst).prodMk measurable_snd
  · exact measurable_fst.prodMk ((measurable_update_zero p).comp measurable_snd)

private lemma measurable_entryVal {N : ℕ} (e : Fin N ⊕ OffDiag N) : Measurable (entryVal e) := by
  rcases e with i | p
  · exact (measurable_pi_apply i).comp measurable_fst
  · exact (measurable_pi_apply p).comp measurable_snd

/-- Pushing a product measure forward under "set coordinate `e` to `0`". -/
private lemma pi_map_update_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (e : ι) :
    (Measure.pi μ).map (fun x => Function.update x e (0 : ℝ)) =
      Measure.pi (Function.update μ e (Measure.dirac 0)) := by
  have hprob : ∀ i, IsProbabilityMeasure (Function.update μ e (Measure.dirac (0 : ℝ)) i) := by
    intro i
    by_cases h : i = e
    · subst h; rw [Function.update_self]; infer_instance
    · rw [Function.update_of_ne h]; infer_instance
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (measurable_update_zero e) (MeasurableSet.univ_pi hs)]
  by_cases h0 : (0 : ℝ) ∈ s e
  · have hpre : (fun x : ι → ℝ => Function.update x e (0 : ℝ)) ⁻¹' Set.pi Set.univ s =
        Set.pi Set.univ (Function.update s e Set.univ) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
      refine forall_congr' fun j => ?_
      by_cases h : j = e
      · subst h; simp [h0]
      · simp [Function.update_of_ne h]
    rw [hpre, Measure.pi_pi]
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases h : j = e
    · subst h; simp [Measure.dirac_apply' _ (hs j), h0]
    · simp [Function.update_of_ne h]
  · have hpre : (fun x : ι → ℝ => Function.update x e (0 : ℝ)) ⁻¹' Set.pi Set.univ s = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_empty_iff_false,
        iff_false, not_forall]
      exact ⟨e, by simpa using h0⟩
    rw [hpre, measure_empty]
    symm
    refine Finset.prod_eq_zero (Finset.mem_univ e) ?_
    simp [Measure.dirac_apply' _ (hs e), h0]

/-- The law of `zeroEntry e` under `L.law`: the entry `e` is replaced by a point mass at `0`. -/
private def zeroLaw {N : ℕ} (L : EntryLaws N) : Fin N ⊕ OffDiag N → Measure (Entries N)
  | Sum.inl i => (Measure.pi (Function.update L.diag i (Measure.dirac 0))).prod (Measure.pi L.off)
  | Sum.inr p => (Measure.pi L.diag).prod (Measure.pi (Function.update L.off p (Measure.dirac 0)))

private lemma law_map_zeroEntry {N : ℕ} {L : EntryLaws N} (hL : L.IsProb)
    (e : Fin N ⊕ OffDiag N) : L.law.map (zeroEntry e) = zeroLaw L e := by
  have : ∀ i, IsProbabilityMeasure (L.diag i) := hL.diag
  have : ∀ p, IsProbabilityMeasure (L.off p) := hL.off
  rcases e with i | p
  · have h : zeroEntry (Sum.inl i) =
        Prod.map (fun x : Fin N → ℝ => Function.update x i (0 : ℝ)) (id : (OffDiag N → ℝ) → _) :=
      rfl
    rw [h, EntryLaws.law, ← Measure.map_prod_map _ _ (measurable_update_zero i) measurable_id,
      pi_map_update_zero, Measure.map_id]
    rfl
  · have h : zeroEntry (Sum.inr p) =
        Prod.map (id : (Fin N → ℝ) → _) (fun x : OffDiag N → ℝ => Function.update x p (0 : ℝ)) :=
      rfl
    rw [h, EntryLaws.law, ← Measure.map_prod_map _ _ measurable_id (measurable_update_zero p),
      pi_map_update_zero, Measure.map_id]
    rfl

private lemma zeroLaw_congr {N : ℕ} {L₁ L₂ : EntryLaws N} (e : Fin N ⊕ OffDiag N)
    (h : ∀ e', e' ≠ e → L₁.entry e' = L₂.entry e') : zeroLaw L₁ e = zeroLaw L₂ e := by
  rcases e with i | p
  · have hd : Function.update L₁.diag i (Measure.dirac 0) =
        Function.update L₂.diag i (Measure.dirac 0) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]
        exact h (Sum.inl j) (fun he => hj (Sum.inl_injective he))
    have ho : L₁.off = L₂.off := funext fun q => h (Sum.inr q) (fun he => nomatch he)
    simp only [zeroLaw, hd, ho]
  · have hd : L₁.diag = L₂.diag := funext fun j => h (Sum.inl j) (fun he => nomatch he)
    have ho : Function.update L₁.off p (Measure.dirac 0) =
        Function.update L₂.off p (Measure.dirac 0) := by
      funext q
      by_cases hq : q = p
      · subst hq; simp
      · rw [Function.update_of_ne hq, Function.update_of_ne hq]
        exact h (Sum.inr q) (fun he => hq (Sum.inr_injective he))
    simp only [zeroLaw, hd, ho]

private lemma interp_isProb {N : ℕ} {Φ : Fin N ⊕ OffDiag N → ℕ} {γ : ℕ} {Lv Lw : EntryLaws N}
    (hv : Lv.IsProb) (hw : Lw.IsProb) : (interp Φ γ Lv Lw).IsProb := by
  refine ⟨fun i => ?_, fun p => ?_⟩ <;> simp only [interp] <;> split_ifs
  exacts [hv.diag i, hw.diag i, hv.off p, hw.off p]

/-- `Q` has the same law under `H_γ` and `H_{γ-1}`, `γ = lexPos N e`. -/
theorem integral_zeroEntry_interp {N : ℕ} {Lv Lw : EntryLaws N} (hv : Lv.IsProb) (hw : Lw.IsProb)
    (e : Fin N ⊕ OffDiag N) (f : Entries N → ℂ) (hf : Measurable f) :
    ∫ ω, f (zeroEntry e ω) ∂(interp (lexPos N) (lexPos N e) Lv Lw).law =
      ∫ ω, f (zeroEntry e ω) ∂(interp (lexPos N) (lexPos N e - 1) Lv Lw).law := by
  have h1 := interp_isProb (Φ := lexPos N) (γ := lexPos N e) hv hw
  have h2 := interp_isProb (Φ := lexPos N) (γ := lexPos N e - 1) hv hw
  rw [← integral_map (measurable_zeroEntry e).aemeasurable hf.aestronglyMeasurable,
    ← integral_map (measurable_zeroEntry e).aemeasurable hf.aestronglyMeasurable,
    law_map_zeroEntry h1, law_map_zeroEntry h2]
  have hc : zeroLaw (interp (lexPos N) (lexPos N e) Lv Lw) e =
      zeroLaw (interp (lexPos N) (lexPos N e - 1) Lv Lw) e := by
    refine zeroLaw_congr e fun e' hne => ?_
    have hlt : lexPos N e' ≠ lexPos N e := fun h => hne (lexPos_injective N h)
    have hge := (lexPos_mem_Icc N e).1
    have hiff : lexPos N e' ≤ lexPos N e ↔ lexPos N e' ≤ lexPos N e - 1 := by omega
    rcases e' with j | q
    · simp only [EntryLaws.entry, interp, Sum.elim_inl, hiff]
    · simp only [EntryLaws.entry, interp, Sum.elim_inr, hiff]
  rw [hc]

private lemma entryCoord_eq_entryVal {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    EntryLaws.entryCoord e = entryVal e := by
  funext ω; cases e <;> rfl

/-- The law of the coordinate `e` under `L.law` is `L.entry e`. -/
private lemma map_entryVal {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) (e : Fin N ⊕ OffDiag N) :
    L.law.map (entryVal e) = L.entry e := by
  have : ∀ i, IsProbabilityMeasure (L.diag i) := hL.diag
  have : ∀ p, IsProbabilityMeasure (L.off p) := hL.off
  have : IsProbabilityMeasure (Measure.pi L.diag) := inferInstance
  have : IsProbabilityMeasure (Measure.pi L.off) := inferInstance
  rcases e with i | p
  · exact ((measurePreserving_eval L.diag i).comp
      (measurePreserving_fst (μ := Measure.pi L.diag) (ν := Measure.pi L.off))).map_eq
  · exact ((measurePreserving_eval L.off p).comp
      (measurePreserving_snd (μ := Measure.pi L.diag) (ν := Measure.pi L.off))).map_eq

/-- Rebuild the entries from the coordinates other than `e`, with `0` at `e`. -/
private def fillEntries {N : ℕ} (e : Fin N ⊕ OffDiag N)
    (y : ((({e} : Finset (Fin N ⊕ OffDiag N))ᶜ : Finset _)) → ℝ) : Entries N :=
  (fun i => if h : Sum.inl i ∈ (({e} : Finset (Fin N ⊕ OffDiag N))ᶜ : Finset _)
      then y ⟨Sum.inl i, h⟩ else 0,
   fun p => if h : Sum.inr p ∈ (({e} : Finset (Fin N ⊕ OffDiag N))ᶜ : Finset _)
      then y ⟨Sum.inr p, h⟩ else 0)

private lemma measurable_fillEntries {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    Measurable (fillEntries e) := by
  refine Measurable.prodMk (measurable_pi_iff.2 fun i => ?_) (measurable_pi_iff.2 fun p => ?_)
  · by_cases h : Sum.inl i ∈ (({e} : Finset (Fin N ⊕ OffDiag N))ᶜ : Finset _)
    · simp only [h, dite_true]; exact measurable_pi_apply _
    · simp only [h, dite_false]; exact measurable_const
  · by_cases h : Sum.inr p ∈ (({e} : Finset (Fin N ⊕ OffDiag N))ᶜ : Finset _)
    · simp only [h, dite_true]; exact measurable_pi_apply _
    · simp only [h, dite_false]; exact measurable_const

private lemma fillEntries_coord {N : ℕ} (e : Fin N ⊕ OffDiag N) (ω : Entries N) :
    fillEntries e (fun i => EntryLaws.entryCoord i.1 ω) = zeroEntry e ω := by
  rcases e with a | q
  · refine Prod.ext (funext fun i => ?_) ?_
    · by_cases h : i = a
      · subst h; simp [fillEntries, zeroEntry]
      · simp [fillEntries, zeroEntry, h, EntryLaws.entryCoord]
    · funext p; simp [fillEntries, zeroEntry, EntryLaws.entryCoord]
  · refine Prod.ext ?_ (funext fun p => ?_)
    · funext i; simp [fillEntries, zeroEntry, EntryLaws.entryCoord]
    · by_cases h : p = q
      · subst h; simp [fillEntries, zeroEntry]
      · simp [fillEntries, zeroEntry, h, EntryLaws.entryCoord]

private lemma measurable_entryCoord {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    Measurable (EntryLaws.entryCoord e) := by
  rw [entryCoord_eq_entryVal]; exact measurable_entryVal e

/-- Partial expectation `E_ab`: `Q` and `v_ab` are independent. -/
theorem integral_mul_zeroEntry {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) (e : Fin N ⊕ OffDiag N)
    (f : Entries N → ℂ) (k : ℕ) (hfm : Measurable f)
    (hf : Integrable (fun ω => f (zeroEntry e ω)) L.law)
    (hk : Integrable (fun x : ℝ => x ^ k) (L.entry e)) :
    ∫ ω, f (zeroEntry e ω) * ((-entryVal e ω) ^ k : ℝ) ∂L.law =
      (∫ ω, f (zeroEntry e ω) ∂L.law) * (L.entryMoment e k : ℂ) := by
  -- the product formula for independent random variables needs no integrability
  have _ := And.intro hf hk
  have hprob := isProbabilityMeasure_law hL
  have hind := (iIndepFun_entryCoord hL).indepFun_finset ({e} : Finset (Fin N ⊕ OffDiag N))
    ({e} : Finset (Fin N ⊕ OffDiag N))ᶜ disjoint_compl_right measurable_entryCoord
  have hφ : Measurable (fun y : (({e} : Finset (Fin N ⊕ OffDiag N)) : Finset _) → ℝ =>
      (((-y ⟨e, Finset.mem_singleton_self e⟩) ^ k : ℝ) : ℂ)) := by
    have : Measurable (fun y : (({e} : Finset (Fin N ⊕ OffDiag N)) : Finset _) → ℝ =>
        (-y ⟨e, Finset.mem_singleton_self e⟩) ^ k) :=
      ((measurable_pi_apply _).neg).pow_const k
    exact Complex.measurable_ofReal.comp this
  have hψ : Measurable (fun y : ((({e} : Finset (Fin N ⊕ OffDiag N))ᶜ : Finset _)) → ℝ =>
      f (fillEntries e y)) := hfm.comp (measurable_fillEntries e)
  have hind' := (hind.comp hφ hψ).symm
  have hfun : (fun y : ((({e} : Finset (Fin N ⊕ OffDiag N))ᶜ : Finset _)) → ℝ =>
      f (fillEntries e y)) ∘ (fun ω (i : (({e} : Finset (Fin N ⊕ OffDiag N))ᶜ : Finset _)) =>
        EntryLaws.entryCoord i.1 ω) = fun ω => f (zeroEntry e ω) := by
    funext ω; simp only [Function.comp, fillEntries_coord]
  have hfun2 : (fun y : (({e} : Finset (Fin N ⊕ OffDiag N)) : Finset _) → ℝ =>
      (((-y ⟨e, Finset.mem_singleton_self e⟩) ^ k : ℝ) : ℂ)) ∘
      (fun ω (i : (({e} : Finset (Fin N ⊕ OffDiag N)) : Finset _)) => EntryLaws.entryCoord i.1 ω)
      = fun ω => (((-entryVal e ω) ^ k : ℝ) : ℂ) := by
    funext ω; simp only [Function.comp, entryCoord_eq_entryVal]
  rw [hfun, hfun2] at hind'
  have hX : AEStronglyMeasurable (fun ω => f (zeroEntry e ω)) L.law :=
    (hfm.comp (measurable_zeroEntry e)).aestronglyMeasurable
  have hY : AEStronglyMeasurable (fun ω => (((-entryVal e ω) ^ k : ℝ) : ℂ)) L.law :=
    (Complex.measurable_ofReal.comp
      (((measurable_entryVal e).neg).pow_const k)).aestronglyMeasurable
  rw [hind'.integral_fun_mul_eq_mul_integral hX hY]
  congr 1
  refine (integral_ofReal (𝕜 := ℂ)).trans ?_
  congr 1
  rw [← map_entryVal hL e]
  exact (integral_map (f := fun x : ℝ => (-x) ^ k) (measurable_entryVal e).aemeasurable
    (((measurable_id.neg).pow_const k).aestronglyMeasurable)).symm

/-! ### Compiled instances at `N = 2` with the Rademacher-type and the Gaussian entry laws -/

/-- The upper entry `(0, 1)` of a `2 × 2` matrix. -/
private def telE : Fin 2 ⊕ OffDiag 2 := Sum.inr ⟨(0, 1), by decide⟩

private lemma lexPos_telE : lexPos 2 telE = 2 := by decide

private lemma radLaws_two_isProb : (radLaws 2).IsProb :=
  (radLaws_isGenWigner (by norm_num)).isProb

private lemma goeLaws_two_isProb : (goeLaws 2).IsProb :=
  (ofIID_isGenWigner goe_wignerLaws (N := 2) (by norm_num)).isProb

/-- The bounded measurable function `ω ↦ exp(i h_11)` of the diagonal entry `h_11`. -/
private def telExp : Entries 2 → ℂ := fun ω => Complex.exp (Complex.I * ((ω.1 1 : ℝ) : ℂ))

private lemma measurable_telExp : Measurable telExp := by
  unfold telExp; fun_prop

/-- The two entry laws of the upper entry `(0, 1)` differ: the Rademacher-type law has an atom
at `2^{-1/2}`, the Gaussian law has none. -/
private lemma entry_telE_ne : (radLaws 2).entry telE ≠ (goeLaws 2).entry telE := by
  have hc : (Real.sqrt ((2 : ℕ) : ℝ))⁻¹ ≠ 0 := by positivity
  have hm : Measurable (fun x : ℝ => (Real.sqrt ((2 : ℕ) : ℝ))⁻¹ * x) := by fun_prop
  have hpre : (fun x : ℝ => (Real.sqrt ((2 : ℕ) : ℝ))⁻¹ * x) ⁻¹'
      {(Real.sqrt ((2 : ℕ) : ℝ))⁻¹ * 1} = {1} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact mul_right_inj' hc
  have hg : gaussianReal 0 1 {(1 : ℝ)} = 0 :=
    haveI := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    measure_singleton 1
  intro h
  have h1 := congrArg (fun m : Measure ℝ => m {(Real.sqrt ((2 : ℕ) : ℝ))⁻¹ * 1}) h
  simp only [telE, EntryLaws.entry, radLaws, goeLaws, ofIID, Sum.elim_inr] at h1
  rw [Measure.map_apply hm (measurableSet_singleton _), hpre,
    Measure.map_apply hm (measurableSet_singleton _), hpre, hg] at h1
  simp [rademacher, Measure.dirac_apply' _ (measurableSet_singleton _)] at h1

/-- `integral_zeroEntry_interp` at `N = 2`, `e = (0, 1)` (`γ = 2`): `H_2` and `H_1` differ in the
law of `h_01` (Rademacher-type against Gaussian), and `f = exp(i h_11)` is bounded. -/
example :
    (∫ ω, telExp (zeroEntry telE ω)
        ∂(interp (lexPos 2) (lexPos 2 telE) (radLaws 2) (goeLaws 2)).law =
      ∫ ω, telExp (zeroEntry telE ω)
        ∂(interp (lexPos 2) (lexPos 2 telE - 1) (radLaws 2) (goeLaws 2)).law) ∧
    (interp (lexPos 2) (lexPos 2 telE) (radLaws 2) (goeLaws 2)).entry telE ≠
      (interp (lexPos 2) (lexPos 2 telE - 1) (radLaws 2) (goeLaws 2)).entry telE := by
  refine ⟨integral_zeroEntry_interp radLaws_two_isProb goeLaws_two_isProb telE telExp
    measurable_telExp, ?_⟩
  rw [lexPos_telE]
  simpa [telE, EntryLaws.entry, interp, lexPos] using entry_telE_ne

/-- The indicator of `h_00 > 0`, a bounded measurable function of the diagonal entry `h_00`. -/
private def telInd : Entries 2 → ℂ := fun ω => if 0 < ω.1 0 then 1 else 0

private lemma measurable_telInd : Measurable telInd :=
  Measurable.ite (measurableSet_lt measurable_const ((measurable_pi_apply 0).comp measurable_fst))
    measurable_const measurable_const

private lemma integral_telInd : ∫ ω, telInd ω ∂(radLaws 2).law = 1 / 2 := by
  have hp := isProbabilityMeasure_law radLaws_two_isProb
  have hS : MeasurableSet {ω : Entries 2 | 0 < ω.1 0} :=
    measurableSet_lt measurable_const ((measurable_pi_apply 0).comp measurable_fst)
  have h1 : telInd = fun ω =>
      (({ω : Entries 2 | 0 < ω.1 0}.indicator (fun _ => (1 : ℝ)) ω : ℝ) : ℂ) := by
    funext ω
    by_cases h : 0 < ω.1 0 <;> simp [telInd, Set.indicator, h]
  have h2 : (radLaws 2).law {ω : Entries 2 | 0 < ω.1 0} = (radLaws 2).diag 0 (Set.Ioi 0) := by
    have := radLaws_two_isProb.diag
    have := radLaws_two_isProb.off
    exact ((measurePreserving_eval (radLaws 2).diag 0).comp
      (measurePreserving_fst (μ := Measure.pi (radLaws 2).diag)
        (ν := Measure.pi (radLaws 2).off))).measure_preimage measurableSet_Ioi.nullMeasurableSet
  have h3 : (radLaws 2).diag 0 (Set.Ioi 0) = 2⁻¹ := by
    have hc : 0 < (Real.sqrt ((2 : ℕ) : ℝ))⁻¹ := by positivity
    have hd : 0 < Real.sqrt 2 := by positivity
    have hm1 : Measurable (fun x : ℝ => Real.sqrt 2 * x) := by fun_prop
    have hm2 : Measurable (fun x : ℝ => (Real.sqrt ((2 : ℕ) : ℝ))⁻¹ * x) := by fun_prop
    have hpre1 : (fun x : ℝ => (Real.sqrt ((2 : ℕ) : ℝ))⁻¹ * x) ⁻¹' Set.Ioi 0 = Set.Ioi 0 := by
      ext x; simp
    have hpre2 : (fun x : ℝ => Real.sqrt 2 * x) ⁻¹' Set.Ioi 0 = Set.Ioi 0 := by
      ext x; simp
    change ((rademacher.map (fun x : ℝ => Real.sqrt 2 * x)).map
      (fun x : ℝ => (Real.sqrt ((2 : ℕ) : ℝ))⁻¹ * x)) (Set.Ioi 0) = 2⁻¹
    rw [Measure.map_apply hm2 measurableSet_Ioi, hpre1, Measure.map_apply hm1 measurableSet_Ioi,
      hpre2]
    simp [rademacher, Measure.dirac_apply' _ measurableSet_Ioi]
  have h4 : ∫ ω, {ω : Entries 2 | 0 < ω.1 0}.indicator (fun _ => (1 : ℝ)) ω ∂(radLaws 2).law =
      1 / 2 := by
    rw [integral_indicator_const _ hS, Measure.real, h2, h3]
    simp
  have h5 := integral_ofReal (𝕜 := ℂ) (μ := (radLaws 2).law)
    (f := fun ω => {ω : Entries 2 | 0 < ω.1 0}.indicator (fun _ => (1 : ℝ)) ω)
  rw [h1]
  refine h5.trans ?_
  rw [h4]
  push_cast
  rfl

/-- `integral_mul_zeroEntry` at `N = 2`, `e = (0, 1)`, `k = 2`, `f = 1_{h_00 > 0}` under the
Rademacher-type law: both factors are `1/2`, so both sides are `1/4`. -/
example :
    (∫ ω, telInd (zeroEntry telE ω) * ((-entryVal telE ω) ^ 2 : ℝ) ∂(radLaws 2).law =
      (∫ ω, telInd (zeroEntry telE ω) ∂(radLaws 2).law) *
        ((radLaws 2).entryMoment telE 2 : ℂ)) ∧
    (radLaws 2).entryMoment telE 2 = 1 / 2 ∧
    ∫ ω, telInd (zeroEntry telE ω) ∂(radLaws 2).law = 1 / 2 := by
  have hp := isProbabilityMeasure_law radLaws_two_isProb
  refine ⟨integral_mul_zeroEntry radLaws_two_isProb telE telInd 2 measurable_telInd ?_ ?_, ?_, ?_⟩
  · refine Integrable.of_bound (C := 1)
      (measurable_telInd.comp (measurable_zeroEntry telE)).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    change ‖telInd (zeroEntry telE ω)‖ ≤ 1
    unfold telInd
    split_ifs <;> simp
  · exact (radLaws_isGenWigner (by norm_num : 0 < 2)).sq_int_off ⟨(0, 1), by decide⟩
  · have h := (radLaws_isGenWigner (by norm_num : 0 < 2)).var_off ⟨(0, 1), by decide⟩
    simp only [EntryLaws.entryMoment, telE, EntryLaws.entry, Sum.elim_inr, neg_sq]
    rw [h]
    norm_num
  · exact integral_telInd

#print axioms lexPos_mem_Icc
#print axioms lexPos_surj
#print axioms interp_lexPos_zero
#print axioms interp_lexPos_top
#print axioms sub_eq_sum_lexPos
#print axioms symOfEntries_eq_zeroEntry_add
#print axioms integral_zeroEntry_interp
#print axioms integral_mul_zeroEntry

end WEdgeNS
