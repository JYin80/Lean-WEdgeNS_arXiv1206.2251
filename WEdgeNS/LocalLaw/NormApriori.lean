import WEdgeNS.Probability.ProductSpace
import WEdgeNS.Probability.LargeDeviation

/-!
# An a priori bound on the norm
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-! ### Walks: classification of the steps and an injective encoding

This section counts the walks of the expansion (A.25)–(A.26) in the proof of Lemma 4.3 of [15]
directly, by an encoding of their steps.

For a walk `W : ℕ → V` the step `t` goes from `W t` to `W (t + 1)` along the edge
`s(W t, W (t + 1))`. A step is *new* if it reaches an unvisited vertex. An edge of a new step is
*open* at time `t` if it has been used exactly once before `t`. A step that is not new and runs
along an open edge is a *minus* step; it is a *back* step if, moreover, at most one open edge
contains the current vertex. Every step that is neither new nor back is recorded by the time of an
earlier visit of its target. For a walk using each of its edges at least twice, with `n` new
steps, at most `2(k - 2n)` steps are recorded this way (`walk_counts`). -/

section Walk

variable {V : Type*} [DecidableEq V]

/-- The vertices `W 0, …, W t`. -/
private def wVis (W : ℕ → V) (t : ℕ) : Finset V := (Finset.range (t + 1)).image W

/-- The edge of the step `t`. -/
private def wEdge (W : ℕ → V) (t : ℕ) : Sym2 V := s(W t, W (t + 1))

/-- The step `t` reaches a vertex not among `W 0, …, W t`. -/
private abbrev wNew (W : ℕ → V) (t : ℕ) : Prop := W (t + 1) ∉ wVis W t

/-- The number of steps before `t` along the edge `e`. -/
private def wUses (W : ℕ → V) (e : Sym2 V) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun τ => wEdge W τ = e)).card

/-- The edges of new steps before `t` that are used exactly once before `t`. -/
private def wOpen (W : ℕ → V) (t : ℕ) : Finset (Sym2 V) :=
  (((Finset.range t).filter (fun τ => wNew W τ)).image (wEdge W)).filter
    (fun e => wUses W e t = 1)

/-- The number of open edges at time `t` containing `v`. -/
private def wDeg (W : ℕ → V) (t : ℕ) (v : V) : ℕ := ((wOpen W t).filter (fun e => v ∈ e)).card

private abbrev wMinus (W : ℕ → V) (t : ℕ) : Prop := ¬ wNew W t ∧ wEdge W t ∈ wOpen W t

private abbrev wBack (W : ℕ → V) (t : ℕ) : Prop := wMinus W t ∧ wDeg W t (W t) < 2

private abbrev wU (W : ℕ → V) (t : ℕ) : Prop := ¬ wNew W t ∧ ¬ wMinus W t

private abbrev wAmb (W : ℕ → V) (t : ℕ) : Prop := wMinus W t ∧ 2 ≤ wDeg W t (W t)

private lemma mem_wVis {W : ℕ → V} {t : ℕ} {v : V} : v ∈ wVis W t ↔ ∃ τ ≤ t, W τ = v := by
  simp [wVis]

private lemma self_mem_wVis (W : ℕ → V) {τ t : ℕ} (h : τ ≤ t) : W τ ∈ wVis W t :=
  mem_wVis.2 ⟨τ, h, rfl⟩

/-- A new step does not repeat an earlier edge. -/
private lemma wEdge_ne_of_new {W : ℕ → V} {τ t : ℕ} (hn : wNew W t) (hτ : τ < t) :
    wEdge W τ ≠ wEdge W t := by
  intro h
  have hm : W (t + 1) ∈ wEdge W τ := h ▸ Sym2.mem_mk_right _ _
  rcases Sym2.mem_iff.1 hm with h1 | h1
  · exact hn (mem_wVis.2 ⟨τ, by omega, h1.symm⟩)
  · exact hn (mem_wVis.2 ⟨τ + 1, by omega, h1.symm⟩)

private lemma wNew_ne {W : ℕ → V} {t : ℕ} (hn : wNew W t) : W t ≠ W (t + 1) :=
  fun h => hn (h ▸ self_mem_wVis W le_rfl)

private lemma wUses_succ (W : ℕ → V) (e : Sym2 V) (t : ℕ) :
    wUses W e (t + 1) = wUses W e t + if wEdge W t = e then 1 else 0 := by
  unfold wUses
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

private lemma mem_wOpen {W : ℕ → V} {t : ℕ} {e : Sym2 V} :
    e ∈ wOpen W t ↔ (∃ τ < t, wNew W τ ∧ wEdge W τ = e) ∧ wUses W e t = 1 := by
  simp only [wOpen, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨τ, ⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨⟨τ, h1, h2, h3⟩, h4⟩
  · rintro ⟨⟨τ, h1, h2, h3⟩, h4⟩
    exact ⟨⟨τ, ⟨h1, h2⟩, h3⟩, h4⟩

private lemma one_le_wUses {W : ℕ → V} {t : ℕ} {e : Sym2 V}
    (h : ∃ τ < t, wNew W τ ∧ wEdge W τ = e) : 1 ≤ wUses W e t := by
  obtain ⟨τ, hτ, -, he⟩ := h
  exact Finset.card_pos.2 ⟨τ, by simp [hτ, he]⟩

private lemma wUses_new {W : ℕ → V} {t : ℕ} (hn : wNew W t) : wUses W (wEdge W t) t = 0 := by
  unfold wUses
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro τ hτ
  exact wEdge_ne_of_new hn (Finset.mem_range.1 hτ)

private lemma tree_succ_iff {W : ℕ → V} {t : ℕ} {e : Sym2 V} :
    (∃ τ < t + 1, wNew W τ ∧ wEdge W τ = e) ↔
      (∃ τ < t, wNew W τ ∧ wEdge W τ = e) ∨ (wNew W t ∧ wEdge W t = e) := by
  constructor
  · rintro ⟨τ, hτ, h⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hτ with h' | rfl
    · exact Or.inl ⟨τ, h', h⟩
    · exact Or.inr h
  · rintro (⟨τ, hτ, h⟩ | h)
    · exact ⟨τ, by omega, h⟩
    · exact ⟨t, by omega, h⟩

private lemma wOpen_succ_new {W : ℕ → V} {t : ℕ} (hn : wNew W t) :
    wOpen W (t + 1) = insert (wEdge W t) (wOpen W t) := by
  ext e
  rw [mem_wOpen, Finset.mem_insert, mem_wOpen, wUses_succ, tree_succ_iff]
  by_cases he : wEdge W t = e
  · subst he
    simp only [wUses_new hn, ite_true, zero_add, true_or, and_true]
    exact iff_of_true (Or.inr hn) trivial
  · have he' : e ≠ wEdge W t := Ne.symm he
    simp only [he, ite_false, add_zero, and_false, or_false, he', false_or]

private lemma wOpen_succ_minus {W : ℕ → V} {t : ℕ} (hm : wMinus W t) :
    wOpen W (t + 1) = (wOpen W t).erase (wEdge W t) := by
  ext e
  rw [mem_wOpen, Finset.mem_erase, mem_wOpen, wUses_succ, tree_succ_iff]
  by_cases he : wEdge W t = e
  · subst he
    have h1 := (mem_wOpen.1 hm.2).2
    simp only [h1, ite_true, ne_eq, not_true_eq_false, false_and, iff_false, not_and]
    intro _
    omega
  · have he' : e ≠ wEdge W t := Ne.symm he
    simp only [he, ite_false, add_zero, and_false, or_false, he', ne_eq, not_false_eq_true,
      true_and]

private lemma wOpen_succ_U {W : ℕ → V} {t : ℕ} (hu : wU W t) : wOpen W (t + 1) = wOpen W t := by
  ext e
  rw [mem_wOpen, mem_wOpen, wUses_succ, tree_succ_iff]
  by_cases he : wEdge W t = e
  · subst he
    have hno : wEdge W t ∉ wOpen W t := fun h => hu.2 ⟨hu.1, h⟩
    rw [mem_wOpen] at hno
    simp only [hu.1, false_and, or_false, ite_true]
    constructor
    · rintro ⟨h1, h2⟩
      have := one_le_wUses h1
      omega
    · intro h
      exact absurd h hno
  · simp only [he, ite_false, add_zero, and_false, or_false]

private lemma mem_wVis_of_mem_wOpen {W : ℕ → V} {t : ℕ} {e : Sym2 V} {v : V}
    (he : e ∈ wOpen W t) (hv : v ∈ e) : v ∈ wVis W t := by
  obtain ⟨⟨τ, hτ, -, rfl⟩, -⟩ := mem_wOpen.1 he
  rcases Sym2.mem_iff.1 hv with rfl | rfl
  · exact self_mem_wVis W (by omega)
  · exact self_mem_wVis W (by omega)

private lemma wDeg_succ_new {W : ℕ → V} {t : ℕ} (hn : wNew W t) (v : V) :
    wDeg W (t + 1) v = wDeg W t v + if v ∈ wEdge W t then 1 else 0 := by
  have hno : wEdge W t ∉ wOpen W t := by
    intro h
    have := (mem_wOpen.1 h).2
    rw [wUses_new hn] at this
    omega
  unfold wDeg
  rw [wOpen_succ_new hn, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun h' => hno (Finset.mem_filter.1 h').1)]
  · rfl

private lemma wDeg_succ_minus {W : ℕ → V} {t : ℕ} (hm : wMinus W t) (v : V) :
    wDeg W (t + 1) v + (if v ∈ wEdge W t then 1 else 0) = wDeg W t v := by
  unfold wDeg
  rw [wOpen_succ_minus hm, Finset.filter_erase]
  split_ifs with h
  · rw [Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨hm.2, h⟩)]
    have : 0 < ((wOpen W t).filter (fun e => v ∈ e)).card :=
      Finset.card_pos.2 ⟨_, Finset.mem_filter.2 ⟨hm.2, h⟩⟩
    omega
  · rw [Finset.erase_eq_of_notMem (s := (wOpen W t).filter (fun e => v ∈ e)) (a := wEdge W t)
      (fun h' => h (Finset.mem_filter.1 h').2)]
    rfl

private lemma wDeg_succ_U {W : ℕ → V} {t : ℕ} (hu : wU W t) (v : V) :
    wDeg W (t + 1) v = wDeg W t v := by
  unfold wDeg
  rw [wOpen_succ_U hu]

private lemma wDeg_eq_zero_of_not_mem {W : ℕ → V} {t : ℕ} {v : V} (hv : v ∉ wVis W t) :
    wDeg W t v = 0 := by
  unfold wDeg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun e he hve => hv (mem_wVis_of_mem_wOpen he hve)

/-- The edge of a minus step joins two distinct vertices. -/
private lemma wMinus_ne {W : ℕ → V} {t : ℕ} (hm : wMinus W t) : W t ≠ W (t + 1) := by
  obtain ⟨⟨τ, -, hn, he⟩, -⟩ := mem_wOpen.1 hm.2
  intro h
  have hd : (wEdge W t).IsDiag := by
    unfold wEdge
    rw [Sym2.mk_isDiag_iff]
    exact h
  rw [← he] at hd
  unfold wEdge at hd
  rw [Sym2.mk_isDiag_iff] at hd
  exact wNew_ne hn hd

/-- The open edges at time `t` depend only on `W 0, …, W t`. -/
private lemma wOpen_congr {W W' : ℕ → V} {t : ℕ} (h : ∀ τ ≤ t, W τ = W' τ) :
    wOpen W t = wOpen W' t := by
  have hv : ∀ τ ≤ t, wVis W τ = wVis W' τ := fun τ hτ => by
    unfold wVis
    exact Finset.image_congr (fun s hs => h s (by simp at hs; omega))
  have he : ∀ τ < t, wEdge W τ = wEdge W' τ := fun τ hτ => by
    unfold wEdge
    rw [h τ (by omega), h (τ + 1) (by omega)]
  have hn : ∀ τ < t, (wNew W τ ↔ wNew W' τ) := fun τ hτ => by
    simp only [wNew]
    rw [hv τ (by omega), h (τ + 1) (by omega)]
  have hu : ∀ e, wUses W e t = wUses W' e t := fun e => by
    unfold wUses
    congr 1
    exact Finset.filter_congr (fun τ hτ => by rw [he τ (Finset.mem_range.1 hτ)])
  unfold wOpen
  have h1 : (Finset.range t).filter (fun τ => wNew W τ) =
      (Finset.range t).filter (fun τ => wNew W' τ) :=
    Finset.filter_congr (fun τ hτ => hn τ (Finset.mem_range.1 hτ))
  rw [h1]
  have h2 : ((Finset.range t).filter (fun τ => wNew W' τ)).image (wEdge W) =
      ((Finset.range t).filter (fun τ => wNew W' τ)).image (wEdge W') :=
    Finset.image_congr (fun τ hτ =>
      he τ (Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hτ)).1))
  rw [h2]
  exact Finset.filter_congr (fun e _ => by rw [hu e])

/-- The code of the step `t < k`: the new vertex, a back step, or the time of an earlier visit of
the target. -/
private def wCode (W : ℕ → V) (k : ℕ) (t : Fin k) : Option (V ⊕ Fin k) :=
  if wNew W t then some (Sum.inl (W (t + 1)))
  else if wBack W t then none
  else some (Sum.inr ⟨Nat.findGreatest (fun τ => W τ = W (t + 1)) t,
    lt_of_le_of_lt (Nat.findGreatest_le _) t.isLt⟩)

private lemma findGreatest_visit {W : ℕ → V} {t : ℕ} (hn : ¬ wNew W t) :
    W (Nat.findGreatest (fun τ => W τ = W (t + 1)) t) = W (t + 1) := by
  obtain ⟨τ, hτ, he⟩ := mem_wVis.1 (not_not.1 hn)
  exact Nat.findGreatest_spec (P := fun τ => W τ = W (t + 1)) hτ he

/-- The start and the codes of the steps determine the walk up to time `k`. -/
private lemma wCode_inj {W W' : ℕ → V} {k : ℕ} (h0 : W 0 = W' 0)
    (hc : wCode W k = wCode W' k) : ∀ t ≤ k, W t = W' t := by
  have key : ∀ t ≤ k, ∀ τ ≤ t, W τ = W' τ := by
    intro t
    induction t with
    | zero =>
      intro _ τ hτ
      rw [Nat.le_zero.1 hτ]
      exact h0
    | succ t ih =>
      intro ht τ hτ
      have hpre := ih (by omega)
      rcases Nat.lt_or_eq_of_le hτ with hτ' | rfl
      · exact hpre τ (by omega)
      have hct := congrFun hc ⟨t, by omega⟩
      have hW : W t = W' t := hpre t le_rfl
      simp only [wCode] at hct
      by_cases h1 : wNew W t <;> by_cases h1' : wNew W' t
      · rw [ite_eq_left h1, ite_eq_left h1'] at hct
        simpa using hct
      · rw [ite_eq_left h1, ite_eq_right h1'] at hct
        split_ifs at hct
        simp at hct
      · rw [ite_eq_right h1, ite_eq_left h1'] at hct
        split_ifs at hct
        simp at hct
      · rw [ite_eq_right h1, ite_eq_right h1'] at hct
        by_cases h2 : wBack W t <;> by_cases h2' : wBack W' t
        · have hO := wOpen_congr hpre
          have e1 : wEdge W t ∈ (wOpen W t).filter (fun e => W t ∈ e) :=
            Finset.mem_filter.2 ⟨h2.1.2, Sym2.mem_mk_left _ _⟩
          have e2 : wEdge W' t ∈ (wOpen W t).filter (fun e => W t ∈ e) := by
            refine Finset.mem_filter.2 ⟨hO ▸ h2'.1.2, ?_⟩
            rw [hW]
            exact Sym2.mem_mk_left _ _
          have hle : ((wOpen W t).filter (fun e => W t ∈ e)).card ≤ 1 := by
            have := h2.2
            unfold wDeg at this
            omega
          have heq := Finset.card_le_one.1 hle _ e1 _ e2
          unfold wEdge at heq
          rw [← hW] at heq
          exact Sym2.congr_right.1 heq
        · rw [ite_eq_left h2, ite_eq_right h2'] at hct
          simp at hct
        · rw [ite_eq_right h2, ite_eq_left h2'] at hct
          simp at hct
        · rw [ite_eq_right h2, ite_eq_right h2'] at hct
          simp only [Option.some.injEq, Sum.inr.injEq, Fin.mk.injEq] at hct
          rw [← findGreatest_visit h1, ← findGreatest_visit h1', hct]
          exact hpre _ (by rw [← hct]; exact Nat.findGreatest_le _)
  exact fun t ht => key t ht t le_rfl

/-- Distinct new steps have distinct edges. -/
private lemma wEdge_inj_new {W : ℕ → V} {a b : ℕ} (ha : wNew W a) (hb : wNew W b)
    (hab : wEdge W a = wEdge W b) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact absurd hab (wEdge_ne_of_new hb h)
  · exact h
  · exact absurd hab.symm (wEdge_ne_of_new ha h)

/-- In a walk using each of its edges at least twice, every new step is followed by a minus step
along the same edge. -/
private lemma card_new_le_card_minus (W : ℕ → V) (k : ℕ)
    (hgood : ∀ t < k, 2 ≤ ((Finset.range k).filter (fun t' => wEdge W t' = wEdge W t)).card) :
    ((Finset.range k).filter (fun t => wNew W t)).card ≤
      ((Finset.range k).filter (fun t => wMinus W t)).card := by
  set SN := (Finset.range k).filter (fun t => wNew W t) with hSN
  set SM := (Finset.range k).filter (fun t => wMinus W t) with hSM
  have hinj : Set.InjOn (wEdge W) SN := by
    intro a ha b hb hab
    have ha' := (Finset.mem_filter.1 ha).2
    have hb' := (Finset.mem_filter.1 hb).2
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (wEdge_ne_of_new hb' h)
    · exact h
    · exact absurd hab.symm (wEdge_ne_of_new ha' h)
  have hsub : SN.image (wEdge W) ⊆ SM.image (wEdge W) := by
    intro e he
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨hτk, hτn⟩ := Finset.mem_filter.1 hτ
    have hτk' := Finset.mem_range.1 hτk
    set T := (Finset.range k).filter (fun t => τ < t ∧ wEdge W t = wEdge W τ) with hT
    have hsubT : (Finset.range k).filter (fun t' => wEdge W t' = wEdge W τ) ⊆ insert τ T := by
      intro t' ht'
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 ht'
      rcases lt_trichotomy t' τ with h | h | h
      · exact absurd h2 (wEdge_ne_of_new hτn h)
      · rw [h]
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨h1, h, h2⟩)
    have hTne : T.Nonempty := by
      rw [← Finset.card_pos]
      have h1 := hgood τ hτk'
      have h2 := Finset.card_le_card hsubT
      have h3 := Finset.card_insert_le τ T
      omega
    have hσ := Finset.min'_mem T hTne
    obtain ⟨hσk, hτσ, hσe⟩ := Finset.mem_filter.1 hσ
    have hσk' := Finset.mem_range.1 hσk
    refine Finset.mem_image.2 ⟨T.min' hTne, Finset.mem_filter.2 ⟨hσk, ?_, ?_⟩, hσe⟩
    · intro hnσ
      have hm : W (T.min' hTne + 1) ∈ wEdge W τ := hσe ▸ Sym2.mem_mk_right _ _
      rcases Sym2.mem_iff.1 hm with h | h
      · exact hnσ (mem_wVis.2 ⟨τ, by omega, h.symm⟩)
      · exact hnσ (mem_wVis.2 ⟨τ + 1, by omega, h.symm⟩)
    · rw [mem_wOpen]
      refine ⟨⟨τ, hτσ, hτn, hσe.symm⟩, ?_⟩
      unfold wUses
      rw [Finset.card_eq_one]
      refine ⟨τ, ?_⟩
      ext t'
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        rw [hσe] at h2
        rcases lt_trichotomy t' τ with h | h | h
        · exact absurd h2 (wEdge_ne_of_new hτn h)
        · exact h
        · have : T.min' hTne ≤ t' :=
            Finset.min'_le T t' (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), h, h2⟩)
          omega
      · rintro rfl
        exact ⟨hτσ, hσe.symm⟩
  calc SN.card = (SN.image (wEdge W)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (SM.image (wEdge W)).card := Finset.card_le_card hsub
    _ ≤ SM.card := Finset.card_image_le

section Pot

variable [Fintype V]

/-- `δ_t(v)`: the open edges at `v`, plus one if `v = W t`, plus one if `v = W 0`. -/
private def wDelta (W : ℕ → V) (t : ℕ) (v : V) : ℕ :=
  wDeg W t v + (if v = W t then 1 else 0) + (if v = W 0 then 1 else 0)

/-- The potential `Σ_v (δ_t(v) - 2)₊`. -/
private def wPot (W : ℕ → V) (t : ℕ) : ℕ := ∑ v, (wDelta W t v - 2)

private lemma sum_add_ite_le {a b : V → ℕ} {x y : V} {α β : ℕ}
    (h : ∀ v, a v + (if v = x then α else 0) ≤ b v + (if v = y then β else 0)) :
    ∑ v, a v + α ≤ ∑ v, b v + β := by
  have := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => h v)
  simpa [Finset.sum_add_distrib, Finset.sum_ite_eq'] using this

/-- A new step keeps the potential, a minus step does not raise it and lowers it when ambiguous,
any other step raises it by at most one. -/
private lemma wPot_succ (W : ℕ → V) (t : ℕ) :
    wPot W (t + 1) + (if wAmb W t then 1 else 0) ≤ wPot W t + (if wU W t then 1 else 0) := by
  unfold wPot
  apply sum_add_ite_le (x := W t) (y := W (t + 1))
  intro v
  unfold wDelta
  have hmem : (v ∈ wEdge W t) ↔ v = W t ∨ v = W (t + 1) := Sym2.mem_iff
  by_cases hn : wNew W t
  · have hA : ¬ wAmb W t := fun h => h.1.1 hn
    have hU : ¬ wU W t := fun h => h.1 hn
    have hd := wDeg_succ_new hn v
    have hy0 : W (t + 1) ≠ W 0 := fun h => hn (h ▸ self_mem_wVis W (Nat.zero_le _))
    have hxy := wNew_ne hn
    have hdy : wDeg W t (W (t + 1)) = 0 := wDeg_eq_zero_of_not_mem hn
    simp only [ite_eq_right hA, ite_eq_right hU, ite_self, add_zero]
    by_cases hvy : v = W (t + 1)
    · subst hvy
      simp only [hmem.2 (Or.inr rfl), ite_true, hdy, zero_add] at hd
      simp only [hd, hy0, Ne.symm hxy, ite_true, ite_false]
      omega
    · by_cases hvx : v = W t
      · subst hvx
        simp only [hmem.2 (Or.inl rfl), ite_true] at hd
        simp only [hd, hxy, ite_true, ite_false]
        omega
      · simp only [show ¬ (v ∈ wEdge W t) from fun h => (hmem.1 h).elim hvx hvy, ite_false,
          add_zero] at hd
        simp only [hd, hvx, hvy, ite_false]
        omega
  · by_cases hm : wMinus W t
    · have hU : ¬ wU W t := fun h => h.2 hm
      have hd := wDeg_succ_minus hm v
      have hxy := wMinus_ne hm
      simp only [ite_eq_right hU, ite_self, add_zero]
      by_cases hvx : v = W t
      · subst hvx
        simp only [hmem.2 (Or.inl rfl), ite_true] at hd
        simp only [hxy, ite_true, ite_false]
        by_cases hA : wAmb W t
        · have h2 := hA.2
          simp only [ite_eq_left hA]
          omega
        · simp only [ite_eq_right hA]
          omega
      · by_cases hvy : v = W (t + 1)
        · subst hvy
          simp only [hmem.2 (Or.inr rfl), ite_true] at hd
          simp only [hvx, ite_true, ite_false]
          omega
        · simp only [show ¬ (v ∈ wEdge W t) from fun h => (hmem.1 h).elim hvx hvy, ite_false,
            add_zero] at hd
          simp only [hd, hvx, hvy, ite_false]
          omega
    · have hu : wU W t := ⟨hn, hm⟩
      have hA : ¬ wAmb W t := fun h => hm h.1
      have hd := wDeg_succ_U hu v
      simp only [ite_eq_right hA, ite_eq_left hu, ite_self, add_zero, hd]
      split_ifs <;> omega

private lemma wPot_zero (W : ℕ → V) : wPot W 0 = 0 := by
  unfold wPot wDelta
  have h0 : ∀ v, wDeg W 0 v = 0 := fun v => by simp [wDeg, wOpen]
  apply Finset.sum_eq_zero
  intro v _
  rw [h0]
  split_ifs <;> omega

omit [Fintype V] in
/-- There are at most as many ambiguous minus steps as other steps. -/
private lemma card_amb_le [Finite V] (W : ℕ → V) (k : ℕ) :
    ((Finset.range k).filter (fun t => wAmb W t)).card ≤
      ((Finset.range k).filter (fun t => wU W t)).card := by
  have := Fintype.ofFinite V
  have hnot : ∀ m (p : ℕ → Prop) [DecidablePred p], m ∉ (Finset.range m).filter p := by simp
  have key : ∀ m, wPot W m + ((Finset.range m).filter (fun t => wAmb W t)).card ≤
      ((Finset.range m).filter (fun t => wU W t)).card := by
    intro m
    induction m with
    | zero => simp [wPot_zero]
    | succ m ih =>
      have := wPot_succ W m
      rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert]
      split_ifs at this ⊢ <;> (try simp only [Finset.card_insert_of_notMem (hnot _ _)]) <;> omega
  exact le_trans (Nat.le_add_left _ _) (key k)

omit [Fintype V] in
/-- For a walk using each of its edges at least twice, with `n` new steps and `d` steps that are
neither new nor back: `2n ≤ k` and `d ≤ 2(k - 2n)`. -/
private lemma walk_counts [Finite V] (W : ℕ → V) (k : ℕ)
    (hgood : ∀ t < k, 2 ≤ ((Finset.range k).filter (fun t' => wEdge W t' = wEdge W t)).card) :
    2 * ((Finset.range k).filter (fun t => wNew W t)).card ≤ k ∧
      ((Finset.range k).filter (fun t => ¬ wNew W t ∧ ¬ wBack W t)).card ≤
        2 * (k - 2 * ((Finset.range k).filter (fun t => wNew W t)).card) := by
  have hnm := card_new_le_card_minus W k hgood
  have hau := card_amb_le W k
  have hsum : ((Finset.range k).filter (fun t => wNew W t)).card +
      ((Finset.range k).filter (fun t => wMinus W t)).card +
      ((Finset.range k).filter (fun t => wU W t)).card = k := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    conv_rhs => rw [← Finset.card_range k, Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h1 : wNew W t <;> by_cases h2 : wEdge W t ∈ wOpen W t <;> simp [wMinus, wU, h1, h2]
  have hprev : ((Finset.range k).filter (fun t => ¬ wNew W t ∧ ¬ wBack W t)).card =
      ((Finset.range k).filter (fun t => wU W t)).card +
      ((Finset.range k).filter (fun t => wAmb W t)).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h1 : wNew W t <;> by_cases h2 : wEdge W t ∈ wOpen W t <;>
      by_cases h3 : wDeg W t (W t) < 2 <;> simp [wMinus, wU, wAmb, wBack, h1, h2, h3]
  omega

end Pot

/-- Weights of the codes: `1` for a back step, `a` for a new step, `ρ` for the other steps. -/
private def codeWt {k : ℕ} (a ρ : ℝ) : Option (V ⊕ Fin k) → ℝ
  | none => 1
  | some (Sum.inl _) => a
  | some (Sum.inr _) => ρ

private lemma prod_codeWt (W : ℕ → V) (k : ℕ) (a ρ : ℝ) :
    ∏ t, codeWt a ρ (wCode W k t) = a ^ ((Finset.range k).filter (fun t => wNew W t)).card *
      ρ ^ ((Finset.range k).filter (fun t => ¬ wNew W t ∧ ¬ wBack W t)).card := by
  rw [Finset.card_filter, Finset.card_filter, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib,
    ← Fin.prod_univ_eq_prod_range (fun t => a ^ (if wNew W t then 1 else 0) *
      ρ ^ (if ¬ wNew W t ∧ ¬ wBack W t then 1 else 0)) k]
  refine Finset.prod_congr rfl fun t _ => ?_
  unfold wCode
  split_ifs <;> simp_all [codeWt]

omit [DecidableEq V] in
private lemma sum_prod_codeWt [Fintype V] (k : ℕ) (a ρ : ℝ) :
    ∑ x : V × (Fin k → Option (V ⊕ Fin k)), ∏ t, codeWt a ρ (x.2 t) =
      Fintype.card V * (1 + Fintype.card V * a + k * ρ) ^ k := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Fintype.prod_sum (fun (_ : Fin k) σ => codeWt a ρ σ), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Fintype.sum_option, Fintype.sum_sum_type]
  have h1 : ∑ v : V, codeWt (k := k) a ρ (some (Sum.inl v)) = Fintype.card V * a := by
    simp only [codeWt, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h2 : ∑ t : Fin k, codeWt (V := V) a ρ (some (Sum.inr t)) = k * ρ := by
    simp only [codeWt, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [h1, h2]
  simp only [codeWt]
  ring

end Walk

/-! ### Traces of powers as sums over closed walks ((A.25) of [15]) -/

/-- `(M^k)_{ij}` is the sum over the paths `v 0 = i, …, v k = j` of the products of the entries
along the path. -/
private lemma pow_apply_eq_sum_paths {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (k : ℕ) (i j : n) :
    (M ^ k) i j = ∑ v : Fin (k + 1) → n,
      if v 0 = i ∧ v (Fin.last k) = j then ∏ t : Fin k, M (v t.castSucc) (v t.succ) else 0 := by
  induction k generalizing j with
  | zero =>
    rw [pow_zero, Matrix.one_apply, ← (Equiv.funUnique (Fin 1) n).symm.sum_comp]
    simp [ite_and, Finset.sum_ite_eq']
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    conv_rhs => rw [← (Fin.snocEquiv (fun _ => n)).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hz : ∀ a : n, (Fin.snoc v a : Fin (k + 2) → n) 0 = v 0 := fun a => by
      rw [show (0 : Fin (k + 2)) = (0 : Fin (k + 1)).castSucc from rfl, Fin.snoc_castSucc]
    simp only [Fin.snocEquiv_apply, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.succ_last,
      Fin.snoc_last, Fin.succ_castSucc, hz, ite_and]
    by_cases hv : v 0 = i
    · simp [hv, Finset.sum_ite_eq']
    · simp [hv]

/-- `Tr M^k` is the sum over the closed paths of length `k` of the products of the entries. -/
private lemma trace_pow_eq_sum_paths {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (k : ℕ) :
    (M ^ k).trace = ∑ v : Fin (k + 1) → n,
      if v 0 = v (Fin.last k) then ∏ t : Fin k, M (v t.castSucc) (v t.succ) else 0 := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply, pow_apply_eq_sum_paths]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [ite_and]
  rw [Finset.sum_ite_eq]
  simp [eq_comm]

/-- The path `v : Fin (k + 1) → Fin N` as a walk indexed by `ℕ`. -/
private def pathW {N k : ℕ} (v : Fin (k + 1) → Fin N) (t : ℕ) : Fin N :=
  if h : t < k + 1 then v ⟨t, h⟩ else v 0

private lemma pathW_castSucc {N k : ℕ} (v : Fin (k + 1) → Fin N) (t : Fin k) :
    pathW v t = v t.castSucc := by
  unfold pathW
  rw [dite_eq_left (by omega)]
  rfl

private lemma pathW_succ {N k : ℕ} (v : Fin (k + 1) → Fin N) (t : Fin k) :
    pathW v (t + 1) = v t.succ := by
  unfold pathW
  rw [dite_eq_left (by omega)]
  rfl

private lemma pathW_val {N k : ℕ} (v : Fin (k + 1) → Fin N) (i : Fin (k + 1)) :
    pathW v i = v i := by
  unfold pathW
  rw [dite_eq_left i.isLt]

private lemma pathW_zero {N k : ℕ} (v : Fin (k + 1) → Fin N) : pathW v 0 = v 0 := by
  unfold pathW
  rw [dite_eq_left (by omega)]
  rfl

private lemma prod_path_eq {N k : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (v : Fin (k + 1) → Fin N) :
    ∏ t : Fin k, M (v t.castSucc) (v t.succ) =
      ∏ t ∈ Finset.range k, M (pathW v t) (pathW v (t + 1)) := by
  rw [← Fin.prod_univ_eq_prod_range (fun t => M (pathW v t) (pathW v (t + 1)))]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [pathW_castSucc, pathW_succ]

/-! ### Coordinates of the entries and moments of products along walks

The bound on the expectation of the product along one walk follows the estimate after (A.26)
of [15]; summed over all walks it gives `E Tr H^k ≤ N (2 + k ((1 + C0)/q)^{1/2})^k`, which takes
the place of (A.24) of [15]. -/

/-- The coordinate of `Entries N` carrying the entry `h_ab` of `symOfEntries`. -/
private def cidxF {N : ℕ} (a b : Fin N) : Fin N ⊕ OffDiag N :=
  if h : a = b then Sum.inl a
  else if h' : a < b then Sum.inr ⟨(a, b), h'⟩
  else Sum.inr ⟨(b, a), lt_of_le_of_ne (not_lt.mp h') (fun e => h e.symm)⟩

private lemma symOfEntries_eq_entryCoord {N : ℕ} (ω : Entries N) (a b : Fin N) :
    symOfEntries ω a b = entryCoord (cidxF a b) ω := by
  unfold symOfEntries cidxF
  split_ifs <;> rfl

private lemma cidxF_comm {N : ℕ} (a b : Fin N) : cidxF a b = cidxF b a := by
  unfold cidxF
  by_cases h : a = b
  · subst h
    rfl
  · have h2 : b ≠ a := Ne.symm h
    rcases lt_or_gt_of_ne h with h' | h'
    · have : ¬ b < a := not_lt.mpr h'.le
      simp [h, h2, h', this]
    · have : ¬ a < b := not_lt.mpr h'.le
      simp [h, h2, h', this]

/-- The coordinate of an edge. -/
private def cidx {N : ℕ} : Sym2 (Fin N) → Fin N ⊕ OffDiag N :=
  Sym2.lift ⟨cidxF, cidxF_comm⟩

private lemma cidx_mk {N : ℕ} (a b : Fin N) : cidx s(a, b) = cidxF a b := rfl

private lemma cidx_injective {N : ℕ} : Function.Injective (cidx (N := N)) := by
  intro e e' h
  induction e using Sym2.ind with | h a b => ?_
  induction e' using Sym2.ind with | h a' b' => ?_
  rw [cidx_mk, cidx_mk] at h
  unfold cidxF at h
  rw [Sym2.eq_iff]
  split_ifs at h <;> simp_all

private lemma cidx_isLeft_of_ne {N : ℕ} {a b : Fin N} (h : a ≠ b) :
    (cidx s(a, b)).isLeft = false := by
  rw [cidx_mk]
  unfold cidxF
  simp only [h, dite_false]
  split_ifs <;> rfl

/-- The number of steps `t < k` of `W` along the coordinate `e`. -/
private def mult {N : ℕ} (W : ℕ → Fin N) (k : ℕ) (e : Fin N ⊕ OffDiag N) : ℕ :=
  ((Finset.range k).filter (fun t => cidx (wEdge W t) = e)).card

private lemma sum_mult {N : ℕ} (W : ℕ → Fin N) (k : ℕ) : ∑ e, mult W k e = k := by
  unfold mult
  rw [← Finset.card_eq_sum_card_fiberwise (by intro t _; simp), Finset.card_range]

private lemma prod_walk_eq {N : ℕ} (ω : Entries N) (W : ℕ → Fin N) (k : ℕ) :
    ∏ t ∈ Finset.range k, symOfEntries ω (W t) (W (t + 1)) =
      ∏ e, entryCoord e ω ^ mult W k e := by
  have h1 : ∀ t, symOfEntries ω (W t) (W (t + 1)) = entryCoord (cidx (wEdge W t)) ω :=
    fun t => by rw [symOfEntries_eq_entryCoord]; rfl
  simp_rw [h1]
  rw [Finset.prod_comp (fun e => entryCoord e ω) (fun t => cidx (wEdge W t))]
  unfold mult
  apply Finset.prod_subset (Finset.subset_univ _)
  intro e _ he
  have : ((Finset.range k).filter (fun t => cidx (wEdge W t) = e)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t ht h
    exact he (Finset.mem_image.2 ⟨t, ht, h⟩)
  rw [this, pow_zero]

/-- The law of the coordinate `e`. -/
private def coordLaw {N : ℕ} (L : EntryLaws N) : Fin N ⊕ OffDiag N → Measure ℝ :=
  Sum.elim L.diag L.off

/-- Independence: the expectation of a product along a walk is the product of the moments
of the coordinates, each to its multiplicity. -/
private lemma integral_prod_walk {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) (W : ℕ → Fin N)
    (k : ℕ) :
    ∫ ω, ∏ t ∈ Finset.range k, symOfEntries ω (W t) (W (t + 1)) ∂L.law =
      ∏ e, ∫ x, x ^ mult W k e ∂(coordLaw L e) := by
  have h1 := hL.diag
  have h2 := hL.off
  have hfun : (fun ω : Entries N => ∏ t ∈ Finset.range k, symOfEntries ω (W t) (W (t + 1))) =
      fun z => (∏ i, z.1 i ^ mult W k (Sum.inl i)) * ∏ p, z.2 p ^ mult W k (Sum.inr p) := by
    funext ω
    rw [prod_walk_eq, Fintype.prod_sum_type]
    rfl
  rw [hfun]
  unfold EntryLaws.law
  rw [integral_prod_mul (fun x : Fin N → ℝ => ∏ i, x i ^ mult W k (Sum.inl i))
    (fun y : OffDiag N → ℝ => ∏ p, y p ^ mult W k (Sum.inr p)),
    integral_fintype_prod_eq_prod (fun i (x : ℝ) => x ^ mult W k (Sum.inl i)),
    integral_fintype_prod_eq_prod (fun p (x : ℝ) => x ^ mult W k (Sum.inr p)),
    Fintype.prod_sum_type]
  rfl

/-- The bound on `|E x^m|`: `1` for `m = 0`, `0` for `m = 1`, `v q^{-(m-2)}` for `m ≥ 2`. -/
private def momBd (v q : ℝ) (m : ℕ) : ℝ :=
  if m = 0 then 1 else if m = 1 then 0 else v * q⁻¹ ^ (m - 2)

private lemma abs_moment_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {q v : ℝ} (hq : 0 < q)
    (hb : μ {x | q⁻¹ < |x|} = 0) (hint : Integrable (fun x => x ^ 2) μ)
    (hv : ∫ x, x ^ 2 ∂μ ≤ v) (hmean : ∫ x, x ∂μ = 0) (m : ℕ) :
    |∫ x, x ^ m ∂μ| ≤ momBd v q m := by
  unfold momBd
  split_ifs with h0 h1
  · subst h0
    simp
  · subst h1
    simp [hmean]
  · have hae : ∀ᵐ x ∂μ, |x| ≤ q⁻¹ := by
      rw [ae_iff]
      simpa [not_le] using hb
    have hint_m : Integrable (fun x => |x ^ m|) μ := by
      refine Integrable.of_bound (C := q⁻¹ ^ m) (by fun_prop) ?_
      filter_upwards [hae] with x hx
      rw [Real.norm_eq_abs, abs_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg x) hx m
    calc |∫ x, x ^ m ∂μ| ≤ ∫ x, |x ^ m| ∂μ := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x : ℝ => x ^ m)
      _ ≤ ∫ x, q⁻¹ ^ (m - 2) * x ^ 2 ∂μ := by
        refine integral_mono_ae hint_m (hint.const_mul _) ?_
        filter_upwards [hae] with x hx
        have : |x ^ m| = |x| ^ (m - 2) * x ^ 2 := by
          rw [abs_pow, ← sq_abs x, ← pow_add, Nat.sub_add_cancel (by omega)]
        rw [this]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg x) hx _) (sq_nonneg x)
      _ = q⁻¹ ^ (m - 2) * ∫ x, x ^ 2 ∂μ := integral_const_mul _ _
      _ ≤ q⁻¹ ^ (m - 2) * v := mul_le_mul_of_nonneg_left hv (by positivity)
      _ = v * q⁻¹ ^ (m - 2) := mul_comm _ _

private lemma abs_coord_moment_le {N : ℕ} {L : EntryLaws N} {C0 q : ℝ} (hL : L.IsGenWigner C0)
    (hq : 0 < q) (hS : L.BoundedSupportAS q) (e : Fin N ⊕ OffDiag N) (m : ℕ) :
    |∫ x, x ^ m ∂(coordLaw L e)| ≤
      momBd (if e.isLeft then (1 + C0) / N else 1 / N) q m := by
  rcases e with i | p
  · have := hL.isProb.diag i
    refine abs_moment_le hq (hS.1 i) (hL.sq_int_diag i) ?_ (hL.mean_diag i) m
    have h := (abs_le.1 (hL.var_diag i)).2
    simp only [Sum.isLeft_inl, ite_true]
    change ∫ x, x ^ 2 ∂(L.diag i) ≤ (1 + C0) / N
    have e : (1 + C0) / (N : ℝ) = (N : ℝ)⁻¹ + C0 * (N : ℝ)⁻¹ := by ring
    rw [e]
    linarith
  · have := hL.isProb.off p
    refine abs_moment_le hq (hS.2 p) (hL.sq_int_off p) ?_ (hL.mean_off p) m
    simp only [Sum.isLeft_inr]
    change ∫ x, x ^ 2 ∂(L.off p) ≤ 1 / N
    rw [hL.var_off p, one_div]

/-- The weight of a walk using each coordinate `e` either `0` or at least twice:
`∏_e momBd(v_e, q, m_e) ≤ R^{-n} (κ/q)^{k-2n}` where `k = Σ m_e`, `v_e = κ/R` on the
diagonal and `1/R` off it, and `n` is at most the number of off-diagonal coordinates used. -/
private lemma weight_le {ι : Type*} [Fintype ι] (m : ι → ℕ) (isL : ι → Bool) {κ q R : ℝ}
    {k n : ℕ} (hκ : 1 ≤ κ) (hq : 0 < q) (hR : q ^ 2 ≤ R) (hm1 : ∀ e, m e ≠ 1)
    (hsum : ∑ e, m e = k)
    (hn : n ≤ ((Finset.univ.filter (fun e => m e ≠ 0)).filter (fun e => isL e = false)).card) :
    2 * n ≤ k ∧
      ∏ e, momBd (if isL e then κ / R else 1 / R) q (m e) ≤ (R⁻¹) ^ n * (κ / q) ^ (k - 2 * n) := by
  set S := Finset.univ.filter (fun e => m e ≠ 0) with hS
  set a := (S.filter (fun e => isL e = true)).card with ha
  set b := (S.filter (fun e => isL e = false)).card with hb
  have hab : a + b = S.card := by
    rw [ha, hb, ← Finset.card_filter_add_card_filter_not (s := S) (p := fun e => isL e = true)]
    congr 2
  have h2S : 2 * S.card ≤ k := by
    rw [← hsum]
    calc 2 * S.card = ∑ e ∈ S, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ e ∈ S, m e := Finset.sum_le_sum (fun e he => by
          have h1 := (Finset.mem_filter.1 he).2
          have h2 := hm1 e
          omega)
      _ ≤ ∑ e, m e := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Nat.zero_le _)
  refine ⟨by omega, ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hβ : ∀ e, momBd (if isL e then κ / R else 1 / R) q (m e) =
      q⁻¹ ^ m e * (if m e ≠ 0 then (if isL e then κ / R else 1 / R) * q ^ 2 else 1) := by
    intro e
    unfold momBd
    by_cases h0 : m e = 0
    · simp [h0]
    · have h1 := hm1 e
      simp only [h0, h1, ite_false, ne_eq, not_false_eq_true, ite_true]
      have hq2 : q⁻¹ ^ 2 * q ^ 2 = 1 := by rw [inv_pow, inv_mul_cancel₀ (by positivity)]
      have : q⁻¹ ^ m e = q⁻¹ ^ (m e - 2) * q⁻¹ ^ 2 := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]
      rw [this]
      calc (if isL e = true then κ / R else 1 / R) * q⁻¹ ^ (m e - 2)
          = (if isL e = true then κ / R else 1 / R) * q⁻¹ ^ (m e - 2) * (q⁻¹ ^ 2 * q ^ 2) := by
            rw [hq2, mul_one]
        _ = _ := by ring
  rw [Finset.prod_congr rfl (fun e _ => hβ e), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hsum, ← Finset.prod_filter,
    ← Finset.prod_filter_mul_prod_filter_not S (fun e => isL e = true)]
  have hA : ∏ e ∈ S.filter (fun e => isL e = true),
      (if isL e then κ / R else 1 / R) * q ^ 2 = (κ / R * q ^ 2) ^ a := by
    rw [Finset.prod_congr rfl (fun e he => by rw [ite_eq_left (Finset.mem_filter.1 he).2]),
      Finset.prod_const]
  have hB : ∏ e ∈ S.filter (fun e => ¬ isL e = true),
      (if isL e then κ / R else 1 / R) * q ^ 2 = (1 / R * q ^ 2) ^ b := by
    rw [hb, Finset.prod_congr rfl (fun e he => by
      rw [ite_eq_right (Finset.mem_filter.1 he).2]), Finset.prod_const]
    congr 2
  rw [hA, hB]
  set r := q ^ 2 / R with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := (div_le_one hR0).2 hR
  have e1 : κ / R * q ^ 2 = κ * r := by rw [hr]; ring
  have e2 : 1 / R * q ^ 2 = r := by rw [hr]; ring
  rw [e1, e2]
  obtain ⟨j, hj⟩ : ∃ j, k = 2 * n + j := ⟨k - 2 * n, by omega⟩
  obtain ⟨b', hb'⟩ : ∃ b', b = n + b' := ⟨b - n, by omega⟩
  have haj : a ≤ j := by omega
  rw [hj, hb', show 2 * n + j - 2 * n = j by omega]
  have e3 : q⁻¹ ^ 2 * r = R⁻¹ := by
    rw [hr, inv_pow]
    field_simp
  have hq0 : 0 ≤ q⁻¹ := by positivity
  calc q⁻¹ ^ (2 * n + j) * ((κ * r) ^ a * r ^ (n + b'))
      = (q⁻¹ ^ 2 * r) ^ n * (q⁻¹ ^ j * κ ^ a * r ^ (a + b')) := by ring
    _ = R⁻¹ ^ n * (q⁻¹ ^ j * κ ^ a * r ^ (a + b')) := by rw [e3]
    _ ≤ R⁻¹ ^ n * (q⁻¹ ^ j * κ ^ j * 1) := by
        have h1 : κ ^ a ≤ κ ^ j := pow_le_pow_right₀ hκ haj
        have h2 : r ^ (a + b') ≤ 1 := pow_le_one₀ hr0.le hr1
        gcongr
    _ = R⁻¹ ^ n * (κ / q) ^ j := by rw [div_pow]; ring

/-- The new steps of a walk use distinct off-diagonal coordinates. -/
private lemma card_new_le_off {N : ℕ} (W : ℕ → Fin N) (k : ℕ) :
    ((Finset.range k).filter (fun t => wNew W t)).card ≤
      ((Finset.univ.filter (fun e => mult W k e ≠ 0)).filter
        (fun e => e.isLeft = false)).card := by
  refine Finset.card_le_card_of_injOn (fun t => cidx (wEdge W t)) ?_ ?_
  · intro t ht
    obtain ⟨htk, hn⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 ht)
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩)
    · change ((Finset.range k).filter (fun t' => cidx (wEdge W t') = cidx (wEdge W t))).card ≠ 0
      exact Finset.card_ne_zero.2 ⟨t, Finset.mem_filter.2 ⟨htk, rfl⟩⟩
    · exact cidx_isLeft_of_ne (wNew_ne hn)
  · intro a ha b hb hab
    exact wEdge_inj_new (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2
      (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2 (cidx_injective hab)

private lemma hgood_of_mult {N : ℕ} {W : ℕ → Fin N} {k : ℕ} (hg : ∀ e, mult W k e ≠ 1) :
    ∀ t < k, 2 ≤ ((Finset.range k).filter (fun t' => wEdge W t' = wEdge W t)).card := by
  intro t ht
  have h1 : (Finset.range k).filter (fun t' => wEdge W t' = wEdge W t) =
      (Finset.range k).filter (fun t' => cidx (wEdge W t') = cidx (wEdge W t)) :=
    Finset.filter_congr (fun t' _ => cidx_injective.eq_iff.symm)
  rw [h1]
  have h2 := hg (cidx (wEdge W t))
  have h3 : 0 < mult W k (cidx (wEdge W t)) :=
    Finset.card_pos.2 ⟨t, Finset.mem_filter.2 ⟨Finset.mem_range.2 ht, rfl⟩⟩
  unfold mult at h2 h3
  omega

/-- The expectation of the product along one walk is at most the weight of its code. -/
private lemma abs_integral_walk_le {N : ℕ} {L : EntryLaws N} {C0 q : ℝ} (hL : L.IsGenWigner C0)
    (hC0 : 0 ≤ C0) (hq : 0 < q) (hqN : q ^ 2 ≤ N) (hκq : 1 + C0 ≤ q)
    (hS : L.BoundedSupportAS q) (W : ℕ → Fin N) (k : ℕ) :
    |∫ ω, ∏ t ∈ Finset.range k, symOfEntries ω (W t) (W (t + 1)) ∂L.law| ≤
      ∏ t, codeWt (N : ℝ)⁻¹ (Real.sqrt ((1 + C0) / q)) (wCode W k t) := by
  set ρ := Real.sqrt ((1 + C0) / q) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := Real.sqrt_le_one.mpr ((div_le_one hq).2 hκq)
  have hρ2 : ρ ^ 2 = (1 + C0) / q := Real.sq_sqrt (by positivity)
  rw [integral_prod_walk hL.isProb, Finset.abs_prod]
  have hbound : ∏ e, |∫ x, x ^ mult W k e ∂(coordLaw L e)| ≤
      ∏ e, momBd (if e.isLeft then (1 + C0) / N else 1 / N) q (mult W k e) :=
    Finset.prod_le_prod₀ (fun e _ => abs_nonneg _) (fun e _ => abs_coord_moment_le hL hq hS e _)
  refine hbound.trans ?_
  have hcw : 0 ≤ ∏ t, codeWt (N : ℝ)⁻¹ ρ (wCode W k t) :=
    Finset.prod_nonneg (fun t _ => by unfold codeWt; split <;> positivity)
  by_cases hg : ∀ e, mult W k e ≠ 1
  · obtain ⟨-, hw⟩ := weight_le (mult W k) Sum.isLeft (κ := 1 + C0) (by linarith) hq hqN hg
      (sum_mult W k) (card_new_le_off W k)
    refine hw.trans ?_
    rw [prod_codeWt]
    obtain ⟨-, hd⟩ := walk_counts W k (hgood_of_mult hg)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← hρ2, ← pow_mul]
    exact pow_le_pow_of_le_one hρ0 hρ1 hd
  · push Not at hg
    obtain ⟨e, he⟩ := hg
    rw [Finset.prod_eq_zero (Finset.mem_univ e) (by simp [momBd, he])]
    exact hcw

/-- Summed over all paths of length `k`, the expectations are at most `N (2 + k ρ)^k`. -/
private lemma sum_abs_integral_paths_le {N : ℕ} {L : EntryLaws N} {C0 q : ℝ}
    (hL : L.IsGenWigner C0) (hC0 : 0 ≤ C0) (hq : 0 < q) (hqN : q ^ 2 ≤ N) (hκq : 1 + C0 ≤ q)
    (hS : L.BoundedSupportAS q) (k : ℕ) :
    ∑ v : Fin (k + 1) → Fin N,
        |∫ ω, ∏ t ∈ Finset.range k, symOfEntries ω (pathW v t) (pathW v (t + 1)) ∂L.law| ≤
      N * (2 + k * Real.sqrt ((1 + C0) / q)) ^ k := by
  set ρ := Real.sqrt ((1 + C0) / q) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  set enc : (Fin (k + 1) → Fin N) → Fin N × (Fin k → Option (Fin N ⊕ Fin k)) :=
    fun v => (v 0, wCode (pathW v) k) with henc_def
  have henc : Function.Injective enc := by
    intro v v' h
    simp only [enc, Prod.mk.injEq] at h
    have := wCode_inj (W := pathW v) (W' := pathW v') (k := k)
      (by rw [pathW_zero, pathW_zero, h.1]) h.2
    funext i
    rw [← pathW_val v i, ← pathW_val v' i]
    exact this i (by omega)
  have hnn : ∀ x : Fin N × (Fin k → Option (Fin N ⊕ Fin k)),
      0 ≤ ∏ t, codeWt (N : ℝ)⁻¹ ρ (x.2 t) :=
    fun x => Finset.prod_nonneg (fun t _ => by unfold codeWt; split <;> positivity)
  calc ∑ v : Fin (k + 1) → Fin N,
        |∫ ω, ∏ t ∈ Finset.range k, symOfEntries ω (pathW v t) (pathW v (t + 1)) ∂L.law|
      ≤ ∑ v : Fin (k + 1) → Fin N, ∏ t, codeWt (N : ℝ)⁻¹ ρ ((enc v).2 t) :=
        Finset.sum_le_sum (fun v _ => abs_integral_walk_le hL hC0 hq hqN hκq hS (pathW v) k)
    _ ≤ ∑ x : Fin N × (Fin k → Option (Fin N ⊕ Fin k)), ∏ t, codeWt (N : ℝ)⁻¹ ρ (x.2 t) := by
        rw [← Finset.sum_image (f := fun x => ∏ t, codeWt (N : ℝ)⁻¹ ρ (x.2 t))
          (fun a _ b _ h => henc h)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hnn x)
    _ = N * (1 + N * (N : ℝ)⁻¹ + k * ρ) ^ k := by rw [sum_prod_codeWt, Fintype.card_fin]
    _ ≤ N * (2 + k * ρ) ^ k := by
        have h1 : (N : ℝ) * (N : ℝ)⁻¹ ≤ 1 := by
          rcases Nat.eq_zero_or_pos N with h | h
          · simp [h]
          · rw [mul_inv_cancel₀ (by positivity)]
        gcongr
        linarith

/-! ### From the trace moment to the eigenvalues -/

private lemma ae_abs_entryCoord_le {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) {q : ℝ}
    (hS : L.BoundedSupportAS q) : ∀ᵐ ω ∂L.law, ∀ e, |entryCoord e ω| ≤ q⁻¹ := by
  have h1 := hL.diag
  have h2 := hL.off
  rw [ae_all_iff]
  intro e
  rw [ae_iff]
  simp only [not_le]
  rcases e with i | p
  · refine measure_mono_null (t := (Function.eval i ⁻¹' {x : ℝ | q⁻¹ < |x|}) ×ˢ Set.univ) ?_ ?_
    · intro ω hω
      exact ⟨hω, trivial⟩
    · change ((Measure.pi L.diag).prod (Measure.pi L.off)) _ = 0
      rw [Measure.prod_prod, Measure.pi_eval_preimage_null _ (hS.1 i), zero_mul]
  · refine measure_mono_null (t := Set.univ ×ˢ (Function.eval p ⁻¹' {x : ℝ | q⁻¹ < |x|})) ?_ ?_
    · intro ω hω
      exact ⟨trivial, hω⟩
    · change ((Measure.pi L.diag).prod (Measure.pi L.off)) _ = 0
      rw [Measure.prod_prod, Measure.pi_eval_preimage_null _ (hS.2 p), mul_zero]

private lemma continuous_entryCoord {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    Continuous (fun ω : Entries N => entryCoord e ω) := by
  rcases e with i | p
  · exact (continuous_apply i).comp continuous_fst
  · exact (continuous_apply p).comp continuous_snd

private lemma integrable_prod_walk {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) {q : ℝ}
    (hS : L.BoundedSupportAS q) (W : ℕ → Fin N) (k : ℕ) :
    Integrable (fun ω => ∏ t ∈ Finset.range k, symOfEntries ω (W t) (W (t + 1))) L.law := by
  have := isProbabilityMeasure_law hL
  refine Integrable.of_bound (C := |q⁻¹| ^ k) ?_ ?_
  · refine (continuous_finsetProd _ (fun t _ => ?_)).aestronglyMeasurable
    simp_rw [symOfEntries_eq_entryCoord]
    exact continuous_entryCoord _
  · filter_upwards [ae_abs_entryCoord_le hL hS] with ω hω
    rw [Real.norm_eq_abs, Finset.abs_prod]
    calc ∏ t ∈ Finset.range k, |symOfEntries ω (W t) (W (t + 1))|
        ≤ ∏ t ∈ Finset.range k, |q⁻¹| := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
          (fun t _ => by rw [symOfEntries_eq_entryCoord]; exact (hω _).trans (le_abs_self _))
      _ = |q⁻¹| ^ k := by rw [Finset.prod_const, Finset.card_range]

/-- `Tr H^k = Σ_α λ_α^k`. -/
private lemma trace_pow_eq_sum_eigenvalues {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (k : ℕ) : (H ^ k).trace = ∑ α, hH.eigenvalues α ^ k := by
  conv_lhs => rw [hH.spectral_theorem]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm, ← mul_assoc,
    Unitary.coe_star_mul_self, one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp

private lemma exists_eigenvalues_eq_eigAsc {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (j : Fin N) : ∃ α, hH.eigenvalues α = eigAsc hH j :=
  ⟨Fintype.equivOfCardEq (Fintype.card_fin _) (Fin.cast (Fintype.card_fin N).symm (Fin.rev j)),
    by simp [Matrix.IsHermitian.eigenvalues, eigAsc]⟩

/-- For even `k`, an eigenvalue of absolute value above `3` forces `Tr H^k ≥ 3^k`. -/
private lemma compl_subset_trace {N k : ℕ} (hk : Even k) :
    {ω : Entries N | ∀ j, |eigAsc (symOfEntries_isHermitian ω) j| ≤ 3}ᶜ ⊆
      {ω | (3 : ℝ) ^ k ≤ ((symOfEntries ω) ^ k).trace} := by
  intro ω hω
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
  obtain ⟨j, hj⟩ := hω
  obtain ⟨α, hα⟩ := exists_eigenvalues_eq_eigAsc (symOfEntries_isHermitian ω) j
  simp only [Set.mem_ofPred_eq]
  rw [trace_pow_eq_sum_eigenvalues (symOfEntries_isHermitian ω)]
  calc (3 : ℝ) ^ k ≤ |(symOfEntries_isHermitian ω).eigenvalues α| ^ k :=
        pow_le_pow_left₀ (by norm_num) (by rw [hα]; exact hj.le) k
    _ = (symOfEntries_isHermitian ω).eigenvalues α ^ k := hk.pow_abs _
    _ ≤ ∑ β, (symOfEntries_isHermitian ω).eigenvalues β ^ k :=
        Finset.single_le_sum (fun β _ => hk.pow_nonneg _) (Finset.mem_univ α)

/-- Markov's inequality for `Tr H^k`, `k` even:
`P(∃ j, |λ_j| > 3) ≤ N ((2 + k ((1 + C0)/q)^{1/2}) / 3)^k`. -/
private lemma law_compl_le {N : ℕ} {L : EntryLaws N} {C0 q : ℝ} (hL : L.IsGenWigner C0)
    (hC0 : 0 ≤ C0) (hq : 0 < q) (hqN : q ^ 2 ≤ N) (hκq : 1 + C0 ≤ q)
    (hS : L.BoundedSupportAS q) {k : ℕ} (hk : Even k) :
    L.law {ω | ∀ j, |eigAsc (symOfEntries_isHermitian ω) j| ≤ 3}ᶜ ≤
      ENNReal.ofReal (N * ((2 + k * Real.sqrt ((1 + C0) / q)) / 3) ^ k) := by
  have hP := isProbabilityMeasure_law hL.isProb
  set T : Entries N → ℝ := fun ω => ((symOfEntries ω) ^ k).trace with hT
  have hTfun : T = fun ω => ∑ v : Fin (k + 1) → Fin N, if v 0 = v (Fin.last k) then
      ∏ t ∈ Finset.range k, symOfEntries ω (pathW v t) (pathW v (t + 1)) else 0 := by
    funext ω
    simp only [hT, trace_pow_eq_sum_paths, prod_path_eq]
  have hint : ∀ v : Fin (k + 1) → Fin N, Integrable (fun ω => if v 0 = v (Fin.last k) then
      ∏ t ∈ Finset.range k, symOfEntries ω (pathW v t) (pathW v (t + 1)) else 0) L.law := by
    intro v
    by_cases hv : v 0 = v (Fin.last k)
    · simp only [hv, ite_true]
      exact integrable_prod_walk hL.isProb hS _ k
    · simp only [hv, ite_false]
      exact integrable_zero _ _ _
  have hTint : Integrable T L.law := by
    rw [hTfun]
    exact integrable_finsetSum _ (fun v _ => hint v)
  have hTnn : 0 ≤ᵐ[L.law] T := ae_of_all _ fun ω => by
    simp only [Pi.zero_apply, hT]
    rw [trace_pow_eq_sum_eigenvalues (symOfEntries_isHermitian ω)]
    exact Finset.sum_nonneg (fun α _ => hk.pow_nonneg _)
  have hE : ∫ ω, T ω ∂L.law ≤ N * (2 + k * Real.sqrt ((1 + C0) / q)) ^ k := by
    rw [hTfun, integral_finsetSum _ (fun v _ => hint v)]
    refine le_trans (Finset.sum_le_sum (fun v _ => ?_))
      (sum_abs_integral_paths_le hL hC0 hq hqN hκq hS k)
    by_cases hv : v 0 = v (Fin.last k)
    · simp only [hv, ite_true]
      exact le_abs_self _
    · simp only [hv, ite_false, integral_zero]
      exact abs_nonneg _
  have hM := mul_meas_ge_le_integral_of_nonneg hTnn hTint ((3 : ℝ) ^ k)
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  calc L.law {ω | ∀ j, |eigAsc (symOfEntries_isHermitian ω) j| ≤ 3}ᶜ
      ≤ L.law {ω | (3 : ℝ) ^ k ≤ T ω} := measure_mono (compl_subset_trace hk)
    _ = ENNReal.ofReal (L.law.real {ω | (3 : ℝ) ^ k ≤ T ω}) := (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal (N * ((2 + k * Real.sqrt ((1 + C0) / q)) / 3) ^ k) := by
        apply ENNReal.ofReal_le_ofReal
        rw [div_pow, mul_div_assoc', le_div_iff₀ h3]
        linarith [hM, hE]

/-! ### The a priori norm bound -/

/-- A priori norm bound (Lemma 4.3 of [15], in the weakened form `≤ 3`). -/
theorem norm_apriori {ζ C0 : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) :
    ∃ C > 0, HighProbOn ζ
      (fun N L => L.IsGenWigner C0 ∧ ∃ q, phi N ^ C ≤ q ∧ L.BoundedSupportAS q)
      (fun N _ => {ω | ∀ j, |eigAsc (symOfEntries_isHermitian ω) j| ≤ 3}) := by
  refine ⟨⌈2 * ζ⌉₊ + 1, Nat.succ_pos _, ?_⟩
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, ∀ N ≥ N0, 256 * (1 + C0) ≤ phi N := by
    refine ⟨max 16 ⌈Real.exp (256 * (1 + C0))⌉₊, fun N hN => ?_⟩
    have h16 : 16 ≤ N := le_trans (le_max_left _ _) hN
    have hNe : Real.exp (256 * (1 + C0)) ≤ N :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
    have hlog : 256 * (1 + C0) ≤ Real.log N := by
      rw [← Real.log_exp (256 * (1 + C0))]
      exact Real.log_le_log (Real.exp_pos _) hNe
    exact hlog.trans (log_le_phi h16)
  refine ⟨1 / 2, by norm_num, 1, one_pos, max N0 16, fun N hN L hL => ?_⟩
  obtain ⟨hGW, q, hq, hS⟩ := hL
  have hN16 : 16 ≤ N := le_trans (le_max_right _ _) hN
  have hφ : 256 * (1 + C0) ≤ phi N := hN0 N (le_trans (le_max_left _ _) hN)
  have hφ1 : 1 ≤ phi N := by linarith
  have hφ0 : 0 < phi N := by linarith
  set x := phi N ^ ζ with hx
  have hx1 : 1 ≤ x := Real.one_le_rpow hφ1 hζ.le
  have hφ2 : phi N ^ (2 * ζ) * phi N ≤ q := by
    refine le_trans ?_ hq
    rw [pow_succ]
    refine mul_le_mul_of_nonneg_right ?_ hφ0.le
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hφ1 (Nat.le_ceil _)
  have hx2 : x ^ 2 = phi N ^ (2 * ζ) := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hφ0.le]
    congr 1
    push_cast
    ring
  have hy1 : 1 ≤ phi N ^ (2 * ζ) := by rw [← hx2]; nlinarith
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hφ2
  have hκq : 1 + C0 ≤ q := by
    have : phi N ≤ phi N ^ (2 * ζ) * phi N := le_mul_of_one_le_left hφ0.le hy1
    linarith
  have hqN : q ^ 2 ≤ N := by
    have hN2 : 2 ≤ N := by omega
    let p0 : OffDiag N := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.lt_def]⟩
    have := hGW.isProb.off p0
    have hv := hGW.var_off p0
    have hae : ∀ᵐ x ∂(L.off p0), |x| ≤ q⁻¹ := by
      rw [ae_iff]
      simpa [not_le] using hS.2 p0
    have hle : ∫ x, x ^ 2 ∂(L.off p0) ≤ q⁻¹ ^ 2 := by
      have : ∫ x, x ^ 2 ∂(L.off p0) ≤ ∫ _x, q⁻¹ ^ 2 ∂(L.off p0) :=
        integral_mono_ae (hGW.sq_int_off p0) (integrable_const _) (by
          filter_upwards [hae] with x hx
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hx 2)
      simpa using this
    rw [hv, inv_pow] at hle
    have hNpos : (0 : ℝ) < N := by positivity
    exact (inv_le_inv₀ hNpos (by positivity)).1 hle
  set k := 2 * ⌈x⌉₊ with hk
  have hkeven : Even k := even_two_mul _
  refine (law_compl_le hGW hC0 hq0 hqN hκq hS hkeven).trans (ENNReal.ofReal_le_ofReal ?_)
  set ρ := Real.sqrt ((1 + C0) / q) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ2 : ρ ^ 2 = (1 + C0) / q := Real.sq_sqrt (by positivity)
  have hk_lo : 2 * x ≤ k := by
    rw [hk]
    push_cast
    linarith [Nat.le_ceil x]
  have hk_hi : (k : ℝ) ≤ 4 * x := by
    rw [hk]
    push_cast
    linarith [Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ x)]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hkρ : (k : ℝ) * ρ ≤ 1 / 4 := by
    have h1 : ((k : ℝ) * ρ) ^ 2 ≤ (1 / 4) ^ 2 := by
      rw [mul_pow, hρ2, mul_div_assoc', div_le_iff₀ hq0]
      have hk2 : (k : ℝ) ^ 2 ≤ 16 * phi N ^ (2 * ζ) := by rw [← hx2]; nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hk2 (by linarith : (0 : ℝ) ≤ 1 + C0),
        mul_le_mul_of_nonneg_left hφ (by positivity : (0 : ℝ) ≤ 16 * phi N ^ (2 * ζ))]
    exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) two_ne_zero).1 h1
  have hbase : (2 + k * ρ) / 3 ≤ Real.exp (-1 / 4) := by
    have := Real.add_one_le_exp (-1 / 4 : ℝ)
    linarith
  calc (N : ℝ) * ((2 + k * ρ) / 3) ^ k ≤ N * Real.exp (-1 / 4) ^ k := by
        gcongr
    _ = N * Real.exp (-(k : ℝ) / 4) := by
        rw [← Real.exp_nat_mul]
        ring_nf
    _ ≤ (N : ℝ) ^ 1 * Real.exp (-(1 / 2) * x) := by
        rw [pow_one]
        gcongr
        linarith

/-! ### Non-vacuity: entries `±N^{-1/2}` with `q = N^{1/2}` -/

/-- The symmetric two-point law `(δ_a + δ_{-a}) / 2`. -/
private def apTwo (a : ℝ) : Measure ℝ :=
  (2⁻¹ : ENNReal) • (Measure.dirac a + Measure.dirac (-a))

private instance apTwo_prob (a : ℝ) : IsProbabilityMeasure (apTwo a) := by
  refine ⟨?_⟩
  simp only [apTwo, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

private lemma apTwo_integral (a : ℝ) (f : ℝ → ℝ) :
    ∫ x, f x ∂(apTwo a) = (f a + f (-a)) / 2 := by
  have hi : ∀ b : ℝ, Integrable f (Measure.dirac b) := fun b => integrable_dirac (by simp)
  unfold apTwo
  rw [integral_smul_measure, integral_add_measure (hi a) (hi (-a)), integral_dirac,
    integral_dirac]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

private lemma apTwo_integrable (a : ℝ) (f : ℝ → ℝ) : Integrable f (apTwo a) :=
  (integrable_dirac (by simp)).add_measure (integrable_dirac (by simp)) |>.smul_measure (by simp)

private lemma apTwo_tail (a q : ℝ) (h : |a| ≤ q⁻¹) : apTwo a {x | q⁻¹ < |x|} = 0 := by
  have h1 : a ∉ {x : ℝ | q⁻¹ < |x|} := by simpa using h
  have h2 : -a ∉ {x : ℝ | q⁻¹ < |x|} := by simpa using h
  have hm : MeasurableSet {x : ℝ | q⁻¹ < |x|} := measurableSet_lt measurable_const measurable_abs
  simp [apTwo, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hm, h1, h2]

/-- Entry laws with all entries `±N^{-1/2}`, diagonal included. -/
private def apLaws (N : ℕ) : EntryLaws N :=
  ⟨fun _ => apTwo (Real.sqrt N)⁻¹, fun _ => apTwo (Real.sqrt N)⁻¹⟩

private lemma apLaws_isGenWigner (N : ℕ) : (apLaws N).IsGenWigner 0 := by
  have h2 : ∫ x, x ^ 2 ∂(apTwo (Real.sqrt N)⁻¹) = (N : ℝ)⁻¹ := by
    rw [apTwo_integral (f := fun x => x ^ 2), neg_sq, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    ring
  have h1 : ∫ x, x ∂(apTwo (Real.sqrt N)⁻¹) = 0 := by
    rw [apTwo_integral (f := fun x => x)]
    ring
  refine ⟨⟨fun _ => apTwo_prob _, fun _ => apTwo_prob _⟩, fun _ => apTwo_integrable _ _,
    fun _ => apTwo_integrable _ _, fun _ => h1, fun _ => h1, fun _ => h2, fun _ => ?_⟩
  change |∫ x, x ^ 2 ∂(apTwo (Real.sqrt N)⁻¹) - (N : ℝ)⁻¹| ≤ 0 * (N : ℝ)⁻¹
  rw [h2]
  simp

private lemma apLaws_boundedSupportAS (N : ℕ) : (apLaws N).BoundedSupportAS (Real.sqrt N) := by
  have h : |(Real.sqrt N)⁻¹| ≤ (Real.sqrt N)⁻¹ := (abs_of_nonneg (by positivity)).le
  exact ⟨fun _ => apTwo_tail _ _ h, fun _ => apTwo_tail _ _ h⟩

/-- For every `C`, the laws `apLaws N` (`C0 = 0`, `q = N^{1/2}`) lie in the class of
`norm_apriori` for all large `N`. -/
example (C : ℕ) : ∀ᶠ N : ℕ in atTop,
    (apLaws N).IsGenWigner 0 ∧ ∃ q, phi N ^ C ≤ q ∧ (apLaws N).BoundedSupportAS q := by
  filter_upwards [phi_rpow_le_rpow (C : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with N hN
  refine ⟨apLaws_isGenWigner N, Real.sqrt N, ?_, apLaws_boundedSupportAS N⟩
  rw [← Real.rpow_natCast, Real.sqrt_eq_rpow]
  exact hN

/-- `norm_apriori` at `ζ = 1`, `C0 = 0`, for the laws `apLaws N`: for all large `N`, some
eigenvalue exceeds `3` in absolute value with probability at most `N^{C'} e^{-c φ}`. -/
example : ∃ c > 0, ∃ C' > 0, ∀ᶠ N : ℕ in atTop,
    (apLaws N).law {ω | ∀ j, |eigAsc (symOfEntries_isHermitian ω) j| ≤ 3}ᶜ ≤
      ENNReal.ofReal ((N : ℝ) ^ C' * Real.exp (-c * phi N ^ (1 : ℝ))) := by
  obtain ⟨C, -, c, hc, C', hC', N0, h⟩ := norm_apriori (ζ := 1) (C0 := 0) one_pos le_rfl
  refine ⟨c, hc, C', hC', ?_⟩
  filter_upwards [eventually_ge_atTop N0,
    phi_rpow_le_rpow (C : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with N hN hφ
  refine h N hN (apLaws N) ⟨apLaws_isGenWigner N, Real.sqrt N, ?_, apLaws_boundedSupportAS N⟩
  rw [← Real.rpow_natCast, Real.sqrt_eq_rpow]
  exact hφ

#print axioms norm_apriori

end WEdgeNS
