import WEdgeNS.Comparison.Iterate

/-!
# Moment comparison of the Stieltjes transform (Lemma 5.4)
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

open private iterate_iterP_props iterate_ord_le iterate_len_le iterate_mem_wordP_length iterate_ord
  iterate_cast_ord iterate_bad_le from WEdgeNS.Comparison.Iterate
open private expansion_norm_integral_le expansion_eventually_le_phi expansion_eventually_log_le
  expansion_matchedPair_radLaws from WEdgeNS.Comparison.Expansion
open private monomial_norm_evalLetter_le from WEdgeNS.Comparison.Monomial

/-! ### Words with one summed index

A word over `Fin (N + 1)` stands for a family of words over `Fin N`: the index `N` (`Fin.last N`)
is a summation variable `i`, and the other indices are fixed. -/

/-- The entry `e` of `Fin N` read in `Fin (N + 1)`. -/
private def mcLiftE {N : ℕ} : Fin N ⊕ OffDiag N → Fin (N + 1) ⊕ OffDiag (N + 1)
  | Sum.inl a => Sum.inl a.castSucc
  | Sum.inr p => Sum.inr ⟨(p.1.1.castSucc, p.1.2.castSucc), Fin.castSucc_lt_castSucc_iff.2 p.2⟩

private lemma mc_entryPairs_liftE {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    entryPairs (mcLiftE e) = (entryPairs e).map fun xy => (xy.1.castSucc, xy.2.castSucc) := by
  rcases e with a | p <;> rfl

private lemma mc_entryPairs_ne_last {N : ℕ} (e : Fin N ⊕ OffDiag N) {xy : Fin (N + 1) × Fin (N + 1)}
    (h : xy ∈ entryPairs (mcLiftE e)) : xy.1 ≠ Fin.last N ∧ xy.2 ≠ Fin.last N := by
  rw [mc_entryPairs_liftE] at h
  obtain ⟨ab, -, rfl⟩ := List.mem_map.1 h
  exact ⟨Fin.castSucc_ne_last _, Fin.castSucc_ne_last _⟩

/-- The value `i` substituted for the summation variable. -/
private def mcSub {N : ℕ} (i : Fin N) (x : Fin (N + 1)) : Fin N :=
  if h : x = Fin.last N then i else x.castPred h

private lemma mcSub_castSucc {N : ℕ} (i a : Fin N) : mcSub i a.castSucc = a := by
  simp [mcSub, Fin.castSucc_ne_last]

private lemma mcSub_last {N : ℕ} (i : Fin N) : mcSub i (Fin.last N) = i := by
  simp [mcSub]

private lemma mcSub_of_ne {N : ℕ} (i i' : Fin N) {x : Fin (N + 1)} (h : x ≠ Fin.last N) :
    mcSub i x = mcSub i' x := by
  simp [mcSub, h]

/-- A letter with the value `i` substituted for the summation variable. -/
private def mcSubL {N : ℕ} (i : Fin N) (ℓ : Letter (N + 1)) : Letter N :=
  ⟨ℓ.kind, mcSub i ℓ.i, mcSub i ℓ.j⟩

private lemma mc_starWords_map {N : ℕ} (e : Fin N ⊕ OffDiag N) (κ : LetterKind) (i : Fin N) :
    ∀ (k : ℕ) (x y : Fin (N + 1)), (starWords (mcLiftE e) κ k x y).map (List.map (mcSubL i)) =
      starWords e κ k (mcSub i x) (mcSub i y)
  | 0, x, y => by simp [starWords, mcSubL]
  | k + 1, x, y => by
    simp only [starWords, List.map_flatMap, mc_entryPairs_liftE, List.flatMap_map]
    refine List.flatMap_congr fun xy _ => ?_
    have h := mc_starWords_map e κ i k xy.2.castSucc y
    rw [mcSub_castSucc] at h
    rw [← h, List.map_map, List.map_map]
    refine List.map_congr_left fun w _ => ?_
    simp [mcSubL, mcSub_castSucc]

private lemma mc_letterP_map {N : ℕ} (e : Fin N ⊕ OffDiag N) (i : Fin N) (k : ℕ)
    (ℓ : Letter (N + 1)) :
    (letterP (mcLiftE e) k ℓ).map (List.map (mcSubL i)) = letterP e k (mcSubL i ℓ) := by
  unfold letterP
  split_ifs
  · simp
  · exact mc_starWords_map e _ i k ℓ.i ℓ.j

private lemma mc_wordP_map {N : ℕ} (e : Fin N ⊕ OffDiag N) (i : Fin N) :
    ∀ (k : List ℕ) (w : Word (N + 1)),
      (wordP (mcLiftE e) k w).map (List.map (mcSubL i)) = wordP e k (w.map (mcSubL i))
  | _, [] => by simp [wordP]
  | [], ℓ :: w => by
    simp only [wordP, List.map_cons, List.map_map, ← mc_wordP_map e i [] w]
    rfl
  | k :: ks, ℓ :: w => by
    simp only [wordP, List.map_cons, List.map_flatMap, ← mc_letterP_map e i k ℓ, List.flatMap_map,
      ← mc_wordP_map e i ks w, List.map_map]
    refine List.flatMap_congr fun u _ => List.map_congr_left fun v _ => ?_
    simp

/-- `P_{γ,k}` on a concatenation, for `k` split at the length of the first factor. -/
private lemma mc_wordP_append {M : ℕ} (e : Fin M ⊕ OffDiag M) :
    ∀ (k₁ : List ℕ) (u : Word M) (k₂ : List ℕ) (v : Word M), k₁.length = u.length →
      wordP e (k₁ ++ k₂) (u ++ v) = (wordP e k₁ u).flatMap fun a => (wordP e k₂ v).map (a ++ ·)
  | [], [], k₂, v, _ => by simp [wordP]
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | k :: k₁, ℓ :: u, k₂, v, h => by
    simp only [List.cons_append, wordP]
    rw [mc_wordP_append e k₁ u k₂ v (by simpa using h)]
    simp [List.flatMap_assoc, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]

/-! ### The shape of the expanded words -/

/-- A letter without the summation variable. -/
private def mcFixed {N : ℕ} (ℓ : Letter (N + 1)) : Prop := ℓ.i ≠ Fin.last N ∧ ℓ.j ≠ Fin.last N

/-- The two shapes of a factor of (6.44)–(6.45): the centred diagonal letter `G_ii - m_sc` (or its
conjugate), or a chain `G_{ia} ⋯ G_{bi}` whose inner letters do not contain `i`. -/
private def mcForm {N : ℕ} (β : Word (N + 1)) : Prop :=
  (∃ κ : LetterKind, (κ = .gc ∨ κ = .gcbar) ∧ β = [⟨κ, Fin.last N, Fin.last N⟩]) ∨
  ∃ ℓ₁ mid ℓ₂, β = ℓ₁ :: (mid ++ [ℓ₂]) ∧ ℓ₁.i = Fin.last N ∧ ℓ₁.j ≠ Fin.last N ∧
    ℓ₂.i ≠ Fin.last N ∧ ℓ₂.j = Fin.last N ∧ ∀ ℓ ∈ mid, mcFixed ℓ

/-- A chain of `starWords` of positive order: `⟨κ, x, a⟩ ⋯ ⟨κ, b, y⟩` with fixed inner letters. -/
private lemma mc_starWords_shape {N : ℕ} (e : Fin N ⊕ OffDiag N) (κ : LetterKind) :
    ∀ (k : ℕ) (x y : Fin (N + 1)), ∀ w ∈ starWords (mcLiftE e) κ (k + 1) x y,
      ∃ a b mid, w = ⟨κ, x, a⟩ :: (mid ++ [⟨κ, b, y⟩]) ∧ a ≠ Fin.last N ∧ b ≠ Fin.last N ∧
        ∀ ℓ ∈ mid, mcFixed ℓ
  | 0, x, y, w, hw => by
    simp only [starWords, List.mem_flatMap, List.mem_map, List.mem_singleton] at hw
    obtain ⟨xy, hxy, w', rfl, rfl⟩ := hw
    exact ⟨xy.1, xy.2, [], by simp, (mc_entryPairs_ne_last e hxy).1,
      (mc_entryPairs_ne_last e hxy).2, by simp⟩
  | k + 1, x, y, w, hw => by
    rw [starWords] at hw
    simp only [List.mem_flatMap, List.mem_map] at hw
    obtain ⟨xy, hxy, w', hw', rfl⟩ := hw
    obtain ⟨a, b, mid, rfl, ha, hb, hmid⟩ := mc_starWords_shape e κ k xy.2 y w' hw'
    refine ⟨xy.1, b, ⟨κ, xy.2, a⟩ :: mid, by simp, (mc_entryPairs_ne_last e hxy).1, hb, ?_⟩
    intro ℓ hℓ
    rcases List.mem_cons.1 hℓ with rfl | hℓ
    · exact ⟨(mc_entryPairs_ne_last e hxy).2, ha⟩
    · exact hmid ℓ hℓ

/-- Chains between fixed indices are fixed. -/
private lemma mc_starWords_fixed {N : ℕ} (e : Fin N ⊕ OffDiag N) (κ : LetterKind) :
    ∀ (k : ℕ) (x y : Fin (N + 1)), x ≠ Fin.last N → y ≠ Fin.last N →
      ∀ w ∈ starWords (mcLiftE e) κ k x y, ∀ ℓ ∈ w, mcFixed ℓ
  | 0, x, y, hx, hy, w, hw, ℓ, hℓ => by
    simp only [starWords, List.mem_singleton] at hw
    subst hw
    simp only [List.mem_singleton] at hℓ
    subst hℓ
    exact ⟨hx, hy⟩
  | k + 1, x, y, hx, hy, w, hw, ℓ, hℓ => by
    simp only [starWords, List.mem_flatMap, List.mem_map] at hw
    obtain ⟨xy, hxy, w', hw', rfl⟩ := hw
    rcases List.mem_cons.1 hℓ with rfl | hℓ
    · exact ⟨hx, (mc_entryPairs_ne_last e hxy).1⟩
    · exact mc_starWords_fixed e κ k xy.2 y (mc_entryPairs_ne_last e hxy).2 hy w' hw' ℓ hℓ

private lemma mc_letterP_fixed {N : ℕ} (e : Fin N ⊕ OffDiag N) (k : ℕ) {ℓ : Letter (N + 1)}
    (hℓ : mcFixed ℓ) : ∀ w ∈ letterP (mcLiftE e) k ℓ, ∀ ℓ' ∈ w, mcFixed ℓ' := by
  intro w hw ℓ' hℓ'
  unfold letterP at hw
  split_ifs at hw
  · simp only [List.mem_singleton] at hw
    subst hw
    simp only [List.mem_singleton] at hℓ'
    subst hℓ'
    exact hℓ
  · exact mc_starWords_fixed e _ k ℓ.i ℓ.j hℓ.1 hℓ.2 w hw ℓ' hℓ'

private lemma mc_wordP_fixed {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    ∀ (k : List ℕ) (w : Word (N + 1)), (∀ ℓ ∈ w, mcFixed ℓ) →
      ∀ u ∈ wordP (mcLiftE e) k w, ∀ ℓ' ∈ u, mcFixed ℓ'
  | _, [], _, u, hu, ℓ', hℓ' => by
    simp only [wordP, List.mem_singleton] at hu
    subst hu
    simp at hℓ'
  | [], ℓ :: w, hw, u, hu, ℓ', hℓ' => by
    simp only [wordP, List.mem_map] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    rcases List.mem_cons.1 hℓ' with rfl | hℓ'
    · exact hw _ List.mem_cons_self
    · exact mc_wordP_fixed e [] w (fun x hx => hw x (List.mem_cons_of_mem _ hx)) u' hu' ℓ' hℓ'
  | k :: ks, ℓ :: w, hw, u, hu, ℓ', hℓ' => by
    simp only [wordP, List.mem_flatMap, List.mem_map] at hu
    obtain ⟨v, hv, u', hu', rfl⟩ := hu
    rcases List.mem_append.1 hℓ' with hℓ' | hℓ'
    · exact mc_letterP_fixed e k (hw ℓ List.mem_cons_self) v hv ℓ' hℓ'
    · exact mc_wordP_fixed e ks w (fun x hx => hw x (List.mem_cons_of_mem _ hx)) u' hu' ℓ' hℓ'

/-- `P_{γ,k}` on the first letter `⟨κ, i, a⟩` of a chain. -/
private lemma mc_letterP_head {N : ℕ} (e : Fin N ⊕ OffDiag N) (k : ℕ) {ℓ : Letter (N + 1)}
    (h1 : ℓ.i = Fin.last N) (h2 : ℓ.j ≠ Fin.last N) : ∀ w ∈ letterP (mcLiftE e) k ℓ,
      ∃ ℓ' r, w = ℓ' :: r ∧ ℓ'.i = Fin.last N ∧ ℓ'.j ≠ Fin.last N ∧ ∀ x ∈ r, mcFixed x := by
  intro w hw
  unfold letterP at hw
  split_ifs at hw with hk
  · simp only [List.mem_singleton] at hw
    exact ⟨ℓ, [], hw, h1, h2, by simp⟩
  · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    obtain ⟨a, b, mid, rfl, ha, hb, hmid⟩ := mc_starWords_shape e _ k' ℓ.i ℓ.j w hw
    refine ⟨⟨ℓ.kind.plain, ℓ.i, a⟩, mid ++ [⟨ℓ.kind.plain, b, ℓ.j⟩], rfl, h1, ha, fun x hx => ?_⟩
    rcases List.mem_append.1 hx with hx | hx
    · exact hmid x hx
    · simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨hb, h2⟩

/-- `P_{γ,k}` on the last letter `⟨κ, b, i⟩` of a chain. -/
private lemma mc_letterP_tail {N : ℕ} (e : Fin N ⊕ OffDiag N) (k : ℕ) {ℓ : Letter (N + 1)}
    (h1 : ℓ.i ≠ Fin.last N) (h2 : ℓ.j = Fin.last N) : ∀ w ∈ letterP (mcLiftE e) k ℓ,
      ∃ r ℓ', w = r ++ [ℓ'] ∧ ℓ'.i ≠ Fin.last N ∧ ℓ'.j = Fin.last N ∧ ∀ x ∈ r, mcFixed x := by
  intro w hw
  unfold letterP at hw
  split_ifs at hw with hk
  · simp only [List.mem_singleton] at hw
    exact ⟨[], ℓ, by simpa using hw, h1, h2, by simp⟩
  · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    obtain ⟨a, b, mid, rfl, ha, hb, hmid⟩ := mc_starWords_shape e _ k' ℓ.i ℓ.j w hw
    refine ⟨⟨ℓ.kind.plain, ℓ.i, a⟩ :: mid, ⟨ℓ.kind.plain, b, ℓ.j⟩, by simp, hb, h2, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨h1, ha⟩
    · exact hmid x hx

/-- `P_{γ,k}` on fixed letters followed by a last letter `⟨κ, b, i⟩`. -/
private lemma mc_wordP_tail {N : ℕ} (e : Fin N ⊕ OffDiag N) {ℓ₂ : Letter (N + 1)}
    (h1 : ℓ₂.i ≠ Fin.last N) (h2 : ℓ₂.j = Fin.last N) :
    ∀ (mid : Word (N + 1)) (k : List ℕ), (∀ x ∈ mid, mcFixed x) →
      k.length = mid.length + 1 → ∀ u ∈ wordP (mcLiftE e) k (mid ++ [ℓ₂]),
      ∃ r ℓ', u = r ++ [ℓ'] ∧ ℓ'.i ≠ Fin.last N ∧ ℓ'.j = Fin.last N ∧ ∀ x ∈ r, mcFixed x
  | [], [], _, h, _, _ => by simp at h
  | [], k :: _ :: _, _, h, _, _ => by simp at h
  | [], [k], _, _, u, hu => by
    simp only [List.nil_append, wordP, List.mem_flatMap, List.mem_map, List.mem_singleton] at hu
    obtain ⟨v, hv, _, rfl, rfl⟩ := hu
    simpa using mc_letterP_tail e k h1 h2 v hv
  | _ :: _, [], _, h, _, _ => by simp at h
  | ℓ :: mid, k :: ks, hmid, h, u, hu => by
    simp only [List.cons_append, wordP, List.mem_flatMap, List.mem_map] at hu
    obtain ⟨v, hv, u', hu', rfl⟩ := hu
    obtain ⟨r, ℓ', rfl, hℓ'1, hℓ'2, hr⟩ := mc_wordP_tail e h1 h2 mid ks
      (fun x hx => hmid x (List.mem_cons_of_mem _ hx)) (by simpa using h) u' hu'
    refine ⟨v ++ r, ℓ', by simp, hℓ'1, hℓ'2, fun x hx => ?_⟩
    rcases List.mem_append.1 hx with hx | hx
    · exact mc_letterP_fixed e k (hmid ℓ List.mem_cons_self) v hv x hx
    · exact hr x hx

/-- The two shapes of `mcForm` are preserved by `P_{γ,k}`. -/
private lemma mc_wordP_form {N : ℕ} (e : Fin N ⊕ OffDiag N) {β : Word (N + 1)} (hβ : mcForm β)
    (k : List ℕ) (hk : k.length = β.length) : ∀ β' ∈ wordP (mcLiftE e) k β, mcForm β' := by
  intro β' hβ'
  rcases hβ with ⟨κ, hκ, rfl⟩ | ⟨ℓ₁, mid, ℓ₂, rfl, h11, h12, h21, h22, hmid⟩
  · obtain ⟨k0, rfl⟩ : ∃ k0, k = [k0] := by
      match k, hk with
      | [k0], _ => exact ⟨k0, rfl⟩
    simp only [wordP, List.mem_flatMap, List.mem_map, List.mem_singleton] at hβ'
    obtain ⟨v, hv, _, rfl, rfl⟩ := hβ'
    rw [List.append_nil]
    unfold letterP at hv
    split_ifs at hv with hk0
    · simp only [List.mem_singleton] at hv
      exact Or.inl ⟨κ, hκ, hv⟩
    · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      obtain ⟨a, b, mid, rfl, ha, hb, hmid⟩ := mc_starWords_shape e _ k' _ _ v hv
      exact Or.inr ⟨_, mid, _, rfl, rfl, ha, hb, rfl, hmid⟩
  · obtain ⟨k0, ks, rfl⟩ : ∃ k0 ks, k = k0 :: ks := by
      match k, hk with
      | k0 :: ks, _ => exact ⟨k0, ks, rfl⟩
    simp only [wordP, List.mem_flatMap, List.mem_map] at hβ'
    obtain ⟨v, hv, u', hu', rfl⟩ := hβ'
    obtain ⟨ℓ', r0, rfl, h1, h2, hr0⟩ := mc_letterP_head e k0 h11 h12 v hv
    obtain ⟨r, ℓ'', rfl, h3, h4, hr⟩ := mc_wordP_tail e h21 h22 mid ks hmid
      (by simpa using hk) u' hu'
    refine Or.inr ⟨ℓ', r0 ++ r, ℓ'', by simp, h1, h2, h3, h4, fun x hx => ?_⟩
    rcases List.mem_append.1 hx with hx | hx
    · exact hr0 x hx
    · exact hr x hx

/-! ### Products of blocks -/

/-- The word `β₁[i₁] ⋯ β_n[i_n]` over `Fin N`, the block `β_t` with `i_t` for its variable. -/
private def mcSubB {N : ℕ} : List (Fin N) → List (Word (N + 1)) → Word N
  | i :: is, β :: βs => β.map (mcSubL i) ++ mcSubB is βs
  | _, _ => []

/-- `P_{γ,k}` on a product of blocks, blockwise. -/
private def mcBlockP {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    List ℕ → List (Word (N + 1)) → List (List (Word (N + 1)))
  | _, [] => [[]]
  | k, β :: βs => (wordP (mcLiftE e) (k.take β.length) β).flatMap fun β' =>
      (mcBlockP e (k.drop β.length) βs).map (β' :: ·)

private lemma mc_wordP_subB {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    ∀ (is : List (Fin N)) (βs : List (Word (N + 1))) (k : List ℕ), is.length = βs.length →
      k.length = (βs.map List.length).sum →
      wordP e k (mcSubB is βs) = (mcBlockP e k βs).map (mcSubB is)
  | [], [], k, _, _ => by simp [mcSubB, mcBlockP, wordP]
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | i :: is, β :: βs, k, h1, h2 => by
    simp only [List.map_cons, List.sum_cons] at h2
    simp only [mcSubB, mcBlockP]
    conv_lhs => rw [← List.take_append_drop β.length k]
    rw [mc_wordP_append e _ _ _ _ (by simp; omega), ← mc_wordP_map,
      mc_wordP_subB e is βs (k.drop β.length) (by simpa using h1) (by simp; omega)]
    simp [List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def, mcSubB]

private lemma mc_mem_blockP {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    ∀ (βs : List (Word (N + 1))) (k : List ℕ), (∀ β ∈ βs, mcForm β) →
      k.length = (βs.map List.length).sum → ∀ βs' ∈ mcBlockP e k βs,
      βs'.length = βs.length ∧ (βs'.map List.length).sum = (βs.map List.length).sum + k.sum ∧
        ∀ β ∈ βs', mcForm β
  | [], k, _, hk, βs', h => by
    simp only [List.map_nil, List.sum_nil, List.length_eq_zero_iff] at hk
    subst hk
    simp only [mcBlockP, List.mem_singleton] at h
    subst h
    simp
  | β :: βs, k, hf, hk, βs', h => by
    simp only [List.map_cons, List.sum_cons] at hk
    simp only [mcBlockP, List.mem_flatMap, List.mem_map] at h
    obtain ⟨β', hβ', r, hr, rfl⟩ := h
    have htake : (k.take β.length).length = β.length := by simp; omega
    obtain ⟨h1, h2, h3⟩ := mc_mem_blockP e βs (k.drop β.length)
      (fun x hx => hf x (List.mem_cons_of_mem _ hx)) (by simp; omega) r hr
    have hl := iterate_mem_wordP_length (mcLiftE e) (k.take β.length) β htake β' hβ'
    refine ⟨by simp [h1], ?_, fun x hx => ?_⟩
    · simp only [List.map_cons, List.sum_cons, h2, hl]
      have := List.sum_take_add_sum_drop k β.length
      omega
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact mc_wordP_form e (hf β List.mem_cons_self) _ htake x hβ'
      · exact h3 x hx

/-! ### Weighted sums of products of blocks -/

/-- All index lists `(i₁, …, i_n)` in `Fin N`. -/
private def mcAllIdx (N : ℕ) : ℕ → List (List (Fin N))
  | 0 => [[]]
  | n + 1 => (List.finRange N).flatMap fun i => (mcAllIdx N n).map (i :: ·)

private lemma mc_mem_allIdx {N : ℕ} : ∀ (n : ℕ), ∀ is ∈ mcAllIdx N n, is.length = n
  | 0, is, h => by simp [mcAllIdx] at h; simp [h]
  | n + 1, is, h => by
    simp only [mcAllIdx, List.mem_flatMap, List.mem_map] at h
    obtain ⟨i, -, is', h', rfl⟩ := h
    simp [mc_mem_allIdx n is' h']

private lemma mc_length_allIdx (N : ℕ) : ∀ n : ℕ, (mcAllIdx N n).length = N ^ n
  | 0 => by simp [mcAllIdx]
  | n + 1 => by
    simp only [mcAllIdx, List.length_flatMap, List.length_map, mc_length_allIdx N n,
      List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul]
    ring

/-- The formal sum `Σ_{i₁…i_n} Σ_{(c, β)} c · β₁[i₁] ⋯ β_n[i_n]`. -/
private def mcInst {N : ℕ} (n : ℕ) (T : List (ℝ × List (Word (N + 1)))) : FSum N :=
  (mcAllIdx N n).flatMap fun is => T.map fun cb => (cb.1, mcSubB is cb.2)

/-- `P_{γ,k}` on weighted products of blocks. -/
private def mcOpB {N : ℕ} (e : Fin N ⊕ OffDiag N) (k : List ℕ)
    (T : List (ℝ × List (Word (N + 1)))) : List (ℝ × List (Word (N + 1))) :=
  T.flatMap fun cb => (mcBlockP e k cb.2).map fun βs => (cb.1, βs)

/-- `P_{γ_n,k_n} ⋯ P_{γ_1,k_1}` on weighted products of blocks. -/
private def mcIterB {N : ℕ} :
    List ((Fin N ⊕ OffDiag N) × List ℕ) → List (ℝ × List (Word (N + 1))) →
      List (ℝ × List (Word (N + 1)))
  | [], T => T
  | x :: d, T => mcIterB d (mcOpB x.1 x.2 T)

/-- Nonnegative weights, `n` blocks of total length `s`, each of one of the two shapes. -/
private def mcInv {N : ℕ} (n s : ℕ) (T : List (ℝ × List (Word (N + 1)))) : Prop :=
  ∀ cb ∈ T, 0 ≤ cb.1 ∧ cb.2.length = n ∧ (cb.2.map List.length).sum = s ∧ ∀ β ∈ cb.2, mcForm β

private lemma mc_opP_inst {N : ℕ} (e : Fin N ⊕ OffDiag N) (k : List ℕ) {n s : ℕ}
    {T : List (ℝ × List (Word (N + 1)))} (hT : mcInv n s T) (hk : k.length = s) :
    opP e k (mcInst n T) = mcInst n (mcOpB e k T) ∧ mcInv n (s + k.sum) (mcOpB e k T) := by
  refine ⟨?_, fun cb hcb => ?_⟩
  · simp only [mcInst, opP, List.flatMap_assoc, mcOpB]
    refine List.flatMap_congr fun is his => ?_
    rw [List.flatMap_map, List.map_flatMap]
    refine List.flatMap_congr fun cb hcb => ?_
    obtain ⟨-, h1, h2, -⟩ := hT cb hcb
    rw [mc_wordP_subB e is cb.2 k (by rw [mc_mem_allIdx n is his, h1]) (by rw [h2, hk]),
      List.map_map, List.map_map]
    rfl
  · simp only [mcOpB, List.mem_flatMap, List.mem_map] at hcb
    obtain ⟨cb0, hcb0, βs, hβs, rfl⟩ := hcb
    obtain ⟨h0, h1, h2, h3⟩ := hT cb0 hcb0
    obtain ⟨g1, g2, g3⟩ := mc_mem_blockP e cb0.2 k h3 (by rw [h2, hk]) βs hβs
    exact ⟨h0, by rw [g1, h1], by rw [g2, h2], g3⟩

private lemma mc_iterP_inst {N : ℕ} {ξ : ℕ} :
    ∀ (d : List ((Fin N ⊕ OffDiag N) × List ℕ)) (n s : ℕ) (T : List (ℝ × List (Word (N + 1)))),
      mcInv n s T → IterAdm ξ s d →
      iterP d (mcInst n T) = mcInst n (mcIterB d T) ∧
        mcInv n (s + (d.map fun x => x.2.sum).sum) (mcIterB d T)
  | [], n, s, T, hT, _ => by simpa [iterP, mcIterB] using hT
  | x :: d, n, s, T, hT, hd => by
    obtain ⟨hl, -, -, hd'⟩ := hd
    obtain ⟨h1, h2⟩ := mc_opP_inst x.1 x.2 hT hl
    obtain ⟨h3, h4⟩ := mc_iterP_inst d n (s + x.2.sum) _ h2 hd'
    refine ⟨by rw [iterP, h1, h3, mcIterB], ?_⟩
    simp only [List.map_cons, List.sum_cons, mcIterB]
    rwa [← add_assoc]

private lemma mc_weight_inst {N : ℕ} (n : ℕ) (T : List (ℝ × List (Word (N + 1)))) :
    ((mcInst n T).map Prod.fst).sum = (N : ℝ) ^ n * (T.map Prod.fst).sum := by
  have h : ∀ L : List (List (Fin N)),
      ((L.flatMap fun is => T.map fun cb => (cb.1, mcSubB is cb.2)).map Prod.fst).sum =
        L.length * (T.map Prod.fst).sum := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_map]
      simp only [Function.comp_def, List.length_cons]
      push_cast
      ring
  rw [mcInst, h, mc_length_allIdx]
  push_cast
  ring

/-! ### Evaluation of products of blocks: the factorisation (6.44)–(6.45) -/

private lemma mc_sum_flatMap {α β : Type*} (L : List α) (f : α → List β) (g : β → ℂ) :
    ((L.flatMap f).map g).sum = (L.map fun a => ((f a).map g).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih]; simp

private lemma mc_sum_comm {α β : Type*} (L : List α) (T : List β) (f : α → β → ℂ) :
    (L.map fun a => (T.map fun b => f a b).sum).sum =
      (T.map fun b => (L.map fun a => f a b).sum).sum := by
  induction T with
  | nil => simp
  | cons b T ih => simp only [List.map_cons, List.sum_cons, List.sum_map_add, ih]

/-- `Σ_{i₁…i_n} β₁[i₁] ⋯ β_n[i_n] = Π_t Σ_i β_t[i]`. -/
private lemma mc_sum_subB {N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (m : ℂ) :
    ∀ (n : ℕ) (βs : List (Word (N + 1))), βs.length = n →
      ((mcAllIdx N n).map fun is => evalWord S m (mcSubB is βs)).sum =
        (βs.map fun β => ∑ i : Fin N, evalWord S m (β.map (mcSubL i))).prod
  | 0, [], _ => by simp [mcAllIdx, mcSubB, evalWord]
  | 0, _ :: _, h => by simp at h
  | n + 1, [], h => by simp at h
  | n + 1, β :: βs, h => by
    rw [mcAllIdx, mc_sum_flatMap, List.map_cons, List.prod_cons, Fin.sum_univ_def,
      ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
    simp only [List.map_map, Function.comp_def, mcSubB, evalWord_append, List.sum_map_mul_left]
    rw [mc_sum_subB S m n βs (by simpa using h)]

/-- The value of the formal sum `mcInst n T`. -/
private lemma mc_evalF_inst {N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (m : ℂ) (n : ℕ)
    (T : List (ℝ × List (Word (N + 1)))) (hT : ∀ cb ∈ T, cb.2.length = n) :
    evalF S m (mcInst n T) = (T.map fun cb => (cb.1 : ℂ) *
      (cb.2.map fun β => ∑ i : Fin N, evalWord S m (β.map (mcSubL i))).prod).sum := by
  rw [evalF, mcInst, mc_sum_flatMap]
  simp only [List.map_map, Function.comp_def]
  rw [mc_sum_comm]
  refine congrArg List.sum (List.map_congr_left fun cb hcb => ?_)
  rw [List.sum_map_mul_left, mc_sum_subB S m n cb.2 (hT cb hcb)]

private lemma mc_norm_evalWord_le {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ) {K : ℝ}
    (hK : 0 ≤ K) : ∀ w : Word N, (∀ ℓ ∈ w, ‖evalLetter G m ℓ‖ ≤ K) →
      ‖evalWord G m w‖ ≤ K ^ w.length
  | [], _ => by simp [evalWord]
  | ℓ :: w, h => by
    have h1 := h ℓ List.mem_cons_self
    have h2 := mc_norm_evalWord_le G m hK w fun x hx => h x (List.mem_cons_of_mem _ hx)
    have : evalWord G m (ℓ :: w) = evalLetter G m ℓ * evalWord G m w := by simp [evalWord]
    rw [this, norm_mul, List.length_cons, pow_succ']
    exact mul_le_mul h1 h2 (norm_nonneg _) hK

private lemma mc_norm_evalLetter_of_ne {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ)
    (ℓ : Letter N) (h : ℓ.i ≠ ℓ.j) : ‖evalLetter G m ℓ‖ = ‖G ℓ.i ℓ.j‖ := by
  rcases ℓ with ⟨κ, i, j⟩
  cases κ <;> simp [evalLetter, h]

private lemma mc_norm_evalLetter_le_add {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ)
    (ℓ : Letter N) : ‖evalLetter G m ℓ‖ ≤ ‖G ℓ.i ℓ.j‖ + ‖m‖ := by
  have hc : ‖G ℓ.i ℓ.j - if ℓ.i = ℓ.j then m else 0‖ ≤ ‖G ℓ.i ℓ.j‖ + ‖m‖ := by
    refine (norm_sub_le _ _).trans ?_
    split_ifs <;> simp
  rcases ℓ with ⟨κ, i, j⟩
  cases κ <;> simp only [evalLetter, norm_star]
  · linarith [norm_nonneg m]
  · linarith [norm_nonneg m]
  · exact hc
  · exact hc

/-- One factor of (6.45): `|Σ_i β[i]| ≤ N 3^{|β|} (X² + Y + 18/N)` when `|G_ij| ≤ 2`,
`|G_ij| ≤ X` for `i ≠ j` and `|Σ_i (G_ii - m)| ≤ N Y`. -/
private lemma mc_block_le {N : ℕ} (hN : 0 < N) {S : Matrix (Fin N) (Fin N) ℂ} {m : ℂ} {X Y : ℝ}
    (hS : ∀ i j, ‖S i j‖ ≤ 2) (hm : ‖m‖ ≤ 1) (hX : ∀ i j, i ≠ j → ‖S i j‖ ≤ X) (hX0 : 0 ≤ X)
    (hY : ‖∑ i, (S i i - m)‖ ≤ N * Y) (hY0 : 0 ≤ Y) {β : Word (N + 1)} (hβ : mcForm β) :
    ‖∑ i : Fin N, evalWord S m (β.map (mcSubL i))‖ ≤ N * 3 ^ β.length * (X ^ 2 + Y + 18 / N) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h18 : (N : ℝ) * (18 / N) = 18 := by field_simp
  rcases hβ with ⟨κ, hκ, rfl⟩ | ⟨ℓ₁, mid, ℓ₂, rfl, h11, h12, h21, h22, hmid⟩
  · have hD : ‖∑ i : Fin N, evalWord S m ([(⟨κ, Fin.last N, Fin.last N⟩ : Letter (N + 1))].map
        (mcSubL i))‖ ≤ N * Y := by
      rcases hκ with rfl | rfl
      · simpa [evalWord, evalLetter, mcSubL, mcSub_last] using hY
      · have e : ∑ i : Fin N, evalWord S m
            ([(⟨.gcbar, Fin.last N, Fin.last N⟩ : Letter (N + 1))].map (mcSubL i)) =
            star (∑ i, (S i i - m)) := by
          rw [star_sum]
          simp [evalWord, evalLetter, mcSubL, mcSub_last]
        rw [e, norm_star]
        exact hY
    refine hD.trans ?_
    simp only [List.length_singleton, pow_one]
    nlinarith [sq_nonneg X]
  · set i0 : Fin N := ⟨0, hN⟩
    set a := mcSub i0 ℓ₁.j
    set b := mcSub i0 ℓ₂.i
    set c := evalWord S m (mid.map (mcSubL i0))
    have hmid' : ∀ i, mid.map (mcSubL i) = mid.map (mcSubL i0) := fun i =>
      List.map_congr_left fun ℓ hℓ => by
        simp only [mcSubL, mcSub_of_ne i i0 (hmid ℓ hℓ).1, mcSub_of_ne i i0 (hmid ℓ hℓ).2]
    have h1 : ∀ i, mcSubL i ℓ₁ = ⟨ℓ₁.kind, i, a⟩ := fun i => by
      simp only [mcSubL, h11, mcSub_last, a, mcSub_of_ne i i0 h12]
    have h2 : ∀ i, mcSubL i ℓ₂ = ⟨ℓ₂.kind, b, i⟩ := fun i => by
      simp only [mcSubL, h22, mcSub_last, b, mcSub_of_ne i i0 h21]
    have hc : ‖c‖ ≤ 3 ^ mid.length := by
      have := mc_norm_evalWord_le S m (by norm_num : (0 : ℝ) ≤ 3) (mid.map (mcSubL i0))
        fun ℓ _ => monomial_norm_evalLetter_le hS hm ℓ
      simpa using this
    have heq : ∀ i, evalWord S m ((ℓ₁ :: (mid ++ [ℓ₂])).map (mcSubL i)) =
        evalLetter S m ⟨ℓ₁.kind, i, a⟩ * c * evalLetter S m ⟨ℓ₂.kind, b, i⟩ := fun i => by
      simp only [List.map_cons, List.map_append, h1, h2, hmid' i, List.map_nil]
      simp only [evalWord, List.map_cons, List.prod_cons, List.map_append, List.prod_append,
        List.map_nil, List.prod_nil, mul_one, c]
      ring
    have hpt : ∀ i, ‖evalLetter S m ⟨ℓ₁.kind, i, a⟩‖ * ‖evalLetter S m ⟨ℓ₂.kind, b, i⟩‖ ≤
        X ^ 2 + (if i = a then 9 else 0) + (if i = b then 9 else 0) := by
      intro i
      have g1 := monomial_norm_evalLetter_le hS hm ⟨ℓ₁.kind, i, a⟩
      have g2 := monomial_norm_evalLetter_le hS hm ⟨ℓ₂.kind, b, i⟩
      have n1 := norm_nonneg (evalLetter S m ⟨ℓ₁.kind, i, a⟩)
      have n2 := norm_nonneg (evalLetter S m ⟨ℓ₂.kind, b, i⟩)
      have hX2 := sq_nonneg X
      have h9 : ‖evalLetter S m ⟨ℓ₁.kind, i, a⟩‖ * ‖evalLetter S m ⟨ℓ₂.kind, b, i⟩‖ ≤ 9 := by
        nlinarith
      split_ifs with ha hb hb
      · linarith
      · linarith
      · linarith
      · rw [add_zero, add_zero, mc_norm_evalLetter_of_ne S m _ ha,
          mc_norm_evalLetter_of_ne S m _ (Ne.symm hb)]
        have := hX i a ha
        have := hX b i (Ne.symm hb)
        nlinarith [norm_nonneg (S i a), norm_nonneg (S b i)]
    have hsum : ∑ i : Fin N, (X ^ 2 + (if i = a then (9 : ℝ) else 0) + (if i = b then 9 else 0)) =
        N * X ^ 2 + 18 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
      simp
      ring
    simp_rw [heq]
    calc ‖∑ i : Fin N, evalLetter S m ⟨ℓ₁.kind, i, a⟩ * c * evalLetter S m ⟨ℓ₂.kind, b, i⟩‖
        ≤ ∑ i : Fin N, ‖c‖ * (‖evalLetter S m ⟨ℓ₁.kind, i, a⟩‖ *
            ‖evalLetter S m ⟨ℓ₂.kind, b, i⟩‖) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [norm_mul, norm_mul]
          exact le_of_eq (by ring)
      _ ≤ ∑ i : Fin N, 3 ^ mid.length *
            (X ^ 2 + (if i = a then (9 : ℝ) else 0) + (if i = b then 9 else 0)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul hc (hpt i) (by positivity) (by positivity)
      _ = 3 ^ mid.length * (N * X ^ 2 + 18) := by rw [← Finset.mul_sum, hsum]
      _ ≤ _ := by
          have hl : (ℓ₁ :: (mid ++ [ℓ₂])).length = mid.length + 2 := by simp
          rw [hl, pow_add]
          have h3 : (0 : ℝ) < 3 ^ mid.length := by positivity
          have : N * X ^ 2 + 18 ≤ N * 3 ^ 2 * (X ^ 2 + Y + 18 / N) := by
            have : (N : ℝ) * 3 ^ 2 * (X ^ 2 + Y + 18 / N) = 9 * N * X ^ 2 + 9 * N * Y + 9 * 18 := by
              have e : (N : ℝ) * 3 ^ 2 * (X ^ 2 + Y + 18 / N) =
                  9 * N * X ^ 2 + 9 * N * Y + 9 * (N * (18 / N)) := by ring
              rw [e, h18]
            rw [this]
            nlinarith [mul_nonneg hNr.le (sq_nonneg X), mul_nonneg hNr.le hY0]
          nlinarith

private lemma mc_norm_list_sum_le {α : Type*} (L : List α) (f : α → ℂ) (g : α → ℝ)
    (h : ∀ a ∈ L, ‖f a‖ ≤ g a) : ‖(L.map f).sum‖ ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add (h a List.mem_cons_self)
      (ih fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- (6.45) for one product of blocks. -/
private lemma mc_norm_prod_le {N : ℕ} (hN : 0 < N) {S : Matrix (Fin N) (Fin N) ℂ} {m : ℂ}
    {X Y : ℝ} (hS : ∀ i j, ‖S i j‖ ≤ 2) (hm : ‖m‖ ≤ 1) (hX : ∀ i j, i ≠ j → ‖S i j‖ ≤ X)
    (hX0 : 0 ≤ X) (hY : ‖∑ i, (S i i - m)‖ ≤ N * Y) (hY0 : 0 ≤ Y) :
    ∀ βs : List (Word (N + 1)), (∀ β ∈ βs, mcForm β) →
      ‖(βs.map fun β => ∑ i : Fin N, evalWord S m (β.map (mcSubL i))).prod‖ ≤
        (N : ℝ) ^ βs.length * 3 ^ (βs.map List.length).sum * (X ^ 2 + Y + 18 / N) ^ βs.length
  | [], _ => by simp
  | β :: βs, h => by
    have h1 := mc_block_le hN hS hm hX hX0 hY hY0 (h β List.mem_cons_self)
    have h2 := mc_norm_prod_le hN hS hm hX hX0 hY hY0 βs fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.map_cons, List.prod_cons, List.length_cons, List.sum_cons, norm_mul]
    calc _ ≤ (N * 3 ^ β.length * (X ^ 2 + Y + 18 / N)) *
          ((N : ℝ) ^ βs.length * 3 ^ (βs.map List.length).sum * (X ^ 2 + Y + 18 / N) ^ βs.length) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring

/-- (6.45): the value of `mcInst n T` on the event. -/
private lemma mc_norm_evalF_inst_le {N : ℕ} (hN : 0 < N) {S : Matrix (Fin N) (Fin N) ℂ} {m : ℂ}
    {X Y : ℝ} (hS : ∀ i j, ‖S i j‖ ≤ 2) (hm : ‖m‖ ≤ 1) (hX : ∀ i j, i ≠ j → ‖S i j‖ ≤ X)
    (hX0 : 0 ≤ X) (hY : ‖∑ i, (S i i - m)‖ ≤ N * Y) (hY0 : 0 ≤ Y) {n s : ℕ}
    {T : List (ℝ × List (Word (N + 1)))} (hT : mcInv n s T) :
    ‖evalF S m (mcInst n T)‖ ≤
      (T.map Prod.fst).sum * ((N : ℝ) ^ n * 3 ^ s * (X ^ 2 + Y + 18 / N) ^ n) := by
  rw [mc_evalF_inst S m n T fun cb hcb => (hT cb hcb).2.1, ← List.sum_map_mul_right]
  refine mc_norm_list_sum_le _ _ _ fun cb hcb => ?_
  obtain ⟨h0, h1, h2, h3⟩ := hT cb hcb
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  refine mul_le_mul_of_nonneg_left ?_ h0
  have := mc_norm_prod_le hN hS hm hX hX0 hY hY0 cb.2 h3
  rwa [h1, h2] at this

/-- A formal sum with nonnegative weights whose words are bounded by `K`. -/
private lemma mc_norm_evalF_le {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ) {K : ℝ} :
    ∀ F : FSum N, (∀ cw ∈ F, 0 ≤ cw.1 ∧ ‖evalWord G m cw.2‖ ≤ K) →
      ‖evalF G m F‖ ≤ (F.map Prod.fst).sum * K := by
  intro F hF
  rw [evalF, ← List.sum_map_mul_right]
  refine mc_norm_list_sum_le _ _ _ fun cw hcw => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hF cw hcw).1]
  exact mul_le_mul_of_nonneg_left (hF cw hcw).2 (hF cw hcw).1

/-! ### The word `|m - m_sc|^p` -/

/-- The blocks of `(m - m_sc)^h (conj (m - m_sc))^h`: `h` centred diagonal letters and `h`
conjugate ones. -/
private def mcBlocks0 (N h : ℕ) : List (Word (N + 1)) :=
  List.replicate h [⟨.gc, Fin.last N, Fin.last N⟩] ++
    List.replicate h [⟨.gcbar, Fin.last N, Fin.last N⟩]

private lemma mc_inv_init (N h : ℕ) :
    mcInv (2 * h) (2 * h) [(((N : ℝ) ^ (2 * h))⁻¹, mcBlocks0 N h)] := by
  intro cb hcb
  simp only [List.mem_singleton] at hcb
  subst hcb
  refine ⟨by positivity, by simp [mcBlocks0]; ring, ?_, fun β hβ => ?_⟩
  · simp only [mcBlocks0, List.map_append, List.map_replicate, List.sum_append,
      List.sum_replicate, List.length_singleton, smul_eq_mul]
    ring
  · simp only [mcBlocks0, List.mem_append, List.mem_replicate] at hβ
    rcases hβ with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact Or.inl ⟨.gc, Or.inl rfl, rfl⟩
    · exact Or.inl ⟨.gcbar, Or.inr rfl, rfl⟩

/-- The formal sum `Σ_I N^{-p} w_I` for the word `|m - m_sc|^p` of (6.39)–(6.42) evaluates to
`|N⁻¹ Σ_i (G_ii - m)|^p`. -/
private lemma mc_evalF_init {N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (m : ℂ)
    (h : ℕ) : evalF S m (mcInst (2 * h) [(((N : ℝ) ^ (2 * h))⁻¹, mcBlocks0 N h)]) =
      ((‖(N : ℂ)⁻¹ * ∑ i, (S i i - m)‖ ^ (2 * h) : ℝ) : ℂ) := by
  rw [mc_evalF_inst S m (2 * h) _ (fun cb hcb => by
    simp only [List.mem_singleton] at hcb; subst hcb; simp [mcBlocks0]; ring)]
  set D := ∑ i, (S i i - m)
  have h1 : ∑ i : Fin N, evalWord S m [mcSubL i (⟨.gc, Fin.last N, Fin.last N⟩ : Letter (N + 1))] =
      D := by
    simp [evalWord, evalLetter, mcSubL, mcSub_last, D]
  have h2 : ∑ i : Fin N, evalWord S m [mcSubL i (⟨.gcbar, Fin.last N, Fin.last N⟩ :
      Letter (N + 1))] = (starRingEnd ℂ) D := by
    have : (starRingEnd ℂ) D = star D := rfl
    rw [this, star_sum]
    simp [evalWord, evalLetter, mcSubL, mcSub_last]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, mcBlocks0,
    List.map_append, List.map_replicate, List.prod_append, List.prod_replicate, h1, h2]
  have hD : D ^ h * (starRingEnd ℂ) D ^ h = ((‖D‖ ^ 2 : ℝ) : ℂ) ^ h := by
    rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hD, norm_mul, norm_inv, Complex.norm_natCast]
  push_cast
  ring

private lemma mc_stieltjes_sub {N : ℕ} (hN : 0 < N) (z : ℂ) (ω : Entries N) :
    stieltjesM (symOfEntries ω) z - msc z = (N : ℂ)⁻¹ * ∑ i, (resS z ω i i - msc z) := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_sub, ← mul_assoc, inv_mul_cancel₀ hN', one_mul]
  rfl

private lemma mc_length_subB {N : ℕ} : ∀ (is : List (Fin N)) (βs : List (Word (N + 1))),
    is.length = βs.length → (mcSubB is βs).length = (βs.map List.length).sum
  | [], [], _ => by simp [mcSubB]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | i :: is, β :: βs, h => by
    simp [mcSubB, mc_length_subB is βs (by simpa using h)]

private lemma mc_mem_inst {N n s : ℕ} {T : List (ℝ × List (Word (N + 1)))} (hT : mcInv n s T) :
    ∀ cw ∈ mcInst n T, 0 ≤ cw.1 ∧ cw.2.length = s := by
  intro cw hcw
  simp only [mcInst, List.mem_flatMap, List.mem_map] at hcw
  obtain ⟨is, his, cb, hcb, rfl⟩ := hcw
  obtain ⟨h0, h1, h2, -⟩ := hT cb hcb
  exact ⟨h0, by rw [mc_length_subB is cb.2 (by rw [mc_mem_allIdx n is his, h1]), h2]⟩

/-- `3^p + 2 ≤ (2p)^{2p}` for `p = 2h ≥ 2`. -/
private lemma mc_const_le (h : ℕ) (hh : 1 ≤ h) :
    (3 : ℝ) ^ (2 * h) + 2 ≤ ((2 : ℝ) * ((2 * h : ℕ) : ℝ)) ^ ((2 : ℝ) * ((2 * h : ℕ) : ℝ)) := by
  have e : (2 : ℝ) * ((2 * h : ℕ) : ℝ) = ((4 * h : ℕ) : ℝ) := by push_cast; ring
  rw [e, Real.rpow_natCast]
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 1 := ⟨h - 1, by omega⟩
  have h1 : (3 : ℝ) ^ (2 * (n + 1)) + 2 ≤ 4 ^ (2 * (n + 1)) := by
    have a1 : (3 : ℝ) ^ (2 * n) ≤ 4 ^ (2 * n) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have a2 : (1 : ℝ) ≤ 4 ^ (2 * n) := one_le_pow₀ (by norm_num)
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add, pow_add]
    norm_num
    linarith
  have h2 : (4 : ℝ) ^ (2 * (n + 1)) ≤ (((4 * (n + 1) : ℕ) : ℝ)) ^ (4 * (n + 1)) := by
    have hb : (4 : ℝ) ≤ ((4 * (n + 1) : ℕ) : ℝ) := by
      push_cast
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    calc (4 : ℝ) ^ (2 * (n + 1)) ≤ ((4 * (n + 1) : ℕ) : ℝ) ^ (2 * (n + 1)) :=
          pow_le_pow_left₀ (by norm_num) hb _
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  linarith

/-! ### Lemma 5.4 -/

/-- Lemma 5.4 (5.11), for matched pairs: if (5.10) holds for `H̃` at `z` with
3-high probability (constants `c', C'`), then for even `p ≤ φ`,
`E|m - m_sc|^p ≤ E|m̃ - m_sc|^p + (Cp)^{Cp} (X² + Y + φ N⁻¹)^p`. -/
theorem moment_comparison {C1 φq : ℝ} (hφq : 0 < φq) :
    ∃ C0 > (0 : ℝ), ∀ c' > (0 : ℝ), ∀ C' > (0 : ℝ), ∃ C > (0 : ℝ), ∃ N0 : ℕ, ∀ N ≥ N0,
      ∀ (Lv Lw : EntryLaws N) (q : ℝ),
      MatchedPair C1 q Lv Lw → (N : ℝ) ^ φq ≤ q →
      ∀ z ∈ specDomain N C0, ∀ X Y : ℝ, 0 ≤ X → 0 ≤ Y →
        Lw.law {ω | (∀ i j, i ≠ j → ‖resS z ω i j‖ ≤ X) ∧
            ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ Y}ᶜ ≤
          ENNReal.ofReal ((N : ℝ) ^ C' * Real.exp (-c' * phi N ^ (3 : ℝ))) →
        ∀ p : ℕ, Even p → (p : ℝ) ≤ phi N →
          ∫ ω, ‖stieltjesM (symOfEntries ω) z - msc z‖ ^ p ∂Lv.law ≤
            ∫ ω, ‖stieltjesM (symOfEntries ω) z - msc z‖ ^ p ∂Lw.law +
              (C * p) ^ (C * p) * (X ^ 2 + Y + phi N / N) ^ p := by
  obtain ⟨C0i, hC0i, N0i, hiter⟩ := comparison_iterate (C1 := C1) (φq := φq) (Ks := 1) hφq one_pos
  obtain ⟨C0g, hC0g, cg, hcg, Cg, hCg, N0g, hgood⟩ := highProb_goodEvent (C1 := C1) hφq
  refine ⟨max C0i C0g, lt_max_of_lt_left hC0i, fun c' hc' C' hC' => ?_⟩
  set K1 : ℝ := 1 + (6 / φq + 1) * (10 / φq + 1) with hK1
  set cm : ℝ := min cg c' with hcmdef
  set Cn : ℕ := ⌈max (Cg : ℝ) C'⌉₊ + 1 with hCndef
  have hcm : 0 < cm := lt_min hcg hc'
  have hev := (eventually_ge_atTop (max (max N0i N0g) 16)).and <|
    (expansion_eventually_le_phi 18).and <|
    (((tendsto_rpow_atTop (by positivity : (0 : ℝ) < φq / 20)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 6).and <|
    (expansion_eventually_log_le ((2 * (2 * K1) + Cn) / cm))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨2, two_pos, N0, fun N hN Lv Lw q hmp hq z hz X Y hX0 hY0 hA p hp hpϕ => ?_⟩
  obtain ⟨hNbig, hϕ18, hρ6, hlogϕ⟩ := hN0 N hN
  have hρ6' : (6 : ℝ) ≤ (N : ℝ) ^ (φq / 20) := hρ6
  clear hρ6 hev hN0
  have hNi : N0i ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hNbig
  have hNg : N0g ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hNbig
  have hN16 : 16 ≤ N := le_trans (le_max_right _ _) hNbig
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hN0r : (0 : ℝ) < N := by linarith
  have hNpos : 0 < N := by omega
  have hϕ1 : 1 ≤ phi N := by linarith
  have hPv := isProbabilityMeasure_law hmp.isProb_v
  have hPw := isProbabilityMeasure_law hmp.isProb_w
  -- `p = 0`
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · simp only [pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one, Nat.cast_zero,
      mul_zero, Real.rpow_zero]
    norm_num
  obtain ⟨h, hh⟩ := hp
  obtain rfl : p = 2 * h := by omega
  have hh1 : 1 ≤ h := by omega
  -- the spectral domain
  have hzi : z ∈ specDomain N C0i := ⟨hz.1, lt_of_le_of_lt (div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hϕ1 (le_max_left _ _)) hN0r.le) hz.2.1, hz.2.2⟩
  have hzg : z ∈ specDomain N C0g := ⟨hz.1, lt_of_le_of_lt (div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hϕ1 (le_max_right _ _)) hN0r.le) hz.2.1, hz.2.2⟩
  have hzim : 0 < z.im := lt_of_le_of_lt (by positivity) hz.2.1
  have hzB : 1 / z.im ≤ N := by
    have h1 : 1 ≤ phi N ^ (max C0i C0g) :=
      Real.one_le_rpow hϕ1 (le_trans hC0i.le (le_max_left _ _))
    have h2 : 1 / (N : ℝ) < z.im := lt_of_le_of_lt (div_le_div_of_nonneg_right h1 hN0r.le) hz.2.1
    rw [div_le_iff₀ hzim]
    rw [div_lt_iff₀ hN0r] at h2
    linarith
  have hm1 : ‖msc z‖ ≤ 1 := (norm_msc_eq_inv_and_lt_one hzim).2.le
  -- the formal sum `F` for the word `|m - m_sc|^p` of (6.39)–(6.42)
  set T0 : List (ℝ × List (Word (N + 1))) := [(((N : ℝ) ^ (2 * h))⁻¹, mcBlocks0 N h)] with hT0
  set F : FSum N := mcInst (2 * h) T0 with hFdef
  have hinv0 := mc_inv_init N h
  have hF : ∀ cw ∈ F, 0 ≤ cw.1 ∧ cw.2.length = 2 * h := mc_mem_inst hinv0
  have hF1 : (F.map Prod.fst).sum = 1 := by
    rw [hFdef, mc_weight_inst]
    simp only [hT0, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact mul_inv_cancel₀ (by positivity)
  have hFval : ∀ ω : Entries N, evalF (resS z ω) (msc z) F =
      ((‖stieltjesM (symOfEntries ω) z - msc z‖ ^ (2 * h) : ℝ) : ℂ) := by
    intro ω
    rw [hFdef, hT0, mc_evalF_init, mc_stieltjes_sub hNpos]
  have hFint : ∀ μ : Measure (Entries N), ∫ ω, evalF (resS z ω) (msc z) F ∂μ =
      ((∫ ω, ‖stieltjesM (symOfEntries ω) z - msc z‖ ^ (2 * h) ∂μ : ℝ) : ℂ) := by
    intro μ
    simp_rw [hFval]
    exact integral_ofReal
  -- the probability of the event `E` = (6.1) ∩ (5.10)
  set A : Set (Entries N) := {ω | (∀ i j, i ≠ j → ‖resS z ω i j‖ ≤ X) ∧
    ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ Y} with hAdef
  set E : Set (Entries N) := goodEvent N C0g ∩ A with hEdef
  set Pb : ℝ := (Lw.law Eᶜ).toReal with hPbdef
  have hP0 : 0 ≤ Pb := ENNReal.toReal_nonneg
  have hPb : Pb ≤ (N : ℝ) ^ Cn * Real.exp (-cm * phi N ^ 3) := by
    have h3 : phi N ^ (3 : ℝ) = phi N ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast (phi N) 3
    have hg := hgood N hNg Lw ⟨Lv, Lw, q, 0, hmp, hq, (interp_lexPos_zero Lv Lw).symm⟩
    simp only [h3] at hg hA
    set M : ℝ := max (Cg : ℝ) C'
    have hφ3 : 0 ≤ phi N ^ 3 := by positivity
    have hMg : (N : ℝ) ^ Cg ≤ (N : ℝ) ^ M := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
    have hMc : (N : ℝ) ^ C' ≤ (N : ℝ) ^ M :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_right _ _)
    have hMn : (N : ℝ) ^ M ≤ (N : ℝ) ^ ⌈M⌉₊ := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil _)
    have he1 : Real.exp (-cg * phi N ^ 3) ≤ Real.exp (-cm * phi N ^ 3) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_left cg c'])
    have he2 : Real.exp (-c' * phi N ^ 3) ≤ Real.exp (-cm * phi N ^ 3) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_right cg c'])
    have hx0 : 0 ≤ (N : ℝ) ^ Cg * Real.exp (-cg * phi N ^ 3) := by positivity
    have hy0 : 0 ≤ (N : ℝ) ^ C' * Real.exp (-c' * phi N ^ 3) := by positivity
    have hU : Lw.law Eᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ Cg * Real.exp (-cg * phi N ^ 3) +
        (N : ℝ) ^ C' * Real.exp (-c' * phi N ^ 3)) := by
      rw [ENNReal.ofReal_add hx0 hy0, hEdef, Set.compl_inter]
      exact (measure_union_le _ _).trans (add_le_add hg hA)
    refine (ENNReal.toReal_le_of_le_ofReal (add_nonneg hx0 hy0) hU).trans ?_
    have hE0 : 0 ≤ Real.exp (-cm * phi N ^ 3) := (Real.exp_pos _).le
    have hNM : 0 ≤ (N : ℝ) ^ M := by positivity
    calc _ ≤ (N : ℝ) ^ M * Real.exp (-cm * phi N ^ 3) + (N : ℝ) ^ M * Real.exp (-cm * phi N ^ 3) :=
          add_le_add (mul_le_mul hMg he1 (Real.exp_pos _).le hNM)
            (mul_le_mul hMc he2 (Real.exp_pos _).le hNM)
      _ = 2 * (N : ℝ) ^ M * Real.exp (-cm * phi N ^ 3) := by ring
      _ ≤ N * (N : ℝ) ^ ⌈M⌉₊ * Real.exp (-cm * phi N ^ 3) := by
          gcongr
          linarith
      _ = _ := by rw [hCndef, pow_succ]; ring
  -- the bound `B` of the premise of `comparison_iterate`
  set Q : ℝ := X ^ 2 + Y + 18 / N with hQdef
  have hQ0 : 0 ≤ Q := by positivity
  set B : ℝ := 3 ^ (2 * h) * Q ^ (2 * h) + ((N : ℝ) ^ (2 * h))⁻¹ with hBdef
  have hB0 : 0 ≤ B := by positivity
  set ζ : ℝ := ((2 * h : ℕ) : ℝ) with hζdef
  have hζ1 : 1 ≤ ζ := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh1
    rw [hζdef]
    push_cast
    linarith
  have hprem : ∀ d : List ((Fin N ⊕ OffDiag N) × List ℕ), d ≠ [] → d.length ≤ ⌈6 * ζ / φq⌉₊ →
      IterAdm (xiOf (2 * ζ + 3) φq) (2 * h) d →
      (N : ℝ) ^ (-(φq / 20) * (d.map fun x => ((x.2.sum : ℕ) : ℝ)).sum) *
        ‖∫ ω, evalF (resS z ω) (msc z) (iterP d F) ∂Lw.law‖ ≤ B := by
    intro d _ hdl hd
    rw [iterate_cast_ord]
    set o := iterate_ord d with hodef
    obtain ⟨hGeq, hGinv⟩ := mc_iterP_inst d (2 * h) (2 * h) T0 hinv0 hd
    change mcInv (2 * h) (2 * h + o) (mcIterB d T0) at hGinv
    obtain ⟨hGp, hGW⟩ := iterate_iterP_props d (2 * h) F hd hF
    rw [hF1, mul_one] at hGW
    change ((iterP d F).map Prod.fst).sum ≤ 2 ^ o at hGW
    have hWT : ((mcIterB d T0).map Prod.fst).sum * (N : ℝ) ^ (2 * h) ≤ 2 ^ o := by
      rw [hGeq, mc_weight_inst] at hGW
      linarith
    -- the length bound
    have hlen : ((2 * (2 * h + o) : ℕ) : ℝ) ≤ 2 * K1 * phi N ^ 2 := by
      have h1 := iterate_ord_le d (2 * h) hd
      have h2 : o ≤ ⌈6 * ζ / φq⌉₊ * xiOf (2 * ζ + 3) φq :=
        h1.trans (Nat.mul_le_mul_right _ hdl)
      have h3 := iterate_len_le hφq one_pos hζ1 hpϕ (s := 2 * h) (by rw [one_mul])
      have h4 : ((2 * h + o : ℕ) : ℝ) ≤
          ((2 * h : ℕ) : ℝ) + (⌈6 * ζ / φq⌉₊ : ℝ) * (xiOf (2 * ζ + 3) φq : ℝ) := by
        push_cast
        exact_mod_cast Nat.add_le_add_left h2 (2 * h)
      have : ((2 * (2 * h + o) : ℕ) : ℝ) = 2 * ((2 * h + o : ℕ) : ℝ) := by push_cast; ring
      rw [this, hK1]
      linarith
    -- the pointwise bounds
    have hgoodpt : ∀ ω ∈ E, ‖evalF (resS z ω) (msc z) (iterP d F)‖ ≤
        2 ^ o * 3 ^ (2 * h + o) * Q ^ (2 * h) := by
      intro ω hω
      obtain ⟨hωg, hωX, hωY⟩ := hω
      have hS : ∀ i j, ‖resS z ω i j‖ ≤ 2 := fun i j => (hωg z hzg i j).1
      have hD : ‖∑ i, (resS z ω i i - msc z)‖ ≤ N * Y := by
        rw [mc_stieltjes_sub hNpos, norm_mul, norm_inv, Complex.norm_natCast] at hωY
        rwa [inv_mul_le_iff₀ hN0r] at hωY
      rw [hGeq]
      refine (mc_norm_evalF_inst_le hNpos hS hm1 hωX hX0 hD hY0 hGinv).trans ?_
      calc _ = (((mcIterB d T0).map Prod.fst).sum * (N : ℝ) ^ (2 * h)) *
            (3 ^ (2 * h + o) * Q ^ (2 * h)) := by ring
        _ ≤ 2 ^ o * (3 ^ (2 * h + o) * Q ^ (2 * h)) :=
            mul_le_mul_of_nonneg_right hWT (by positivity)
        _ = _ := by ring
    have hbadpt : ∀ ω, ‖evalF (resS z ω) (msc z) (iterP d F)‖ ≤
        2 ^ o * ((N : ℝ) + 1) ^ (2 * h + o) := by
      intro ω
      refine (mc_norm_evalF_le _ _ (K := ((N : ℝ) + 1) ^ (2 * h + o)) (iterP d F)
        fun cw hcw => ⟨(hGp cw hcw).1, ?_⟩).trans ?_
      · rw [← (hGp cw hcw).2]
        refine mc_norm_evalWord_le _ _ (by positivity) _ fun ℓ _ => ?_
        refine (mc_norm_evalLetter_le_add _ _ ℓ).trans ?_
        have := (norm_resolventC_apply_le (symOfEntries_isHermitian ω) hzim ℓ.i ℓ.j).trans hzB
        exact add_le_add this hm1
      · exact mul_le_mul_of_nonneg_right hGW (by positivity)
    have hint := expansion_norm_integral_le (μ := Lw.law) (G := E) (by positivity)
      (Eventually.of_forall hgoodpt) (Eventually.of_forall hbadpt)
    -- the exponents
    have hbad := iterate_bad_le (by omega : 2 ≤ N) hcm hlen hϕ1 hlogϕ hPb hP0
    set ρ : ℝ := (N : ℝ) ^ (φq / 20) with hρ
    have hρ0 : 0 < ρ := by positivity
    have hpow : (N : ℝ) ^ (-(φq / 20) * (o : ℝ)) = (ρ ^ o)⁻¹ := by
      rw [show -(φq / 20) * (o : ℝ) = (φq / 20) * (-(o : ℝ)) by ring, Real.rpow_mul hN0r.le,
        Real.rpow_neg hρ0.le, Real.rpow_natCast]
    rw [hpow]
    have h6 : (6 : ℝ) ^ o ≤ ρ ^ o := pow_le_pow_left₀ (by norm_num) hρ6' o
    have hρ1 : (ρ ^ o)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    have hgood' : (ρ ^ o)⁻¹ * (2 ^ o * 3 ^ (2 * h + o) * Q ^ (2 * h)) ≤
        3 ^ (2 * h) * Q ^ (2 * h) := by
      have e : (2 : ℝ) ^ o * 3 ^ (2 * h + o) * Q ^ (2 * h) =
          6 ^ o * (3 ^ (2 * h) * Q ^ (2 * h)) := by
        rw [pow_add, show (6 : ℝ) = 2 * 3 by norm_num, mul_pow]; ring
      rw [e, ← mul_assoc]
      have : (ρ ^ o)⁻¹ * 6 ^ o ≤ 1 := by
        rw [inv_mul_le_iff₀ (by positivity), mul_one]; exact h6
      have h0 : 0 ≤ 3 ^ (2 * h) * Q ^ (2 * h) := by positivity
      simpa using mul_le_mul_of_nonneg_right this h0
    have hbad' : 2 ^ o * ((N : ℝ) + 1) ^ (2 * h + o) * Pb ≤ ((N : ℝ) ^ (2 * h))⁻¹ := by
      have hNp : 0 < (N : ℝ) ^ (2 * h) := by positivity
      have h2N : (N : ℝ) ^ (2 * h) * 2 ^ o ≤ ((N : ℝ) + 1) ^ (2 * h + o) := by
        rw [pow_add]
        exact mul_le_mul (pow_le_pow_left₀ hN0r.le (by linarith) _)
          (pow_le_pow_left₀ (by norm_num) (by linarith) _) (by positivity) (by positivity)
      have key : (N : ℝ) ^ (2 * h) * (2 ^ o * ((N : ℝ) + 1) ^ (2 * h + o) * Pb) ≤ 1 := by
        calc _ = ((N : ℝ) ^ (2 * h) * 2 ^ o) * ((N : ℝ) + 1) ^ (2 * h + o) * Pb := by ring
          _ ≤ ((N : ℝ) + 1) ^ (2 * h + o) * ((N : ℝ) + 1) ^ (2 * h + o) * Pb := by gcongr
          _ = ((N : ℝ) + 1) ^ (2 * (2 * h + o)) * Pb := by ring
          _ ≤ 1 := hbad
      calc _ = ((N : ℝ) ^ (2 * h))⁻¹ * ((N : ℝ) ^ (2 * h) *
            (2 ^ o * ((N : ℝ) + 1) ^ (2 * h + o) * Pb)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hNp.ne', one_mul]
        _ ≤ ((N : ℝ) ^ (2 * h))⁻¹ * 1 := mul_le_mul_of_nonneg_left key (by positivity)
        _ = _ := mul_one _
    have hρ0' : 0 ≤ (ρ ^ o)⁻¹ := by positivity
    have hbP : 0 ≤ 2 ^ o * ((N : ℝ) + 1) ^ (2 * h + o) * Pb := by positivity
    calc (ρ ^ o)⁻¹ * ‖∫ ω, evalF (resS z ω) (msc z) (iterP d F) ∂Lw.law‖
        ≤ (ρ ^ o)⁻¹ * (2 ^ o * 3 ^ (2 * h + o) * Q ^ (2 * h) +
            2 ^ o * ((N : ℝ) + 1) ^ (2 * h + o) * Pb) := mul_le_mul_of_nonneg_left hint hρ0'
      _ = (ρ ^ o)⁻¹ * (2 ^ o * 3 ^ (2 * h + o) * Q ^ (2 * h)) +
            (ρ ^ o)⁻¹ * (2 ^ o * ((N : ℝ) + 1) ^ (2 * h + o) * Pb) := mul_add _ _ _
      _ ≤ 3 ^ (2 * h) * Q ^ (2 * h) + 1 * (2 ^ o * ((N : ℝ) + 1) ^ (2 * h + o) * Pb) :=
          add_le_add hgood' (mul_le_mul_of_nonneg_right hρ1 hbP)
      _ ≤ B := by rw [one_mul, hBdef]; linarith
  -- the iteration
  have hmain := hiter N hNi Lv Lw q hmp hq (N * (N + 1) / 2) ζ hζ1 (by rw [hζdef]; exact hpϕ)
    (2 * h) (by rw [hζdef, one_mul]) z hzi F hF hF1 B hB0 hprem
  rw [interp_lexPos_top, hFint, hFint, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs] at hmain
  have hIw : 0 ≤ ∫ ω, ‖stieltjesM (symOfEntries ω) z - msc z‖ ^ (2 * h) ∂Lw.law :=
    integral_nonneg fun ω => by positivity
  rw [abs_of_nonneg hIw] at hmain
  have hIv := le_abs_self (∫ ω, ‖stieltjesM (symOfEntries ω) z - msc z‖ ^ (2 * h) ∂Lv.law)
  have hNζ : (N : ℝ) ^ (-ζ) = ((N : ℝ) ^ (2 * h))⁻¹ := by
    rw [hζdef, Real.rpow_neg hN0r.le, Real.rpow_natCast]
  rw [hNζ] at hmain
  -- the normalisation
  set R : ℝ := X ^ 2 + Y + phi N / N with hRdef
  have hQR : Q ≤ R := by
    have : 18 / (N : ℝ) ≤ phi N / N := div_le_div_of_nonneg_right hϕ18 hN0r.le
    rw [hQdef, hRdef]
    linarith
  have hNR : ((N : ℝ) ^ (2 * h))⁻¹ ≤ R ^ (2 * h) := by
    rw [← inv_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have : (N : ℝ)⁻¹ ≤ phi N / N := by
      rw [div_eq_mul_inv]
      exact le_mul_of_one_le_left (by positivity) hϕ1
    rw [hRdef]
    nlinarith [sq_nonneg X]
  have hQR' : Q ^ (2 * h) ≤ R ^ (2 * h) := pow_le_pow_left₀ hQ0 hQR _
  have hC := mc_const_le h hh1
  have hR0 : 0 ≤ R ^ (2 * h) := by positivity
  have h3 : (0 : ℝ) ≤ 3 ^ (2 * h) := by positivity
  calc _ ≤ _ := hIv
    _ ≤ _ := hmain
    _ = (∫ ω, ‖stieltjesM (symOfEntries ω) z - msc z‖ ^ (2 * h) ∂Lw.law) +
        3 ^ (2 * h) * Q ^ (2 * h) + 2 * ((N : ℝ) ^ (2 * h))⁻¹ := by rw [hBdef]; ring
    _ ≤ (∫ ω, ‖stieltjesM (symOfEntries ω) z - msc z‖ ^ (2 * h) ∂Lw.law) +
        (3 ^ (2 * h) + 2) * R ^ (2 * h) := by
          have := mul_le_mul_of_nonneg_left hQR' h3
          linarith
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_right hC hR0
        linarith

/-! ### Compiled checks at concrete nondegenerate points -/

open private lawV lawW lawVW_matchedPair diagV diagW
  from WEdgeNS.Comparison.Classes
open private phi_sixteen_bounds from WEdgeNS.Comparison.GoodEvent

/-- With `X ≥ η⁻¹` and `Y ≥ η⁻¹ + 1` the event of (5.10) is everything, so its complement has
probability `0`. -/
private lemma mc_law_compl_le {N : ℕ} (hN : 0 < N) (L : EntryLaws N) {z : ℂ} (hz : 0 < z.im)
    {X Y : ℝ} (hX : 1 / z.im ≤ X) (hY : 1 / z.im + 1 ≤ Y) (r : ℝ) :
    L.law {ω | (∀ i j, i ≠ j → ‖resS z ω i j‖ ≤ X) ∧
        ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ Y}ᶜ ≤ ENNReal.ofReal r := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have huniv : {ω : Entries N | (∀ i j, i ≠ j → ‖resS z ω i j‖ ≤ X) ∧
      ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ Y} = Set.univ := by
    refine Set.eq_univ_of_forall fun ω => ⟨fun i j _ =>
      (norm_resolventC_apply_le (symOfEntries_isHermitian ω) hz i j).trans hX, ?_⟩
    have hm : ‖stieltjesM (symOfEntries ω) z‖ ≤ 1 / z.im := by
      have h1 : ‖∑ i, resS z ω i i‖ ≤ N * (1 / z.im) := by
        refine (norm_sum_le _ _).trans ?_
        calc ∑ i, ‖resS z ω i i‖ ≤ ∑ _i : Fin N, 1 / z.im := Finset.sum_le_sum fun i _ =>
              norm_resolventC_apply_le (symOfEntries_isHermitian ω) hz i i
          _ = _ := by simp
      have e : stieltjesM (symOfEntries ω) z = (N : ℂ)⁻¹ * ∑ i, resS z ω i i := rfl
      rw [e, norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hNr]
      exact h1
    calc _ ≤ ‖stieltjesM (symOfEntries ω) z‖ + ‖msc z‖ := norm_sub_le _ _
      _ ≤ 1 / z.im + 1 := add_le_add hm (norm_msc_eq_inv_and_lt_one hz).2.le
      _ ≤ Y := hY
  rw [huniv, Set.compl_univ, measure_empty]
  exact zero_le

/-- The (5.10) hypothesis of `moment_comparison` at a concrete point: `X = η⁻¹`, `Y = η⁻¹ + 1`,
for every law, every `z` in the upper half-plane and all constants `c', C'`. -/
example {N : ℕ} (hN : 0 < N) (L : EntryLaws N) {z : ℂ} (hz : 0 < z.im) (c' C' : ℝ) :
    L.law {ω | (∀ i j, i ≠ j → ‖resS z ω i j‖ ≤ 1 / z.im) ∧
        ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ 1 / z.im + 1}ᶜ ≤
      ENNReal.ofReal ((N : ℝ) ^ C' * Real.exp (-c' * phi N ^ (3 : ℝ))) :=
  mc_law_compl_le hN L hz le_rfl le_rfl _

/-- The class of `moment_comparison` (`MatchedPair` with `q ≥ N^{φq}`) is nonempty for all large
`N`: it contains the Rademacher laws against themselves, `C1 = 2`, `φq = 2/5`, `q = N^{2/5}`. -/
example : ∀ᶠ N : ℕ in atTop, ∃ (Lv Lw : EntryLaws N) (q : ℝ),
    MatchedPair 2 q Lv Lw ∧ (N : ℝ) ^ (2 / 5 : ℝ) ≤ q := by
  filter_upwards [expansion_matchedPair_radLaws] with N h
  exact ⟨radLaws N, radLaws N, _, h, le_rfl⟩

/-- `moment_comparison` for `C1 = 2`, `φq = 2/5`, `c' = C' = 1`, the Rademacher laws against
themselves with `q = N^{2/5}`, `z = i`, `X = 1`, `Y = 2` and `p = 2`: all hypotheses hold for all
large `N`. -/
example : ∃ C0 > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, Complex.I ∈ specDomain N C0 ∧
    ∫ ω, ‖stieltjesM (symOfEntries ω) Complex.I - msc Complex.I‖ ^ 2 ∂(radLaws N).law ≤
      ∫ ω, ‖stieltjesM (symOfEntries ω) Complex.I - msc Complex.I‖ ^ 2 ∂(radLaws N).law +
        (C * (2 : ℕ)) ^ (C * (2 : ℕ)) * ((1 : ℝ) ^ 2 + 2 + phi N / N) ^ 2 := by
  obtain ⟨C0, hC0, h⟩ := moment_comparison (C1 := 2) (φq := 2 / 5) (by norm_num)
  obtain ⟨C, hC, N0, h⟩ := h 1 one_pos 1 one_pos
  refine ⟨C0, hC0, C, hC, ?_⟩
  filter_upwards [expansion_matchedPair_radLaws, eventually_ge_atTop N0, eventually_ge_atTop 16,
    expansion_eventually_le_phi 2, phi_rpow_le_rpow C0 (by norm_num : (0 : ℝ) < 1 / 2)]
    with N hmp hN h16 hφ hφC
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast h16
  have hzI : Complex.I ∈ specDomain N C0 := by
    refine ⟨by simp, ?_, by simp⟩
    have h1 : (N : ℝ) ^ (1 / 2 : ℝ) < (N : ℝ) ^ (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
    rw [Real.rpow_one] at h1
    rw [Complex.I_im, div_lt_one (by linarith)]
    linarith
  refine ⟨hzI, ?_⟩
  exact h N hN (radLaws N) (radLaws N) _ hmp le_rfl Complex.I hzI 1 2 zero_le_one zero_le_two
    (mc_law_compl_le (by omega) _ (by simp) (by simp) (by norm_num) _) 2 even_two
    (by exact_mod_cast hφ)

/-- The hypotheses of `moment_comparison` other than `N ≥ N0` and `z ∈ S(C0)`, at `N = 16`,
`C1 = 2`, `φq = 1/4`, `z = i`, `X = 1`, `Y = 2`, `p = 2` and all `c', C'`, for two different
laws: `lawV` and `lawW` form a matched pair with `q = 16^{1/4}` and differ in the fourth diagonal
moment. -/
example (c' C' : ℝ) : ∃ q : ℝ, MatchedPair 2 q lawV lawW ∧ ((16 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) ≤ q ∧
    lawW.law {ω | (∀ i j, i ≠ j → ‖resS Complex.I ω i j‖ ≤ 1) ∧
        ‖stieltjesM (symOfEntries ω) Complex.I - msc Complex.I‖ ≤ 2}ᶜ ≤
      ENNReal.ofReal (((16 : ℕ) : ℝ) ^ C' * Real.exp (-c' * phi 16 ^ (3 : ℝ))) ∧
    Even 2 ∧ ((2 : ℕ) : ℝ) ≤ phi 16 ∧
    lawV.entryMoment (Sum.inl 0) 4 ≠ lawW.entryMoment (Sum.inl 0) 4 := by
  obtain ⟨h1, -⟩ := phi_sixteen_bounds
  refine ⟨_, lawVW_matchedPair, le_rfl, mc_law_compl_le (by norm_num) _ (by simp) (by simp)
    (by norm_num) _, even_two, by exact_mod_cast h1, ?_⟩
  simp only [EntryLaws.entryMoment, EntryLaws.entry, Sum.elim_inl, lawV, lawW]
  rw [integral_unifList, integral_unifList]
  norm_num [diagV, diagW]

#print axioms moment_comparison

end WEdgeNS
