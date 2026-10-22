import WEdgeNS.Comparison.ExpansionInv
import WEdgeNS.Comparison.Iterate

/-!
# Moments of expanded resolvent pairs
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

open private iterate_ord iterate_ord_le iterate_wordP_length_le iterate_mem_wordP_length
  iterate_opP_props iterate_integral_evalF_cons iterate_integral_evalF_opP_cons
  from WEdgeNS.Comparison.Iterate
open private expansion_norm_integral_le expansion_continuous_resR expansion_card_highIdx_le
  expansion_mem_highIdx expansion_eventually_le_phi expansion_eventually_log_le
  from WEdgeNS.Comparison.Expansion
open private tilde_pos from WEdgeNS.Comparison.Classes

/-! ### Off-diagonal letters with a free index

For a set `D` of fixed indices, a letter `G_xy` is counted when `x ≠ y` and one of `x, y` is not in
`D`. The operators `P_{γ,k}` whose entries have their indices in `D` never decrease this count:
each chain of (6.12) starts at `x` and ends at `y`, and its inner indices lie in `D`. -/

/-- The indices of the entry `e`: `{a}` on the diagonal, `{a, b}` off it. -/
private def pm_idx {N : ℕ} : Fin N ⊕ OffDiag N → Finset (Fin N)
  | Sum.inl a => {a}
  | Sum.inr p => {p.1.1, p.1.2}

private lemma pm_idx_card_le {N : ℕ} (e : Fin N ⊕ OffDiag N) : (pm_idx e).card ≤ 2 := by
  rcases e with a | p
  · simp [pm_idx]
  · exact Finset.card_le_two

private lemma pm_mem_entryPairs {N : ℕ} {e : Fin N ⊕ OffDiag N} {xy : Fin N × Fin N}
    (h : xy ∈ entryPairs e) : xy.1 ∈ pm_idx e ∧ xy.2 ∈ pm_idx e := by
  rcases e with a | p
  · simp only [entryPairs, List.mem_singleton] at h
    subst h
    simp [pm_idx]
  · simp only [entryPairs, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp [pm_idx]

/-- The number of letters `G_xy` of `w` with `x ≠ y` and `x ∉ D` or `y ∉ D`. -/
private def pm_nD {N : ℕ} (D : Finset (Fin N)) (w : Word N) : ℕ :=
  w.countP fun ℓ => decide (ℓ.i ≠ ℓ.j ∧ (ℓ.i ∉ D ∨ ℓ.j ∉ D))

private lemma pm_nD_cons {N : ℕ} (D : Finset (Fin N)) (ℓ : Letter N) (w : Word N) :
    pm_nD D (ℓ :: w) = pm_nD D w + if ℓ.i ≠ ℓ.j ∧ (ℓ.i ∉ D ∨ ℓ.j ∉ D) then 1 else 0 := by
  simp only [pm_nD, List.countP_cons, decide_eq_true_eq]

private lemma pm_nD_append {N : ℕ} (D : Finset (Fin N)) (w w' : Word N) :
    pm_nD D (w ++ w') = pm_nD D w + pm_nD D w' := by
  simp only [pm_nD, List.countP_append]

private lemma pm_nD_nil {N : ℕ} (D : Finset (Fin N)) : pm_nD D [] = 0 := rfl

/-- A chain `G_{y x₁} ⋯ G_{y_n j}` with `y ∈ D`-inner indices ends with a counted letter when
`j ∉ D`. -/
private lemma pm_star_last {N : ℕ} {e : Fin N ⊕ OffDiag N} {D : Finset (Fin N)}
    (hD : pm_idx e ⊆ D) (κ : LetterKind) :
    ∀ (n : ℕ) (y j : Fin N) (c : Word N), c ∈ starWords e κ n y j → j ∉ D →
      (y ≠ j ∨ 0 < n) → 1 ≤ pm_nD D c
  | 0, y, j, c, hc, hj, h => by
    simp only [starWords, List.mem_singleton] at hc
    subst hc
    have hyj : y ≠ j := h.resolve_right (lt_irrefl 0)
    rw [pm_nD_cons, pm_nD_nil]
    simp [hyj, hj]
  | n + 1, y, j, c, hc, hj, _ => by
    simp only [starWords, List.mem_flatMap, List.mem_map] at hc
    obtain ⟨xy, hxy, c', hc', rfl⟩ := hc
    have h2 := hD (pm_mem_entryPairs hxy).2
    have ih := pm_star_last hD κ n xy.2 j c' hc' hj (Or.inl fun h => hj (h ▸ h2))
    rw [pm_nD_cons]
    omega

/-- A chain of at least one step from `i ∉ D` starts with a counted letter, and ends with another
one when `j ∉ D`. -/
private lemma pm_star_first {N : ℕ} {e : Fin N ⊕ OffDiag N} {D : Finset (Fin N)}
    (hD : pm_idx e ⊆ D) (κ : LetterKind) (n : ℕ) (i j : Fin N) (c : Word N)
    (hc : c ∈ starWords e κ (n + 1) i j) (hi : i ∉ D) :
    1 + (if j ∉ D then 1 else 0) ≤ pm_nD D c := by
  simp only [starWords, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨xy, hxy, c', hc', rfl⟩ := hc
  have h1 := hD (pm_mem_entryPairs hxy).1
  have h2 := hD (pm_mem_entryPairs hxy).2
  have hix : i ≠ xy.1 := fun h => hi (h ▸ h1)
  rw [pm_nD_cons]
  have hfirst : (if (⟨κ, i, xy.1⟩ : Letter N).i ≠ (⟨κ, i, xy.1⟩ : Letter N).j ∧
      ((⟨κ, i, xy.1⟩ : Letter N).i ∉ D ∨ (⟨κ, i, xy.1⟩ : Letter N).j ∉ D) then 1 else 0) = 1 :=
    ite_eq_left ⟨hix, Or.inl hi⟩
  rw [hfirst]
  by_cases hj : j ∈ D
  · simp only [hj, not_true_eq_false, ↓reduceIte]
    omega
  · have := pm_star_last hD κ n xy.2 j c' hc' hj (Or.inl fun h => hj (h ▸ h2))
    simp only [hj, not_false_eq_true, ↓reduceIte]
    omega

/-- `P_{γ,k}` on one letter does not decrease the count. -/
private lemma pm_letterP_mono {N : ℕ} {e : Fin N ⊕ OffDiag N} {D : Finset (Fin N)}
    (hD : pm_idx e ⊆ D) (k : ℕ) (ℓ : Letter N) :
    ∀ c ∈ letterP e k ℓ, pm_nD D [ℓ] ≤ pm_nD D c := by
  intro c hc
  unfold letterP at hc
  split_ifs at hc with hk
  · simp only [List.mem_singleton] at hc
    rw [hc]
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := Nat.exists_eq_succ_of_ne_zero hk
    rw [pm_nD_cons, pm_nD_nil]
    split_ifs with hℓ
    · rcases hℓ.2 with hi | hj
      · have := pm_star_first hD _ n ℓ.i ℓ.j c hc hi
        omega
      · have := pm_star_last hD _ (n + 1) ℓ.i ℓ.j c hc hj (Or.inr (Nat.succ_pos n))
        omega
    · omega

/-- `P_{γ,k}` on a word does not decrease the count. -/
private lemma pm_wordP_mono {N : ℕ} {e : Fin N ⊕ OffDiag N} {D : Finset (Fin N)}
    (hD : pm_idx e ⊆ D) : ∀ (k : List ℕ) (w : Word N), ∀ u ∈ wordP e k w, pm_nD D w ≤ pm_nD D u
  | _, [] => by
    intro u hu
    simp only [wordP, List.mem_singleton] at hu
    rw [hu]
  | [], ℓ :: w => by
    intro u hu
    simp only [wordP, List.mem_map] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    have := pm_wordP_mono hD [] w u' hu'
    rw [pm_nD_cons, pm_nD_cons]
    omega
  | k :: ks, ℓ :: w => by
    intro u hu
    simp only [wordP, List.mem_flatMap, List.mem_map] at hu
    obtain ⟨c, hc, u', hu', rfl⟩ := hu
    have h1 := pm_letterP_mono hD k ℓ c hc
    have h2 := pm_wordP_mono hD ks w u' hu'
    have e1 : pm_nD D (ℓ :: w) = pm_nD D [ℓ] + pm_nD D w := by
      rw [← pm_nD_append]; rfl
    rw [e1, pm_nD_append]
    omega

/-- `P_{γ,k}` on a counted letter `G_ij` with `i ∉ D`, `j ∉ D`: at least one counted letter, and
two when `k ≥ 1`. -/
private lemma pm_letterP_gen {N : ℕ} {e : Fin N ⊕ OffDiag N} {D : Finset (Fin N)}
    (hD : pm_idx e ⊆ D) (k : ℕ) {κ : LetterKind} {i j : Fin N} (hij : i ≠ j) (hi : i ∉ D)
    (hj : j ∉ D) : ∀ c ∈ letterP e k ⟨κ, i, j⟩, 1 + (if k = 0 then 0 else 1) ≤ pm_nD D c := by
  intro c hc
  by_cases hk : k = 0
  · have := pm_letterP_mono hD k ⟨κ, i, j⟩ c hc
    rw [pm_nD_cons, pm_nD_nil] at this
    simp only [ne_eq, hij, not_false_eq_true, hi, true_or, and_self, ↓reduceIte] at this
    simp only [hk, ↓reduceIte]
    omega
  · unfold letterP at hc
    rw [ite_eq_right hk] at hc
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := Nat.exists_eq_succ_of_ne_zero hk
    have := pm_star_first hD _ n i j c hc hi
    simp only [hj, not_false_eq_true, ↓reduceIte] at this
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    omega

/-- (6.99): every word of `P_{γ,k}(G_ij conj G_ij)` with `|k| ≥ 1`, `i ≠ j`, `i, j ∉ D` has at
least three counted letters. -/
private lemma pm_pair_gen {N : ℕ} {e : Fin N ⊕ OffDiag N} {D : Finset (Fin N)}
    (hD : pm_idx e ⊆ D) {k : List ℕ} (hk2 : k.length = 2) (hk1 : 1 ≤ k.sum) {i j : Fin N}
    (hij : i ≠ j) (hi : i ∉ D) (hj : j ∉ D) (κ₁ κ₂ : LetterKind) :
    ∀ u ∈ wordP e k [⟨κ₁, i, j⟩, ⟨κ₂, i, j⟩], 3 ≤ pm_nD D u := by
  obtain ⟨k₁, k₂, rfl⟩ := List.length_eq_two.1 hk2
  intro u hu
  simp only [wordP, List.mem_flatMap, List.mem_map, List.mem_singleton] at hu
  obtain ⟨c₁, hc₁, u', ⟨c₂, hc₂, u'', rfl, rfl⟩, rfl⟩ := hu
  have h1 := pm_letterP_gen hD k₁ hij hi hj c₁ hc₁
  have h2 := pm_letterP_gen hD k₂ hij hi hj c₂ hc₂
  simp only [List.sum_cons, List.sum_nil] at hk1
  rw [pm_nD_append, pm_nD_append, pm_nD_nil]
  split_ifs at h1 h2 <;> omega

/-! ### Conjugate words and words of plain letters -/

/-- The conjugate letter: `G_ij ↔ conj G_ij`, centred or not. -/
private def pm_conjL {N : ℕ} (ℓ : Letter N) : Letter N :=
  ⟨match ℓ.kind with
    | .g => .gbar
    | .gbar => .g
    | .gc => .gcbar
    | .gcbar => .gc, ℓ.i, ℓ.j⟩

private lemma pm_evalLetter_conjL {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ) (ℓ : Letter N) :
    evalLetter G m (pm_conjL ℓ) = star (evalLetter G m ℓ) := by
  rcases ℓ with ⟨κ, i, j⟩
  cases κ <;> simp only [pm_conjL, evalLetter, star_star] <;> congr 2

private lemma pm_evalWord_conj {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ) :
    ∀ w : Word N, evalWord G m (w.map pm_conjL) = star (evalWord G m w)
  | [] => by simp [evalWord]
  | ℓ :: w => by
    have ih := pm_evalWord_conj G m w
    simp only [evalWord, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, pm_evalLetter_conjL, star_mul']

private lemma pm_nD_conj {N : ℕ} (D : Finset (Fin N)) (w : Word N) :
    pm_nD D (w.map pm_conjL) = pm_nD D w := by
  simp only [pm_nD, List.countP_map]
  rfl

private lemma pm_evalWord_flatten {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ) :
    ∀ L : List (Word N), evalWord G m L.flatten = (L.map (evalWord G m)).prod
  | [] => by simp [evalWord]
  | w :: L => by
    rw [List.flatten_cons, evalWord_append, pm_evalWord_flatten G m L, List.map_cons,
      List.prod_cons]

/-- A letter is plain when it is `G_ij` or `conj G_ij` (no centring). -/
private def pm_plainL {N : ℕ} (ℓ : Letter N) : Prop := ℓ.kind = .g ∨ ℓ.kind = .gbar

private lemma pm_evalLetter_plain {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m m' : ℂ) {ℓ : Letter N}
    (h : pm_plainL ℓ) : evalLetter G m ℓ = evalLetter G m' ℓ := by
  rcases ℓ with ⟨κ, i, j⟩
  rcases h with h | h <;> simp only at h <;> subst h <;> rfl

private lemma pm_evalWord_plain {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m m' : ℂ) :
    ∀ w : Word N, (∀ ℓ ∈ w, pm_plainL ℓ) → evalWord G m w = evalWord G m' w
  | [], _ => rfl
  | ℓ :: w, h => by
    simp only [evalWord, List.map_cons, List.prod_cons] at *
    rw [pm_evalLetter_plain G m m' (h ℓ List.mem_cons_self)]
    have := pm_evalWord_plain G m m' w fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [evalWord] at this
    rw [this]

private lemma pm_starWords_kind {N : ℕ} (e : Fin N ⊕ OffDiag N) (κ : LetterKind) :
    ∀ (n : ℕ) (i j : Fin N), ∀ c ∈ starWords e κ n i j, ∀ ℓ ∈ c, ℓ.kind = κ
  | 0, i, j => by
    intro c hc ℓ hℓ
    simp only [starWords, List.mem_singleton] at hc
    subst hc
    simp only [List.mem_singleton] at hℓ
    subst hℓ
    rfl
  | n + 1, i, j => by
    intro c hc ℓ hℓ
    simp only [starWords, List.mem_flatMap, List.mem_map] at hc
    obtain ⟨xy, -, c', hc', rfl⟩ := hc
    rcases List.mem_cons.1 hℓ with rfl | hℓ
    · rfl
    · exact pm_starWords_kind e κ n xy.2 j c' hc' ℓ hℓ

private lemma pm_wordP_plain {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    ∀ (k : List ℕ) (w : Word N), (∀ ℓ ∈ w, pm_plainL ℓ) → ∀ u ∈ wordP e k w, ∀ ℓ ∈ u, pm_plainL ℓ
  | _, [], _ => by
    intro u hu ℓ hℓ
    simp only [wordP, List.mem_singleton] at hu
    subst hu
    simp at hℓ
  | [], x :: w, h => by
    intro u hu ℓ hℓ
    simp only [wordP, List.mem_map] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    rcases List.mem_cons.1 hℓ with rfl | hℓ
    · exact h _ List.mem_cons_self
    · exact pm_wordP_plain e [] w (fun y hy => h y (List.mem_cons_of_mem _ hy)) u' hu' ℓ hℓ
  | k :: ks, x :: w, h => by
    intro u hu ℓ hℓ
    simp only [wordP, List.mem_flatMap, List.mem_map] at hu
    obtain ⟨c, hc, u', hu', rfl⟩ := hu
    rcases List.mem_append.1 hℓ with hℓ | hℓ
    · unfold letterP at hc
      split_ifs at hc
      · simp only [List.mem_singleton] at hc
        subst hc
        simp only [List.mem_singleton] at hℓ
        subst hℓ
        exact h _ List.mem_cons_self
      · have hk := pm_starWords_kind e _ k x.i x.j c hc ℓ hℓ
        rcases h x List.mem_cons_self with hx | hx
        · left; rw [hk, hx]; rfl
        · right; rw [hk, hx]; rfl
    · exact pm_wordP_plain e ks w (fun y hy => h y (List.mem_cons_of_mem _ hy)) u' hu' ℓ hℓ

/-! ### Formal sums under the operators `P_{γ,k}` -/

/-- Data whose multi-indices have the lengths `s, s + |k_1|, …` of the successive words. -/
private def pm_LenAdm {N : ℕ} : ℕ → List ((Fin N ⊕ OffDiag N) × List ℕ) → Prop
  | _, [] => True
  | s, x :: d => x.2.length = s ∧ pm_LenAdm (s + x.2.sum) d

private lemma pm_lenAdm_of_iterAdm {N : ℕ} {ξ : ℕ} :
    ∀ (s : ℕ) (d : List ((Fin N ⊕ OffDiag N) × List ℕ)), IterAdm ξ s d → pm_LenAdm s d
  | _, [], _ => trivial
  | s, x :: d, h => ⟨h.1, pm_lenAdm_of_iterAdm (s + x.2.sum) d h.2.2.2⟩

private lemma pm_iterP_append {N : ℕ} :
    ∀ (d₁ d₂ : List ((Fin N ⊕ OffDiag N) × List ℕ)) (G : FSum N),
      iterP (d₁ ++ d₂) G = iterP d₂ (iterP d₁ G)
  | [], _, _ => rfl
  | x :: d₁, d₂, G => pm_iterP_append d₁ d₂ (opP x.1 x.2 G)

private lemma pm_ord_append {N : ℕ} (d₁ d₂ : List ((Fin N ⊕ OffDiag N) × List ℕ)) :
    iterate_ord (d₁ ++ d₂) = iterate_ord d₁ + iterate_ord d₂ := by
  simp [iterate_ord]

private lemma pm_lenAdm_append {N : ℕ} :
    ∀ (s : ℕ) (d₁ d₂ : List ((Fin N ⊕ OffDiag N) × List ℕ)), pm_LenAdm s d₁ →
      pm_LenAdm (s + iterate_ord d₁) d₂ → pm_LenAdm s (d₁ ++ d₂)
  | s, [], d₂, _, h => by simpa [iterate_ord] using h
  | s, x :: d₁, d₂, h₁, h₂ => by
    refine ⟨h₁.1, pm_lenAdm_append (s + x.2.sum) d₁ d₂ h₁.2 ?_⟩
    have e : s + iterate_ord (x :: d₁) = s + x.2.sum + iterate_ord d₁ := by
      simp only [iterate_ord, List.map_cons, List.sum_cons]; ring
    rwa [e] at h₂

/-- The data `d` act with nonnegative weights and words of length `s + |d|`, the total weight
grows by at most `2^{|d|}`. -/
private lemma pm_iterP_props {N : ℕ} :
    ∀ (d : List ((Fin N ⊕ OffDiag N) × List ℕ)) (s : ℕ) (G : FSum N), pm_LenAdm s d →
      (∀ cw ∈ G, 0 ≤ cw.1 ∧ cw.2.length = s) →
      (∀ cw ∈ iterP d G, 0 ≤ cw.1 ∧ cw.2.length = s + iterate_ord d) ∧
        ((iterP d G).map Prod.fst).sum ≤ 2 ^ iterate_ord d * (G.map Prod.fst).sum
  | [], s, G, _, hG => by simpa [iterP, iterate_ord] using hG
  | x :: d, s, G, hd, hG => by
    have h1 := iterate_opP_props x.1 x.2 hd.1 G hG
    have h2 := pm_iterP_props d (s + x.2.sum) (opP x.1 x.2 G) hd.2 h1.1
    simp only [iterP, iterate_ord, List.map_cons, List.sum_cons] at h2 ⊢
    refine ⟨fun cw hcw => ⟨(h2.1 cw hcw).1, by rw [(h2.1 cw hcw).2]; ring⟩, ?_⟩
    calc _ ≤ _ := h2.2
      _ ≤ 2 ^ (d.map fun x => x.2.sum).sum * (2 ^ x.2.sum * (G.map Prod.fst).sum) :=
          mul_le_mul_of_nonneg_left h1.2 (by positivity)
      _ = _ := by rw [pow_add]; ring

/-- A weight `f` on words that does not increase under `P_{γ,k}` grows by at most `2^{|k|}` in
total under `P_{γ,k}`. -/
private lemma pm_opP_sum_le {N : ℕ} (e : Fin N ⊕ OffDiag N) (k : List ℕ) (f : Word N → ℝ)
    (hf0 : ∀ w, 0 ≤ f w) (hf : ∀ w, ∀ u ∈ wordP e k w, f u ≤ f w) :
    ∀ G : FSum N, (∀ cw ∈ G, 0 ≤ cw.1) →
      ((opP e k G).map fun cw => cw.1 * f cw.2).sum ≤
        2 ^ k.sum * (G.map fun cw => cw.1 * f cw.2).sum
  | [], _ => by simp [opP]
  | cw :: G, hG => by
    have ih := pm_opP_sum_le e k f hf0 hf G fun x hx => hG x (List.mem_cons_of_mem _ hx)
    have hcw := hG cw List.mem_cons_self
    have hsplit : opP e k (cw :: G) = (wordP e k cw.2).map (fun w => (cw.1, w)) ++ opP e k G := by
      simp [opP]
    rw [hsplit, List.map_append, List.sum_append, List.map_cons, List.sum_cons, mul_add]
    have h1 : (((wordP e k cw.2).map (fun w => (cw.1, w))).map fun cw' => cw'.1 * f cw'.2).sum ≤
        2 ^ k.sum * (cw.1 * f cw.2) := by
      rw [List.map_map]
      have h2 := List.sum_le_length_nsmul
        ((wordP e k cw.2).map ((fun cw' : ℝ × Word N => cw'.1 * f cw'.2) ∘ fun w => (cw.1, w)))
        (cw.1 * f cw.2) (by
          intro x hx
          obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
          exact mul_le_mul_of_nonneg_left (hf cw.2 u hu) hcw)
      rw [List.length_map, nsmul_eq_mul] at h2
      have hlen : ((wordP e k cw.2).length : ℝ) ≤ 2 ^ k.sum := by
        exact_mod_cast iterate_wordP_length_le e k cw.2
      refine h2.trans (mul_le_mul_of_nonneg_right hlen (mul_nonneg hcw (hf0 _)))
    linarith

private lemma pm_opP_nonneg {N : ℕ} (e : Fin N ⊕ OffDiag N) (k : List ℕ) (G : FSum N)
    (hG : ∀ cw ∈ G, 0 ≤ cw.1) : ∀ cw ∈ opP e k G, 0 ≤ cw.1 := by
  intro cw hcw
  simp only [opP, List.mem_flatMap, List.mem_map] at hcw
  obtain ⟨cw', hcw', u, -, rfl⟩ := hcw
  exact hG cw' hcw'

private lemma pm_iterP_sum_le {N : ℕ} (f : Word N → ℝ) (hf0 : ∀ w, 0 ≤ f w) :
    ∀ (d : List ((Fin N ⊕ OffDiag N) × List ℕ)) (G : FSum N),
      (∀ x ∈ d, ∀ w, ∀ u ∈ wordP x.1 x.2 w, f u ≤ f w) → (∀ cw ∈ G, 0 ≤ cw.1) →
      ((iterP d G).map fun cw => cw.1 * f cw.2).sum ≤
        2 ^ iterate_ord d * (G.map fun cw => cw.1 * f cw.2).sum
  | [], G, _, _ => by simp [iterP, iterate_ord]
  | x :: d, G, hd, hG => by
    have h1 := pm_opP_sum_le x.1 x.2 f hf0 (hd x List.mem_cons_self) G hG
    have h2 := pm_iterP_sum_le f hf0 d (opP x.1 x.2 G)
      (fun y hy => hd y (List.mem_cons_of_mem _ hy)) (pm_opP_nonneg x.1 x.2 G hG)
    simp only [iterP, iterate_ord, List.map_cons, List.sum_cons] at h2 ⊢
    calc _ ≤ _ := h2
      _ ≤ 2 ^ (d.map fun x => x.2.sum).sum * (2 ^ x.2.sum * (G.map fun cw => cw.1 * f cw.2).sum) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by rw [pow_add]; ring

/-! ### Bounds on the words on the event of the entrywise local law -/

/-- The event of (3.3) at one point `z` with the bound `ψ`: `|G_ij - δ_ij m_sc| ≤ ψ`. -/
private def pm_good {N : ℕ} (z : ℂ) (ψ : ℝ) : Set (Entries N) :=
  {ω | ∀ i j, ‖resS z ω i j - (if i = j then msc z else 0)‖ ≤ ψ}

private lemma pm_norm_evalLetter_le {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ)
    (ℓ : Letter N) :
    ‖evalLetter G m ℓ‖ ≤
      ‖G ℓ.i ℓ.j - (if ℓ.i = ℓ.j then m else 0)‖ + (if ℓ.i = ℓ.j then ‖m‖ else 0) := by
  rcases ℓ with ⟨κ, i, j⟩
  simp only
  by_cases h : i = j
  · subst h
    simp only [↓reduceIte]
    have hg : ‖G i i‖ ≤ ‖G i i - m‖ + ‖m‖ := by
      calc ‖G i i‖ = ‖(G i i - m) + m‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    cases κ <;> simp only [evalLetter, ↓reduceIte, norm_star]
    · exact hg
    · exact hg
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_right (norm_nonneg _)
  · simp only [h, ↓reduceIte, sub_zero, add_zero]
    cases κ <;> simp [evalLetter, h]

private lemma pm_norm_evalLetter_le' {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ)
    (ℓ : Letter N) : ‖evalLetter G m ℓ‖ ≤ ‖G ℓ.i ℓ.j‖ + ‖m‖ := by
  rcases ℓ with ⟨κ, i, j⟩
  have hc : ‖G i j - (if i = j then m else 0)‖ ≤ ‖G i j‖ + ‖m‖ := by
    refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
    split_ifs <;> simp
  cases κ <;> simp only [evalLetter, norm_star]
  · exact le_add_of_nonneg_right (norm_nonneg _)
  · exact le_add_of_nonneg_right (norm_nonneg _)
  · exact hc
  · exact hc

/-- On the event `|G_ij - δ_ij m_sc| ≤ ψ ≤ 1`, a word is at most `3^{length} ψ^{n_D}`: every
counted letter is off-diagonal. -/
private lemma pm_norm_evalWord_good {N : ℕ} {z : ℂ} {ψ : ℝ} (hψ0 : 0 ≤ ψ) (hψ1 : ψ ≤ 1)
    (hm : ‖msc z‖ ≤ 1) {ω : Entries N} (hω : ω ∈ pm_good z ψ) (D : Finset (Fin N)) :
    ∀ w : Word N, ‖evalWord (resS z ω) (msc z) w‖ ≤ 3 ^ w.length * ψ ^ pm_nD D w
  | [] => by simp [evalWord, pm_nD_nil]
  | ℓ :: w => by
    have ih := pm_norm_evalWord_good hψ0 hψ1 hm hω D w
    have hl := pm_norm_evalLetter_le (resS z ω) (msc z) ℓ
    have h1 := hω ℓ.i ℓ.j
    have e1 : evalWord (resS z ω) (msc z) (ℓ :: w) =
        evalLetter (resS z ω) (msc z) ℓ * evalWord (resS z ω) (msc z) w := by
      simp [evalWord]
    have hA : 0 ≤ 3 ^ w.length * ψ ^ pm_nD D w := by positivity
    rw [e1, norm_mul, pm_nD_cons, List.length_cons, pow_succ, pow_add]
    split_ifs with hc
    · have hle : ‖evalLetter (resS z ω) (msc z) ℓ‖ ≤ ψ := by
        simp only [hc.1, ↓reduceIte, add_zero, sub_zero] at hl h1
        linarith
      calc _ ≤ ψ * (3 ^ w.length * ψ ^ pm_nD D w) := mul_le_mul hle ih (norm_nonneg _) hψ0
        _ ≤ 3 ^ w.length * 3 * (ψ ^ pm_nD D w * ψ ^ 1) := by
            rw [pow_one]; nlinarith [hA]
    · have hle : ‖evalLetter (resS z ω) (msc z) ℓ‖ ≤ 3 := by
        refine hl.trans ?_
        split_ifs at h1 ⊢ <;> linarith [norm_nonneg (msc z)]
      calc _ ≤ 3 * (3 ^ w.length * ψ ^ pm_nD D w) := mul_le_mul hle ih (norm_nonneg _)
            (by norm_num)
        _ = 3 ^ w.length * 3 * (ψ ^ pm_nD D w * ψ ^ 0) := by ring

private lemma pm_norm_evalWord_le {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ) {B : ℝ}
    (hB : ∀ ℓ : Letter N, ‖evalLetter G m ℓ‖ ≤ B) : ∀ w : Word N, ‖evalWord G m w‖ ≤ B ^ w.length
  | [] => by simp [evalWord]
  | ℓ :: w => by
    have ih := pm_norm_evalWord_le G m hB w
    have e1 : evalWord G m (ℓ :: w) = evalLetter G m ℓ * evalWord G m w := by simp [evalWord]
    rw [e1, norm_mul, List.length_cons, pow_succ']
    exact mul_le_mul (hB ℓ) ih (norm_nonneg _) ((norm_nonneg _).trans (hB ℓ))

private lemma pm_norm_evalF_le {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ) :
    ∀ F : FSum N, (∀ cw ∈ F, 0 ≤ cw.1) →
      ‖evalF G m F‖ ≤ (F.map fun cw => cw.1 * ‖evalWord G m cw.2‖).sum
  | [], _ => by simp [evalF]
  | cw :: F, hF => by
    have ih := pm_norm_evalF_le G m F fun x hx => hF x (List.mem_cons_of_mem _ hx)
    have hcw := hF cw List.mem_cons_self
    simp only [evalF, List.map_cons, List.sum_cons] at ih ⊢
    refine (norm_add_le _ _).trans (add_le_add ?_ ih)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcw]

/-- The expectation of a formal sum of words of length `s` in `S`: at most `3^s Σ f ψ^{n_D}` on
the event `|G_ij - δ_ij m_sc| ≤ ψ`, and `(N + 1)^s Σ f` off it (since `1/η ≤ N`). -/
private lemma pm_norm_integral_evalF_le {N : ℕ} {μ : Measure (Entries N)}
    [IsProbabilityMeasure μ] {z : ℂ} (hz : 0 < z.im) (hB : 1 / z.im ≤ N) {ψ : ℝ} (hψ0 : 0 ≤ ψ)
    (hψ1 : ψ ≤ 1) (D : Finset (Fin N)) {s : ℕ} (F : FSum N)
    (hF : ∀ cw ∈ F, 0 ≤ cw.1 ∧ cw.2.length = s) :
    ‖∫ ω, evalF (resS z ω) (msc z) F ∂μ‖ ≤
      3 ^ s * (F.map fun cw => cw.1 * ψ ^ pm_nD D cw.2).sum +
        ((N : ℝ) + 1) ^ s * (F.map Prod.fst).sum * (μ (pm_good z ψ)ᶜ).toReal := by
  have hm : ‖msc z‖ ≤ 1 := (norm_msc_eq_inv_and_lt_one hz).2.le
  have hF0 : ∀ cw ∈ F, 0 ≤ cw.1 := fun cw h => (hF cw h).1
  have ha : 0 ≤ 3 ^ s * (F.map fun cw => cw.1 * ψ ^ pm_nD D cw.2).sum :=
    mul_nonneg (by positivity) (List.sum_nonneg fun x hx => by
      obtain ⟨cw, hcw, rfl⟩ := List.mem_map.1 hx
      exact mul_nonneg (hF0 cw hcw) (by positivity))
  refine (expansion_norm_integral_le (G := pm_good z ψ)
    (b := ((N : ℝ) + 1) ^ s * (F.map Prod.fst).sum) ha (Eventually.of_forall fun ω hω => ?_)
    (Eventually.of_forall fun ω => ?_)).trans_eq (by ring)
  · refine (pm_norm_evalF_le _ _ F hF0).trans ?_
    rw [← List.sum_map_mul_left]
    refine List.sum_le_sum fun cw hcw => ?_
    have h := pm_norm_evalWord_good hψ0 hψ1 hm hω D cw.2
    rw [(hF cw hcw).2] at h
    calc cw.1 * ‖evalWord (resS z ω) (msc z) cw.2‖ ≤ cw.1 * (3 ^ s * ψ ^ pm_nD D cw.2) :=
          mul_le_mul_of_nonneg_left h (hF0 cw hcw)
      _ = 3 ^ s * (cw.1 * ψ ^ pm_nD D cw.2) := by ring
  · refine (pm_norm_evalF_le _ _ F hF0).trans ?_
    rw [← List.sum_map_mul_left]
    refine List.sum_le_sum fun cw hcw => ?_
    have hl : ∀ ℓ : Letter N, ‖evalLetter (resS z ω) (msc z) ℓ‖ ≤ (N : ℝ) + 1 := fun ℓ =>
      (pm_norm_evalLetter_le' _ _ ℓ).trans (add_le_add
        ((norm_resolventC_apply_le (symOfEntries_isHermitian ω) hz _ _).trans hB) hm)
    have h := pm_norm_evalWord_le _ _ hl cw.2
    rw [(hF cw hcw).2] at h
    calc cw.1 * ‖evalWord (resS z ω) (msc z) cw.2‖ ≤ cw.1 * ((N : ℝ) + 1) ^ s :=
          mul_le_mul_of_nonneg_left h (hF0 cw hcw)
      _ = ((N : ℝ) + 1) ^ s * cw.1 := by ring

/-! ### The formal sum of `|X|^p`, `X = Σ_ij P_{γ,k}(G_ij conj G_ij)` -/

/-- The words of `P_{γ,k}(G_ij conj G_ij)`. -/
private def pm_L {N : ℕ} (e : Fin N ⊕ OffDiag N) (k : List ℕ) (i j : Fin N) : List (Word N) :=
  wordP e k [⟨.g, i, j⟩, ⟨.gbar, i, j⟩]

/-- The index set of the words of `Σ_ij P_{γ,k}(G_ij conj G_ij)`. -/
private abbrev pm_ι {N : ℕ} (e : Fin N ⊕ OffDiag N) (k : List ℕ) : Type :=
  Σ ij : Fin N × Fin N, Fin (pm_L e k ij.1 ij.2).length

private def pm_U {N : ℕ} {e : Fin N ⊕ OffDiag N} {k : List ℕ} (x : pm_ι e k) : Word N :=
  (pm_L e k x.1.1 x.1.2)[(x.2 : ℕ)]

/-- The words of `X^r conj X^r`, indexed by `τ : Fin r → ι × ι`. -/
private def pm_word {N : ℕ} {e : Fin N ⊕ OffDiag N} {k : List ℕ} {r : ℕ}
    (τ : Fin r → pm_ι e k × pm_ι e k) : Word N :=
  (List.ofFn fun t => pm_U (τ t).1 ++ (pm_U (τ t).2).map pm_conjL).flatten

/-- The normalised formal sum of `|X|^{2r}`: all words `pm_word τ` with the weight
`|ι|^{-2r}`. -/
private def pm_F {N : ℕ} (e : Fin N ⊕ OffDiag N) (k : List ℕ) (r : ℕ) : FSum N :=
  (Finset.univ : Finset (Fin r → pm_ι e k × pm_ι e k)).toList.map fun τ =>
    (((Fintype.card (pm_ι e k) : ℝ) ^ (2 * r))⁻¹, pm_word τ)

private lemma pm_U_mem {N : ℕ} {e : Fin N ⊕ OffDiag N} {k : List ℕ} (x : pm_ι e k) :
    pm_U x ∈ pm_L e k x.1.1 x.1.2 :=
  List.getElem_mem _

private lemma pm_U_length {N : ℕ} {e : Fin N ⊕ OffDiag N} {k : List ℕ} (hk2 : k.length = 2)
    (x : pm_ι e k) : (pm_U x).length = 2 + k.sum :=
  iterate_mem_wordP_length e k _ (by simp [hk2]) _ (pm_U_mem x)

private lemma pm_U_plain {N : ℕ} {e : Fin N ⊕ OffDiag N} {k : List ℕ} (x : pm_ι e k) :
    ∀ ℓ ∈ pm_U x, pm_plainL ℓ :=
  pm_wordP_plain e k _ (by
    intro ℓ hℓ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
    rcases hℓ with rfl | rfl
    · left; rfl
    · right; rfl) _ (pm_U_mem x)

private lemma pm_card_eq {N : ℕ} (e : Fin N ⊕ OffDiag N) (k : List ℕ) :
    (Fintype.card (pm_ι e k) : ℝ) = ∑ ij : Fin N × Fin N, ((pm_L e k ij.1 ij.2).length : ℝ) := by
  rw [Fintype.card_sigma]
  push_cast
  simp

private lemma pm_card_le {N : ℕ} (e : Fin N ⊕ OffDiag N) (k : List ℕ) :
    (Fintype.card (pm_ι e k) : ℝ) ≤ 2 ^ k.sum * (N : ℝ) ^ 2 := by
  rw [pm_card_eq]
  calc ∑ ij : Fin N × Fin N, ((pm_L e k ij.1 ij.2).length : ℝ) ≤
        ∑ _ij : Fin N × Fin N, (2 : ℝ) ^ k.sum :=
        Finset.sum_le_sum fun ij _ => by exact_mod_cast iterate_wordP_length_le e k _
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

private lemma pm_F_props {N : ℕ} (e : Fin N ⊕ OffDiag N) {k : List ℕ} (hk2 : k.length = 2)
    (r : ℕ) : ∀ cw ∈ pm_F e k r, 0 ≤ cw.1 ∧ cw.2.length = 2 * r * (2 + k.sum) := by
  intro cw hcw
  simp only [pm_F, List.mem_map] at hcw
  obtain ⟨τ, -, rfl⟩ := hcw
  refine ⟨by positivity, ?_⟩
  simp only [pm_word, List.length_flatten, List.map_ofFn, Function.comp_def, List.length_append,
    List.length_map, pm_U_length hk2, List.sum_ofFn, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  ring

private lemma pm_F_sum {N : ℕ} (e : Fin N ⊕ OffDiag N) (k : List ℕ) (r : ℕ)
    (hcard : 0 < Fintype.card (pm_ι e k)) : ((pm_F e k r).map Prod.fst).sum = 1 := by
  simp only [pm_F, List.map_map, Function.comp_def, Finset.sum_map_toList, Finset.sum_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  have h0 : (Fintype.card (pm_ι e k) : ℝ) ≠ 0 := by exact_mod_cast hcard.ne'
  push_cast
  rw [← pow_two, ← pow_mul, mul_inv_cancel₀ (pow_ne_zero _ h0)]

private lemma pm_evalF_F {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ)
    (e : Fin N ⊕ OffDiag N) (k : List ℕ) (r : ℕ) :
    evalF G m (pm_F e k r) = (((Fintype.card (pm_ι e k) : ℝ) ^ (2 * r))⁻¹ : ℝ) *
      ∑ τ : Fin r → pm_ι e k × pm_ι e k,
        ∏ t, (evalWord G m (pm_U (τ t).1) * star (evalWord G m (pm_U (τ t).2))) := by
  simp only [evalF, pm_F, List.map_map, Function.comp_def, Finset.sum_map_toList, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  rw [pm_word, pm_evalWord_flatten, List.map_ofFn, List.prod_ofFn]
  refine Finset.prod_congr rfl fun t _ => ?_
  simp only [Function.comp_apply, evalWord_append, pm_evalWord_conj]

/-- `X = Σ_ij P_{γ,k}(G_ij conj G_ij)` as the sum over `ι` of its words, for every value of `m`
(the words have no centred letters). -/
private lemma pm_X_eq {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ) {e : Fin N ⊕ OffDiag N}
    {k : List ℕ} :
    ∑ i, ∑ j, evalW G 0 (pm_L e k i j) = ∑ x : pm_ι e k, evalWord G m (pm_U x) := by
  rw [Fintype.sum_sigma, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [evalW, ← Fin.sum_univ_fun_getElem]
  refine Finset.sum_congr rfl fun t _ => ?_
  exact pm_evalWord_plain G 0 m _ (pm_U_plain ⟨(i, j), t⟩)

/-- `|X|^{2r} = |ι|^{2r} Σ f(w) w`: the formal sum `pm_F` evaluates `|X|^{2r}` up to the factor
`|ι|^{2r}`, for every value of `m` (the words have no centred letters). -/
private lemma pm_norm_pow_eq {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ)
    (e : Fin N ⊕ OffDiag N) (k : List ℕ) (r : ℕ) (hcard : 0 < Fintype.card (pm_ι e k)) :
    ((‖∑ i, ∑ j, evalW G 0 (pm_L e k i j)‖ ^ (2 * r) : ℝ) : ℂ) =
      ((Fintype.card (pm_ι e k) : ℝ) ^ (2 * r) : ℝ) * evalF G m (pm_F e k r) := by
  rw [pm_X_eq G m, pm_evalF_F, ← mul_assoc]
  have h0 : (Fintype.card (pm_ι e k) : ℝ) ≠ 0 := by exact_mod_cast hcard.ne'
  rw [← Complex.ofReal_mul, mul_inv_cancel₀ (pow_ne_zero _ h0), Complex.ofReal_one, one_mul]
  set Y := ∑ x : pm_ι e k, evalWord G m (pm_U x)
  have hY : ((‖Y‖ ^ 2 : ℝ) : ℂ) = Y * star Y := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    rfl
  rw [pow_mul, Complex.ofReal_pow, hY, star_sum, Fintype.sum_mul_sum, ← Fintype.sum_prod_type',
    Fintype.sum_pow]

/-- The fixed indices `D` for the data `d`: the indices of `e` and of every entry of `d`. -/
private def pm_Dset {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    List ((Fin N ⊕ OffDiag N) × List ℕ) → Finset (Fin N)
  | [] => pm_idx e
  | x :: d => pm_idx x.1 ∪ pm_Dset e d

private lemma pm_Dset_props {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    ∀ d : List ((Fin N ⊕ OffDiag N) × List ℕ), pm_idx e ⊆ pm_Dset e d ∧
      (∀ x ∈ d, pm_idx x.1 ⊆ pm_Dset e d) ∧ (pm_Dset e d).card ≤ 2 * (d.length + 1)
  | [] => ⟨subset_rfl, by simp, by simpa [pm_Dset] using pm_idx_card_le e⟩
  | x :: d => by
    obtain ⟨h1, h2, h3⟩ := pm_Dset_props e d
    refine ⟨h1.trans Finset.subset_union_right, fun y hy => ?_, ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact Finset.subset_union_left
      · exact (h2 y hy).trans Finset.subset_union_right
    · simp only [pm_Dset, List.length_cons]
      have := Finset.card_union_le (pm_idx x.1) (pm_Dset e d)
      have := pm_idx_card_le x.1
      omega

/-- The weight of an index pair `(i, j)`: `ψ³` when `i ≠ j` and `i, j ∉ D`, `1` otherwise. -/
private def pm_h {N : ℕ} {e : Fin N ⊕ OffDiag N} {k : List ℕ} (D : Finset (Fin N)) (ψ : ℝ)
    (x : pm_ι e k) : ℝ :=
  if x.1.1 ≠ x.1.2 ∧ x.1.1 ∉ D ∧ x.1.2 ∉ D then ψ ^ 3 else 1

private lemma pm_nD_word {N : ℕ} {e : Fin N ⊕ OffDiag N} {k : List ℕ} {r : ℕ}
    (D : Finset (Fin N)) (τ : Fin r → pm_ι e k × pm_ι e k) :
    pm_nD D (pm_word τ) = ∑ t, (pm_nD D (pm_U (τ t).1) + pm_nD D (pm_U (τ t).2)) := by
  have h : ∀ L : List (Word N), pm_nD D L.flatten = (L.map (pm_nD D)).sum := by
    intro L
    simp only [pm_nD, List.countP_flatten]
    rfl
  rw [pm_word, h, List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Function.comp_apply, pm_nD_append, pm_nD_conj]

private lemma pm_pow_nD_le {N : ℕ} {e : Fin N ⊕ OffDiag N} {k : List ℕ} (hk2 : k.length = 2)
    (hk1 : 1 ≤ k.sum) {D : Finset (Fin N)} (hD : pm_idx e ⊆ D) {ψ : ℝ} (hψ0 : 0 ≤ ψ)
    (hψ1 : ψ ≤ 1) (x : pm_ι e k) : ψ ^ pm_nD D (pm_U x) ≤ pm_h D ψ x := by
  unfold pm_h
  split_ifs with hx
  · exact pow_le_pow_of_le_one hψ0 hψ1
      (pm_pair_gen hD hk2 hk1 hx.1 hx.2.1 hx.2.2 _ _ _ (pm_U_mem x))
  · exact pow_le_one₀ hψ0 hψ1

/-- (6.99)–(6.100) for the initial sum: `Σ_w f(w) ψ^{n_D(w)} ≤ |ι|^{-2r} (Σ_x h(x))^{2r}`. -/
private lemma pm_F_nD_le {N : ℕ} (e : Fin N ⊕ OffDiag N) {k : List ℕ} (hk2 : k.length = 2)
    (hk1 : 1 ≤ k.sum) (r : ℕ) {D : Finset (Fin N)} (hD : pm_idx e ⊆ D) {ψ : ℝ} (hψ0 : 0 ≤ ψ)
    (hψ1 : ψ ≤ 1) :
    ((pm_F e k r).map fun cw => cw.1 * ψ ^ pm_nD D cw.2).sum ≤
      ((Fintype.card (pm_ι e k) : ℝ) ^ (2 * r))⁻¹ * (∑ x : pm_ι e k, pm_h D ψ x) ^ (2 * r) := by
  simp only [pm_F, List.map_map, Function.comp_def, Finset.sum_map_toList]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hh0 : ∀ x : pm_ι e k, 0 ≤ pm_h D ψ x := fun x => by unfold pm_h; split_ifs <;> positivity
  calc ∑ τ : Fin r → pm_ι e k × pm_ι e k, ψ ^ pm_nD D (pm_word τ) ≤
        ∑ τ : Fin r → pm_ι e k × pm_ι e k, ∏ t, (pm_h D ψ (τ t).1 * pm_h D ψ (τ t).2) := by
        refine Finset.sum_le_sum fun τ _ => ?_
        rw [pm_nD_word, ← Finset.prod_pow_eq_pow_sum]
        refine Finset.prod_le_prod₀ (fun t _ => by positivity) (fun t _ => ?_)
        rw [pow_add]
        exact mul_le_mul (pm_pow_nD_le hk2 hk1 hD hψ0 hψ1 _) (pm_pow_nD_le hk2 hk1 hD hψ0 hψ1 _)
          (by positivity) (hh0 _)
    _ = (∑ x : pm_ι e k, pm_h D ψ x) ^ (2 * r) := by
        symm
        calc (∑ x : pm_ι e k, pm_h D ψ x) ^ (2 * r) =
              ((∑ x : pm_ι e k, pm_h D ψ x) * ∑ x : pm_ι e k, pm_h D ψ x) ^ r := by
              rw [pow_mul, sq]
          _ = (∑ xy : pm_ι e k × pm_ι e k, pm_h D ψ xy.1 * pm_h D ψ xy.2) ^ r := by
              rw [Fintype.sum_mul_sum, Fintype.sum_prod_type]
          _ = _ := Fintype.sum_pow _ _

/-- The pairs `(i, j)` with `i = j`, `i ∈ D` or `j ∈ D` are at most `N + 2|D|N`; each carries at
most `2^{|k|}` words. -/
private lemma pm_sum_h_le {N : ℕ} (e : Fin N ⊕ OffDiag N) (k : List ℕ) (D : Finset (Fin N))
    {ψ : ℝ} (hψ0 : 0 ≤ ψ) :
    ∑ x : pm_ι e k, pm_h D ψ x ≤ (Fintype.card (pm_ι e k) : ℝ) * ψ ^ 3 +
      2 ^ k.sum * ((N : ℝ) + 2 * D.card * N) := by
  have hL : ∀ ij : Fin N × Fin N, ((pm_L e k ij.1 ij.2).length : ℝ) ≤ 2 ^ k.sum := fun ij => by
    exact_mod_cast iterate_wordP_length_le e k _
  have hterm : ∀ ij : Fin N × Fin N, ∑ t : Fin (pm_L e k ij.1 ij.2).length,
      pm_h D ψ (⟨ij, t⟩ : pm_ι e k) ≤ ((pm_L e k ij.1 ij.2).length : ℝ) * ψ ^ 3 +
        2 ^ k.sum * ((if ij.1 = ij.2 then 1 else 0) + (if ij.1 ∈ D then 1 else 0) +
          (if ij.2 ∈ D then 1 else 0)) := by
    intro ij
    have hc : ∀ t, pm_h D ψ (⟨ij, t⟩ : pm_ι e k) =
        (if ij.1 ≠ ij.2 ∧ ij.1 ∉ D ∧ ij.2 ∉ D then ψ ^ 3 else 1) := fun t => rfl
    rw [Finset.sum_congr rfl fun t _ => hc t, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have h0 : (0 : ℝ) ≤ ((pm_L e k ij.1 ij.2).length : ℝ) := Nat.cast_nonneg _
    have hp : (0 : ℝ) ≤ 2 ^ k.sum := by positivity
    have hI0 : (0 : ℝ) ≤ (if ij.1 = ij.2 then 1 else 0) + (if ij.1 ∈ D then 1 else 0) +
        (if ij.2 ∈ D then 1 else 0) := by positivity
    by_cases hg : ij.1 ≠ ij.2 ∧ ij.1 ∉ D ∧ ij.2 ∉ D
    · rw [ite_eq_left hg]
      exact le_add_of_nonneg_right (mul_nonneg hp hI0)
    · rw [ite_eq_right hg, mul_one]
      have hI : (1 : ℝ) ≤ (if ij.1 = ij.2 then 1 else 0) + (if ij.1 ∈ D then 1 else 0) +
          (if ij.2 ∈ D then 1 else 0) := by
        by_cases h1 : ij.1 = ij.2
        · rw [ite_eq_left h1]; split_ifs <;> norm_num
        · by_cases h2 : ij.1 ∈ D
          · rw [ite_eq_left h2]; split_ifs <;> norm_num
          · have h3 : ij.2 ∈ D := by tauto
            rw [ite_eq_left h3]; split_ifs; norm_num
      have h3 : 0 ≤ ψ ^ 3 := by positivity
      nlinarith [hL ij]
  rw [Fintype.sum_sigma]
  refine (Finset.sum_le_sum fun ij _ => hterm ij).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← pm_card_eq, ← Finset.mul_sum]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_of_eq ?_) (by positivity))
  have hb : ∑ x : Fin N, (if x ∈ D then (1 : ℝ) else 0) = D.card := by
    rw [Finset.sum_boole]
    simp
  have hA : ∑ x : Fin N, ∑ y : Fin N, (if x = y then (1 : ℝ) else 0) = N := by
    simp
  have hB : ∑ x : Fin N, ∑ _y : Fin N, (if x ∈ D then (1 : ℝ) else 0) = D.card * N := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, hb, mul_comm]
  have hC : ∑ _x : Fin N, ∑ y : Fin N, (if y ∈ D then (1 : ℝ) else 0) = D.card * N := by
    simp only [hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_add_distrib]
  rw [hA, hB, hC]
  ring

/-- (6.97)–(6.100) for every iterate: the expectation in `S` of `P_d` applied to the formal sum of
`|X|^{2r}`, on the event `|G_ij - δ_ij m_sc| ≤ ψ` and off it, with `D` the indices of `e` and of
the entries of `d`. -/
private lemma pm_iterate_le {N : ℕ} {μ : Measure (Entries N)} [IsProbabilityMeasure μ] {z : ℂ}
    (hz : 0 < z.im) (hB : 1 / z.im ≤ N) {ψ : ℝ} (hψ0 : 0 ≤ ψ) (hψ1 : ψ ≤ 1)
    (e : Fin N ⊕ OffDiag N) {k : List ℕ} (hk2 : k.length = 2) (hk1 : 1 ≤ k.sum) (r : ℕ)
    (hcard : 0 < Fintype.card (pm_ι e k)) (d : List ((Fin N ⊕ OffDiag N) × List ℕ))
    (hd : pm_LenAdm (2 * r * (2 + k.sum)) d) :
    ‖∫ ω, evalF (resS z ω) (msc z) (iterP d (pm_F e k r)) ∂μ‖ ≤
      3 ^ (2 * r * (2 + k.sum) + iterate_ord d) * 2 ^ iterate_ord d *
          (((Fintype.card (pm_ι e k) : ℝ) ^ (2 * r))⁻¹ *
            ((Fintype.card (pm_ι e k) : ℝ) * ψ ^ 3 +
              2 ^ k.sum * ((N : ℝ) + 2 * (2 * ((d.length : ℝ) + 1)) * N)) ^ (2 * r)) +
        ((N : ℝ) + 1) ^ (2 * r * (2 + k.sum) + iterate_ord d) * 2 ^ iterate_ord d *
          (μ (pm_good z ψ)ᶜ).toReal := by
  set F := pm_F e k r
  set D := pm_Dset e d
  obtain ⟨hDe, hDd, hDc⟩ := pm_Dset_props e d
  have hF := pm_F_props e hk2 r
  obtain ⟨hP, hW⟩ := pm_iterP_props d _ F hd hF
  rw [pm_F_sum e k r hcard, mul_one] at hW
  have h1 := pm_norm_integral_evalF_le (μ := μ) hz hB hψ0 hψ1 D (iterP d F) hP
  have h2 := pm_iterP_sum_le (fun w => ψ ^ pm_nD D w) (fun w => by positivity) d F
    (fun x hx w u hu => pow_le_pow_of_le_one hψ0 hψ1 (pm_wordP_mono (hDd x hx) x.2 w u hu))
    (fun cw h => (hF cw h).1)
  have h3 := pm_F_nD_le e hk2 hk1 r hDe hψ0 hψ1
  have h4 := pm_sum_h_le e k D hψ0
  have hDc' : (D.card : ℝ) ≤ 2 * ((d.length : ℝ) + 1) := by exact_mod_cast hDc
  have hh0 : 0 ≤ ∑ x : pm_ι e k, pm_h D ψ x :=
    Finset.sum_nonneg fun x _ => by unfold pm_h; split_ifs <;> positivity
  have h5 : (∑ x : pm_ι e k, pm_h D ψ x) ^ (2 * r) ≤
      ((Fintype.card (pm_ι e k) : ℝ) * ψ ^ 3 +
        2 ^ k.sum * ((N : ℝ) + 2 * (2 * ((d.length : ℝ) + 1)) * N)) ^ (2 * r) := by
    refine pow_le_pow_left₀ hh0 (h4.trans ?_) _
    gcongr
  have hP0 : 0 ≤ (μ (pm_good z ψ)ᶜ).toReal := ENNReal.toReal_nonneg
  have hc0 : 0 ≤ ((Fintype.card (pm_ι e k) : ℝ) ^ (2 * r))⁻¹ := by positivity
  calc _ ≤ _ := h1
    _ ≤ 3 ^ (2 * r * (2 + k.sum) + iterate_ord d) *
          (2 ^ iterate_ord d * (((Fintype.card (pm_ι e k) : ℝ) ^ (2 * r))⁻¹ *
            (∑ x : pm_ι e k, pm_h D ψ x) ^ (2 * r))) +
        ((N : ℝ) + 1) ^ (2 * r * (2 + k.sum) + iterate_ord d) * 2 ^ iterate_ord d *
          (μ (pm_good z ψ)ᶜ).toReal := by
        gcongr
        exact h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
    _ ≤ _ := by
        rw [← mul_assoc]
        gcongr

/-! ### Scaled formal sums and the expansion of `R` in `S` for formal sums -/

/-- The formal sum `c F`. -/
private def pm_smul {N : ℕ} (c : ℝ) (F : FSum N) : FSum N := F.map fun cw => (c * cw.1, cw.2)

private lemma pm_evalF_smul {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ) (c : ℝ) (F : FSum N) :
    evalF G m (pm_smul c F) = (c : ℂ) * evalF G m F := by
  simp only [evalF, pm_smul, List.map_map, Function.comp_def, Complex.ofReal_mul, mul_assoc,
    List.sum_map_mul_left]

private lemma pm_opP_smul {N : ℕ} (e : Fin N ⊕ OffDiag N) (k : List ℕ) (c : ℝ) (F : FSum N) :
    opP e k (pm_smul c F) = pm_smul c (opP e k F) := by
  simp [opP, pm_smul, List.flatMap_map, List.map_flatMap, Function.comp_def]

private lemma pm_iterP_smul {N : ℕ} (c : ℝ) :
    ∀ (d : List ((Fin N ⊕ OffDiag N) × List ℕ)) (F : FSum N),
      iterP d (pm_smul c F) = pm_smul c (iterP d F)
  | [], _ => rfl
  | x :: d, F => by
    simp only [iterP]
    rw [pm_opP_smul, pm_iterP_smul c d]

private lemma pm_smul_props {N : ℕ} {c : ℝ} (hc : 0 ≤ c) {s : ℕ} (F : FSum N)
    (hF : ∀ cw ∈ F, 0 ≤ cw.1 ∧ cw.2.length = s) :
    (∀ cw ∈ pm_smul c F, 0 ≤ cw.1 ∧ cw.2.length = s) ∧
      ((pm_smul c F).map Prod.fst).sum = c * (F.map Prod.fst).sum := by
  refine ⟨fun cw hcw => ?_, ?_⟩
  · simp only [pm_smul, List.mem_map] at hcw
    obtain ⟨cw', h', rfl⟩ := hcw
    exact ⟨mul_nonneg hc (hF cw' h').1, (hF cw' h').2⟩
  · simp [pm_smul, List.map_map, Function.comp_def, List.sum_map_mul_left]

private lemma pm_integrable_evalWord_R {N : ℕ} {μ : Measure (Entries N)} [IsFiniteMeasure μ]
    {z : ℂ} (hz : 0 < z.im) (e : Fin N ⊕ OffDiag N) (w : Word N) :
    Integrable (fun ω => evalWord (resR e z ω) (msc z) w) μ := by
  have hc : Continuous fun ω : Entries N => evalWord (resR e z ω) (msc z) w := by
    have := expansion_continuous_resR (N := N) hz.ne' e (msc z) [w]
    simpa [evalW] using this
  refine Integrable.of_bound hc.aestronglyMeasurable ((1 / z.im + 1) ^ w.length)
    (Eventually.of_forall fun ω => ?_)
  exact pm_norm_evalWord_le _ _ (fun ℓ => (pm_norm_evalLetter_le' _ _ ℓ).trans
    (add_le_add (norm_resolventC_apply_le (symOfEntries_isHermitian (zeroEntry e ω)) hz _ _)
      (norm_msc_eq_inv_and_lt_one hz).2.le)) w

private lemma pm_integrable_evalF_R {N : ℕ} {μ : Measure (Entries N)} [IsFiniteMeasure μ]
    {z : ℂ} (hz : 0 < z.im) (e : Fin N ⊕ OffDiag N) :
    ∀ G : FSum N, Integrable (fun ω => evalF (resR e z ω) (msc z) G) μ
  | [] => by simp [evalF]
  | cw :: G => by
    simpa [evalF, Pi.add_def] using
      ((pm_integrable_evalWord_R hz e cw.2).const_mul (cw.1 : ℂ)).add
        (pm_integrable_evalF_R hz e G)

private lemma pm_integral_evalF_R_cons {N : ℕ} {μ : Measure (Entries N)} [IsFiniteMeasure μ]
    {z : ℂ} (hz : 0 < z.im) (e : Fin N ⊕ OffDiag N) (cw : ℝ × Word N) (G : FSum N) :
    ∫ ω, evalF (resR e z ω) (msc z) (cw :: G) ∂μ =
      (cw.1 : ℂ) * (∫ ω, evalWord (resR e z ω) (msc z) cw.2 ∂μ) +
        ∫ ω, evalF (resR e z ω) (msc z) G ∂μ := by
  have h : ∀ ω, evalF (resR e z ω) (msc z) (cw :: G) =
      (cw.1 : ℂ) * evalWord (resR e z ω) (msc z) cw.2 + evalF (resR e z ω) (msc z) G := by
    intro ω; simp [evalF]
  simp_rw [h]
  rw [integral_add ((pm_integrable_evalWord_R hz e cw.2).const_mul _)
    (pm_integrable_evalF_R hz e G), integral_const_mul]

/-- (6.92) for formal sums: if every word of length `s` satisfies Lemma 6.5 up to `εw`, then a
formal sum with nonnegative weights of such words satisfies it up to `εw Σ f`. -/
private lemma pm_expansion_sum {N : ℕ} {μ : Measure (Entries N)} [IsFiniteMeasure μ] {z : ℂ}
    (hz : 0 < z.im) (e : Fin N ⊕ OffDiag N) {s : ℕ} (H : Finset (Fin s → ℕ))
    (A : (Fin s → ℕ) → ℝ) {εw : ℝ}
    (hw : ∀ w : Word N, w.length = s →
      ‖(∫ ω, evalWord (resS z ω) (msc z) w ∂μ) - (∫ ω, evalWord (resR e z ω) (msc z) w ∂μ)
        - ∑ α ∈ H, (A α : ℂ) * ∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) w) ∂μ‖ ≤ εw)
    (G : FSum N) (hG : ∀ cw ∈ G, 0 ≤ cw.1 ∧ cw.2.length = s) :
    ‖∫ ω, evalF (resR e z ω) (msc z) G ∂μ‖ ≤ ‖∫ ω, evalF (resS z ω) (msc z) G ∂μ‖ +
      ∑ α ∈ H, |A α| * ‖∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) G) ∂μ‖ +
      (G.map Prod.fst).sum * εw := by
  have hD : ∀ G : FSum N, (∀ cw ∈ G, 0 ≤ cw.1 ∧ cw.2.length = s) →
      ‖(∫ ω, evalF (resS z ω) (msc z) G ∂μ) - (∫ ω, evalF (resR e z ω) (msc z) G ∂μ)
        - ∑ α ∈ H, (A α : ℂ) * ∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) G) ∂μ‖ ≤
        (G.map Prod.fst).sum * εw := by
    intro G
    induction G with
    | nil => intro _; simp [evalF, opP]
    | cons cw G ih =>
      intro hG
      have hcw := hG cw List.mem_cons_self
      have ih' := ih fun x hx => hG x (List.mem_cons_of_mem _ hx)
      simp only [iterate_integral_evalF_cons hz e, iterate_integral_evalF_opP_cons hz e,
        pm_integral_evalF_R_cons hz e]
      set X₀ := ∫ ω, evalWord (resS z ω) (msc z) cw.2 ∂μ
      set X₁ := ∫ ω, evalWord (resR e z ω) (msc z) cw.2 ∂μ
      set Y₀ := ∫ ω, evalF (resS z ω) (msc z) G ∂μ
      set Y₁ := ∫ ω, evalF (resR e z ω) (msc z) G ∂μ
      set S₁ := ∑ α ∈ H, (A α : ℂ) *
        ∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) cw.2) ∂μ
      set S₂ := ∑ α ∈ H, (A α : ℂ) *
        ∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) G) ∂μ
      have hsum : ∑ α ∈ H, (A α : ℂ) * ((cw.1 : ℂ) *
            (∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) cw.2) ∂μ) +
            ∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) G) ∂μ) =
          (cw.1 : ℂ) * S₁ + S₂ := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun α _ => by ring
      rw [hsum]
      have hid : (cw.1 : ℂ) * X₀ + Y₀ - ((cw.1 : ℂ) * X₁ + Y₁) - ((cw.1 : ℂ) * S₁ + S₂) =
          (cw.1 : ℂ) * (X₀ - X₁ - S₁) + (Y₀ - Y₁ - S₂) := by ring
      rw [hid]
      have h1 : ‖(cw.1 : ℂ) * (X₀ - X₁ - S₁)‖ ≤ cw.1 * εw := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcw.1]
        exact mul_le_mul_of_nonneg_left (hw cw.2 hcw.2) hcw.1
      calc _ ≤ ‖(cw.1 : ℂ) * (X₀ - X₁ - S₁)‖ + ‖Y₀ - Y₁ - S₂‖ := norm_add_le _ _
        _ ≤ cw.1 * εw + (G.map Prod.fst).sum * εw := add_le_add h1 ih'
        _ = _ := by simp only [List.map_cons, List.sum_cons]; ring
  set S := ∑ α ∈ H, (A α : ℂ) * ∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) G) ∂μ
  have hS : ‖S‖ ≤ ∑ α ∈ H, |A α| *
      ‖∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) G) ∂μ‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, le_refl]
  have h := hD G hG
  set a := ∫ ω, evalF (resS z ω) (msc z) G ∂μ
  set b := ∫ ω, evalF (resR e z ω) (msc z) G ∂μ
  have e1 : b = a - S - (a - b - S) := by ring
  rw [e1]
  calc ‖a - S - (a - b - S)‖ ≤ ‖a - S‖ + ‖a - b - S‖ := norm_sub_le _ _
    _ ≤ ‖a‖ + ‖S‖ + ‖a - b - S‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ _ := by gcongr

/-! ### The spectral parameter `z = E + iN^{-2/3-ε}` of (5.13) and the local law at it -/

/-- `N^{1/3} ≤ √N / (K log N)` for all large `N`. -/
private lemma pm_tilde_ge (K : ℝ) :
    ∀ᶠ N : ℕ in atTop, 0 < K → (N : ℝ) ^ ((1 : ℝ) / 3) ≤ Real.sqrt N / (K * Real.log N) := by
  filter_upwards [eventually_ge_atTop 3, ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop (12 * K)] with N hN hK hK0
  simp only [Function.comp] at hK
  have hN0 : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  set a : ℝ := (N : ℝ) ^ ((1 : ℝ) / 12) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hN0 _
  have hpow : ∀ m : ℕ, (N : ℝ) ^ ((m : ℝ) / 12) = a ^ m := fun m => by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    ring
  have h3 : (N : ℝ) ^ ((1 : ℝ) / 3) = a ^ 4 := by
    rw [← hpow 4]; norm_num
  have h2 : Real.sqrt N = a ^ 6 := by
    rw [Real.sqrt_eq_rpow, ← hpow 6]; norm_num
  have hlog_le : Real.log N ≤ 12 * a := by
    have := Real.log_le_rpow_div hN0.le (show (0 : ℝ) < 1 / 12 by norm_num)
    calc Real.log N ≤ (N : ℝ) ^ ((1 : ℝ) / 12) / (1 / 12) := this
      _ = 12 * a := by rw [← ha]; ring
  rw [h3, h2, le_div_iff₀ (by positivity)]
  calc a ^ 4 * (K * Real.log N) ≤ a ^ 4 * (K * (12 * a)) := by gcongr
    _ = a ^ 5 * (12 * K) := by ring
    _ ≤ a ^ 5 * a := by gcongr
    _ = a ^ 6 := by ring

private lemma pm_rpow_le_one {N : ℕ} (hN : 1 ≤ (N : ℝ)) {x : ℝ} (hx : x ≤ 0) :
    (N : ℝ) ^ x ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hN hx

/-- `z = E + iN^{-2/3-ε}` with `|E - 2| ≤ N^{-2/3+ε}`, `0 < ε < 1/12`, lies in `S(C)` once
`φ^C ≤ N^{1/8}`. -/
private lemma pm_mem_specDomain {N : ℕ} (hN : 2 ≤ N) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 12)
    {E : ℝ} (hE : |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) {C : ℝ}
    (hC : phi N ^ C ≤ (N : ℝ) ^ ((1 : ℝ) / 8)) :
    (⟨E, etaEdge N ε⟩ : ℂ) ∈ specDomain N C := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have h1 := pm_rpow_le_one hN1 (by linarith : -(2 : ℝ) / 3 + ε ≤ 0)
    have h2 : |E| ≤ |E - 2| + 2 := by
      have := abs_sub_abs_le_abs_sub E 2
      rw [abs_two] at this
      linarith
    simp only
    linarith
  · simp only [etaEdge]
    have h1 : (N : ℝ) ^ ((1 : ℝ) / 8) < (N : ℝ) ^ ((1 : ℝ) / 3 - ε) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)
    have h2 : (N : ℝ) ^ ((1 : ℝ) / 3 - ε) / N = (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hN0]
      congr 1
      ring
    rw [← h2]
    exact div_lt_div_of_pos_right (hC.trans_lt h1) hN0
  · simp only [etaEdge]
    have := pm_rpow_le_one hN1 (by linarith : -(2 : ℝ) / 3 - ε ≤ 0)
    linarith

/-- `Im m_sc ≤ C √(κ + η)` on `S`, in both regimes of `msc_bounds`. -/
private lemma pm_im_msc_le {Cm : ℝ} (hCm : 1 ≤ Cm)
    (hb : ∀ z : ℂ, |z.re| ≤ 5 → 0 < z.im → z.im ≤ 10 →
      (Cm⁻¹ ≤ ‖msc z‖ ∧ ‖msc z‖ ≤ Cm) ∧
      (Cm⁻¹ * Real.sqrt (kappa z.re + z.im) ≤ ‖1 - msc z ^ 2‖ ∧
        ‖1 - msc z ^ 2‖ ≤ Cm * Real.sqrt (kappa z.re + z.im)) ∧
      (z.im ≤ kappa z.re → 2 ≤ |z.re| →
        Cm⁻¹ * (z.im / Real.sqrt (kappa z.re + z.im)) ≤ (msc z).im ∧
        (msc z).im ≤ Cm * (z.im / Real.sqrt (kappa z.re + z.im))) ∧
      (kappa z.re ≤ z.im ∨ |z.re| ≤ 2 →
        Cm⁻¹ * Real.sqrt (kappa z.re + z.im) ≤ (msc z).im ∧
        (msc z).im ≤ Cm * Real.sqrt (kappa z.re + z.im)))
    {z : ℂ} (h5 : |z.re| ≤ 5) (h0 : 0 < z.im) (h10 : z.im ≤ 10) :
    (msc z).im ≤ Cm * Real.sqrt (kappa z.re + z.im) := by
  obtain ⟨-, -, h3, h4⟩ := hb z h5 h0 h10
  by_cases hc : kappa z.re ≤ z.im ∨ |z.re| ≤ 2
  · exact (h4 hc).2
  · rw [not_or, not_le, not_le] at hc
    refine (h3 hc.1.le hc.2.le).2.trans ?_
    have hk0 : 0 ≤ kappa z.re := abs_nonneg _
    have hs : 0 < Real.sqrt (kappa z.re + z.im) := Real.sqrt_pos.2 (by linarith)
    have hsq := Real.sq_sqrt (by linarith : 0 ≤ kappa z.re + z.im)
    gcongr
    rw [div_le_iff₀ hs]
    nlinarith

/-- (6.97): at `z = E + iN^{-2/3-ε}`, `|E - 2| ≤ N^{-2/3+ε}`, the right side of (3.3) with
`q ≥ N^{1/3}` is at most `N^{-1/3+2ε}` once `4 C φ^{C'} ≤ N^ε`. -/
private lemma pm_entryErr_le {N : ℕ} (hN : 2 ≤ N) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 12)
    {E : ℝ} (hE : |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) {Cm C q : ℝ} (hCm : 1 ≤ Cm)
    (hb : ∀ z : ℂ, |z.re| ≤ 5 → 0 < z.im → z.im ≤ 10 →
      (Cm⁻¹ ≤ ‖msc z‖ ∧ ‖msc z‖ ≤ Cm) ∧
      (Cm⁻¹ * Real.sqrt (kappa z.re + z.im) ≤ ‖1 - msc z ^ 2‖ ∧
        ‖1 - msc z ^ 2‖ ≤ Cm * Real.sqrt (kappa z.re + z.im)) ∧
      (z.im ≤ kappa z.re → 2 ≤ |z.re| →
        Cm⁻¹ * (z.im / Real.sqrt (kappa z.re + z.im)) ≤ (msc z).im ∧
        (msc z).im ≤ Cm * (z.im / Real.sqrt (kappa z.re + z.im))) ∧
      (kappa z.re ≤ z.im ∨ |z.re| ≤ 2 →
        Cm⁻¹ * Real.sqrt (kappa z.re + z.im) ≤ (msc z).im ∧
        (msc z).im ≤ Cm * Real.sqrt (kappa z.re + z.im)))
    (hφ : 4 * Cm * phi N ^ C ≤ (N : ℝ) ^ ε) (hq : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ q) :
    entryErr N C q ⟨E, etaEdge N ε⟩ ≤ (N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  set u : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 3 + ε) with hu
  set v : ℝ := (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) with hv
  set η : ℝ := etaEdge N ε with hη
  have hu0 : 0 < u := Real.rpow_pos_of_pos hN0 _
  have hη0 : 0 < η := Real.rpow_pos_of_pos hN0 _
  have hηv : η ≤ v := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hNη : 1 / ((N : ℝ) * η) = u := by
    rw [hη, etaEdge, one_div, ← Real.rpow_one_add' hN0.le (by norm_num; linarith),
      ← Real.rpow_neg hN0.le]
    congr 1
    ring
  have hq0 : 0 < q := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hq
  have h1q : 1 / q ≤ u := by
    rw [one_div]
    calc q⁻¹ ≤ ((N : ℝ) ^ ((1 : ℝ) / 3))⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hN0 _) hq
      _ = (N : ℝ) ^ (-(1 : ℝ) / 3) := by rw [← Real.rpow_neg hN0.le]; ring_nf
      _ ≤ u := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  -- `Im m_sc ≤ 2 C u`
  have hz5 : |(⟨E, η⟩ : ℂ).re| ≤ 5 := by
    have h1 := pm_rpow_le_one hN1 (by linarith : -(2 : ℝ) / 3 + ε ≤ 0)
    have h2 : |E| ≤ |E - 2| + 2 := by
      have := abs_sub_abs_le_abs_sub E 2
      rw [abs_two] at this
      linarith
    simp only
    linarith
  have hz10 : (⟨E, η⟩ : ℂ).im ≤ 10 := by
    have := pm_rpow_le_one hN1 (by linarith : -(2 : ℝ) / 3 - ε ≤ 0)
    simp only [hη, etaEdge]
    linarith
  have him := pm_im_msc_le hCm hb hz5 hη0 hz10
  simp only at him
  have hκ : kappa E ≤ v := by
    have := abs_abs_sub_abs_le E 2
    rw [abs_two] at this
    exact this.trans hE
  have hsv : Real.sqrt v ≤ u := by
    rw [Real.sqrt_eq_rpow, hv, ← Real.rpow_mul hN0.le]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hv0 : 0 ≤ v := (Real.rpow_pos_of_pos hN0 _).le
  have hφ0 : 0 ≤ phi N ^ C :=
    Real.rpow_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg N) _) _
  have hIm : (msc ⟨E, η⟩).im ≤ 2 * Cm * u := by
    refine him.trans ?_
    have h2 : Real.sqrt (kappa E + η) ≤ 2 * u := by
      calc Real.sqrt (kappa E + η) ≤ Real.sqrt (2 * v) := Real.sqrt_le_sqrt (by linarith)
        _ = Real.sqrt 2 * Real.sqrt v := Real.sqrt_mul (by norm_num) v
        _ ≤ 2 * u := by
            have : Real.sqrt 2 ≤ 2 := by
              rw [Real.sqrt_le_left (by norm_num)]; norm_num
            nlinarith [Real.sqrt_nonneg v, Real.sqrt_nonneg 2]
    calc Cm * Real.sqrt (kappa E + η) ≤ Cm * (2 * u) := by gcongr
      _ = 2 * Cm * u := by ring
  have hIm0 : 0 ≤ (msc ⟨E, η⟩).im := (im_msc_pos hη0).le
  have hsq : Real.sqrt ((msc ⟨E, η⟩).im / (N * η)) ≤ 2 * Cm * u := by
    have h1 : (msc ⟨E, η⟩).im / (N * η) ≤ (2 * Cm) * u ^ 2 := by
      rw [div_eq_mul_one_div, hNη]
      nlinarith
    calc Real.sqrt ((msc ⟨E, η⟩).im / (N * η)) ≤ Real.sqrt ((2 * Cm) * u ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt (2 * Cm) * u := by
          rw [Real.sqrt_mul (by linarith), Real.sqrt_sq hu0.le]
      _ ≤ 2 * Cm * u := by
          have : Real.sqrt (2 * Cm) ≤ 2 * Cm := by
            rw [Real.sqrt_le_left (by linarith)]; nlinarith
          gcongr
  change phi N ^ C * (1 / q + Real.sqrt ((msc ⟨E, η⟩).im / (N * η)) + 1 / (N * η)) ≤ _
  rw [hNη]
  have hsum : 1 / q + Real.sqrt ((msc ⟨E, η⟩).im / (N * η)) + u ≤ 4 * Cm * u := by
    nlinarith
  have e1 : (N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε) = (N : ℝ) ^ ε * u := by
    rw [hu, ← Real.rpow_add hN0]
    congr 1
    ring
  rw [e1]
  calc phi N ^ C * (1 / q + Real.sqrt ((msc ⟨E, η⟩).im / (N * η)) + u) ≤
        phi N ^ C * (4 * Cm * u) := mul_le_mul_of_nonneg_left hsum hφ0
    _ = 4 * Cm * phi N ^ C * u := by ring
    _ ≤ (N : ℝ) ^ ε * u := mul_le_mul_of_nonneg_right hφ hu0.le

/-! ### Assembly -/

/-- `E|X|^{2r} ≤ |ι|^{2r} |E Σ f(w) w(R)|`. -/
private lemma pm_step_pow {N : ℕ} {μ : Measure (Entries N)} [IsProbabilityMeasure μ] {z : ℂ}
    (e : Fin N ⊕ OffDiag N) (k : List ℕ) (r : ℕ) (hcard : 0 < Fintype.card (pm_ι e k)) :
    ∫ ω, ‖∑ i, ∑ j, evalW (resR e z ω) 0 (pm_L e k i j)‖ ^ (2 * r) ∂μ ≤
      (Fintype.card (pm_ι e k) : ℝ) ^ (2 * r) *
        ‖∫ ω, evalF (resR e z ω) (msc z) (pm_F e k r) ∂μ‖ := by
  have h1 : ∀ ω, (((‖∑ i, ∑ j, evalW (resR e z ω) 0 (pm_L e k i j)‖ ^ (2 * r) : ℝ)) : ℂ) =
      (((Fintype.card (pm_ι e k) : ℝ) ^ (2 * r) : ℝ) : ℂ) *
        evalF (resR e z ω) (msc z) (pm_F e k r) :=
    fun ω => pm_norm_pow_eq _ _ e k r hcard
  calc ∫ ω, ‖∑ i, ∑ j, evalW (resR e z ω) 0 (pm_L e k i j)‖ ^ (2 * r) ∂μ =
        (∫ ω, (((‖∑ i, ∑ j, evalW (resR e z ω) 0 (pm_L e k i j)‖ ^ (2 * r) : ℝ)) : ℂ) ∂μ).re := by
        rw [integral_complex_ofReal, Complex.ofReal_re]
    _ = ((((Fintype.card (pm_ι e k) : ℝ) ^ (2 * r) : ℝ) : ℂ) *
          ∫ ω, evalF (resR e z ω) (msc z) (pm_F e k r) ∂μ).re := by
        simp_rw [h1]
        rw [integral_const_mul]
    _ ≤ ‖(((Fintype.card (pm_ι e k) : ℝ) ^ (2 * r) : ℝ) : ℂ) *
          ∫ ω, evalF (resR e z ω) (msc z) (pm_F e k r) ∂μ‖ := Complex.re_le_norm _
    _ = _ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- A formal sum with nonnegative weights of total weight `0` evaluates to `0`. -/
private lemma pm_evalF_eq_zero {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ) :
    ∀ F : FSum N, (∀ cw ∈ F, 0 ≤ cw.1) → (F.map Prod.fst).sum = 0 → evalF G m F = 0
  | [], _, _ => by simp [evalF]
  | cw :: F, hF, h0 => by
    have hcw := hF cw List.mem_cons_self
    have hF' : ∀ x ∈ F, 0 ≤ x.1 := fun x hx => hF x (List.mem_cons_of_mem _ hx)
    have hs : 0 ≤ (F.map Prod.fst).sum := List.sum_nonneg fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hF' y hy
    simp only [List.map_cons, List.sum_cons] at h0
    have h1 : cw.1 = 0 := by linarith
    have h2 : (F.map Prod.fst).sum = 0 := by linarith
    simp only [evalF, List.map_cons, List.sum_cons] at ⊢
    have := pm_evalF_eq_zero G m F hF' h2
    simp only [evalF] at this
    rw [this, h1]
    simp

/-- One application of the iteration (6.93)–(6.95) to the formal sum `P_{d₀} F` (with `d₀` empty
or one operator `P_{γ,α}`, `|α| ≤ ξ`): if every iterate `P_d` of `F` with at most `L + 1`
operators and `|d| ≤ ξ + L ξ'` has `|E_{H̃} P_d F| ≤ B`, then
`|E_{H_γ} P_{d₀} F| ≤ 2B + 2^{|d₀|} N^{-ζ}`. -/
private lemma pm_compare {N : ℕ} {μ₀ μ₁ : Measure (Entries N)} [IsProbabilityMeasure μ₀]
    [IsProbabilityMeasure μ₁] {z : ℂ} {φq ζ : ℝ} {s ξ L : ℕ} (F : FSum N)
    (hF : ∀ cw ∈ F, 0 ≤ cw.1 ∧ cw.2.length = s) (hF1 : (F.map Prod.fst).sum = 1)
    (hcomp : ∀ (s' : ℕ) (G : FSum N), s ≤ s' → s' ≤ s + ξ →
      (∀ cw ∈ G, 0 ≤ cw.1 ∧ cw.2.length = s') → (G.map Prod.fst).sum = 1 → ∀ B : ℝ, 0 ≤ B →
      (∀ d : List ((Fin N ⊕ OffDiag N) × List ℕ), d ≠ [] → d.length ≤ L →
        IterAdm (xiOf (2 * ζ + 3) φq) s' d →
        (N : ℝ) ^ (-(φq / 20) * ((d.map fun x => x.2.sum).sum : ℝ)) *
          ‖∫ ω, evalF (resS z ω) (msc z) (iterP d G) ∂μ₁‖ ≤ B) →
      ‖∫ ω, evalF (resS z ω) (msc z) G ∂μ₀‖ ≤
        ‖∫ ω, evalF (resS z ω) (msc z) G ∂μ₁‖ + B + (N : ℝ) ^ (-ζ))
    (hN : 1 ≤ (N : ℝ)) (hφq : 0 < φq) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ d : List ((Fin N ⊕ OffDiag N) × List ℕ), pm_LenAdm s d → d.length ≤ L + 1 →
      iterate_ord d ≤ ξ + L * xiOf (2 * ζ + 3) φq →
      ‖∫ ω, evalF (resS z ω) (msc z) (iterP d F) ∂μ₁‖ ≤ B)
    (d₀ : List ((Fin N ⊕ OffDiag N) × List ℕ)) (hd₀ : pm_LenAdm s d₀) (hl₀ : d₀.length ≤ 1)
    (ho₀ : iterate_ord d₀ ≤ ξ) :
    ‖∫ ω, evalF (resS z ω) (msc z) (iterP d₀ F) ∂μ₀‖ ≤
      2 * B + 2 ^ iterate_ord d₀ * (N : ℝ) ^ (-ζ) := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ (-ζ) := Real.rpow_nonneg (by linarith) _
  obtain ⟨hP, hW⟩ := pm_iterP_props d₀ s F hd₀ hF
  rw [hF1, mul_one] at hW
  set W := ((iterP d₀ F).map Prod.fst).sum with hWdef
  have hW0 : 0 ≤ W := List.sum_nonneg fun x hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact (hP y hy).1
  have hB1 := hB d₀ hd₀ (by omega) (by omega)
  rcases hW0.eq_or_lt with hWz | hWp
  · have h0 : ∀ ω, evalF (resS z ω) (msc z) (iterP d₀ F) = 0 := fun ω =>
      pm_evalF_eq_zero _ _ _ (fun cw h => (hP cw h).1) hWz.symm
    simp_rw [h0]
    simp only [integral_zero, norm_zero]
    positivity
  · set G := pm_smul W⁻¹ (iterP d₀ F) with hG
    obtain ⟨hGp, hGs⟩ := pm_smul_props (inv_nonneg.2 hW0) (iterP d₀ F) hP
    rw [← hWdef, inv_mul_cancel₀ hWp.ne'] at hGs
    have hint : ∀ (μ : Measure (Entries N)) [IsProbabilityMeasure μ] (H : FSum N),
        ∫ ω, evalF (resS z ω) (msc z) (pm_smul W⁻¹ H) ∂μ =
          (W⁻¹ : ℂ) * ∫ ω, evalF (resS z ω) (msc z) H ∂μ := by
      intro μ _ H
      simp_rw [pm_evalF_smul]
      rw [integral_const_mul]
      push_cast
      rfl
    have hnorm : ∀ (μ : Measure (Entries N)) [IsProbabilityMeasure μ] (H : FSum N),
        ‖∫ ω, evalF (resS z ω) (msc z) (pm_smul W⁻¹ H) ∂μ‖ =
          W⁻¹ * ‖∫ ω, evalF (resS z ω) (msc z) H ∂μ‖ := by
      intro μ _ H
      rw [hint μ H, norm_mul, ← Complex.ofReal_inv, Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.2 hW0)]
    have hc := hcomp (s + iterate_ord d₀) G (by omega) (by omega) hGp hGs (W⁻¹ * B)
      (mul_nonneg (inv_nonneg.2 hW0) hB0) (by
        intro d _ hdl hdA
        rw [hG, pm_iterP_smul, ← pm_iterP_append, hnorm μ₁]
        have h1 : (N : ℝ) ^ (-(φq / 20) * ((d.map fun x => x.2.sum).sum : ℝ)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hN (by
            have : (0 : ℝ) ≤ ((d.map fun x => x.2.sum).sum : ℝ) :=
              List.sum_nonneg fun x hx => by
                obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
                positivity
            nlinarith)
        have h2 := hB (d₀ ++ d) (pm_lenAdm_append s d₀ d hd₀ (pm_lenAdm_of_iterAdm _ d hdA))
          (by simp only [List.length_append]; omega) (by
            rw [pm_ord_append]
            have := iterate_ord_le d _ hdA
            have : d.length * xiOf (2 * ζ + 3) φq ≤ L * xiOf (2 * ζ + 3) φq :=
              Nat.mul_le_mul_right _ hdl
            omega)
        calc _ ≤ 1 * (W⁻¹ * ‖∫ ω, evalF (resS z ω) (msc z) (iterP (d₀ ++ d) F) ∂μ₁‖) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ ≤ W⁻¹ * B := by rw [one_mul]; exact mul_le_mul_of_nonneg_left h2 (by positivity))
    rw [hG, hnorm μ₀, hnorm μ₁] at hc
    have hc' := mul_le_mul_of_nonneg_left hc hW0
    rw [← mul_assoc, mul_inv_cancel₀ hWp.ne', one_mul, mul_add, mul_add, ← mul_assoc,
      mul_inv_cancel₀ hWp.ne', one_mul, ← mul_assoc, mul_inv_cancel₀ hWp.ne', one_mul] at hc'
    have hW2 : W * (N : ℝ) ^ (-ζ) ≤ 2 ^ iterate_ord d₀ * (N : ℝ) ^ (-ζ) :=
      mul_le_mul_of_nonneg_right hW hN0
    linarith

/-- The bad event of (6.97) costs at most `N^{n} (N + 1)^m N^{C'} e^{-c φ} ≤ 1` once
`(n + 2m + C') log N ≤ c φ`. -/
private lemma pm_bad_le {N : ℕ} (hN : 2 ≤ N) (n m : ℕ) {C' c ϕ : ℝ}
    (h : ((n : ℝ) + 2 * m + C') * Real.log N ≤ c * ϕ) :
    (N : ℝ) ^ n * ((N : ℝ) + 1) ^ m * ((N : ℝ) ^ C' * Real.exp (-c * ϕ)) ≤ 1 := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have h1 : ((N : ℝ) + 1) ^ m ≤ ((N : ℝ) ^ 2) ^ m :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) m
  have e1 : ∀ x : ℝ, (N : ℝ) ^ x = Real.exp (Real.log N * x) := fun x => Real.rpow_def_of_pos hN0 x
  have e2 : (N : ℝ) ^ n * ((N : ℝ) ^ 2) ^ m * (N : ℝ) ^ C' =
      Real.exp (Real.log N * ((n : ℝ) + 2 * m + C')) := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hN0,
      ← Real.rpow_add hN0, e1]
    push_cast
    ring_nf
  calc (N : ℝ) ^ n * ((N : ℝ) + 1) ^ m * ((N : ℝ) ^ C' * Real.exp (-c * ϕ)) ≤
        (N : ℝ) ^ n * ((N : ℝ) ^ 2) ^ m * ((N : ℝ) ^ C' * Real.exp (-c * ϕ)) := by gcongr
    _ = Real.exp (Real.log N * ((n : ℝ) + 2 * m + C') + -c * ϕ) := by
        rw [← mul_assoc, e2, Real.exp_add]
    _ ≤ Real.exp 0 := Real.exp_le_exp.2 (by nlinarith)
    _ = 1 := Real.exp_zero

/-- The final count of (6.89): `E|X|^p ≤ u P`, `P ≤ (1 + n)(2B + L Z) + L' Z`,
`u B ≤ G V + L₂`, `u Z ≤ L₃`, `V ≥ 1` give `E|X|^p ≤ M V` when the constant is at most `M`. -/
private lemma pm_final {X0 P u B Z n L L' G V L₂ L₃ M : ℝ} (hu : 0 ≤ u) (hn : 0 ≤ n)
    (hL : 0 ≤ L) (hL' : 0 ≤ L') (hX0 : X0 ≤ u * P) (hP : P ≤ (1 + n) * (2 * B + L * Z) + L' * Z)
    (hB : u * B ≤ G * V + L₂) (hZ : u * Z ≤ L₃) (hV : 1 ≤ V) (hL₂ : 0 ≤ L₂)
    (hL₃ : 0 ≤ L₃) (hM : (1 + n) * (2 * (G + L₂) + L * L₃) + L' * L₃ ≤ M) : X0 ≤ M * V := by
  have h1 : u * P ≤ (1 + n) * (2 * (u * B) + L * (u * Z)) + L' * (u * Z) := by
    have := mul_le_mul_of_nonneg_left hP hu
    linarith [this]
  have h2 : (1 + n) * (2 * (u * B) + L * (u * Z)) + L' * (u * Z) ≤
      (1 + n) * (2 * (G * V + L₂) + L * L₃) + L' * L₃ := by
    gcongr
  have h3 : (1 + n) * (2 * (G * V + L₂) + L * L₃) + L' * L₃ ≤
      ((1 + n) * (2 * (G + L₂) + L * L₃) + L' * L₃) * V := by
    have : 0 ≤ (V - 1) * ((1 + n) * (2 * L₂ + L * L₃) + L' * L₃) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith
  have h4 : ((1 + n) * (2 * (G + L₂) + L * L₃) + L' * L₃) * V ≤ M * V :=
    mul_le_mul_of_nonneg_right hM (by linarith)
  linarith

/-- (6.89): for `k ∈ ℕ²`, `1 ≤ |k| ≤ ⌈3/φs⌉`, and even `p`,
`E |Σ_{ij} P_{γ,k}(R_ij conj R_ij)|^p ≤ (N^{1+Cε})^p` at `z = E + iN^{-2/3-ε}`, `E ∈ I_ε`. -/
theorem moment_opP_pair_le {C1 φs : ℝ} (hφs : 0 < φs) :
    ∃ ε₀ > (0 : ℝ), ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ p : ℕ, Even p → ∃ N0 : ℕ, ∀ N ≥ N0,
      ∀ (Lv Lw : EntryLaws N) (γ : ℕ), SmallQClass C1 φs N Lv → Lv.IsMomentMatch Lw C1 →
      ∀ (e : Fin N ⊕ OffDiag N) (k : List ℕ), k.length = 2 → 1 ≤ k.sum → k.sum ≤ ⌈3 / φs⌉₊ →
      ∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
        ∫ ω, ‖∑ i, ∑ j, evalW (resR e ⟨E, etaEdge N ε⟩ ω) 0
            (wordP e k [⟨.g, i, j⟩, ⟨.gbar, i, j⟩])‖ ^ p ∂(interp (lexPos N) γ Lv Lw).law ≤
          ((N : ℝ) ^ (1 + C * ε)) ^ p := by
  refine ⟨1 / 12, by norm_num, 7, by norm_num, fun ε hε hε1 p hp => ?_⟩
  obtain ⟨r, hr⟩ := hp
  obtain rfl : p = 2 * r := by omega
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · refine ⟨3, fun N hN Lv Lw γ hv hw e k _ _ _ E _ => ?_⟩
    subst hr0
    have hmp := (MatchedPair.of_smallQ hN hv hw).interp γ
    have := isProbabilityMeasure_law hmp.isProb_v
    simp
  -- the constants
  set φq : ℝ := min φs (1 / 4) with hφqdef
  have hφq : 0 < φq := lt_min hφs (by norm_num)
  set K : ℕ := ⌈3 / φs⌉₊ with hKdef
  set ζ : ℝ := ((4 * r : ℕ) : ℝ) with hζdef
  have hζ1 : 1 ≤ ζ := by rw [hζdef]; exact_mod_cast (by omega : 1 ≤ 4 * r)
  set smax : ℕ := 2 * r * (2 + K) with hsmax
  set ξ : ℕ := xiOf ζ φq with hξ
  set ξ' : ℕ := xiOf (2 * ζ + 3) φq with hξ'
  set Lc : ℕ := ⌈6 * ζ / φq⌉₊ with hLc
  set Om : ℕ := ξ + Lc * ξ' with hOm
  set Λ : ℝ := 2 ^ K with hΛ
  set Dm : ℝ := 2 * ((Lc : ℝ) + 2) with hDm
  set nα : ℝ := ((ξ : ℝ) + 1) * ((smax : ℝ) + 1) ^ ξ with hnα
  have hKse : (0 : ℝ) < smax := by rw [hsmax]; positivity
  have hKsc : (0 : ℝ) < (smax : ℝ) + ξ := by positivity
  obtain ⟨C0e, hC0e, N0e, hexp⟩ := expectation_expansion_inv (C1 := C1) (φq := φq)
    (Ks := smax) hφq hKse
  obtain ⟨C0c, hC0c, N0c, hcomp⟩ := comparison_iterate (C1 := C1) (φq := φq)
    (Ks := smax + ξ) hφq hKsc
  obtain ⟨Cl, hCl, cl, hcl, Cl', hCl', N0l, hll⟩ := localLaw (ζ := 1) (C0 := max C1 1) (c := 1)
    one_pos (le_max_of_le_right zero_le_one) one_pos
  obtain ⟨Cm, hCm, hmsc⟩ := msc_bounds
  set Kt : ℝ := (2 * C1 + 4) * C1 with hKt
  set Cx : ℝ := max (max C0e C0c) Cl with hCx
  set A : ℝ := 4 * r + 2 * ((smax : ℝ) + Om) + Cl' with hA
  set Ctot : ℝ := (1 + nα) * (2 * (3 ^ (smax + Om) * 2 ^ Om * (Λ * (2 + 2 * Dm)) ^ (2 * r) +
      2 ^ Om * Λ ^ (2 * r)) + 2 ^ ξ * Λ ^ (2 * r)) + 4 ^ smax * Λ ^ (2 * r) with hCtot
  have hev := (eventually_ge_atTop (max (max N0e N0c) (max N0l 16))).and <|
    (phi_rpow_le_rpow Cx (by norm_num : (0 : ℝ) < 1 / 8)).and <|
    (phi_rpow_le_rpow Cl (by positivity : (0 : ℝ) < ε / 2)).and <|
    (((tendsto_rpow_atTop (by positivity : (0 : ℝ) < ε / 2)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (4 * Cm)).and <|
    (pm_tilde_ge Kt).and <|
    (expansion_eventually_le_phi ζ).and <|
    (expansion_eventually_log_le (A / cl)).and <|
    (((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (max Ctot 1))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨N0, fun N hN Lv Lw γ hv hw e k hk2 hk1 hkK E hE => ?_⟩
  obtain ⟨hNb, hφx, hφl, hNε, hqt, hζφ, hlog, hNC⟩ := hN0 N hN
  simp only [Function.comp] at hNε hNC
  -- facts on `N`, `φ` and `z`
  have hNe : N0e ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hNb
  have hNc : N0c ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hNb
  have hNl : N0l ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hNb
  have hN16 : 16 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hNb
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hN0r : (0 : ℝ) < N := by linarith
  have hN1r : (1 : ℝ) ≤ N := by linarith
  have hlog1 : 1 ≤ Real.log N := by
    have h1 : Real.log 16 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
    have h2 : (1 : ℝ) < Real.log 16 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast
      linarith
    linarith
  have hφ1 : 1 ≤ phi N := hlog1.trans (log_le_phi hN16)
  have hφC : ∀ C ≤ Cx, phi N ^ C ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := fun C hC =>
    (Real.rpow_le_rpow_of_exponent_le hφ1 hC).trans hφx
  set z : ℂ := ⟨E, etaEdge N ε⟩ with hzdef
  have hzC : ∀ C ≤ Cx, z ∈ specDomain N C := fun C hC =>
    pm_mem_specDomain (by omega) hε (by linarith) hE (hφC C hC)
  have hze := hzC C0e (le_trans (le_max_left _ _) (le_max_left _ _))
  have hzc := hzC C0c (le_trans (le_max_right _ _) (le_max_left _ _))
  have hzl := hzC Cl (le_max_right _ _)
  have hzim : 0 < z.im := Real.rpow_pos_of_pos hN0r _
  have hzB : 1 / z.im ≤ N := by
    change 1 / (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) ≤ N
    rw [one_div, ← Real.rpow_neg hN0r.le]
    calc (N : ℝ) ^ (-(-(2 : ℝ) / 3 - ε)) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
      _ = N := Real.rpow_one _
  set ψ : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε) with hψdef
  have hψ0 : 0 ≤ ψ := (Real.rpow_pos_of_pos hN0r _).le
  have hψ1 : ψ ≤ 1 := pm_rpow_le_one hN1r (by linarith)
  -- the classes
  have hN3 : 3 ≤ N := by omega
  set qt : ℝ := Real.sqrt N / ((2 * C1 + 4) * C1 * Real.log N) with hqtdef
  have hqt0 := tilde_pos hN3 hv.1 hw
  have hKt0 : 0 < Kt := by
    have hlogp : 0 < Real.log N := by linarith
    have h1 : 0 < Kt * Real.log N :=
      (div_pos_iff_of_pos_left (Real.sqrt_pos.mpr hN0r)).1 hqt0
    exact (mul_pos_iff_of_pos_right hlogp).1 h1
  have hqt' : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ qt := hqt hKt0
  have hmp0 := MatchedPair.of_smallQ hN3 hv hw
  set q : ℝ := min ((N : ℝ) ^ φs) qt with hqdef
  have hq : (N : ℝ) ^ φq ≤ q := le_min
    (Real.rpow_le_rpow_of_exponent_le hN1r (min_le_left _ _))
    ((Real.rpow_le_rpow_of_exponent_le hN1r ((min_le_right _ _).trans (by norm_num))).trans hqt')
  have hL : PairInterpClass C1 φq N (interp (lexPos N) γ Lv Lw) := ⟨Lv, Lw, q, γ, hmp0, hq, rfl⟩
  have hμγ := isProbabilityMeasure_law (hmp0.interp γ).isProb_v
  have hμw := isProbabilityMeasure_law hmp0.isProb_w
  -- the local law for `H̃` at `z` (6.97)
  set Pw : ℝ := (Lw.law (pm_good z ψ)ᶜ).toReal with hPwdef
  have hPw : Pw ≤ (N : ℝ) ^ Cl' * Real.exp (-cl * phi N) := by
    have hgw := hmp0.isGenWigner.2
    have hb := hll N hNl Lw hgw
    have hsp : Lw.SupportParam (phi N ^ Cl) 1 qt :=
      ⟨(hφC Cl (le_max_right _ _)).trans ((Real.rpow_le_rpow_of_exponent_le hN1r
        (by norm_num)).trans hqt'), hw.2.1.boundedSupport 1, hw.2.1.tailVarOff 1⟩
    have h4 : 4 * Cm * phi N ^ Cl ≤ (N : ℝ) ^ ε := by
      have e1 : (N : ℝ) ^ ε = (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) := by
        rw [← Real.rpow_add hN0r]; ring_nf
      rw [e1]
      have h0 : 0 ≤ phi N ^ Cl := Real.rpow_nonneg (by linarith) _
      exact mul_le_mul hNε hφl h0 (by positivity)
    have hent := pm_entryErr_le (by omega) hε (by linarith) hE hCm hmsc h4 hqt'
    have hsub : (pm_good z ψ)ᶜ ⊆ {ω : Entries N | ∀ q', Lw.SupportParam (phi N ^ Cl) 1 q' →
        ω ∈ localLawEvent N Cl q'}ᶜ := by
      refine Set.compl_subset_compl.2 fun ω hω i j => ?_
      exact ((hω qt hsp) z hzl).2 i j |>.trans hent
    have h1 : Lw.law (pm_good z ψ)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ Cl' * Real.exp (-cl * phi N)) := by
      refine (measure_mono hsub).trans (hb.trans_eq ?_)
      rw [Real.rpow_one]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h1
  -- the expansion (6.92) of `R` in `S`
  set s : ℕ := 2 * r * (2 + k.sum) with hsdef
  have hs_le : s ≤ smax := Nat.mul_le_mul_left _ (by omega)
  have hφ2 : 1 ≤ phi N ^ 2 := one_le_pow₀ hφ1
  have hζ2 : ζ ≤ phi N ^ 2 := hζφ.trans (le_self_pow₀ hφ1 (by norm_num))
  have hsK : (s : ℝ) ≤ (smax : ℝ) * phi N ^ 2 :=
    (show (s : ℝ) ≤ smax by exact_mod_cast hs_le).trans (le_mul_of_one_le_right hKse.le hφ2)
  obtain ⟨Ac, hAc, hAz⟩ := hexp N hNe _ hL e ζ hζ1 hζ2 s hsK
  have hAw := hAz z hze
  have hA1 : ∀ α, |Ac α| ≤ 1 := fun α => (hAc α).trans (pm_rpow_le_one hN1r (by
    have : (0 : ℝ) ≤ ((∑ t, α t : ℕ) : ℝ) * φq := by positivity
    have h : -((∑ t, α t : ℕ) : ℝ) * φq / 10 = -(((∑ t, α t : ℕ) : ℝ) * φq / 10) := by ring
    rw [h]
    have := div_nonneg this (by norm_num : (0 : ℝ) ≤ 10)
    linarith))
  -- the empty index set
  change ∫ ω, ‖∑ i, ∑ j, evalW (resR e z ω) 0 (pm_L e k i j)‖ ^ (2 * r)
      ∂(interp (lexPos N) γ Lv Lw).law ≤ ((N : ℝ) ^ (1 + 7 * ε)) ^ (2 * r)
  rcases Nat.eq_zero_or_pos (Fintype.card (pm_ι e k)) with hc0 | hcard
  · have h0 : ∀ ω, ∑ i, ∑ j, evalW (resR e z ω) 0 (pm_L e k i j) = 0 := by
      intro ω
      rw [pm_X_eq (resR e z ω) (msc z)]
      have : IsEmpty (pm_ι e k) := Fintype.card_eq_zero_iff.1 hc0
      simp
    simp_rw [h0]
    simp only [norm_zero, ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, hr0.ne',
      not_false_eq_true, zero_pow, integral_zero]
    positivity
  set F := pm_F e k r with hFdef
  have hF := pm_F_props e hk2 r
  have hF1 := pm_F_sum e k r hcard
  set c : ℝ := (Fintype.card (pm_ι e k) : ℝ) with hcdef
  have hc0 : 0 < c := by rw [hcdef]; exact_mod_cast hcard
  have hstep1 := pm_step_pow (μ := (interp (lexPos N) γ Lv Lw).law) (z := z) e k r hcard
  have hstep2 := pm_expansion_sum (μ := (interp (lexPos N) γ Lv Lw).law) hzim e _ Ac hAw F hF
  rw [hF1, one_mul] at hstep2
  -- the iterates (6.93)–(6.100) under `H̃`
  set a : ℕ := smax + Om with hadef
  set Gb : ℝ := 3 ^ a * 2 ^ Om * ((c ^ (2 * r))⁻¹ * (c * ψ ^ 3 + Λ * ((N : ℝ) + 2 * Dm * N)) ^
    (2 * r)) + ((N : ℝ) + 1) ^ a * 2 ^ Om * Pw with hGbdef
  have hPw0 : 0 ≤ Pw := ENNReal.toReal_nonneg
  have hGb0 : 0 ≤ Gb := by positivity
  have hGb : ∀ d : List ((Fin N ⊕ OffDiag N) × List ℕ), pm_LenAdm s d → d.length ≤ Lc + 1 →
      iterate_ord d ≤ Om →
      ‖∫ ω, evalF (resS z ω) (msc z) (iterP d F) ∂Lw.law‖ ≤ Gb := by
    intro d hd hdl hdo
    refine (pm_iterate_le (μ := Lw.law) hzim hzB hψ0 hψ1 e hk2 hk1 r hcard d hd).trans ?_
    have ha : s + iterate_ord d ≤ a := by omega
    have hb : iterate_ord d ≤ Om := hdo
    have hk : (2 : ℝ) ^ k.sum ≤ Λ := pow_le_pow_right₀ (by norm_num) hkK
    have hdl' : 2 * ((d.length : ℝ) + 1) ≤ Dm := by
      rw [hDm]
      have : (d.length : ℝ) ≤ Lc + 1 := by exact_mod_cast hdl
      linarith
    rw [hGbdef, hcdef]
    have h3 : (3 : ℝ) ^ (s + iterate_ord d) ≤ 3 ^ a := pow_le_pow_right₀ (by norm_num) ha
    have h2 : (2 : ℝ) ^ iterate_ord d ≤ 2 ^ Om := pow_le_pow_right₀ (by norm_num) hb
    have hN : ((N : ℝ) + 1) ^ (s + iterate_ord d) ≤ ((N : ℝ) + 1) ^ a :=
      pow_le_pow_right₀ (by linarith) ha
    gcongr
  have hcompN : ∀ (s' : ℕ) (G : FSum N), s ≤ s' → s' ≤ s + ξ →
      (∀ cw ∈ G, 0 ≤ cw.1 ∧ cw.2.length = s') → (G.map Prod.fst).sum = 1 → ∀ B : ℝ, 0 ≤ B →
      (∀ d : List ((Fin N ⊕ OffDiag N) × List ℕ), d ≠ [] → d.length ≤ Lc →
        IterAdm (xiOf (2 * ζ + 3) φq) s' d →
        (N : ℝ) ^ (-(φq / 20) * ((d.map fun x => x.2.sum).sum : ℝ)) *
          ‖∫ ω, evalF (resS z ω) (msc z) (iterP d G) ∂Lw.law‖ ≤ B) →
      ‖∫ ω, evalF (resS z ω) (msc z) G ∂(interp (lexPos N) γ Lv Lw).law‖ ≤
        ‖∫ ω, evalF (resS z ω) (msc z) G ∂Lw.law‖ + B + (N : ℝ) ^ (-ζ) := by
    intro s' G _ hs2 hGp hGs B hB hprem
    have hs' : (s' : ℝ) ≤ ((smax : ℝ) + ξ) * ζ := by
      have : (s' : ℝ) ≤ (smax : ℝ) + ξ := by exact_mod_cast (by omega : s' ≤ smax + ξ)
      exact this.trans (le_mul_of_one_le_right hKsc.le hζ1)
    exact hcomp N hNc Lv Lw q hmp0 hq γ ζ hζ1 hζφ s' hs' z hzc G hGp hGs B hB hprem
  have hT0 := pm_compare (μ₀ := (interp (lexPos N) γ Lv Lw).law) (μ₁ := Lw.law) F hF hF1 hcompN
    hN1r hφq hGb0 hGb [] trivial (by simp) (by simp [iterate_ord])
  have hTα : ∀ α ∈ highIdx s 0 ξ,
      ‖∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) F) ∂(interp (lexPos N) γ Lv Lw).law‖ ≤
        2 * Gb + 2 ^ ξ * (N : ℝ) ^ (-ζ) := by
    intro α hα
    have hαξ := ((expansion_mem_highIdx α).1 hα).2
    have ho : iterate_ord [(e, List.ofFn α)] = ∑ t, α t := by
      simp [iterate_ord, List.sum_ofFn]
    have h := pm_compare (μ₀ := (interp (lexPos N) γ Lv Lw).law) (μ₁ := Lw.law) F hF hF1 hcompN
      hN1r hφq hGb0 hGb [(e, List.ofFn α)] ⟨List.length_ofFn, trivial⟩ (by simp)
      (by rw [ho]; exact hαξ)
    refine h.trans ?_
    gcongr
    · norm_num
    · rw [ho]; exact hαξ
  -- the count
  set Z : ℝ := (N : ℝ) ^ (-ζ) with hZdef
  have hZ0 : 0 ≤ Z := (Real.rpow_pos_of_pos hN0r _).le
  have hZe : Z = ((N : ℝ) ^ (4 * r))⁻¹ := by
    rw [hZdef, hζdef, Real.rpow_neg hN0r.le, Real.rpow_natCast]
  set Y : ℝ := (N : ℝ) ^ (1 + 6 * ε) with hYdef
  have hY1 : 1 ≤ Y := Real.one_le_rpow hN1r (by linarith)
  have hNY : (N : ℝ) ≤ Y := by
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ Y := Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
  have hψ3 : (N : ℝ) ^ 2 * ψ ^ 3 = Y := by
    rw [hψdef, hYdef, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hN0r.le,
      ← Real.rpow_add hN0r]
    congr 1
    push_cast
    ring
  have hcN : c ≤ Λ * (N : ℝ) ^ 2 := (pm_card_le e k).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hkK) (by positivity))
  have hc2r : c ^ (2 * r) ≤ Λ ^ (2 * r) * (N : ℝ) ^ (4 * r) := by
    calc c ^ (2 * r) ≤ (Λ * (N : ℝ) ^ 2) ^ (2 * r) := pow_le_pow_left₀ hc0.le hcN _
      _ = Λ ^ (2 * r) * (N : ℝ) ^ (4 * r) := by rw [mul_pow, ← pow_mul]; ring_nf
  have hΛ0 : 0 ≤ Λ := by positivity
  have hcZ : c ^ (2 * r) * Z ≤ Λ ^ (2 * r) := by
    rw [hZe]
    calc c ^ (2 * r) * ((N : ℝ) ^ (4 * r))⁻¹ ≤
          Λ ^ (2 * r) * (N : ℝ) ^ (4 * r) * ((N : ℝ) ^ (4 * r))⁻¹ :=
          mul_le_mul_of_nonneg_right hc2r (by positivity)
      _ = Λ ^ (2 * r) := by
          rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hN0r.ne'), mul_one]
  have hbad : c ^ (2 * r) * (((N : ℝ) + 1) ^ a * Pw) ≤ Λ ^ (2 * r) := by
    have h1 : ((N : ℝ) + 1) ^ a * Pw ≤
        ((N : ℝ) + 1) ^ a * ((N : ℝ) ^ Cl' * Real.exp (-cl * phi N)) :=
      mul_le_mul_of_nonneg_left hPw (by positivity)
    have h2 := pm_bad_le (N := N) (by omega) (4 * r) a (C' := (Cl' : ℝ)) (c := cl) (ϕ := phi N) (by
      have := mul_le_mul_of_nonneg_left hlog hcl.le
      rw [← mul_assoc, mul_div_cancel₀ _ hcl.ne'] at this
      rw [hA] at this
      push_cast
      rw [hadef] at *
      push_cast at this ⊢
      linarith)
    rw [Real.rpow_natCast] at h2
    calc c ^ (2 * r) * (((N : ℝ) + 1) ^ a * Pw) ≤
          Λ ^ (2 * r) * (N : ℝ) ^ (4 * r) *
            (((N : ℝ) + 1) ^ a * ((N : ℝ) ^ Cl' * Real.exp (-cl * phi N))) :=
          mul_le_mul hc2r h1 (by positivity) (by positivity)
      _ = Λ ^ (2 * r) * ((N : ℝ) ^ (4 * r) * ((N : ℝ) + 1) ^ a *
            ((N : ℝ) ^ Cl' * Real.exp (-cl * phi N))) := by ring
      _ ≤ Λ ^ (2 * r) * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Λ ^ (2 * r) := mul_one _
  have hbase : c * ψ ^ 3 + Λ * ((N : ℝ) + 2 * Dm * N) ≤ Λ * (2 + 2 * Dm) * Y := by
    have h1 : c * ψ ^ 3 ≤ Λ * Y := by
      rw [← hψ3]
      calc c * ψ ^ 3 ≤ Λ * (N : ℝ) ^ 2 * ψ ^ 3 := mul_le_mul_of_nonneg_right hcN (by positivity)
        _ = Λ * ((N : ℝ) ^ 2 * ψ ^ 3) := by ring
    have hDm0 : 0 ≤ Dm := by positivity
    have h2 : Λ * ((N : ℝ) + 2 * Dm * N) ≤ Λ * (1 + 2 * Dm) * Y := by
      have : Λ * ((N : ℝ) + 2 * Dm * N) = Λ * (1 + 2 * Dm) * N := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hNY (by positivity)
    have e3 : Λ * (2 + 2 * Dm) * Y = Λ * Y + Λ * (1 + 2 * Dm) * Y := by ring
    linarith
  have hcGb : c ^ (2 * r) * Gb ≤ 3 ^ a * 2 ^ Om * (Λ * (2 + 2 * Dm)) ^ (2 * r) * Y ^ (2 * r) +
      2 ^ Om * Λ ^ (2 * r) := by
    have hc2 : c ^ (2 * r) * (c ^ (2 * r))⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    have hb0 : 0 ≤ c * ψ ^ 3 + Λ * ((N : ℝ) + 2 * Dm * N) := by positivity
    have e1 : c ^ (2 * r) * Gb = 3 ^ a * 2 ^ Om *
        (c * ψ ^ 3 + Λ * ((N : ℝ) + 2 * Dm * N)) ^ (2 * r) +
        2 ^ Om * (c ^ (2 * r) * (((N : ℝ) + 1) ^ a * Pw)) := by
      rw [hGbdef]
      have : c ^ (2 * r) * (3 ^ a * 2 ^ Om * ((c ^ (2 * r))⁻¹ *
          (c * ψ ^ 3 + Λ * ((N : ℝ) + 2 * Dm * N)) ^ (2 * r))) =
          3 ^ a * 2 ^ Om * (c ^ (2 * r) * (c ^ (2 * r))⁻¹) *
            (c * ψ ^ 3 + Λ * ((N : ℝ) + 2 * Dm * N)) ^ (2 * r) := by ring
      rw [mul_add, this, hc2]
      ring
    rw [e1, mul_assoc (3 ^ a * 2 ^ Om : ℝ), ← mul_pow (Λ * (2 + 2 * Dm)) Y]
    gcongr
  have hP : ‖∫ ω, evalF (resR e z ω) (msc z) F ∂(interp (lexPos N) γ Lv Lw).law‖ ≤
      (1 + nα) * (2 * Gb + 2 ^ ξ * Z) + 4 ^ smax * Z := by
    refine hstep2.trans ?_
    have hT0' : ‖∫ ω, evalF (resS z ω) (msc z) F ∂(interp (lexPos N) γ Lv Lw).law‖ ≤
        2 * Gb + 2 ^ ξ * Z := by
      refine hT0.trans ?_
      simp only [iterate_ord, List.map_nil, List.sum_nil, pow_zero, one_mul]
      have : Z ≤ 2 ^ ξ * Z := le_mul_of_one_le_left hZ0 (one_le_pow₀ (by norm_num))
      linarith
    have hsum : ∑ α ∈ highIdx s 0 ξ, |Ac α| *
        ‖∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) F) ∂(interp (lexPos N) γ Lv Lw).law‖
        ≤ nα * (2 * Gb + 2 ^ ξ * Z) := by
      calc _ ≤ ∑ α ∈ highIdx s 0 ξ, (2 * Gb + 2 ^ ξ * Z) := Finset.sum_le_sum fun α hα =>
            (mul_le_mul (hA1 α) (hTα α hα) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
        _ = ((highIdx s 0 ξ).card : ℝ) * (2 * Gb + 2 ^ ξ * Z) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ nα * (2 * Gb + 2 ^ ξ * Z) := by
            refine mul_le_mul_of_nonneg_right ((expansion_card_highIdx_le s 0 ξ).trans ?_)
              (by positivity)
            rw [hnα]
            gcongr
    have h4 : (4 : ℝ) ^ s * Z ≤ 4 ^ smax * Z :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hs_le) hZ0
    have : (4 : ℝ) ^ s * (N : ℝ) ^ (-ζ) = 4 ^ s * Z := rfl
    linarith
  have hM : Ctot ≤ ((N : ℝ) ^ ε) ^ (2 * r) := by
    have h1 : 1 ≤ (N : ℝ) ^ ε := (le_max_right _ _).trans hNC
    exact ((le_max_left _ _).trans hNC).trans (le_self_pow₀ h1 (by omega))
  have hfin := pm_final (X0 := ∫ ω, ‖∑ i, ∑ j, evalW (resR e z ω) 0 (pm_L e k i j)‖ ^ (2 * r)
      ∂(interp (lexPos N) γ Lv Lw).law) (u := c ^ (2 * r)) (V := Y ^ (2 * r))
    (by positivity) (by positivity) (by positivity) (by positivity) hstep1 hP hcGb hcZ
    (one_le_pow₀ hY1) (by positivity) (by positivity) hM
  refine hfin.trans_eq ?_
  rw [← mul_pow, hYdef, ← Real.rpow_add hN0r]
  ring_nf

/-! ### Compiled checks at a concrete nondegenerate point -/

open private expansion_matchedPair_radLaws from WEdgeNS.Comparison.Expansion
open private lawV lawW lawV_momentCond lawV_supp lawVW_isMomentMatch
  from WEdgeNS.Comparison.Classes

/-- For all large `N` the Rademacher laws satisfy the moment conditions of Theorem 3.6 with
`C1 = 2`, the support condition with `φs = 2/5`, and are their own Lemma 5.1 match. -/
private lemma pm_radLaws_class :
    ∀ᶠ N : ℕ in atTop, SmallQClass 2 (2 / 5) N (radLaws N) ∧
      (radLaws N).IsMomentMatch (radLaws N) 2 := by
  filter_upwards [expansion_matchedPair_radLaws, eventually_ge_atTop 32] with N hmp h32
  have hN0 : 0 < N := by omega
  have hNr : (32 : ℝ) ≤ N := by exact_mod_cast h32
  have hN0r : (0 : ℝ) < N := by linarith
  have hsupp := radLaws_boundedSupportAS h32
  have hint := hsupp.integrable_pow hmp.isProb_v
  refine ⟨⟨⟨hmp.isProb_v, (hint 2).1, (hint 4).2, hmp.mean_diag, hmp.mean_off, hmp.var_diag_le,
    hmp.var_off, fun p => ?_, hmp.fourth_off_le⟩, hsupp⟩, ⟨hmp.isProb_v, ?_, fun _ _ _ => rfl,
    fun _ _ _ => rfl⟩⟩
  · rw [integral_abs_pow_three_radLaws_off hN0 p]
    have : (0 : ℝ) ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) := by positivity
    linarith
  · have hlog : 1 ≤ Real.log N := by
      have h1 : Real.log 32 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
      have h2 : (1 : ℝ) < Real.log 32 := by
        rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
        have := Real.log_two_gt_d9
        push_cast
        linarith
      linarith
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0r
    have hq : (Real.sqrt N / ((2 * 2 + 4) * 2 * Real.log N))⁻¹ = 16 * Real.log N / Real.sqrt N := by
      rw [inv_div]; ring
    have hs2 : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    refine ⟨fun i => ?_, fun p => ?_⟩
    · change ((rademacher.map (fun x => Real.sqrt 2 * x)).map
        (fun x => (Real.sqrt N)⁻¹ * x)) _ = 0
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      have hcomp : ((fun x : ℝ => (Real.sqrt N)⁻¹ * x) ∘ fun x : ℝ => Real.sqrt 2 * x) =
          fun x => ((Real.sqrt N)⁻¹ * Real.sqrt 2) * x := by
        funext x
        simp only [Function.comp]
        ring
      rw [hcomp]
      refine rademacher_map_mul_tail_eq_zero ?_
      rw [abs_of_nonneg (by positivity), hq, div_eq_mul_inv, mul_comm]
      gcongr
      linarith
    · change (rademacher.map (fun x => (Real.sqrt N)⁻¹ * x)) _ = 0
      refine rademacher_map_mul_tail_eq_zero ?_
      rw [abs_of_pos (inv_pos.mpr hs), hq, div_eq_mul_inv]
      have : (1 : ℝ) ≤ 16 * Real.log N := by linarith
      calc (Real.sqrt N)⁻¹ = 1 * (Real.sqrt N)⁻¹ := (one_mul _).symm
        _ ≤ 16 * Real.log N * (Real.sqrt N)⁻¹ := by gcongr

/-- The hypotheses `SmallQClass` and `IsMomentMatch` of (6.89) hold for all large `N`
(Rademacher laws, `C1 = 2`, `φs = 2/5`). -/
example : ∀ᶠ N : ℕ in atTop, ∃ Lv Lw : EntryLaws N,
    SmallQClass 2 (2 / 5) N Lv ∧ Lv.IsMomentMatch Lw 2 := by
  filter_upwards [pm_radLaws_class] with N h
  exact ⟨radLaws N, radLaws N, h⟩

/-- The same hypotheses for two different laws at `N = 16`, `C1 = 2`, `φs = 1/4`: `lawW` is a
Lemma 5.1 match of `lawV` with a different fourth diagonal moment. -/
example : SmallQClass 2 (1 / 4) 16 lawV ∧ lawV.IsMomentMatch lawW 2 :=
  ⟨⟨lawV_momentCond, lawV_supp⟩, lawVW_isMomentMatch⟩

/-- `moment_opP_pair_le` for `C1 = 2`, `φs = 2/5`, `p = 2`, `k = (1, 0)`, `E = 2`, at every
interpolation `H_γ` of the Rademacher laws and every entry `e`: all hypotheses hold for all large
`N`. -/
example : ∃ ε₀ > (0 : ℝ), ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ᶠ N : ℕ in atTop,
    ∀ (γ : ℕ) (e : Fin N ⊕ OffDiag N),
      ∫ ω, ‖∑ i, ∑ j, evalW (resR e ⟨2, etaEdge N ε⟩ ω) 0
          (wordP e [1, 0] [⟨.g, i, j⟩, ⟨.gbar, i, j⟩])‖ ^ 2
          ∂(interp (lexPos N) γ (radLaws N) (radLaws N)).law ≤
        ((N : ℝ) ^ (1 + C * ε)) ^ 2 := by
  obtain ⟨ε₀, hε₀, C, hC, h⟩ := moment_opP_pair_le (C1 := 2) (φs := 2 / 5) (by norm_num)
  refine ⟨ε₀, hε₀, C, hC, fun ε hε hεε => ?_⟩
  obtain ⟨N0, hN0⟩ := h ε hε hεε 2 even_two
  filter_upwards [pm_radLaws_class, eventually_ge_atTop N0] with N hcl hN γ e
  have hk : ([1, 0] : List ℕ).sum ≤ ⌈3 / (2 / 5 : ℝ)⌉₊ := by
    simp only [List.sum_cons, List.sum_nil, add_zero]
    exact Nat.one_le_ceil_iff.2 (by norm_num)
  have hE : |(2 : ℝ) - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) := by
    rw [sub_self, abs_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg N) _
  exact hN0 N hN _ _ γ hcl.1 hcl.2 e [1, 0] rfl (by norm_num) hk 2 hE

#print axioms moment_opP_pair_le

end WEdgeNS
