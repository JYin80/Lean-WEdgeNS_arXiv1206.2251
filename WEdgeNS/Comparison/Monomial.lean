import WEdgeNS.Comparison.Telescope

/-!
# Formal monomials in resolvent entries and their evaluation
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- Kinds of resolvent letters: `G_ij`, `conj G_ij`, `G_ij - δ_ij m_sc`, `conj (G_ij - δ_ij m_sc)`. -/
inductive LetterKind
  | g | gbar | gc | gcbar
  deriving DecidableEq, Repr

/-- The uncentred kind of the same conjugacy. -/
def LetterKind.plain : LetterKind → LetterKind
  | .g => .g
  | .gbar => .gbar
  | .gc => .g
  | .gcbar => .gbar

/-- A resolvent letter of kind `kind` at the index pair `(i, j)`. -/
structure Letter (N : ℕ) where
  kind : LetterKind
  i : Fin N
  j : Fin N
  deriving DecidableEq, Repr

/-- A formal product of letters. -/
abbrev Word (N : ℕ) := List (Letter N)

/-- A formal real-weighted sum of words (the coefficients `f(I, J)` of (6.36)). -/
abbrev FSum (N : ℕ) := List (ℝ × Word N)

/-- The words of `(G^{*_γ (k+1)})_{ij}` (6.12): chains `G_{i x₁} G_{y₁ x₂} ⋯ G_{y_k j}` with
`(x_t, y_t)` in `entryPairs e`, every letter of kind `κ`. -/
def starWords {N : ℕ} (e : Fin N ⊕ OffDiag N) (κ : LetterKind) :
    ℕ → Fin N → Fin N → List (Word N)
  | 0, i, j => [[⟨κ, i, j⟩]]
  | k + 1, i, j => (entryPairs e).flatMap fun xy =>
      (starWords e κ k xy.2 j).map fun w => ⟨κ, i, xy.1⟩ :: w

/-- `P_{γ,k}` on a letter (6.13), and `P̃_{γ,k}` on a centred letter (6.17). -/
def letterP {N : ℕ} (e : Fin N ⊕ OffDiag N) (k : ℕ) (ℓ : Letter N) : List (Word N) :=
  if k = 0 then [[ℓ]] else starWords e ℓ.kind.plain k ℓ.i ℓ.j

/-- `P_{γ,k}` on a word (6.14), (6.16): position `t` is expanded `k_t` times; missing entries of
`k` count as `0`. -/
def wordP {N : ℕ} (e : Fin N ⊕ OffDiag N) : List ℕ → Word N → List (Word N)
  | _, [] => [[]]
  | [], ℓ :: w => (wordP e [] w).map (ℓ :: ·)
  | k :: ks, ℓ :: w => (letterP e k ℓ).flatMap fun u => (wordP e ks w).map (u ++ ·)

/-- `P_{γ,k}` on a formal sum (6.15). -/
def opP {N : ℕ} (e : Fin N ⊕ OffDiag N) (k : List ℕ) (F : FSum N) : FSum N :=
  F.flatMap fun cw => (wordP e k cw.2).map fun w => (cw.1, w)

/-- `P_{γ_n,k_n} ⋯ P_{γ_1,k_1}` of (6.33); the head of the list acts first. -/
def iterP {N : ℕ} : List ((Fin N ⊕ OffDiag N) × List ℕ) → FSum N → FSum N
  | [], F => F
  | d :: rest, F => iterP rest (opP d.1 d.2 F)

/-- Number of moments matched at the entry `e` (Lemma 5.1): `2` on the diagonal, `4` off it. -/
def matchedOrder {N : ℕ} : Fin N ⊕ OffDiag N → ℕ
  | Sum.inl _ => 2
  | Sum.inr _ => 4

/-- Admissible data of (6.34): `k_i` has length `s + |k_1| + ⋯ + |k_{i-1}|` and
`matchedOrder e_i < |k_i| ≤ ξ`. -/
def IterAdm {N : ℕ} (ξ : ℕ) : ℕ → List ((Fin N ⊕ OffDiag N) × List ℕ) → Prop
  | _, [] => True
  | s, d :: rest => d.2.length = s ∧ matchedOrder d.1 < d.2.sum ∧ d.2.sum ≤ ξ ∧
      IterAdm ξ (s + d.2.sum) rest

/-- Number of index sequences `(k_1, …, k_n)`, `k_i ∈ ℕ^{s + m_1 + ⋯ + m_{i-1}}`, `|k_i| = m_i`. -/
def iterCount (s : ℕ) : List ℕ → ℕ
  | [] => 1
  | m :: ms => (Finset.Nat.antidiagonalTuple s m).card * iterCount (s + m) ms

/-- Value of a letter at the matrix `G` with `m` in place of `m_sc`. -/
def evalLetter {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ) (ℓ : Letter N) : ℂ :=
  match ℓ.kind with
  | .g => G ℓ.i ℓ.j
  | .gbar => star (G ℓ.i ℓ.j)
  | .gc => G ℓ.i ℓ.j - if ℓ.i = ℓ.j then m else 0
  | .gcbar => star (G ℓ.i ℓ.j - if ℓ.i = ℓ.j then m else 0)

/-- Value of a word: the product of its letters. -/
def evalWord {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ) (w : Word N) : ℂ :=
  (w.map (evalLetter G m)).prod

/-- Value of an unweighted list of words: the sum of their values. -/
def evalW {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ) (ws : List (Word N)) : ℂ :=
  (ws.map (evalWord G m)).sum

/-- Value of a weighted formal sum. -/
def evalF {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ) (F : FSum N) : ℂ :=
  (F.map fun cw => (cw.1 : ℂ) * evalWord G m cw.2).sum

/-- Swapping two nested `flatMap`s gives a permutation. -/
private lemma monomial_flatMap_comm {α β γ : Type*} (l₁ : List α) (l₂ : List β)
    (f : α → β → List γ) :
    (l₁.flatMap fun a => l₂.flatMap fun b => f a b).Perm
      (l₂.flatMap fun b => l₁.flatMap fun a => f a b) := by
  rw [← Multiset.coe_eq_coe]
  have h1 : ((l₁.flatMap fun a => l₂.flatMap fun b => f a b : List γ) : Multiset γ) =
      Multiset.bind (l₁ : Multiset α) fun a =>
        Multiset.bind (l₂ : Multiset β) fun b => (f a b : Multiset γ) := by
    simp only [Multiset.coe_bind]
  have h2 : ((l₂.flatMap fun b => l₁.flatMap fun a => f a b : List γ) : Multiset γ) =
      Multiset.bind (l₂ : Multiset β) fun b =>
        Multiset.bind (l₁ : Multiset α) fun a => (f a b : Multiset γ) := by
    simp only [Multiset.coe_bind]
  rw [h1, h2]
  exact Multiset.bind_bind _ _

/-- A chain of `a + 1 + b` steps is, up to order, an `a`-step chain from `i` to `x`, the pair
`(x, y)` of the entry `e`, and a `b`-step chain from `y` to `j`. -/
private lemma monomial_starWords_split {N : ℕ} (e : Fin N ⊕ OffDiag N) (κ : LetterKind) (b : ℕ) :
    ∀ (a : ℕ) (i j : Fin N), (starWords e κ (a + 1 + b) i j).Perm
      ((entryPairs e).flatMap fun xy => (starWords e κ a i xy.1).flatMap fun u =>
        (starWords e κ b xy.2 j).map fun v => u ++ v) := by
  intro a
  induction a with
  | zero =>
    intro i j
    rw [show 0 + 1 + b = b + 1 by omega]
    simp [starWords]
  | succ a ih =>
    intro i j
    have e1 : a + 1 + 1 + b = (a + 1 + b) + 1 := by omega
    rw [e1]
    set F : Fin N × Fin N → Fin N × Fin N → List (Word N) := fun p q =>
      (starWords e κ a p.2 q.1).flatMap fun u =>
        (starWords e κ b q.2 j).map fun v => (⟨κ, i, p.1⟩ : Letter N) :: (u ++ v) with hF
    have h1 : (starWords e κ (a + 1 + b + 1) i j).Perm
        ((entryPairs e).flatMap fun p => (entryPairs e).flatMap fun q => F p q) := by
      simp only [starWords]
      refine List.Perm.trans (List.Perm.flatMap_left _ fun p _ => (List.Perm.map _ (ih p.2 j))) ?_
      simp only [List.map_flatMap, List.map_map, Function.comp_def, hF]
      exact List.Perm.refl _
    have h2 : ((entryPairs e).flatMap fun q => (entryPairs e).flatMap fun p => F p q) =
        (entryPairs e).flatMap fun xy => (starWords e κ (a + 1) i xy.1).flatMap fun u =>
          (starWords e κ b xy.2 j).map fun v => u ++ v := by
      simp only [starWords, List.flatMap_assoc, List.flatMap_map, List.cons_append, hF]
    rw [← h2]
    exact h1.trans (monomial_flatMap_comm _ _ _)

/-- On a letter of uncentred kind, `P_{γ,k}` is the chain of `k` steps. -/
private lemma monomial_letterP_plain {N : ℕ} (e : Fin N ⊕ OffDiag N) (κ : LetterKind)
    (hκ : κ.plain = κ) (k : ℕ) (i j : Fin N) :
    letterP e k ⟨κ, i, j⟩ = starWords e κ k i j := by
  by_cases hk : k = 0
  · subst hk
    simp [letterP, starWords]
  · simp [letterP, hk, hκ]

/-- Expanding the `m + 1` letters of the chains of `m` steps by `k` gives the chains of `m + |k|`
steps, up to order. -/
private lemma monomial_starWords_wordP {N : ℕ} (e : Fin N ⊕ OffDiag N) (κ : LetterKind)
    (hκ : κ.plain = κ) :
    ∀ (m : ℕ) (i j : Fin N) (k : List ℕ), k.length = m + 1 →
      ((starWords e κ m i j).flatMap (wordP e k)).Perm (starWords e κ (m + k.sum) i j) := by
  intro m
  induction m with
  | zero =>
    intro i j k hk
    obtain ⟨k0, rfl⟩ : ∃ k0, k = [k0] := by
      match k, hk with
      | [k0], _ => exact ⟨k0, rfl⟩
    simp [starWords, wordP, monomial_letterP_plain e κ hκ]
  | succ m ih =>
    intro i j k hk
    obtain ⟨k0, k', rfl⟩ : ∃ k0 k', k = k0 :: k' := by
      match k, hk with
      | k0 :: k', _ => exact ⟨k0, k', rfl⟩
    have hk' : k'.length = m + 1 := by simpa using hk
    have h1 : ((starWords e κ (m + 1) i j).flatMap (wordP e (k0 :: k'))).Perm
        ((entryPairs e).flatMap fun xy => (starWords e κ k0 i xy.1).flatMap fun u =>
          (starWords e κ (m + k'.sum) xy.2 j).map fun v => u ++ v) := by
      simp only [starWords, List.flatMap_assoc, List.flatMap_map, wordP,
        monomial_letterP_plain e κ hκ]
      refine List.Perm.flatMap_left _ fun xy _ => ?_
      refine (monomial_flatMap_comm (starWords e κ m xy.2 j) (starWords e κ k0 i xy.1)
        (fun w u => (wordP e k' w).map fun v => u ++ v)).trans ?_
      refine List.Perm.flatMap_left _ fun u _ => ?_
      have := (ih xy.2 j k' hk').map fun v => u ++ v
      simpa [List.map_flatMap] using this
    refine h1.trans ?_
    rw [List.sum_cons, show m + 1 + (k0 + k'.sum) = k0 + 1 + (m + k'.sum) by omega]
    exact (monomial_starWords_split e κ (m + k'.sum) k0 i j).symm

/-- (6.19): `P_{γ,k} (P_{γ,m} G_ij) = P_{γ,m+|k|} G_ij` as formal sums
(equality up to the order of the terms), for `k ∈ ℕ^{m+1}`. -/
theorem flatMap_wordP_letterP_perm {N : ℕ} (e : Fin N ⊕ OffDiag N) (m : ℕ) (k : List ℕ)
    (hk : k.length = m + 1) (ℓ : Letter N) :
    ((letterP e m ℓ).flatMap (wordP e k)).Perm (letterP e (m + k.sum) ℓ) := by
  by_cases hm : m = 0
  · subst hm
    obtain ⟨k0, rfl⟩ : ∃ k0, k = [k0] := by
      match k, hk with
      | [k0], _ => exact ⟨k0, rfl⟩
    have h0 : letterP e 0 ℓ = [[ℓ]] := by simp [letterP]
    rw [h0]
    simp [wordP]
  · have hκ : ℓ.kind.plain.plain = ℓ.kind.plain := by cases ℓ.kind <;> rfl
    have h1 : letterP e m ℓ = starWords e ℓ.kind.plain m ℓ.i ℓ.j := by simp [letterP, hm]
    have h2 : letterP e (m + k.sum) ℓ = starWords e ℓ.kind.plain (m + k.sum) ℓ.i ℓ.j := by
      have : m + k.sum ≠ 0 := by omega
      simp only [letterP, this, ↓reduceIte]
    rw [h1, h2]
    exact monomial_starWords_wordP e _ hκ m _ _ k hk

/-- The entry `e` has at most two ordered pairs. -/
private lemma monomial_entryPairs_length_le {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    (entryPairs e).length ≤ 2 := by
  cases e <;> simp [entryPairs]

/-- There are at most `2^n` chains of `n` steps. -/
private lemma monomial_starWords_length_le {N : ℕ} (e : Fin N ⊕ OffDiag N) (κ : LetterKind) :
    ∀ (n : ℕ) (i j : Fin N), (starWords e κ n i j).length ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => intro i j; simp [starWords]
  | succ n ih =>
    intro i j
    simp only [starWords, List.length_flatMap, List.length_map]
    have h := List.sum_le_length_nsmul
      ((entryPairs e).map fun xy => (starWords e κ n xy.2 j).length) (2 ^ n) (by
        intro x hx
        obtain ⟨xy, -, rfl⟩ := List.mem_map.1 hx
        exact ih _ _)
    rw [List.length_map, smul_eq_mul] at h
    calc _ ≤ _ := h
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_right _ (monomial_entryPairs_length_le e)
      _ = 2 ^ (n + 1) := by ring

/-- A chain of `n` steps has `n + 1` letters, all of kind `κ`. -/
private lemma monomial_starWords_mem {N : ℕ} (e : Fin N ⊕ OffDiag N) (κ : LetterKind) :
    ∀ (n : ℕ) (i j : Fin N), ∀ w ∈ starWords e κ n i j,
      w.length = n + 1 ∧ ∀ ℓ ∈ w, ℓ.kind = κ := by
  intro n
  induction n with
  | zero =>
    intro i j w hw
    simp only [starWords, List.mem_singleton] at hw
    subst hw
    simp
  | succ n ih =>
    intro i j w hw
    simp only [starWords, List.mem_flatMap, List.mem_map] at hw
    obtain ⟨xy, -, w', hw', rfl⟩ := hw
    obtain ⟨h1, h2⟩ := ih xy.2 j w' hw'
    refine ⟨by simp [h1], ?_⟩
    intro ℓ hℓ
    rcases List.mem_cons.1 hℓ with rfl | hℓ
    · rfl
    · exact h2 ℓ hℓ

/-- Each word of `P_{γ,k} G_ij` has `k + 1` letters, and there are at most `2^k` of them. -/
theorem letterP_length_le {N : ℕ} (e : Fin N ⊕ OffDiag N) (k : ℕ) (ℓ : Letter N) :
    (letterP e k ℓ).length ≤ 2 ^ k ∧ ∀ w ∈ letterP e k ℓ, w.length = k + 1 := by
  by_cases hk : k = 0
  · subst hk
    simp [letterP]
  · simp only [letterP, hk, ↓reduceIte]
    exact ⟨monomial_starWords_length_le e _ k _ _,
      fun w hw => (monomial_starWords_mem e _ k _ _ w hw).1⟩

/-- The geometric sum `∑_{i ≤ n} k^(n-i)` is at most `(k+1)^n`. -/
private lemma monomial_geom_le (k n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), k ^ (n - i) ≤ (k + 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have h1 : ∑ i ∈ Finset.range (n + 1), k ^ (n + 1 - (i + 1)) =
        ∑ i ∈ Finset.range (n + 1), k ^ (n - i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.add_sub_add_right]
    rw [h1]
    have h2 : k ^ (n + 1 - 0) ≤ k * (k + 1) ^ n := by
      rw [Nat.sub_zero, pow_succ, mul_comm]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ k) n)
    calc _ ≤ (k + 1) ^ n + k * (k + 1) ^ n := Nat.add_le_add ih h2
      _ = (k + 1) ^ (n + 1) := by ring

/-- The list of `k`-tuples of natural numbers with sum `n` has at most `k^n` entries. -/
private lemma monomial_length_antidiagonalTuple_le (k : ℕ) :
    ∀ n, (List.Nat.antidiagonalTuple k n).length ≤ k ^ n := by
  induction k with
  | zero => intro n; cases n <;> simp
  | succ k ih =>
    intro n
    have h : (List.Nat.antidiagonalTuple (k + 1) n).length =
        ∑ i ∈ Finset.range (n + 1), (List.Nat.antidiagonalTuple k (n - i)).length := by
      simp only [List.Nat.antidiagonalTuple, List.length_flatMap, List.length_map,
        List.Nat.antidiagonal, List.map_map, Function.comp_def]
      rfl
    rw [h]
    calc _ ≤ ∑ i ∈ Finset.range (n + 1), k ^ (n - i) := Finset.sum_le_sum fun i _ => ih _
      _ ≤ _ := monomial_geom_le k n

/-- (6.54): `|I^a_{b,c}| ≤ |{k ∈ ℕ^a : |k| = c}| ≤ a^c`. -/
theorem card_antidiagonalTuple_le (a c : ℕ) :
    (Finset.Nat.antidiagonalTuple a c).card ≤ a ^ c := by
  exact monomial_length_antidiagonalTuple_le a c

/-- (6.75) in the word form: at most `(s + k)^k ≤ s^k (k+1)^k` index sequences
with `|k_1| + ⋯ + |k_n| = k`. -/
theorem iterCount_le (s : ℕ) (ms : List ℕ) : iterCount s ms ≤ (s + ms.sum) ^ ms.sum := by
  induction ms generalizing s with
  | nil => simp [iterCount]
  | cons m ms ih =>
    simp only [iterCount, List.sum_cons]
    have h1 := card_antidiagonalTuple_le s m
    have h2 := ih (s + m)
    rw [add_assoc] at h2
    have h3 : s ^ m ≤ (s + (m + ms.sum)) ^ m :=
      Nat.pow_le_pow_left (by omega) m
    calc _ ≤ (s + (m + ms.sum)) ^ m * (s + (m + ms.sum)) ^ ms.sum :=
          Nat.mul_le_mul (h1.trans h3) h2
      _ = _ := by rw [← pow_add]

/-- The value of a concatenation is the product of the values. -/
lemma evalWord_append {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ)
    (u v : Word N) : evalWord G m (u ++ v) = evalWord G m u * evalWord G m v := by
  simp [evalWord]

/-- The value of a `flatMap` is the sum of the values over the index list. -/
lemma evalW_flatMap {N : ℕ} {α : Type*} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ)
    (l : List α) (f : α → List (Word N)) :
    evalW G m (l.flatMap f) = (l.map fun a => evalW G m (f a)).sum := by
  induction l with
  | nil => simp [evalW]
  | cons a t ih =>
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← ih]
    simp [evalW]

/-- The value of `P_{γ,(k, ks)}` on a word `ℓ :: w` factorises over the first letter (6.14). -/
lemma evalW_wordP_cons {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ)
    (e : Fin N ⊕ OffDiag N) (k : ℕ) (ks : List ℕ) (ℓ : Letter N) (w : Word N) :
    evalW G m (wordP e (k :: ks) (ℓ :: w)) =
      evalW G m (letterP e k ℓ) * evalW G m (wordP e ks w) := by
  simp only [wordP]
  rw [evalW_flatMap]
  have h : ∀ u : Word N, evalW G m ((wordP e ks w).map fun v => u ++ v) =
      evalWord G m u * evalW G m (wordP e ks w) := by
    intro u
    simp only [evalW, List.map_map, Function.comp_def, evalWord_append]
    rw [List.sum_map_mul_left]
  simp only [h]
  have h2 : evalW G m (letterP e k ℓ) = ((letterP e k ℓ).map (evalWord G m)).sum := rfl
  rw [h2, ← List.sum_map_mul_right]

/-- A sum of `n` terms of norm at most `c` has norm at most `n c`. -/
lemma norm_list_sum_le_length_mul {ι : Type*} (l : List ι) (f : ι → ℂ) (c : ℝ)
    (h : ∀ x ∈ l, ‖f x‖ ≤ c) : ‖(l.map f).sum‖ ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons]
    calc ‖f a + (t.map f).sum‖ ≤ ‖f a‖ + ‖(t.map f).sum‖ := norm_add_le _ _
      _ ≤ c + t.length * c :=
        add_le_add (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))
      _ = ((t.length + 1 : ℕ) : ℝ) * c := by push_cast; ring

/-- A letter has modulus at most `3` when `|G_ij| ≤ 2` and `|m| ≤ 1`. -/
private lemma monomial_norm_evalLetter_le {N : ℕ} {G : Matrix (Fin N) (Fin N) ℂ} {m : ℂ}
    (hG : ∀ i j, ‖G i j‖ ≤ 2) (hm : ‖m‖ ≤ 1) (ℓ : Letter N) :
    ‖evalLetter G m ℓ‖ ≤ 3 := by
  have hc : ‖G ℓ.i ℓ.j - if ℓ.i = ℓ.j then m else 0‖ ≤ 3 := by
    refine (norm_sub_le _ _).trans ?_
    have := hG ℓ.i ℓ.j
    split_ifs <;> simp <;> linarith
  rcases ℓ with ⟨κ, i, j⟩
  cases κ <;> simp only [evalLetter, norm_star]
  · linarith [hG i j]
  · linarith [hG i j]
  · exact hc
  · exact hc

/-- An uncentred letter has modulus at most `2` when `|G_ij| ≤ 2`. -/
private lemma monomial_norm_evalLetter_plain_le {N : ℕ} {G : Matrix (Fin N) (Fin N) ℂ} {m : ℂ}
    (hG : ∀ i j, ‖G i j‖ ≤ 2) (ℓ : Letter N) (hℓ : ℓ.kind.plain = ℓ.kind) :
    ‖evalLetter G m ℓ‖ ≤ 2 := by
  rcases ℓ with ⟨κ, i, j⟩
  cases κ <;> simp only [LetterKind.plain, reduceCtorEq] at hℓ <;>
    simp only [evalLetter, norm_star] <;> exact hG i j

/-- A word of uncentred letters has modulus at most `2^(length)` when `|G_ij| ≤ 2`. -/
private lemma monomial_norm_evalWord_le {N : ℕ} {G : Matrix (Fin N) (Fin N) ℂ} {m : ℂ}
    (hG : ∀ i j, ‖G i j‖ ≤ 2) :
    ∀ w : Word N, (∀ ℓ ∈ w, ℓ.kind.plain = ℓ.kind) → ‖evalWord G m w‖ ≤ 2 ^ w.length := by
  intro w
  induction w with
  | nil => intro _; simp [evalWord]
  | cons ℓ t ih =>
    intro h
    have h1 := monomial_norm_evalLetter_plain_le (m := m) hG ℓ (h ℓ List.mem_cons_self)
    have h2 := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have : evalWord G m (ℓ :: t) = evalLetter G m ℓ * evalWord G m t := by simp [evalWord]
    rw [this, norm_mul, List.length_cons, pow_succ']
    exact mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)

/-- The value of `P_{γ,k}` on a letter has modulus at most `3 · 4^k`. -/
private lemma monomial_norm_evalW_letterP_le {N : ℕ} {G : Matrix (Fin N) (Fin N) ℂ} {m : ℂ}
    (hG : ∀ i j, ‖G i j‖ ≤ 2) (hm : ‖m‖ ≤ 1) (e : Fin N ⊕ OffDiag N) (k : ℕ) (ℓ : Letter N) :
    ‖evalW G m (letterP e k ℓ)‖ ≤ 3 * 4 ^ k := by
  by_cases hk : k = 0
  · subst hk
    have h0 : letterP e 0 ℓ = [[ℓ]] := by simp [letterP]
    rw [h0]
    simpa [evalW, evalWord] using monomial_norm_evalLetter_le hG hm ℓ
  · have hL : letterP e k ℓ = starWords e ℓ.kind.plain k ℓ.i ℓ.j := by simp [letterP, hk]
    have hmem := monomial_starWords_mem e ℓ.kind.plain k ℓ.i ℓ.j
    have hlen := monomial_starWords_length_le e ℓ.kind.plain k ℓ.i ℓ.j
    rw [hL]
    have hb : ∀ w ∈ starWords e ℓ.kind.plain k ℓ.i ℓ.j, ‖evalWord G m w‖ ≤ 2 ^ (k + 1) := by
      intro w hw
      obtain ⟨h1, h2⟩ := hmem w hw
      have := monomial_norm_evalWord_le (m := m) hG w
        (fun x hx => by rw [h2 x hx]; cases ℓ.kind <;> rfl)
      rwa [h1] at this
    have hs := norm_list_sum_le_length_mul _ (evalWord G m) _ hb
    have h4 : (4 : ℝ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
    have hp : (0 : ℝ) < 4 ^ k := by positivity
    calc ‖evalW G m (starWords e ℓ.kind.plain k ℓ.i ℓ.j)‖
        ≤ _ := hs
      _ ≤ 2 ^ k * 2 ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) (by positivity)
      _ = 2 * 4 ^ k := by rw [h4]; ring
      _ ≤ 3 * 4 ^ k := by linarith

/-- The value of `P_{γ,k}` on a word of length `s` has modulus at most `3^s 4^|k|`. -/
private lemma monomial_norm_evalW_wordP_aux {N : ℕ} {G : Matrix (Fin N) (Fin N) ℂ} {m : ℂ}
    (hG : ∀ i j, ‖G i j‖ ≤ 2) (hm : ‖m‖ ≤ 1) (e : Fin N ⊕ OffDiag N) :
    ∀ (w : Word N) (k : List ℕ), k.length = w.length →
      ‖evalW G m (wordP e k w)‖ ≤ 3 ^ w.length * 4 ^ k.sum := by
  intro w
  induction w with
  | nil =>
    intro k _
    have h1 : (1 : ℝ) ≤ 4 ^ k.sum := one_le_pow₀ (by norm_num)
    simpa [wordP, evalW, evalWord] using h1
  | cons ℓ t ih =>
    intro k hk
    obtain ⟨k0, ks, rfl⟩ : ∃ k0 ks, k = k0 :: ks := by
      match k, hk with
      | k0 :: ks, _ => exact ⟨k0, ks, rfl⟩
    rw [evalW_wordP_cons, norm_mul]
    have h1 := monomial_norm_evalW_letterP_le hG hm e k0 ℓ
    have h2 := ih ks (by simpa using hk)
    calc _ ≤ (3 * 4 ^ k0) * (3 ^ t.length * 4 ^ ks.sum) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = 3 ^ (ℓ :: t).length * 4 ^ (k0 :: ks).sum := by
          rw [List.length_cons, List.sum_cons, pow_succ, pow_add]; ring

/-- Lemma 6.4 (6.20), deterministic part: if `|G_ij| ≤ 2` and `|m| ≤ 1`, then every
`P_{γ,k}` (and `P̃_{γ,k}`) image of a word of length `s` is at most `4^{s + |k| + 1}`. -/
theorem norm_evalW_wordP_le {N : ℕ} {G : Matrix (Fin N) (Fin N) ℂ} {m : ℂ}
    (hG : ∀ i j, ‖G i j‖ ≤ 2) (hm : ‖m‖ ≤ 1) (e : Fin N ⊕ OffDiag N) (k : List ℕ)
    (w : Word N) (hk : k.length = w.length) :
    ‖evalW G m (wordP e k w)‖ ≤ 4 ^ (w.length + k.sum + 1) := by
  refine (monomial_norm_evalW_wordP_aux hG hm e w k hk).trans ?_
  calc (3 : ℝ) ^ w.length * 4 ^ k.sum ≤ 4 ^ w.length * 4 ^ k.sum := by
        gcongr; norm_num
    _ = 4 ^ (w.length + k.sum) := by rw [pow_add]
    _ ≤ 4 ^ (w.length + k.sum + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)

/-! ### Formal monomials at `γ = (1, 2)` on `Fin 4`

Paper indices `1, …, 4` are the `Fin 4` indices `0, …, 3`. -/

/-- The upper entry `(1, 2)` of a `4 × 4` matrix (`Fin 4` indices `0, 1`). -/
private def e12 : Fin 4 ⊕ OffDiag 4 := Sum.inr ⟨(0, 1), by decide⟩

/-- `P_{γ,1} G_34 = G_31 G_24 + G_32 G_14`. -/
example : letterP e12 1 ⟨.g, 2, 3⟩ = [[⟨.g, 2, 0⟩, ⟨.g, 1, 3⟩], [⟨.g, 2, 1⟩, ⟨.g, 0, 3⟩]] := by
  decide

/-- `P_{γ,2} G_34 = G_31 G_21 G_24 + G_31 G_22 G_14 + G_32 G_11 G_24 + G_32 G_12 G_14`. -/
example : letterP e12 2 ⟨.g, 2, 3⟩ =
    [[⟨.g, 2, 0⟩, ⟨.g, 1, 0⟩, ⟨.g, 1, 3⟩], [⟨.g, 2, 0⟩, ⟨.g, 1, 1⟩, ⟨.g, 0, 3⟩],
     [⟨.g, 2, 1⟩, ⟨.g, 0, 0⟩, ⟨.g, 1, 3⟩], [⟨.g, 2, 1⟩, ⟨.g, 0, 1⟩, ⟨.g, 0, 3⟩]] := by
  decide

/-- (6.19) at `m = 1`: `P_{γ,(1,0)} (P_{γ,1} G_34) = P_{γ,(0,1)} (P_{γ,1} G_34) = P_{γ,2} G_34`. -/
example : ((letterP e12 1 ⟨.g, 2, 3⟩).flatMap (wordP e12 [1, 0])).Perm (letterP e12 2 ⟨.g, 2, 3⟩) ∧
    ((letterP e12 1 ⟨.g, 2, 3⟩).flatMap (wordP e12 [0, 1])).Perm (letterP e12 2 ⟨.g, 2, 3⟩) := by
  decide

/-- (6.19) at `m = 2`, `k = (1, 0, 2)`; for a centred letter with `k = (0, 2, 1)`; for a conjugate
letter at the diagonal entry `(4, 4)` with `k = (2, 0, 1)`; at `m = 0` for a centred letter. -/
example : ((letterP e12 2 ⟨.g, 2, 3⟩).flatMap (wordP e12 [1, 0, 2])).Perm
      (letterP e12 5 ⟨.g, 2, 3⟩) ∧
    ((letterP e12 2 ⟨.gc, 2, 2⟩).flatMap (wordP e12 [0, 2, 1])).Perm
      (letterP e12 5 ⟨.gc, 2, 2⟩) ∧
    ((letterP (Sum.inl 3 : Fin 4 ⊕ OffDiag 4) 2 ⟨.gbar, 1, 2⟩).flatMap
      (wordP (Sum.inl 3) [2, 0, 1])).Perm (letterP (Sum.inl 3) 5 ⟨.gbar, 1, 2⟩) ∧
    ((letterP e12 0 ⟨.gc, 2, 2⟩).flatMap (wordP e12 [3])).Perm (letterP e12 3 ⟨.gc, 2, 2⟩) := by
  decide

/-- (6.17): `P̃_{γ,0}(G_33 - m_sc) = G_33 - m_sc` and
`P̃_{γ,1}(G_33 - m_sc) = G_31 G_23 + G_32 G_13`. -/
example : letterP e12 0 ⟨.gc, 2, 2⟩ = [[⟨.gc, 2, 2⟩]] ∧
    letterP e12 1 ⟨.gc, 2, 2⟩ = [[⟨.g, 2, 0⟩, ⟨.g, 1, 2⟩], [⟨.g, 2, 1⟩, ⟨.g, 0, 2⟩]] := by
  decide

/-- A diagonal entry `γ = (2, 2)`: a single chain, `P_{γ,2} G_34 = G_32 G_22 G_24`. -/
example : letterP (Sum.inl 1 : Fin 4 ⊕ OffDiag 4) 2 ⟨.g, 2, 3⟩ =
    [[⟨.g, 2, 1⟩, ⟨.g, 1, 1⟩, ⟨.g, 1, 3⟩]] := by
  decide

/-- Conjugate letters stay conjugate:
`P_{γ,1} conj G_34 = conj G_31 conj G_24 + conj G_32 conj G_14`. -/
example : letterP e12 1 ⟨.gbar, 2, 3⟩ =
    [[⟨.gbar, 2, 0⟩, ⟨.gbar, 1, 3⟩], [⟨.gbar, 2, 1⟩, ⟨.gbar, 0, 3⟩]] := by
  decide

/-- The word `G_34 conj G_34` under `P_{γ,(1,1)}`: four products of four letters. -/
example : (wordP e12 [1, 1] [⟨.g, 2, 3⟩, ⟨.gbar, 2, 3⟩]).length = 4 ∧
    ∀ w ∈ wordP e12 [1, 1] [⟨.g, 2, 3⟩, ⟨.gbar, 2, 3⟩], w.length = 4 := by
  decide

/-- (6.54) and (6.75) at small values: `|I^3_{·,2}| = 6 ≤ 3^2` and
`iterCount 2 [1, 2] = 2 · 6 ≤ 5^3`. -/
example : (Finset.Nat.antidiagonalTuple 3 2).card = 6 ∧ iterCount 2 [1, 2] = 12 := by
  decide

/-- Lemma 6.4 hypotheses at a nondegenerate point: `G = I + E_12` (all entries of modulus `≤ 2`),
`m = 1/2`. -/
example : (∀ i j : Fin 4,
      ‖((1 : Matrix (Fin 4) (Fin 4) ℂ) + Matrix.single (0 : Fin 4) (1 : Fin 4) (1 : ℂ)) i j‖ ≤ 2) ∧
    ‖(1 / 2 : ℂ)‖ ≤ 1 := by
  refine ⟨fun i j => ?_, by norm_num⟩
  rw [Matrix.add_apply]
  have h1 : ‖(1 : Matrix (Fin 4) (Fin 4) ℂ) i j‖ ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  have h2 : ‖Matrix.single (0 : Fin 4) (1 : Fin 4) (1 : ℂ) i j‖ ≤ 1 := by
    rw [Matrix.single_apply]; split_ifs <;> simp
  linarith [norm_add_le ((1 : Matrix (Fin 4) (Fin 4) ℂ) i j)
    (Matrix.single (0 : Fin 4) (1 : Fin 4) (1 : ℂ) i j)]

/-- The five targets applied at the data above: (6.19) at `m = 1`, `k = (1, 0)`; the length
bound for `P_{γ,2} G_34`; (6.54) and (6.75) at `(3, 2)` and `(2, [1, 2])`; and Lemma 6.4 for the
word `G_12` under `P_{γ,(1)}` with `G = I + E_12`, `m = 1/2`. -/
example :
    ((letterP e12 1 ⟨.g, 2, 3⟩).flatMap (wordP e12 [1, 0])).Perm
      (letterP e12 (1 + [1, 0].sum) ⟨.g, 2, 3⟩) ∧
    (letterP e12 2 ⟨.g, 2, 3⟩).length ≤ 2 ^ 2 ∧
    (Finset.Nat.antidiagonalTuple 3 2).card ≤ 3 ^ 2 ∧
    iterCount 2 [1, 2] ≤ (2 + [1, 2].sum) ^ [1, 2].sum ∧
    ‖evalW ((1 : Matrix (Fin 4) (Fin 4) ℂ) + Matrix.single (0 : Fin 4) (1 : Fin 4) (1 : ℂ))
        (1 / 2) (wordP e12 [1] [⟨.g, 0, 1⟩])‖ ≤
      4 ^ ([(⟨.g, 0, 1⟩ : Letter 4)].length + [1].sum + 1) := by
  refine ⟨flatMap_wordP_letterP_perm e12 1 [1, 0] rfl _, (letterP_length_le e12 2 _).1,
    card_antidiagonalTuple_le 3 2, iterCount_le 2 [1, 2], ?_⟩
  refine norm_evalW_wordP_le (fun i j => ?_) (by norm_num) e12 [1] _ rfl
  rw [Matrix.add_apply]
  have h1 : ‖(1 : Matrix (Fin 4) (Fin 4) ℂ) i j‖ ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  have h2 : ‖Matrix.single (0 : Fin 4) (1 : Fin 4) (1 : ℂ) i j‖ ≤ 1 := by
    rw [Matrix.single_apply]; split_ifs <;> simp
  linarith [norm_add_le ((1 : Matrix (Fin 4) (Fin 4) ℂ) i j)
    (Matrix.single (0 : Fin 4) (1 : Fin 4) (1 : ℂ) i j)]

/-- The sum bound `‖∑ f‖ ≤ n c` for two terms of norm `1`. -/
example : ‖(([(1 : ℂ), 1]).map id).sum‖ ≤ ([(1 : ℂ), 1].length : ℝ) * 1 :=
  norm_list_sum_le_length_mul _ id 1 (by simp)

#print axioms flatMap_wordP_letterP_perm
#print axioms letterP_length_le
#print axioms card_antidiagonalTuple_le
#print axioms iterCount_le
#print axioms norm_evalW_wordP_le

end WEdgeNS
