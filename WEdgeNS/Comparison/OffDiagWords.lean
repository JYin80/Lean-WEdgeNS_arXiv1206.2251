import WEdgeNS.Comparison.Iterate

/-!
# Words of the iterates of an off-diagonal pair
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

open private monomial_starWords_mem from WEdgeNS.Comparison.Monomial
open private iterate_iterP_props iterate_ord_le iterate_ord from WEdgeNS.Comparison.Iterate
open private expansion_norm_integral_le from WEdgeNS.Comparison.Expansion

/-- The entry `e` meets `{i, j}`. -/
def touchesEntry {N : ℕ} (i j : Fin N) (e : Fin N ⊕ OffDiag N) : Bool :=
  (entryPairs e).any fun xy => decide (xy.1 = i) || decide (xy.1 = j)

/-- Some entry of the data `d` meets `{i, j}`. -/
def touchesData {N : ℕ} (i j : Fin N) (d : List ((Fin N ⊕ OffDiag N) × List ℕ)) : Bool :=
  d.any fun x => touchesEntry i j x.1

/-! ### Uncentred letters along `P_d` -/

/-- The uncentred kind is idempotent. -/
private lemma offDiagWords_plain_plain (κ : LetterKind) : κ.plain.plain = κ.plain := by
  cases κ <;> rfl

/-- `P_{γ,k}` on an uncentred letter gives uncentred letters. -/
private lemma offDiagWords_letterP_plain {N : ℕ} (e : Fin N ⊕ OffDiag N) (k : ℕ) (ℓ : Letter N)
    (hℓ : ℓ.kind.plain = ℓ.kind) : ∀ v ∈ letterP e k ℓ, ∀ x ∈ v, x.kind.plain = x.kind := by
  intro v hv x hx
  by_cases hk : k = 0
  · subst hk
    simp only [letterP, ite_true, List.mem_singleton] at hv
    subst hv
    rw [List.mem_singleton.1 hx]; exact hℓ
  · simp only [letterP, hk, ite_false] at hv
    rw [(monomial_starWords_mem e ℓ.kind.plain k ℓ.i ℓ.j v hv).2 x hx]
    exact offDiagWords_plain_plain _

/-- `P_{γ,k}` on a word of uncentred letters gives words of uncentred letters. -/
private lemma offDiagWords_wordP_plain {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    ∀ (w : Word N) (k : List ℕ), (∀ x ∈ w, x.kind.plain = x.kind) →
      ∀ u ∈ wordP e k w, ∀ x ∈ u, x.kind.plain = x.kind := by
  intro w
  induction w with
  | nil =>
    intro k _ u hu
    simp only [wordP, List.mem_singleton] at hu
    subst hu
    simp
  | cons ℓ w ih =>
    intro k h u hu x hx
    have hℓ : ℓ.kind.plain = ℓ.kind := h _ List.mem_cons_self
    have hw : ∀ y ∈ w, y.kind.plain = y.kind := fun y hy => h y (List.mem_cons_of_mem _ hy)
    rcases k with _ | ⟨k0, ks⟩
    · simp only [wordP, List.mem_map] at hu
      obtain ⟨u', hu', rfl⟩ := hu
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hℓ
      · exact ih [] hw u' hu' x hx
    · simp only [wordP, List.mem_flatMap, List.mem_map] at hu
      obtain ⟨v, hv, u', hu', rfl⟩ := hu
      rcases List.mem_append.1 hx with hx | hx
      · exact offDiagWords_letterP_plain e k0 ℓ hℓ v hv x hx
      · exact ih ks hw u' hu' x hx

/-- `P_d` on a formal sum of words of uncentred letters gives such words. -/
private lemma offDiagWords_iterP_plain {N : ℕ} :
    ∀ (d : List ((Fin N ⊕ OffDiag N) × List ℕ)) (F : FSum N),
      (∀ cw ∈ F, ∀ x ∈ cw.2, x.kind.plain = x.kind) →
        ∀ cw ∈ iterP d F, ∀ x ∈ cw.2, x.kind.plain = x.kind := by
  intro d
  induction d with
  | nil => intro F hF; simpa [iterP] using hF
  | cons y d ih =>
    intro F hF
    refine ih (opP y.1 y.2 F) ?_
    intro cw hcw
    simp only [opP, List.mem_flatMap, List.mem_map] at hcw
    obtain ⟨cw0, hcw0, u, hu, rfl⟩ := hcw
    exact offDiagWords_wordP_plain y.1 cw0.2 y.2 (hF cw0 hcw0) u hu

/-! ### Row and column counts along `P_d` -/

/-- Both coordinates of every pair of an entry avoiding `{i, j}` differ from `i`. -/
private lemma offDiagWords_pairs_ne {N : ℕ} {i j : Fin N} {e : Fin N ⊕ OffDiag N}
    (he : touchesEntry i j e = false) : ∀ xy ∈ entryPairs e, xy.1 ≠ i ∧ xy.2 ≠ i := by
  have h1 : ∀ xy ∈ entryPairs e, xy.1 ≠ i := by
    intro xy hxy
    have := he
    simp only [touchesEntry, List.any_eq_false, Bool.or_eq_true, decide_eq_true_eq,
      not_or] at this
    exact (this xy hxy).1
  have h2 : ∀ xy ∈ entryPairs e, ∃ xy' ∈ entryPairs e, xy'.1 = xy.2 := by
    intro xy hxy
    rcases e with a | p
    · simp only [entryPairs, List.mem_singleton] at hxy
      exact ⟨xy, by simp [entryPairs, hxy], by simp [hxy]⟩
    · simp only [entryPairs, List.mem_cons, List.not_mem_nil, or_false] at hxy
      rcases hxy with rfl | rfl
      · exact ⟨(p.1.2, p.1.1), by simp [entryPairs], rfl⟩
      · exact ⟨(p.1.1, p.1.2), by simp [entryPairs], rfl⟩
  intro xy hxy
  refine ⟨h1 xy hxy, ?_⟩
  obtain ⟨xy', h', he'⟩ := h2 xy hxy
  rw [← he']
  exact h1 xy' h'

/-- A chain of `k + 1` letters from `a` to `b` through pairs of an entry whose coordinates differ
from `i`: its row-`i` count is `[a = i]`, its column-`i` count is `[b = i]`. -/
private lemma offDiagWords_starWords_count {N : ℕ} {i : Fin N} {e : Fin N ⊕ OffDiag N}
    (hp : ∀ xy ∈ entryPairs e, xy.1 ≠ i ∧ xy.2 ≠ i) (κ : LetterKind) :
    ∀ (k : ℕ) (a b : Fin N), ∀ w ∈ starWords e κ k a b,
      w.countP (fun x => decide (x.i = i)) = (if a = i then 1 else 0) ∧
        w.countP (fun x => decide (x.j = i)) = (if b = i then 1 else 0) := by
  intro k
  induction k with
  | zero =>
    intro a b w hw
    simp only [starWords, List.mem_singleton] at hw
    subst hw
    simp [List.countP_cons]
  | succ k ih =>
    intro a b w hw
    simp only [starWords, List.mem_flatMap, List.mem_map] at hw
    obtain ⟨xy, hxy, w', hw', rfl⟩ := hw
    obtain ⟨h2, h3⟩ := ih xy.2 b w' hw'
    obtain ⟨hx1, hx2⟩ := hp xy hxy
    refine ⟨?_, ?_⟩
    · simp [List.countP_cons, h2, hx2]
    · simp [h3, hx1]

/-- `P_{γ,k}` on a letter, for an entry avoiding `i`, keeps the row-`i` and column-`i`
counts. -/
private lemma offDiagWords_letterP_count {N : ℕ} {i : Fin N} {e : Fin N ⊕ OffDiag N}
    (hp : ∀ xy ∈ entryPairs e, xy.1 ≠ i ∧ xy.2 ≠ i) (k : ℕ) (ℓ : Letter N) :
    ∀ v ∈ letterP e k ℓ, v.countP (fun x => decide (x.i = i)) = (if ℓ.i = i then 1 else 0) ∧
      v.countP (fun x => decide (x.j = i)) = (if ℓ.j = i then 1 else 0) := by
  intro v hv
  by_cases hk : k = 0
  · subst hk
    simp only [letterP, ite_true, List.mem_singleton] at hv
    subst hv
    simp [List.countP_cons]
  · simp only [letterP, hk, ite_false] at hv
    exact offDiagWords_starWords_count hp ℓ.kind.plain k ℓ.i ℓ.j v hv

/-- `P_{γ,k}` on a word, for an entry avoiding `i`, keeps the row-`i` and column-`i` counts. -/
private lemma offDiagWords_wordP_count {N : ℕ} {i : Fin N} {e : Fin N ⊕ OffDiag N}
    (hp : ∀ xy ∈ entryPairs e, xy.1 ≠ i ∧ xy.2 ≠ i) :
    ∀ (w : Word N) (k : List ℕ), ∀ u ∈ wordP e k w,
      u.countP (fun x => decide (x.i = i)) = w.countP (fun x => decide (x.i = i)) ∧
        u.countP (fun x => decide (x.j = i)) = w.countP (fun x => decide (x.j = i)) := by
  intro w
  induction w with
  | nil =>
    intro k u hu
    simp only [wordP, List.mem_singleton] at hu
    subst hu
    simp
  | cons ℓ w ih =>
    intro k u hu
    rcases k with _ | ⟨k0, ks⟩
    · simp only [wordP, List.mem_map] at hu
      obtain ⟨u', hu', rfl⟩ := hu
      obtain ⟨h2, h3⟩ := ih [] u' hu'
      refine ⟨?_, ?_⟩
      · simp [List.countP_cons, h2]
      · simp [List.countP_cons, h3]
    · simp only [wordP, List.mem_flatMap, List.mem_map] at hu
      obtain ⟨v, hv, u', hu', rfl⟩ := hu
      obtain ⟨h2, h3⟩ := ih ks u' hu'
      obtain ⟨g2, g3⟩ := offDiagWords_letterP_count hp k0 ℓ v hv
      refine ⟨?_, ?_⟩
      · rw [List.countP_append, g2, h2, List.countP_cons]
        simp [add_comm]
      · rw [List.countP_append, g3, h3, List.countP_cons]
        simp [add_comm]

/-- Two letters with row index `i` and none with column index `i`. -/
private def offDiagWords_Inv {N : ℕ} (i : Fin N) (w : Word N) : Prop :=
  w.countP (fun x => decide (x.i = i)) = 2 ∧ w.countP (fun x => decide (x.j = i)) = 0

/-- `P_d` keeps the counts for data avoiding `{i, j}`. -/
private lemma offDiagWords_iterP_inv {N : ℕ} {i j : Fin N} :
    ∀ (d : List ((Fin N ⊕ OffDiag N) × List ℕ)) (F : FSum N), touchesData i j d = false →
      (∀ cw ∈ F, offDiagWords_Inv i cw.2) → ∀ cw ∈ iterP d F, offDiagWords_Inv i cw.2 := by
  intro d
  induction d with
  | nil => intro F _ hF; simpa [iterP] using hF
  | cons x d ih =>
    intro F hd hF
    simp only [touchesData, List.any_cons, Bool.or_eq_false_iff] at hd
    refine ih (opP x.1 x.2 F) hd.2 ?_
    intro cw hcw
    simp only [opP, List.mem_flatMap, List.mem_map] at hcw
    obtain ⟨cw0, hcw0, u, hu, rfl⟩ := hcw
    obtain ⟨h2, h3⟩ := offDiagWords_wordP_count (offDiagWords_pairs_ne hd.1) cw0.2 x.2 u hu
    obtain ⟨g2, g3⟩ := hF cw0 hcw0
    exact ⟨h2.trans g2, h3.trans g3⟩

/-- A word with two row-`i` letters and no column-`i` letter has two off-diagonal letters. -/
private lemma offDiagWords_two_le {N : ℕ} {i : Fin N} {w : Word N} (h : offDiagWords_Inv i w) :
    2 ≤ (w.filter fun ℓ => ℓ.i ≠ ℓ.j).length := by
  obtain ⟨h2, h3⟩ := h
  rw [← h2, ← List.countP_eq_length_filter]
  refine List.countP_mono_left fun x hx hxi => ?_
  have hj : x.j ≠ i := fun hj => by
    have := (List.countP_eq_zero.1 h3) x hx
    simp [hj] at this
  have hxi' : x.i = i := by simpa using hxi
  simpa [hxi'] using hj.symm

/-- For `i ≠ j` and data whose entries avoid `{i, j}`, every word of
`P_d (G_ij Ḡ_ij)` consists of uncentred letters and has at least two off-diagonal letters. -/
theorem iterP_offDiag_two {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    ∀ d : List ((Fin N ⊕ OffDiag N) × List ℕ), touchesData i j d = false →
      ∀ cw ∈ iterP d [(1, [⟨.g, i, j⟩, ⟨.gbar, i, j⟩])],
        (∀ ℓ ∈ cw.2, ℓ.kind.plain = ℓ.kind) ∧ 2 ≤ (cw.2.filter fun ℓ => ℓ.i ≠ ℓ.j).length := by
  intro d hd cw hcw
  have hp0 : ∀ cw ∈ ([(1, [⟨.g, i, j⟩, ⟨.gbar, i, j⟩])] : FSum N),
      ∀ x ∈ cw.2, x.kind.plain = x.kind := by
    intro cw hcw x hx
    rw [List.mem_singleton] at hcw
    subst hcw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> rfl
  have h0 : ∀ cw ∈ ([(1, [⟨.g, i, j⟩, ⟨.gbar, i, j⟩])] : FSum N), offDiagWords_Inv i cw.2 := by
    intro cw hcw
    rw [List.mem_singleton] at hcw
    subst hcw
    refine ⟨?_, ?_⟩
    · simp
    · simp [hij.symm]
  exact ⟨offDiagWords_iterP_plain d _ hp0 cw hcw,
    offDiagWords_two_le (offDiagWords_iterP_inv d _ hd h0 cw hcw)⟩

/-! ### Bounds on the iterate -/

/-- A formal sum with nonnegative weights and words of value at most `K` has value at most the
total weight times `K`. -/
private lemma offDiagWords_norm_evalF_le {N : ℕ} {G : Matrix (Fin N) (Fin N) ℂ} {m : ℂ} {K : ℝ} :
    ∀ F : FSum N, (∀ cw ∈ F, 0 ≤ cw.1) → (∀ cw ∈ F, ‖evalWord G m cw.2‖ ≤ K) →
      ‖evalF G m F‖ ≤ (F.map Prod.fst).sum * K
  | [], _, _ => by simp [evalF]
  | cw :: F, h0, hK => by
    have ih := offDiagWords_norm_evalF_le (G := G) (m := m) F
      (fun x hx => h0 x (List.mem_cons_of_mem _ hx))
      (fun x hx => hK x (List.mem_cons_of_mem _ hx))
    have hc : evalF G m (cw :: F) = (cw.1 : ℂ) * evalWord G m cw.2 + evalF G m F := by
      simp [evalF]
    have h1 : ‖(cw.1 : ℂ) * evalWord G m cw.2‖ ≤ cw.1 * K := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 cw List.mem_cons_self)]
      exact mul_le_mul_of_nonneg_left (hK cw List.mem_cons_self) (h0 cw List.mem_cons_self)
    rw [hc]
    calc _ ≤ ‖(cw.1 : ℂ) * evalWord G m cw.2‖ + ‖evalF G m F‖ := norm_add_le _ _
      _ ≤ cw.1 * K + (F.map Prod.fst).sum * K := add_le_add h1 ih
      _ = _ := by simp only [List.map_cons, List.sum_cons]; ring

/-- A letter has modulus at most `B + 1` when `|G_xy| ≤ B` and `|m| ≤ 1`. -/
private lemma offDiagWords_norm_evalLetter_le {N : ℕ} {G : Matrix (Fin N) (Fin N) ℂ} {m : ℂ}
    {B : ℝ} (hG : ∀ x y, ‖G x y‖ ≤ B) (hm : ‖m‖ ≤ 1) (ℓ : Letter N) :
    ‖evalLetter G m ℓ‖ ≤ B + 1 := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hG ℓ.i ℓ.j)
  have hc : ‖G ℓ.i ℓ.j - if ℓ.i = ℓ.j then m else 0‖ ≤ B + 1 := by
    refine (norm_sub_le _ _).trans ?_
    have := hG ℓ.i ℓ.j
    split_ifs <;> simp <;> linarith
  rcases ℓ with ⟨κ, x, y⟩
  cases κ <;> simp only [evalLetter, norm_star]
  · linarith [hG x y]
  · linarith [hG x y]
  · exact hc
  · exact hc

/-- A word of length `L` has modulus at most `(B + 1)^L` when `|G_xy| ≤ B` and `|m| ≤ 1`. -/
private lemma offDiagWords_norm_evalWord_le {N : ℕ} {G : Matrix (Fin N) (Fin N) ℂ} {m : ℂ}
    {B : ℝ} (hG : ∀ x y, ‖G x y‖ ≤ B) (hm : ‖m‖ ≤ 1) :
    ∀ w : Word N, ‖evalWord G m w‖ ≤ (B + 1) ^ w.length
  | [] => by simp [evalWord]
  | ℓ :: w => by
    have h1 := offDiagWords_norm_evalLetter_le hG hm ℓ
    have h2 := offDiagWords_norm_evalWord_le hG hm w
    have hc : evalWord G m (ℓ :: w) = evalLetter G m ℓ * evalWord G m w := by simp [evalWord]
    rw [hc, norm_mul, List.length_cons, pow_succ']
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)

/-- The value of an uncentred letter is `G_xy` or its conjugate. -/
private lemma offDiagWords_norm_evalLetter_plain {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ)
    (ℓ : Letter N) (hℓ : ℓ.kind.plain = ℓ.kind) : ‖evalLetter G m ℓ‖ = ‖G ℓ.i ℓ.j‖ := by
  rcases ℓ with ⟨κ, x, y⟩
  cases κ <;> simp only [LetterKind.plain, reduceCtorEq] at hℓ <;>
    simp only [evalLetter, norm_star]

/-- A word of `t + r` uncentred letters, at least `t` of them off-diagonal, has modulus at most
`ε^t 2^r` when `|G_xy| ≤ 2` and `|G_xy| ≤ ε` off the diagonal. -/
private lemma offDiagWords_norm_evalWord_off_le {N : ℕ} {G : Matrix (Fin N) (Fin N) ℂ} {m : ℂ}
    {ε : ℝ} (hε0 : 0 ≤ ε) (hG2 : ∀ x y, ‖G x y‖ ≤ 2) (hoff : ∀ x y, x ≠ y → ‖G x y‖ ≤ ε) :
    ∀ (w : Word N) (t r : ℕ), (∀ x ∈ w, x.kind.plain = x.kind) → w.length = t + r →
      t ≤ (w.filter fun ℓ => ℓ.i ≠ ℓ.j).length → ‖evalWord G m w‖ ≤ ε ^ t * 2 ^ r := by
  intro w
  induction w with
  | nil =>
    intro t r _ hl ht
    have ht0 : t = 0 := by simp at ht; omega
    have hr0 : r = 0 := by simp at hl; omega
    subst ht0; subst hr0
    simp [evalWord]
  | cons ℓ w ih =>
    intro t r hp hl ht
    have hℓ : ℓ.kind.plain = ℓ.kind := hp ℓ List.mem_cons_self
    have hw : ∀ y ∈ w, y.kind.plain = y.kind := fun y hy => hp y (List.mem_cons_of_mem _ hy)
    have hc : evalWord G m (ℓ :: w) = evalLetter G m ℓ * evalWord G m w := by simp [evalWord]
    have hn : ‖evalLetter G m ℓ‖ = ‖G ℓ.i ℓ.j‖ := offDiagWords_norm_evalLetter_plain G m ℓ hℓ
    have hl' : w.length + 1 = t + r := by simpa using hl
    have hfl : (w.filter fun ℓ => ℓ.i ≠ ℓ.j).length ≤ w.length := List.length_filter_le _ _
    rw [hc, norm_mul, hn]
    by_cases hd : ℓ.i = ℓ.j
    · have hf : ((ℓ :: w).filter fun ℓ => ℓ.i ≠ ℓ.j).length =
          (w.filter fun ℓ => ℓ.i ≠ ℓ.j).length := by simp [hd]
      rw [hf] at ht
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      have h2 := ih t r' hw (by omega) ht
      calc _ ≤ 2 * (ε ^ t * 2 ^ r') :=
            mul_le_mul (hG2 _ _) h2 (norm_nonneg _) (by norm_num)
        _ = _ := by ring
    · have hf : ((ℓ :: w).filter fun ℓ => ℓ.i ≠ ℓ.j).length =
          (w.filter fun ℓ => ℓ.i ≠ ℓ.j).length + 1 := by simp [hd]
      rw [hf] at ht
      rcases t with _ | t
      · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        have h2 := ih 0 r' hw (by omega) (Nat.zero_le _)
        calc _ ≤ 2 * (ε ^ 0 * 2 ^ r') :=
              mul_le_mul (hG2 _ _) h2 (norm_nonneg _) (by norm_num)
          _ = _ := by ring
      · have h2 := ih t r hw (by omega) (by omega)
        calc _ ≤ ε * (ε ^ t * 2 ^ r) :=
              mul_le_mul (hoff _ _ hd) h2 (norm_nonneg _) hε0
          _ = _ := by ring

/-- If `|G_xy - δ_xy m_sc| ≤ ε ≤ 1` on `Ω`, then the
iterate of `G_ij Ḡ_ij` along admissible data of length `≤ n` is at most `4^{|d|}` times
`ε²` (data avoiding `{i, j}`) or `4` (data meeting `{i, j}`), plus `(1/η + 1)^{2 + nξ} P(Ωᶜ)`. -/
theorem norm_integral_evalF_iterP_le {N : ℕ} {μ : Measure (Entries N)} [IsProbabilityMeasure μ]
    {z : ℂ} (hz : 0 < z.im) {i j : Fin N} (hij : i ≠ j) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (Ω : Set (Entries N))
    (hΩ : ∀ ω ∈ Ω, ∀ x y, ‖resS z ω x y - (if x = y then msc z else 0)‖ ≤ ε)
    {ξ n : ℕ} {d : List ((Fin N ⊕ OffDiag N) × List ℕ)} (hdn : d.length ≤ n)
    (hd : IterAdm ξ 2 d) :
    ‖∫ ω, evalF (resS z ω) (msc z) (iterP d [(1, [⟨.g, i, j⟩, ⟨.gbar, i, j⟩])]) ∂μ‖ ≤
      4 ^ (d.map fun x => x.2.sum).sum * ((if touchesData i j d then 4 else ε ^ 2) +
        (1 / z.im + 1) ^ (2 + n * ξ) * (μ Ωᶜ).toReal) := by
  classical
  set S : ℕ := (d.map fun x => x.2.sum).sum with hS
  set F0 : FSum N := [(1, [⟨.g, i, j⟩, ⟨.gbar, i, j⟩])] with hF0
  have hF0w : ∀ cw ∈ F0, 0 ≤ cw.1 ∧ cw.2.length = 2 := by
    intro cw hcw
    rw [hF0, List.mem_singleton] at hcw
    subst hcw
    simp
  obtain ⟨hprops, hsum⟩ := iterate_iterP_props d 2 F0 hd hF0w
  have hord : iterate_ord d = S := rfl
  rw [hord] at hprops hsum
  have hsum1 : ((iterP d F0).map Prod.fst).sum ≤ 2 ^ S := by simpa [hF0] using hsum
  have hSn : S ≤ n * ξ := (iterate_ord_le d 2 hd).trans (Nat.mul_le_mul_right ξ hdn)
  have hm : ‖msc z‖ ≤ 1 := (norm_msc_eq_inv_and_lt_one hz).2.le
  have hplain : ∀ cw ∈ iterP d F0, ∀ x ∈ cw.2, x.kind.plain = x.kind := by
    refine offDiagWords_iterP_plain d F0 ?_
    intro cw hcw x hx
    rw [hF0, List.mem_singleton] at hcw
    subst hcw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> rfl
  have hε2 : 0 ≤ ε ^ 2 := by positivity
  have hη1 : (1 : ℝ) ≤ 1 / z.im + 1 := by
    have : 0 ≤ 1 / z.im := by positivity
    linarith
  have h2S : (2 : ℝ) ^ S ≤ 4 ^ S := pow_le_pow_left₀ (by norm_num) (by norm_num) S
  have h4S : (0 : ℝ) < 4 ^ S := by positivity
  refine (expansion_norm_integral_le (G := Ω)
    (a := 4 ^ S * (if touchesData i j d then 4 else ε ^ 2))
    (b := 4 ^ S * (1 / z.im + 1) ^ (2 + n * ξ)) ?_ ?_ ?_).trans_eq (by ring)
  · refine mul_nonneg h4S.le ?_
    split_ifs <;> positivity
  · refine Eventually.of_forall fun ω hω => ?_
    have hG2 : ∀ x y, ‖resS z ω x y‖ ≤ 2 := by
      intro x y
      have h := hΩ ω hω x y
      have h1 : ‖resS z ω x y‖ ≤ ‖resS z ω x y - (if x = y then msc z else 0)‖ +
          ‖(if x = y then msc z else 0)‖ := by
        have := norm_add_le (resS z ω x y - (if x = y then msc z else 0))
          (if x = y then msc z else 0)
        simpa using this
      have h2 : ‖(if x = y then msc z else (0 : ℂ))‖ ≤ 1 := by split_ifs <;> simp [hm]
      linarith
    have hoff : ∀ x y, x ≠ y → ‖resS z ω x y‖ ≤ ε := by
      intro x y hxy
      simpa [hxy] using hΩ ω hω x y
    have hlen : ∀ cw ∈ iterP d F0, cw.2.length = S + 2 := fun cw hcw => by
      rw [(hprops cw hcw).2]; ring
    by_cases ht : touchesData i j d = true
    · simp only [ht, ite_true]
      have hw : ∀ cw ∈ iterP d F0, ‖evalWord (resS z ω) (msc z) cw.2‖ ≤ 2 ^ S * 4 := by
        intro cw hcw
        have h := offDiagWords_norm_evalWord_off_le (m := msc z) hε0 hG2 hoff cw.2 0 (S + 2)
          (hplain cw hcw) (by simpa using hlen cw hcw) (Nat.zero_le _)
        calc _ ≤ ε ^ 0 * 2 ^ (S + 2) := h
          _ = _ := by ring
      have := offDiagWords_norm_evalF_le (G := resS z ω) (m := msc z) (iterP d F0)
        (fun cw hcw => (hprops cw hcw).1) hw
      calc _ ≤ _ := this
        _ ≤ 2 ^ S * (2 ^ S * 4) := mul_le_mul_of_nonneg_right hsum1 (by positivity)
        _ = 4 ^ S * 4 := by rw [← mul_assoc, ← mul_pow]; norm_num
    · have hf : touchesData i j d = false := by simpa using ht
      simp only [hf, Bool.false_eq_true, ite_false]
      have hw : ∀ cw ∈ iterP d F0, ‖evalWord (resS z ω) (msc z) cw.2‖ ≤ ε ^ 2 * 2 ^ S := by
        intro cw hcw
        obtain ⟨hpl, h2⟩ := iterP_offDiag_two hij d hf cw hcw
        exact offDiagWords_norm_evalWord_off_le (m := msc z) hε0 hG2 hoff cw.2 2 S hpl
          (by rw [hlen cw hcw]; ring) h2
      have := offDiagWords_norm_evalF_le (G := resS z ω) (m := msc z) (iterP d F0)
        (fun cw hcw => (hprops cw hcw).1) hw
      calc _ ≤ _ := this
        _ ≤ 2 ^ S * (ε ^ 2 * 2 ^ S) := mul_le_mul_of_nonneg_right hsum1 (by positivity)
        _ = 4 ^ S * ε ^ 2 := by
          have : (4 : ℝ) ^ S = 2 ^ S * 2 ^ S := by rw [← mul_pow]; norm_num
          rw [this]; ring
  · refine Eventually.of_forall fun ω => ?_
    have hG : ∀ x y, ‖resS z ω x y‖ ≤ 1 / z.im := fun x y =>
      norm_resolventC_apply_le (symOfEntries_isHermitian ω) hz x y
    have hw : ∀ cw ∈ iterP d F0, ‖evalWord (resS z ω) (msc z) cw.2‖ ≤
        (1 / z.im + 1) ^ (2 + n * ξ) := by
      intro cw hcw
      refine (offDiagWords_norm_evalWord_le hG hm cw.2).trans ?_
      refine pow_le_pow_right₀ hη1 ?_
      rw [(hprops cw hcw).2]
      omega
    have := offDiagWords_norm_evalF_le (G := resS z ω) (m := msc z) (iterP d F0)
      (fun cw hcw => (hprops cw hcw).1) hw
    calc _ ≤ _ := this
      _ ≤ 2 ^ S * (1 / z.im + 1) ^ (2 + n * ξ) :=
          mul_le_mul_of_nonneg_right hsum1 (by positivity)
      _ ≤ 4 ^ S * (1 / z.im + 1) ^ (2 + n * ξ) := mul_le_mul_of_nonneg_right h2S (by positivity)

/-! ### Compiled checks -/

/-- At `N = 5`, `i = 1`, `j = 2` (`Fin 5` indices `0, 1`): along the entry `{3, 4}`, which
avoids `{i, j}`, every word of `P_{γ,(3,3)}(G_12 Ḡ_12)` has at least two off-diagonal letters;
along `{1, 2}` some word has none. -/
example : (∀ cw ∈ iterP [((Sum.inr ⟨(2, 3), by decide⟩ : Fin 5 ⊕ OffDiag 5), [3, 3])]
      ([(1, [⟨.g, 0, 1⟩, ⟨.gbar, 0, 1⟩])] : FSum 5),
      2 ≤ (cw.2.filter fun ℓ => ℓ.i ≠ ℓ.j).length) ∧
    (∃ cw ∈ iterP [((Sum.inr ⟨(0, 1), by decide⟩ : Fin 5 ⊕ OffDiag 5), [3, 3])]
      ([(1, [⟨.g, 0, 1⟩, ⟨.gbar, 0, 1⟩])] : FSum 5),
      (cw.2.filter fun ℓ => ℓ.i ≠ ℓ.j).length = 0) := by
  decide

/-- `m_sc(i) = i (√5 - 1)/2`. -/
private lemma offDiagWords_msc_I :
    msc Complex.I = Complex.I * (((Real.sqrt 5 - 1) / 2 : ℝ) : ℂ) := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : (2 : ℝ) < Real.sqrt 5 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  set t : ℝ := (Real.sqrt 5 - 1) / 2 with ht
  have ht0 : 0 < t := by rw [ht]; linarith
  have ht2 : t ^ 2 + t - 1 = 0 := by rw [ht]; nlinarith
  symm
  refine eq_msc_of_add_inv (by simp) ?_ (by simpa using ht0)
  have ht2' : ((t : ℂ)) ^ 2 + t - 1 = 0 := by exact_mod_cast ht2
  have hinv : (Complex.I + Complex.I * (t : ℂ))⁻¹ = -(Complex.I * (t : ℂ)) :=
    inv_eq_of_mul_eq_one_right (by
      linear_combination ht2' + (-(t : ℂ) - (t : ℂ) ^ 2) * Complex.I_sq)
  rw [hinv]
  ring

/-- The resolvent of the zero entries at `z = i` is `i` times the identity. -/
private lemma offDiagWords_resS_zero {N : ℕ} :
    resS Complex.I (0 : Entries N) = Complex.I • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  have h0 : symOfEntries (0 : Entries N) = 0 := by
    ext x y
    simp [symOfEntries]
  unfold resS resolventC
  rw [h0]
  refine Matrix.inv_eq_right_inv ?_
  simp [Matrix.smul_eq_diagonal_mul]

/-- `norm_integral_evalF_iterP_le` at `N = 3`, `z = i`, `i = 1`, `j = 2` (`Fin 3` indices `0, 1`),
`ξ = 6`, `n = 1`, `ε = 1`, `Ω = {0}` and `μ` the point mass at the zero entries, for the data
`[(3, (3, 3))]` (diagonal entry `3`, avoiding `{1, 2}`) and `[(1, (3, 0))]` (diagonal entry `1`,
meeting `{1, 2}`). All hypotheses hold and `μ Ωᶜ = 0`. -/
example :
    ‖∫ ω, evalF (resS Complex.I ω) (msc Complex.I)
        (iterP [((Sum.inl 2 : Fin 3 ⊕ OffDiag 3), [3, 3])] [(1, [⟨.g, 0, 1⟩, ⟨.gbar, 0, 1⟩])])
        ∂(Measure.dirac (0 : Entries 3))‖ ≤ 4 ^ 6 ∧
    ‖∫ ω, evalF (resS Complex.I ω) (msc Complex.I)
        (iterP [((Sum.inl 0 : Fin 3 ⊕ OffDiag 3), [3, 0])] [(1, [⟨.g, 0, 1⟩, ⟨.gbar, 0, 1⟩])])
        ∂(Measure.dirac (0 : Entries 3))‖ ≤ 4 ^ 3 * 4 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs2 : (2 : ℝ) < Real.sqrt 5 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs3 : Real.sqrt 5 < 3 := by
    rw [show (3 : ℝ) = Real.sqrt (3 ^ 2) by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hΩ : ∀ ω ∈ ({0} : Set (Entries 3)), ∀ x y : Fin 3,
      ‖resS Complex.I ω x y - (if x = y then msc Complex.I else 0)‖ ≤ 1 := by
    intro ω hω x y
    rw [Set.mem_singleton_iff.1 hω, offDiagWords_resS_zero, offDiagWords_msc_I]
    by_cases hxy : x = y
    · subst hxy
      have : (Complex.I • (1 : Matrix (Fin 3) (Fin 3) ℂ)) x x -
          Complex.I * (((Real.sqrt 5 - 1) / 2 : ℝ) : ℂ) =
          Complex.I * ((1 - (Real.sqrt 5 - 1) / 2 : ℝ) : ℂ) := by
        simp; ring
      simp only [ite_true]
      rw [this, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_le]
      constructor <;> linarith
    · simp [hxy]
  have hμ : (Measure.dirac (0 : Entries 3) ({0} : Set (Entries 3))ᶜ).toReal = 0 := by
    simp [Measure.dirac_apply']
  have key : ∀ d : List ((Fin 3 ⊕ OffDiag 3) × List ℕ), d.length ≤ 1 → IterAdm 6 2 d →
      ‖∫ ω, evalF (resS Complex.I ω) (msc Complex.I)
        (iterP d [(1, [⟨.g, 0, 1⟩, ⟨.gbar, 0, 1⟩])]) ∂(Measure.dirac (0 : Entries 3))‖ ≤
        4 ^ (d.map fun x => x.2.sum).sum * ((if touchesData 0 1 d then 4 else 1 ^ 2) +
          2 ^ (2 + 1 * 6) * 0) := by
    intro d hdn hd
    have h := norm_integral_evalF_iterP_le (μ := Measure.dirac (0 : Entries 3))
      (z := Complex.I) (by simp) (i := 0) (j := 1) (by decide) (ε := 1) zero_le_one le_rfl
      {0} hΩ (ξ := 6) (n := 1) hdn hd
    rw [hμ] at h
    simpa [one_add_one_eq_two] using h
  refine ⟨?_, ?_⟩
  · have := key [((Sum.inl 2 : Fin 3 ⊕ OffDiag 3), [3, 3])] (by simp)
      ⟨rfl, by simp [matchedOrder], by simp, trivial⟩
    have ht : touchesData 0 1 [((Sum.inl 2 : Fin 3 ⊕ OffDiag 3), [3, 3])] = false := by decide
    simpa [ht] using this
  · have := key [((Sum.inl 0 : Fin 3 ⊕ OffDiag 3), [3, 0])] (by simp)
      ⟨rfl, by simp [matchedOrder], by simp, trivial⟩
    have ht : touchesData 0 1 [((Sum.inl 0 : Fin 3 ⊕ OffDiag 3), [3, 0])] = true := by decide
    simpa [ht] using this

#print axioms iterP_offDiag_two
#print axioms norm_integral_evalF_iterP_le

end WEdgeNS
