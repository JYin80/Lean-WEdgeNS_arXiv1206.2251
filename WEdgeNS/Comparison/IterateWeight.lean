import WEdgeNS.Comparison.IterateSum
import WEdgeNS.Comparison.OffDiagWords

/-!
# Total weight of the admissible data
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

open private iterate_sum_highIdx_le from WEdgeNS.Comparison.Iterate
open private expansion_rpow_pow expansion_mem_highIdx from WEdgeNS.Comparison.Expansion
open private iterateSum_sum_succ iterateSum_iterWeight_nonneg from WEdgeNS.Comparison.IterateSum

/-- The weight `w(d)` of the data `d` times the word-count factor `4^{|d|}`. -/
private def iterateWeight_w4 (N : ℕ) (φq : ℝ) (d : List ((Fin N ⊕ OffDiag N) × List ℕ)) : ℝ :=
  iterWeight N φq d * 4 ^ (d.map fun x => x.2.sum).sum

private lemma iterateWeight_w4_nil (N : ℕ) (φq : ℝ) : iterateWeight_w4 N φq [] = 1 := by
  simp [iterateWeight_w4, iterWeight]

private lemma iterateWeight_w4_nonneg (N : ℕ) (φq : ℝ) (d : List ((Fin N ⊕ OffDiag N) × List ℕ)) :
    0 ≤ iterateWeight_w4 N φq d :=
  mul_nonneg (iterateSum_iterWeight_nonneg N φq d) (by positivity)

/-- One step of the weight with the word-count factor: `W(e) (4 N^{-φq/20})^{|k|}`. -/
private lemma iterateWeight_w4_cons (N : ℕ) {φq : ℝ} (e : Fin N ⊕ OffDiag N) (k : List ℕ)
    (d : List ((Fin N ⊕ OffDiag N) × List ℕ)) :
    iterateWeight_w4 N φq ((e, k) :: d) =
      entryWeight N e * (4 * (N : ℝ) ^ (-(φq / 20))) ^ k.sum * iterateWeight_w4 N φq d := by
  simp only [iterateWeight_w4, iterWeight, List.map_cons, List.prod_cons, List.sum_cons, pow_add,
    mul_pow, expansion_rpow_pow (Nat.cast_nonneg N)]
  ring


/-- The mass of one entry `e` at current word length `s`: `W(e) Σ_α y^{|α|}` over the indices
`α ∈ ℕ^s` with `matchedOrder e < |α| ≤ ξ`. -/
private def iterateWeight_mass (N ξ s : ℕ) (y : ℝ) (e : Fin N ⊕ OffDiag N) : ℝ :=
  entryWeight N e * ∑ α ∈ highIdx s (matchedOrder e) ξ, y ^ (∑ i, α i)

private lemma iterateWeight_entryWeight_nonneg (N : ℕ) (e : Fin N ⊕ OffDiag N) :
    0 ≤ entryWeight N e := by
  rcases e with e | e <;> simp only [entryWeight] <;> positivity

private lemma iterateWeight_mass_inl_le {N : ℕ} (ξ s : ℕ) {y t : ℝ} (hy : 0 ≤ y)
    (hts : (s : ℝ) ≤ t) (hty : t * y ≤ 1 / 8) (a : Fin N) :
    iterateWeight_mass N ξ s y (Sum.inl a) ≤ (N : ℝ)⁻¹ * (2 * (t * y) ^ 3) := by
  simp only [iterateWeight_mass, entryWeight, matchedOrder]
  gcongr
  exact iterate_sum_highIdx_le s 2 ξ hy hts (by linarith)

private lemma iterateWeight_mass_inr_le {N : ℕ} (ξ s : ℕ) {y t : ℝ} (hy : 0 ≤ y)
    (hts : (s : ℝ) ≤ t) (hty : t * y ≤ 1 / 8) (p : OffDiag N) :
    iterateWeight_mass N ξ s y (Sum.inr p) ≤ ((N : ℝ) ^ 2)⁻¹ * (2 * (t * y) ^ 5) := by
  simp only [iterateWeight_mass, entryWeight, matchedOrder]
  gcongr
  exact iterate_sum_highIdx_le s 4 ξ hy hts (by linarith)

private lemma iterateWeight_card_offDiag (N : ℕ) :
    (Fintype.card (OffDiag N) : ℝ) ≤ (N : ℝ) ^ 2 := by
  have := Fintype.card_subtype_le (fun p : Fin N × Fin N => p.1 < p.2)
  rw [Fintype.card_prod, Fintype.card_fin] at this
  rw [sq]
  exact_mod_cast this

/-- The total mass of all entries is at most `1/4`. -/
private lemma iterateWeight_mass_sum_le {N : ℕ} (hN : 1 ≤ N) (ξ s : ℕ) {y t : ℝ} (hy : 0 ≤ y)
    (hts : (s : ℝ) ≤ t) (hty : t * y ≤ 1 / 8) :
    ∑ e, iterateWeight_mass N ξ s y e ≤ 1 / 4 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have ht0 : 0 ≤ t := (Nat.cast_nonneg s).trans hts
  have hx0 : 0 ≤ t * y := mul_nonneg ht0 hy
  rw [Fintype.sum_sum_type]
  have hA : ∑ a : Fin N, iterateWeight_mass N ξ s y (Sum.inl a) ≤ 2 * (t * y) ^ 3 := by
    calc _ ≤ ∑ a : Fin N, (N : ℝ)⁻¹ * (2 * (t * y) ^ 3) :=
          Finset.sum_le_sum fun a _ => iterateWeight_mass_inl_le ξ s hy hts hty a
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
            mul_inv_cancel₀ hN0.ne', one_mul]
  have hB : ∑ p : OffDiag N, iterateWeight_mass N ξ s y (Sum.inr p) ≤ 2 * (t * y) ^ 5 := by
    calc _ ≤ ∑ p : OffDiag N, ((N : ℝ) ^ 2)⁻¹ * (2 * (t * y) ^ 5) :=
          Finset.sum_le_sum fun p _ => iterateWeight_mass_inr_le ξ s hy hts hty p
      _ = (Fintype.card (OffDiag N) : ℝ) * ((N : ℝ) ^ 2)⁻¹ * (2 * (t * y) ^ 5) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
      _ ≤ (N : ℝ) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * (2 * (t * y) ^ 5) := by
          gcongr
          exact iterateWeight_card_offDiag N
      _ = _ := by rw [mul_inv_cancel₀ (by positivity), one_mul]
  have h3 : (t * y) ^ 3 ≤ (1 / 8) ^ 3 := pow_le_pow_left₀ hx0 hty 3
  have h5 : (t * y) ^ 5 ≤ (1 / 8) ^ 5 := pow_le_pow_left₀ hx0 hty 5
  norm_num at h3 h5
  linarith


private lemma iterateWeight_touchesEntry_inl {N : ℕ} (i j a : Fin N) :
    touchesEntry i j (Sum.inl a) = true ↔ a = i ∨ a = j := by
  simp [touchesEntry, entryPairs]

private lemma iterateWeight_touchesEntry_inr {N : ℕ} (i j : Fin N) (p : OffDiag N) :
    touchesEntry i j (Sum.inr p) = true ↔
      p.1.1 = i ∨ p.1.1 = j ∨ p.1.2 = i ∨ p.1.2 = j := by
  simp only [touchesEntry, entryPairs, List.any_cons, List.any_nil, Bool.or_false,
    Bool.or_eq_true, decide_eq_true_eq]
  tauto

/-- At most `N` off-diagonal pairs have a prescribed first coordinate. -/
private lemma iterateWeight_card_fst (N : ℕ) (i : Fin N) :
    (Finset.univ.filter fun p : OffDiag N => p.1.1 = i).card ≤ N := by
  calc _ ≤ (Finset.univ : Finset (Fin N)).card := by
        refine Finset.card_le_card_of_injOn (fun p => p.1.2) (fun _ _ => Finset.mem_coe.2
          (Finset.mem_univ _)) ?_
        intro p hp q hq h
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
        exact Subtype.ext (Prod.ext (hp.trans hq.symm) h)
    _ = N := by simp

/-- At most `N` off-diagonal pairs have a prescribed second coordinate. -/
private lemma iterateWeight_card_snd (N : ℕ) (i : Fin N) :
    (Finset.univ.filter fun p : OffDiag N => p.1.2 = i).card ≤ N := by
  calc _ ≤ (Finset.univ : Finset (Fin N)).card := by
        refine Finset.card_le_card_of_injOn (fun p => p.1.1) (fun _ _ => Finset.mem_coe.2
          (Finset.mem_univ _)) ?_
        intro p hp q hq h
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
        exact Subtype.ext (Prod.ext h (hp.trans hq.symm))
    _ = N := by simp

/-- The mass of the entries meeting `{i, j}` is at most `1/(16 N)`. -/
private lemma iterateWeight_mass_touch_le {N : ℕ} (hN : 1 ≤ N) (ξ s : ℕ) {y t : ℝ} (hy : 0 ≤ y)
    (hts : (s : ℝ) ≤ t) (hty : t * y ≤ 1 / 8) (i j : Fin N) :
    ∑ e, (if touchesEntry i j e then iterateWeight_mass N ξ s y e else 0) ≤ 1 / (16 * N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have ht0 : 0 ≤ t := (Nat.cast_nonneg s).trans hts
  have hx0 : 0 ≤ t * y := mul_nonneg ht0 hy
  rw [Fintype.sum_sum_type]
  set c : ℝ := (N : ℝ)⁻¹ * (2 * (t * y) ^ 3) with hc
  set c' : ℝ := ((N : ℝ) ^ 2)⁻¹ * (2 * (t * y) ^ 5) with hc'
  have hc0 : 0 ≤ c := by positivity
  have hc'0 : 0 ≤ c' := by positivity
  have hA : ∑ a : Fin N, (if touchesEntry i j (Sum.inl a) then
      iterateWeight_mass N ξ s y (Sum.inl a) else 0) ≤ 2 * c := by
    calc _ ≤ ∑ a : Fin N, ((if a = i then c else 0) + (if a = j then c else 0)) := by
          refine Finset.sum_le_sum fun a _ => ?_
          have hm := iterateWeight_mass_inl_le ξ s hy hts hty a
          by_cases h : touchesEntry i j (Sum.inl a) = true
          · rw [ite_eq_left h]
            rcases (iterateWeight_touchesEntry_inl i j a).1 h with h1 | h1
            · rw [ite_eq_left h1]
              split_ifs <;> linarith
            · rw [ite_eq_left h1]
              split_ifs <;> linarith
          · rw [ite_eq_right h]
            split_ifs <;> linarith
      _ = 2 * c := by
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          ring
  have hB : ∑ p : OffDiag N, (if touchesEntry i j (Sum.inr p) then
      iterateWeight_mass N ξ s y (Sum.inr p) else 0) ≤ 4 * N * c' := by
    calc _ ≤ ∑ p : OffDiag N, (((if p.1.1 = i then c' else 0) + (if p.1.1 = j then c' else 0)) +
          ((if p.1.2 = i then c' else 0) + (if p.1.2 = j then c' else 0))) := by
          refine Finset.sum_le_sum fun p _ => ?_
          have hm := iterateWeight_mass_inr_le ξ s hy hts hty p
          by_cases h : touchesEntry i j (Sum.inr p) = true
          · rw [ite_eq_left h]
            rcases (iterateWeight_touchesEntry_inr i j p).1 h with h1 | h1 | h1 | h1
            · rw [ite_eq_left h1]
              split_ifs <;> linarith
            · rw [ite_eq_left h1]
              split_ifs <;> linarith
            · rw [ite_eq_left h1]
              split_ifs <;> linarith
            · rw [ite_eq_left h1]
              split_ifs <;> linarith
          · rw [ite_eq_right h]
            split_ifs <;> linarith
      _ = (c' * (Finset.univ.filter fun p : OffDiag N => p.1.1 = i).card +
            c' * (Finset.univ.filter fun p : OffDiag N => p.1.1 = j).card) +
          (c' * (Finset.univ.filter fun p : OffDiag N => p.1.2 = i).card +
            c' * (Finset.univ.filter fun p : OffDiag N => p.1.2 = j).card) := by
          simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
            Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ (c' * N + c' * N) + (c' * N + c' * N) := by
          have h1 := iterateWeight_card_fst N i
          have h2 := iterateWeight_card_fst N j
          have h3 := iterateWeight_card_snd N i
          have h4 := iterateWeight_card_snd N j
          gcongr
      _ = 4 * N * c' := by ring
  have hx3 : (t * y) ^ 3 ≤ (1 / 8) ^ 3 := pow_le_pow_left₀ hx0 hty 3
  have hx5 : (t * y) ^ 5 ≤ (1 / 8) ^ 5 := pow_le_pow_left₀ hx0 hty 5
  have hcN : 2 * c = (4 * (t * y) ^ 3) / N := by rw [hc]; field_simp; ring
  have hc'N : 4 * N * c' = (8 * (t * y) ^ 5) / N := by rw [hc']; field_simp; ring
  have hfin : (4 * (t * y) ^ 3) / N + (8 * (t * y) ^ 5) / N ≤ 1 / (16 * N) := by
    rw [← add_div, div_le_div_iff₀ hN0 (by positivity)]
    norm_num at hx3 hx5
    nlinarith
  linarith


private lemma iterateWeight_touchesData_cons {N : ℕ} (i j : Fin N) (e : Fin N ⊕ OffDiag N)
    (k : List ℕ) (d : List ((Fin N ⊕ OffDiag N) × List ℕ)) :
    touchesData i j ((e, k) :: d) = (touchesEntry i j e || touchesData i j d) := by
  simp [touchesData]

/-- After one step `(e, α)` of the recursion, the remaining word length and depth stay within
the budget `t`. -/
private lemma iterateWeight_budget {ξ n s : ℕ} {t : ℝ} {m : ℕ}
    (h : ((s + (n + 1) * ξ : ℕ) : ℝ) ≤ t) (hm : m ≤ ξ) :
    ((s + m + n * ξ : ℕ) : ℝ) ≤ t := by
  refine le_trans ?_ h
  exact_mod_cast (by rw [add_mul, one_mul]; omega : s + m + n * ξ ≤ s + (n + 1) * ξ)

/-- The total weight with the word-count factor is at most `2`. -/
private lemma iterateWeight_total_le {N : ℕ} (hN : 1 ≤ N) {φq t : ℝ} (ξ : ℕ)
    (hx : t * (4 * (N : ℝ) ^ (-(φq / 20))) ≤ 1 / 8) :
    ∀ n s : ℕ, ((s + n * ξ : ℕ) : ℝ) ≤ t →
      ∑ d ∈ iterAdmSet N ξ s n, iterateWeight_w4 N φq d ≤ 2 := by
  have hy : 0 ≤ 4 * (N : ℝ) ^ (-(φq / 20)) := by positivity
  intro n
  induction n with
  | zero =>
    intro s _
    simp [iterAdmSet, iterateWeight_w4_nil]
  | succ n ih =>
    intro s hs
    have hts : (s : ℝ) ≤ t := le_trans (by exact_mod_cast Nat.le_add_right _ _) hs
    rw [iterateSum_sum_succ s n (iterateWeight_w4 N φq), iterateWeight_w4_nil]
    have hstep : ∀ (e : Fin N ⊕ OffDiag N) (α : Fin s → ℕ), α ∈ highIdx s (matchedOrder e) ξ →
        ∑ d ∈ iterAdmSet N ξ (s + ∑ i, α i) n,
          iterateWeight_w4 N φq ((e, List.ofFn α) :: d) ≤
        entryWeight N e * (4 * (N : ℝ) ^ (-(φq / 20))) ^ (∑ i, α i) * 2 := by
      intro e α hα
      have hα2 := ((expansion_mem_highIdx α).1 hα).2
      have h := ih (s + ∑ i, α i) (iterateWeight_budget hs hα2)
      simp only [iterateWeight_w4_cons, List.sum_ofFn]
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left h (mul_nonneg (iterateWeight_entryWeight_nonneg N e)
        (pow_nonneg hy _))
    have hsum : ∑ e : Fin N ⊕ OffDiag N, ∑ α ∈ highIdx s (matchedOrder e) ξ,
        ∑ d ∈ iterAdmSet N ξ (s + ∑ i, α i) n,
          iterateWeight_w4 N φq ((e, List.ofFn α) :: d) ≤
        2 * ∑ e, iterateWeight_mass N ξ s (4 * (N : ℝ) ^ (-(φq / 20))) e := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun e _ => ?_
      calc _ ≤ ∑ α ∈ highIdx s (matchedOrder e) ξ,
            entryWeight N e * (4 * (N : ℝ) ^ (-(φq / 20))) ^ (∑ i, α i) * 2 :=
            Finset.sum_le_sum fun α hα => hstep e α hα
        _ = _ := by
            simp only [iterateWeight_mass, ← Finset.sum_mul, ← Finset.mul_sum]
            ring
    have hmass := iterateWeight_mass_sum_le hN ξ s hy hts hx
    linarith

/-- The weight with the word-count factor of the data meeting `{i, j}` is at most
`1/(4 N)`. -/
private lemma iterateWeight_touch_le {N : ℕ} (hN : 1 ≤ N) {φq t : ℝ} (ξ : ℕ)
    (hx : t * (4 * (N : ℝ) ^ (-(φq / 20))) ≤ 1 / 8) (i j : Fin N) :
    ∀ n s : ℕ, ((s + n * ξ : ℕ) : ℝ) ≤ t →
      ∑ d ∈ iterAdmSet N ξ s n, (if touchesData i j d then iterateWeight_w4 N φq d else 0) ≤
        1 / (4 * N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hy : 0 ≤ 4 * (N : ℝ) ^ (-(φq / 20)) := by positivity
  have hτ : (0 : ℝ) ≤ 1 / (4 * N) := by positivity
  intro n
  induction n with
  | zero =>
    intro s _
    simp [iterAdmSet, touchesData]
  | succ n ih =>
    intro s hs
    have hts : (s : ℝ) ≤ t := le_trans (by exact_mod_cast Nat.le_add_right _ _) hs
    rw [iterateSum_sum_succ s n (fun d => if touchesData i j d then iterateWeight_w4 N φq d
      else 0)]
    have hnil : (if touchesData i j [] then iterateWeight_w4 N φq [] else 0) = 0 := by
      simp [touchesData]
    rw [hnil, zero_add]
    -- the bound for one first step
    have hstep : ∀ (e : Fin N ⊕ OffDiag N) (α : Fin s → ℕ), α ∈ highIdx s (matchedOrder e) ξ →
        ∑ d ∈ iterAdmSet N ξ (s + ∑ i, α i) n,
          (if touchesData i j ((e, List.ofFn α) :: d) then
            iterateWeight_w4 N φq ((e, List.ofFn α) :: d) else 0) ≤
        entryWeight N e * (4 * (N : ℝ) ^ (-(φq / 20))) ^ (∑ i, α i) *
          ((if touchesEntry i j e then 2 else 0) + 1 / (4 * N)) := by
      intro e α hα
      have hα2 := ((expansion_mem_highIdx α).1 hα).2
      have hb := iterateWeight_budget hs hα2
      have hA := iterateWeight_total_le hN ξ hx n (s + ∑ i, α i) hb
      have hT := ih (s + ∑ i, α i) hb
      set c : ℝ := entryWeight N e * (4 * (N : ℝ) ^ (-(φq / 20))) ^ (∑ i, α i) with hc
      have hc0 : 0 ≤ c := mul_nonneg (iterateWeight_entryWeight_nonneg N e) (pow_nonneg hy _)
      have hcons : ∀ d, iterateWeight_w4 N φq ((e, List.ofFn α) :: d) =
          c * iterateWeight_w4 N φq d := by
        intro d
        rw [iterateWeight_w4_cons, List.sum_ofFn]
      by_cases hte : touchesEntry i j e = true
      · simp only [iterateWeight_touchesData_cons, hte, Bool.true_or, ite_true, hcons]
        calc _ ≤ ∑ d ∈ iterAdmSet N ξ (s + ∑ i, α i) n, c * iterateWeight_w4 N φq d :=
              Finset.sum_le_sum fun d _ => le_rfl
          _ = c * ∑ d ∈ iterAdmSet N ξ (s + ∑ i, α i) n, iterateWeight_w4 N φq d := by
              rw [Finset.mul_sum]
          _ ≤ c * 2 := mul_le_mul_of_nonneg_left hA hc0
          _ ≤ _ := by nlinarith
      · have hte' : touchesEntry i j e = false := by simpa using hte
        simp only [iterateWeight_touchesData_cons, hte', Bool.false_or]
        calc _ = ∑ d ∈ iterAdmSet N ξ (s + ∑ i, α i) n,
              c * (if touchesData i j d then iterateWeight_w4 N φq d else 0) := by
              refine Finset.sum_congr rfl fun d _ => ?_
              rw [hcons]
              split_ifs <;> simp
          _ = c * ∑ d ∈ iterAdmSet N ξ (s + ∑ i, α i) n,
              (if touchesData i j d then iterateWeight_w4 N φq d else 0) := by
              rw [Finset.mul_sum]
          _ ≤ c * (1 / (4 * N)) := mul_le_mul_of_nonneg_left hT hc0
          _ = _ := by simp
    have hsum : ∑ e : Fin N ⊕ OffDiag N, ∑ α ∈ highIdx s (matchedOrder e) ξ,
        ∑ d ∈ iterAdmSet N ξ (s + ∑ i, α i) n,
          (if touchesData i j ((e, List.ofFn α) :: d) then
            iterateWeight_w4 N φq ((e, List.ofFn α) :: d) else 0) ≤
        2 * ∑ e, (if touchesEntry i j e then
          iterateWeight_mass N ξ s (4 * (N : ℝ) ^ (-(φq / 20))) e else 0) +
          1 / (4 * N) * ∑ e, iterateWeight_mass N ξ s (4 * (N : ℝ) ^ (-(φq / 20))) e := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun e _ => ?_
      calc _ ≤ ∑ α ∈ highIdx s (matchedOrder e) ξ,
            entryWeight N e * (4 * (N : ℝ) ^ (-(φq / 20))) ^ (∑ i, α i) *
              ((if touchesEntry i j e then 2 else 0) + 1 / (4 * N)) :=
            Finset.sum_le_sum fun α hα => hstep e α hα
        _ = _ := by
            simp only [iterateWeight_mass, ← Finset.sum_mul, ← Finset.mul_sum]
            split_ifs <;> ring
    have hmass := iterateWeight_mass_sum_le hN ξ s hy hts hx
    have htouch := iterateWeight_mass_touch_le hN ξ s hy hts hx i j
    have hinv : 1 / (4 * (N : ℝ)) = 4 * (1 / (16 * (N : ℝ))) := by field_simp; ring
    have hmul : 1 / (4 * (N : ℝ)) * ∑ e, iterateWeight_mass N ξ s
        (4 * (N : ℝ) ^ (-(φq / 20))) e ≤ 1 / (4 * (N : ℝ)) * (1 / 4) :=
      mul_le_mul_of_nonneg_left hmass hτ
    have hfin : 2 * (1 / (16 * (N : ℝ))) + 1 / (4 * (N : ℝ)) * (1 / 4) ≤ 1 / (4 * (N : ℝ)) := by
      rw [hinv]
      have : 0 ≤ 1 / (16 * (N : ℝ)) := by positivity
      linarith
    linarith

/-- The total weight (with the word-count factor `4^{|d|}`) of the admissible
data is at most `2`, and that of the data meeting `{i, j}` is at most `⌈6ζ/φq⌉ / N`. -/
theorem iterWeight_sum_le {φq ζ : ℝ} (hφq : 0 < φq) (hζ : 1 ≤ ζ) (s : ℕ) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ i j : Fin N,
      ∑ d ∈ iterAdmSet N (xiOf (2 * ζ + 3) φq) s ⌈6 * ζ / φq⌉₊,
          iterWeight N φq d * 4 ^ (d.map fun x => x.2.sum).sum ≤ 2 ∧
      ∑ d ∈ (iterAdmSet N (xiOf (2 * ζ + 3) φq) s ⌈6 * ζ / φq⌉₊).filter
          (fun d => touchesData i j d),
          iterWeight N φq d * 4 ^ (d.map fun x => x.2.sum).sum ≤ (⌈6 * ζ / φq⌉₊ : ℝ) / N := by
  set ξ : ℕ := xiOf (2 * ζ + 3) φq with hξ
  set n : ℕ := ⌈6 * ζ / φq⌉₊ with hn
  set t : ℝ := ((s + n * ξ : ℕ) : ℝ) with ht
  have hev := ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < φq / 20)).comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop (32 * t)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hev.and (eventually_ge_atTop 1))
  refine ⟨N0, fun N hN i j => ?_⟩
  obtain ⟨hρ, hN1⟩ := hN0 N hN
  have hρ' : 32 * t ≤ (N : ℝ) ^ (φq / 20) := hρ
  have hN0r : (0 : ℝ) < N := by exact_mod_cast hN1
  have hx0 : 0 < (N : ℝ) ^ (-(φq / 20)) := Real.rpow_pos_of_pos hN0r _
  have hxρ : (N : ℝ) ^ (-(φq / 20)) * (N : ℝ) ^ (φq / 20) = 1 := by
    rw [← Real.rpow_add hN0r, neg_add_cancel, Real.rpow_zero]
  have hx : t * (4 * (N : ℝ) ^ (-(φq / 20))) ≤ 1 / 8 := by
    have := mul_le_mul_of_nonneg_right hρ' hx0.le
    nlinarith
  have hn1 : 1 ≤ n := Nat.ceil_pos.2 (div_pos (by linarith) hφq)
  refine ⟨iterateWeight_total_le hN1 ξ hx n s le_rfl, ?_⟩
  rw [Finset.sum_filter]
  have h := iterateWeight_touch_le hN1 ξ hx i j n s le_rfl
  refine le_trans h ?_
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  rw [div_le_div_iff₀ (by positivity) hN0r]
  nlinarith

/-- Instance of `iterWeight_sum_le` at `φq = 1/4`, `ζ = 1`, `s = 2`, with `N` the larger of the
threshold and `2`, and `i ≠ j`: the first sum is at least `1` (the empty data) and at most `2`; the
second is positive (the datum `[(i, (3, 0))]` is admissible and meets `{i, j}`) and at most
`⌈6ζ/φq⌉ / N`. -/
example : ∃ N : ℕ, ∃ i j : Fin N, i ≠ j ∧
    1 ≤ ∑ d ∈ iterAdmSet N (xiOf (2 * 1 + 3) (1 / 4)) 2 ⌈6 * 1 / (1 / 4 : ℝ)⌉₊,
        iterWeight N (1 / 4) d * 4 ^ (d.map fun x => x.2.sum).sum ∧
    ∑ d ∈ iterAdmSet N (xiOf (2 * 1 + 3) (1 / 4)) 2 ⌈6 * 1 / (1 / 4 : ℝ)⌉₊,
        iterWeight N (1 / 4) d * 4 ^ (d.map fun x => x.2.sum).sum ≤ 2 ∧
    0 < ∑ d ∈ (iterAdmSet N (xiOf (2 * 1 + 3) (1 / 4)) 2 ⌈6 * 1 / (1 / 4 : ℝ)⌉₊).filter
        (fun d => touchesData i j d),
        iterWeight N (1 / 4) d * 4 ^ (d.map fun x => x.2.sum).sum ∧
    ∑ d ∈ (iterAdmSet N (xiOf (2 * 1 + 3) (1 / 4)) 2 ⌈6 * 1 / (1 / 4 : ℝ)⌉₊).filter
        (fun d => touchesData i j d),
        iterWeight N (1 / 4) d * 4 ^ (d.map fun x => x.2.sum).sum ≤
      (⌈6 * 1 / (1 / 4 : ℝ)⌉₊ : ℝ) / N := by
  obtain ⟨N0, hN0⟩ := iterWeight_sum_le (φq := 1 / 4) (ζ := 1) (by norm_num) le_rfl 2
  have hN2 : 2 ≤ max N0 2 := le_max_right _ _
  set N : ℕ := max N0 2 with hN
  have hξ : 3 ≤ xiOf (2 * 1 + 3) (1 / 4 : ℝ) := by
    unfold xiOf; norm_num
  have hn : 1 ≤ ⌈6 * 1 / (1 / 4 : ℝ)⌉₊ := by norm_num
  set i : Fin N := ⟨0, by omega⟩ with hi
  set j : Fin N := ⟨1, by omega⟩ with hj
  obtain ⟨h1, h2⟩ := hN0 N (le_max_left _ _) i j
  refine ⟨N, i, j, by simp [hi, hj, Fin.ext_iff], ?_, h1, ?_, h2⟩
  · have hmem : ([] : List ((Fin N ⊕ OffDiag N) × List ℕ)) ∈
        iterAdmSet N (xiOf (2 * 1 + 3) (1 / 4)) 2 ⌈6 * 1 / (1 / 4 : ℝ)⌉₊ :=
      (mem_iterAdmSet _ _ _).2 ⟨by simp, trivial⟩
    have := Finset.single_le_sum (f := fun d => iterWeight N (1 / 4) d *
      4 ^ (d.map fun x => x.2.sum).sum) (fun d _ => iterateWeight_w4_nonneg N (1 / 4) d) hmem
    simpa [iterWeight] using this
  · set d : List ((Fin N ⊕ OffDiag N) × List ℕ) := [(Sum.inl i, [3, 0])] with hd
    have hmem : d ∈ (iterAdmSet N (xiOf (2 * 1 + 3) (1 / 4)) 2 ⌈6 * 1 / (1 / 4 : ℝ)⌉₊).filter
        (fun d => touchesData i j d) := by
      rw [Finset.mem_filter, mem_iterAdmSet]
      refine ⟨⟨by simp [hd], rfl, by simp [matchedOrder], by simpa using hξ,
        trivial⟩, by simp [hd, touchesData, touchesEntry, entryPairs]⟩
    have hpos : 0 < iterWeight N (1 / 4) d * 4 ^ (d.map fun x => x.2.sum).sum := by
      have hN0r : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      simp only [hd, iterWeight, entryWeight, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one]
      positivity
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun d => iterWeight N (1 / 4) d *
      4 ^ (d.map fun x => x.2.sum).sum) (fun d _ => iterateWeight_w4_nonneg N (1 / 4) d) hmem)

#print axioms iterWeight_sum_le

end WEdgeNS
