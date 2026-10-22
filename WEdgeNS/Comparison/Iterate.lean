import WEdgeNS.Comparison.ExpansionInv
import WEdgeNS.Comparison.Swap

/-!
# Iteration of the swaps
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

open private expansion_wordP_replicate_zero expansion_continuous_resS expansion_norm_integral_le
  expansion_eventually_le_phi expansion_eventually_log_le expansion_rpow_pow
  expansion_sum_highIdx expansion_mem_highIdx expansion_matchedPair_radLaws
  from WEdgeNS.Comparison.Expansion

/-! ### Formal sums: lengths, weights and admissible data -/

/-- `P_{γ,k}` applied to a word gives at most `2^{|k|}` words. -/
private lemma iterate_wordP_length_le {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    ∀ (k : List ℕ) (w : Word N), (wordP e k w).length ≤ 2 ^ k.sum
  | _, [] => by simpa [wordP] using Nat.one_le_two_pow
  | [], ℓ :: w => by simpa [wordP] using iterate_wordP_length_le e [] w
  | k :: ks, ℓ :: w => by
    simp only [wordP, List.length_flatMap, List.length_map, List.sum_cons]
    have h1 := (letterP_length_le e k ℓ).1
    have h2 := iterate_wordP_length_le e ks w
    have h3 := List.sum_le_length_nsmul
      ((letterP e k ℓ).map fun _ => (wordP e ks w).length) (2 ^ ks.sum) (by
        intro x hx
        obtain ⟨_, _, rfl⟩ := List.mem_map.1 hx
        exact h2)
    rw [List.length_map, smul_eq_mul] at h3
    calc _ ≤ _ := h3
      _ ≤ 2 ^ k * 2 ^ ks.sum := Nat.mul_le_mul_right _ h1
      _ = _ := by rw [pow_add]

/-- Every word of `P_{γ,k}` applied to a word of length `s` has length `s + |k|`. -/
private lemma iterate_mem_wordP_length {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    ∀ (k : List ℕ) (w : Word N), k.length = w.length →
      ∀ u ∈ wordP e k w, u.length = w.length + k.sum
  | [], [], _ => by simp [wordP]
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | k :: ks, ℓ :: w, h => by
    intro u hu
    simp only [wordP, List.mem_flatMap, List.mem_map] at hu
    obtain ⟨v, hv, u', hu', rfl⟩ := hu
    have h1 := (letterP_length_le e k ℓ).2 v hv
    have h2 := iterate_mem_wordP_length e ks w (by simpa using h) u' hu'
    simp only [List.length_append, h1, h2, List.length_cons, List.sum_cons]
    ring

/-- `P_{γ,k}` on a formal sum with nonnegative weights and words of length `s`: the weights stay
nonnegative, the words have length `s + |k|`, and the total weight grows by at most `2^{|k|}`. -/
private lemma iterate_opP_props {N : ℕ} (e : Fin N ⊕ OffDiag N) (k : List ℕ) {s : ℕ}
    (hk : k.length = s) : ∀ G : FSum N, (∀ cw ∈ G, 0 ≤ cw.1 ∧ cw.2.length = s) →
      (∀ cw ∈ opP e k G, 0 ≤ cw.1 ∧ cw.2.length = s + k.sum) ∧
        ((opP e k G).map Prod.fst).sum ≤ 2 ^ k.sum * (G.map Prod.fst).sum
  | [], _ => by simp [opP]
  | cw :: G, hG => by
    have ih := iterate_opP_props e k hk G fun x hx => hG x (List.mem_cons_of_mem _ hx)
    have hcw := hG cw List.mem_cons_self
    have hsplit : opP e k (cw :: G) = (wordP e k cw.2).map (fun w => (cw.1, w)) ++ opP e k G := by
      simp [opP]
    rw [hsplit]
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
        refine ⟨hcw.1, ?_⟩
        rw [iterate_mem_wordP_length e k cw.2 (by rw [hk, hcw.2]) u hu, hcw.2]
      · exact ih.1 x hx
    · have hl : (((wordP e k cw.2).map (fun w => (cw.1, w))).map Prod.fst).sum =
          (wordP e k cw.2).length * cw.1 := by
        simp [List.map_map, Function.comp_def]
      have hlen : ((wordP e k cw.2).length : ℝ) ≤ 2 ^ k.sum := by
        exact_mod_cast iterate_wordP_length_le e k cw.2
      rw [List.map_append, List.sum_append, hl, List.map_cons, List.sum_cons, mul_add]
      have := mul_le_mul_of_nonneg_right hlen hcw.1
      linarith [ih.2]

/-- The order `|d| = |k_1| + ⋯ + |k_n|` of the data `d`. -/
private def iterate_ord {N : ℕ} (d : List ((Fin N ⊕ OffDiag N) × List ℕ)) : ℕ :=
  (d.map fun x => x.2.sum).sum

/-- `P_{γ_n,k_n} ⋯ P_{γ_1,k_1}` on a formal sum with nonnegative weights and words of length `s`,
for admissible data: nonnegative weights, words of length `s + |d|`, total weight at most
`2^{|d|}` times the initial one. -/
private lemma iterate_iterP_props {N : ℕ} {ξ : ℕ} :
    ∀ (d : List ((Fin N ⊕ OffDiag N) × List ℕ)) (s : ℕ) (G : FSum N), IterAdm ξ s d →
      (∀ cw ∈ G, 0 ≤ cw.1 ∧ cw.2.length = s) →
      (∀ cw ∈ iterP d G, 0 ≤ cw.1 ∧ cw.2.length = s + iterate_ord d) ∧
        ((iterP d G).map Prod.fst).sum ≤ 2 ^ iterate_ord d * (G.map Prod.fst).sum
  | [], s, G, _, hG => by simpa [iterP, iterate_ord] using hG
  | x :: d, s, G, hd, hG => by
    obtain ⟨hl, -, -, hd'⟩ := hd
    have h1 := iterate_opP_props x.1 x.2 hl G hG
    have h2 := iterate_iterP_props d (s + x.2.sum) (opP x.1 x.2 G) hd' h1.1
    simp only [iterP, iterate_ord, List.map_cons, List.sum_cons] at h2 ⊢
    refine ⟨fun cw hcw => ⟨(h2.1 cw hcw).1, by rw [(h2.1 cw hcw).2]; ring⟩, ?_⟩
    calc _ ≤ _ := h2.2
      _ ≤ 2 ^ (d.map fun x => x.2.sum).sum * (2 ^ x.2.sum * (G.map Prod.fst).sum) :=
          mul_le_mul_of_nonneg_left h1.2 (by positivity)
      _ = _ := by rw [pow_add]; ring

/-- Admissible data of length `n` have order at most `n ξ`. -/
private lemma iterate_ord_le {N : ℕ} {ξ : ℕ} :
    ∀ (d : List ((Fin N ⊕ OffDiag N) × List ℕ)) (s : ℕ), IterAdm ξ s d →
      iterate_ord d ≤ d.length * ξ
  | [], _, _ => by simp [iterate_ord]
  | x :: d, s, hd => by
    obtain ⟨-, -, hx, hd'⟩ := hd
    have := iterate_ord_le d (s + x.2.sum) hd'
    simp only [iterate_ord, List.map_cons, List.sum_cons, List.length_cons] at this ⊢
    nlinarith

/-- Appending one operator to the data acts last. -/
private lemma iterate_iterP_append {N : ℕ} (x : (Fin N ⊕ OffDiag N) × List ℕ) :
    ∀ (d : List ((Fin N ⊕ OffDiag N) × List ℕ)) (G : FSum N),
      iterP (d ++ [x]) G = opP x.1 x.2 (iterP d G)
  | [], G => by simp [iterP]
  | y :: d, G => by simp [iterP, iterate_iterP_append x d]

/-- Appending one admissible operator keeps the data admissible. -/
private lemma iterate_iterAdm_append {N : ℕ} {ξ : ℕ} (x : (Fin N ⊕ OffDiag N) × List ℕ) :
    ∀ (d : List ((Fin N ⊕ OffDiag N) × List ℕ)) (s : ℕ), IterAdm ξ s d →
      x.2.length = s + iterate_ord d → matchedOrder x.1 < x.2.sum → x.2.sum ≤ ξ →
      IterAdm ξ s (d ++ [x])
  | [], s, _, h1, h2, h3 => by simpa [IterAdm, iterate_ord] using ⟨h1, h2, h3⟩
  | y :: d, s, hd, h1, h2, h3 => by
    obtain ⟨hy1, hy2, hy3, hd'⟩ := hd
    refine ⟨hy1, hy2, hy3, iterate_iterAdm_append x d (s + y.2.sum) hd' ?_ h2 h3⟩
    rw [h1]
    simp only [iterate_ord, List.map_cons, List.sum_cons]
    ring

private lemma iterate_cast_ord {N : ℕ} (d : List ((Fin N ⊕ OffDiag N) × List ℕ)) :
    (d.map fun x => ((x.2.sum : ℕ) : ℝ)).sum = (iterate_ord d : ℝ) := by
  simp [iterate_ord, Nat.cast_list_sum, List.map_map, Function.comp_def]

private lemma iterate_ord_append {N : ℕ} (d : List ((Fin N ⊕ OffDiag N) × List ℕ))
    (x : (Fin N ⊕ OffDiag N) × List ℕ) : iterate_ord (d ++ [x]) = iterate_ord d + x.2.sum := by
  simp [iterate_ord]

/-! ### Expectations of formal sums -/

/-- `P_{γ,0}` leaves a word unchanged. -/
private lemma iterate_evalW_singleton {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ)
    (e : Fin N ⊕ OffDiag N) (w : Word N) :
    evalW G m (wordP e (List.replicate w.length 0) w) = evalWord G m w := by
  rw [expansion_wordP_replicate_zero]
  simp [evalW]

/-- Every word in `S` is integrable (its letters are continuous and at most `1/η + 1`). -/
private lemma iterate_integrable_evalWord {N : ℕ} {μ : Measure (Entries N)} [IsFiniteMeasure μ]
    {z : ℂ} (hz : 0 < z.im) (e : Fin N ⊕ OffDiag N) (w : Word N) :
    Integrable (fun ω => evalWord (resS z ω) (msc z) w) μ := by
  have hc : Continuous fun ω : Entries N => evalWord (resS z ω) (msc z) w := by
    have := expansion_continuous_resS (N := N) hz.ne' (msc z) [w]
    simpa [evalW] using this
  refine Integrable.of_bound hc.aestronglyMeasurable (2 ^ 0 * (1 / z.im + 1) ^ w.length)
    (Eventually.of_forall fun ω => ?_)
  have h := norm_evalW_wordP_le_of_le (G := resS z ω) (m := msc z) (B := 1 / z.im)
    (fun i j => norm_resolventC_apply_le (symOfEntries_isHermitian ω) hz i j)
    (norm_msc_eq_inv_and_lt_one hz).2.le e (List.replicate w.length 0) w (by simp)
  rw [iterate_evalW_singleton] at h
  simpa using h

private lemma iterate_integrable_evalW {N : ℕ} {μ : Measure (Entries N)} [IsFiniteMeasure μ]
    {z : ℂ} (hz : 0 < z.im) (e : Fin N ⊕ OffDiag N) :
    ∀ ws : List (Word N), Integrable (fun ω => evalW (resS z ω) (msc z) ws) μ
  | [] => by simp [evalW]
  | w :: ws => by
    simpa [evalW, Pi.add_def] using (iterate_integrable_evalWord hz e w).add
      (iterate_integrable_evalW hz e ws)

private lemma iterate_integrable_evalF {N : ℕ} {μ : Measure (Entries N)} [IsFiniteMeasure μ]
    {z : ℂ} (hz : 0 < z.im) (e : Fin N ⊕ OffDiag N) :
    ∀ G : FSum N, Integrable (fun ω => evalF (resS z ω) (msc z) G) μ
  | [] => by simp [evalF]
  | cw :: G => by
    simpa [evalF, Pi.add_def] using
      ((iterate_integrable_evalWord hz e cw.2).const_mul (cw.1 : ℂ)).add
        (iterate_integrable_evalF hz e G)

private lemma iterate_integral_evalF_cons {N : ℕ} {μ : Measure (Entries N)} [IsFiniteMeasure μ]
    {z : ℂ} (hz : 0 < z.im) (e : Fin N ⊕ OffDiag N) (cw : ℝ × Word N) (G : FSum N) :
    ∫ ω, evalF (resS z ω) (msc z) (cw :: G) ∂μ =
      (cw.1 : ℂ) * (∫ ω, evalWord (resS z ω) (msc z) cw.2 ∂μ) +
        ∫ ω, evalF (resS z ω) (msc z) G ∂μ := by
  have h : ∀ ω, evalF (resS z ω) (msc z) (cw :: G) =
      (cw.1 : ℂ) * evalWord (resS z ω) (msc z) cw.2 + evalF (resS z ω) (msc z) G := by
    intro ω; simp [evalF]
  simp_rw [h]
  rw [integral_add ((iterate_integrable_evalWord hz e cw.2).const_mul _)
    (iterate_integrable_evalF hz e G), integral_const_mul]

private lemma iterate_integral_evalF_opP_cons {N : ℕ} {μ : Measure (Entries N)}
    [IsFiniteMeasure μ] {z : ℂ} (hz : 0 < z.im) (e : Fin N ⊕ OffDiag N) (k : List ℕ)
    (cw : ℝ × Word N) (G : FSum N) :
    ∫ ω, evalF (resS z ω) (msc z) (opP e k (cw :: G)) ∂μ =
      (cw.1 : ℂ) * (∫ ω, evalW (resS z ω) (msc z) (wordP e k cw.2) ∂μ) +
        ∫ ω, evalF (resS z ω) (msc z) (opP e k G) ∂μ := by
  have h : ∀ ω, evalF (resS z ω) (msc z) (opP e k (cw :: G)) =
      (cw.1 : ℂ) * evalW (resS z ω) (msc z) (wordP e k cw.2) +
        evalF (resS z ω) (msc z) (opP e k G) := by
    intro ω
    simp [evalF, evalW, opP, List.map_map, Function.comp_def, List.sum_map_mul_left]
  simp_rw [h]
  rw [integral_add ((iterate_integrable_evalW hz e _).const_mul _)
    (iterate_integrable_evalF hz e _), integral_const_mul]

/-- One swap for a formal sum (6.28) with (6.36): if every word of length `s` satisfies the swap
identity up to `ε`, then a formal sum with nonnegative weights of such words satisfies it up to
`ε Σ f`, and the difference of its expectations is bounded by the `P_{γ,α}` images. -/
private lemma iterate_swap_sum {N : ℕ} {μ₀ μ₁ : Measure (Entries N)} [IsFiniteMeasure μ₀]
    [IsFiniteMeasure μ₁] {z : ℂ} (hz : 0 < z.im) (e : Fin N ⊕ OffDiag N) {s : ℕ}
    (H : Finset (Fin s → ℕ)) (A₀ A₁ : (Fin s → ℕ) → ℝ) {ε : ℝ}
    (hw : ∀ w : Word N, w.length = s →
      ‖(∫ ω, evalWord (resS z ω) (msc z) w ∂μ₀) - (∫ ω, evalWord (resS z ω) (msc z) w ∂μ₁)
        - ∑ α ∈ H, ((A₀ α : ℂ) * ∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) w) ∂μ₀
          - (A₁ α : ℂ) * ∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) w) ∂μ₁)‖ ≤ ε)
    (G : FSum N) (hG : ∀ cw ∈ G, 0 ≤ cw.1 ∧ cw.2.length = s) :
    ‖(∫ ω, evalF (resS z ω) (msc z) G ∂μ₀) - (∫ ω, evalF (resS z ω) (msc z) G ∂μ₁)‖ ≤
      ∑ α ∈ H, (|A₀ α| * ‖∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) G) ∂μ₀‖ +
        |A₁ α| * ‖∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) G) ∂μ₁‖) +
      (G.map Prod.fst).sum * ε := by
  have hD : ∀ G : FSum N, (∀ cw ∈ G, 0 ≤ cw.1 ∧ cw.2.length = s) →
      ‖(∫ ω, evalF (resS z ω) (msc z) G ∂μ₀) - (∫ ω, evalF (resS z ω) (msc z) G ∂μ₁)
        - ∑ α ∈ H, ((A₀ α : ℂ) * ∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) G) ∂μ₀
          - (A₁ α : ℂ) * ∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) G) ∂μ₁)‖ ≤
        (G.map Prod.fst).sum * ε := by
    intro G
    induction G with
    | nil => intro _; simp [evalF, opP]
    | cons cw G ih =>
      intro hG
      have hcw := hG cw List.mem_cons_self
      have ih' := ih fun x hx => hG x (List.mem_cons_of_mem _ hx)
      simp only [iterate_integral_evalF_cons hz e, iterate_integral_evalF_opP_cons hz e]
      set X₀ := ∫ ω, evalWord (resS z ω) (msc z) cw.2 ∂μ₀
      set X₁ := ∫ ω, evalWord (resS z ω) (msc z) cw.2 ∂μ₁
      set Y₀ := ∫ ω, evalF (resS z ω) (msc z) G ∂μ₀
      set Y₁ := ∫ ω, evalF (resS z ω) (msc z) G ∂μ₁
      have hsum : ∑ α ∈ H, ((A₀ α : ℂ) * ((cw.1 : ℂ) *
            (∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) cw.2) ∂μ₀) +
            ∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) G) ∂μ₀) -
          (A₁ α : ℂ) * ((cw.1 : ℂ) *
            (∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) cw.2) ∂μ₁) +
            ∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) G) ∂μ₁)) =
          (cw.1 : ℂ) * ∑ α ∈ H, ((A₀ α : ℂ) *
            (∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) cw.2) ∂μ₀) -
            (A₁ α : ℂ) * ∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) cw.2) ∂μ₁) +
          ∑ α ∈ H, ((A₀ α : ℂ) *
            (∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) G) ∂μ₀) -
            (A₁ α : ℂ) * ∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) G) ∂μ₁) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun α _ => by ring
      rw [hsum]
      set S₁ := ∑ α ∈ H, ((A₀ α : ℂ) *
            (∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) cw.2) ∂μ₀) -
            (A₁ α : ℂ) * ∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) cw.2) ∂μ₁)
      set S₂ := ∑ α ∈ H, ((A₀ α : ℂ) *
            (∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) G) ∂μ₀) -
            (A₁ α : ℂ) * ∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) G) ∂μ₁)
      have hid : (cw.1 : ℂ) * X₀ + Y₀ - ((cw.1 : ℂ) * X₁ + Y₁) - ((cw.1 : ℂ) * S₁ + S₂) =
          (cw.1 : ℂ) * (X₀ - X₁ - S₁) + (Y₀ - Y₁ - S₂) := by ring
      rw [hid]
      have h1 : ‖(cw.1 : ℂ) * (X₀ - X₁ - S₁)‖ ≤ cw.1 * ε := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcw.1]
        exact mul_le_mul_of_nonneg_left (hw cw.2 hcw.2) hcw.1
      calc _ ≤ ‖(cw.1 : ℂ) * (X₀ - X₁ - S₁)‖ + ‖Y₀ - Y₁ - S₂‖ := norm_add_le _ _
        _ ≤ cw.1 * ε + (G.map Prod.fst).sum * ε := add_le_add h1 ih'
        _ = _ := by simp only [List.map_cons, List.sum_cons]; ring
  set S := ∑ α ∈ H, ((A₀ α : ℂ) * ∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) G) ∂μ₀
          - (A₁ α : ℂ) * ∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) G) ∂μ₁)
  have hS : ‖S‖ ≤ ∑ α ∈ H, (|A₀ α| *
      ‖∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) G) ∂μ₀‖ +
        |A₁ α| * ‖∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) G) ∂μ₁‖) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    refine (norm_sub_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, le_refl]
  have h := hD G hG
  calc _ = ‖S + ((∫ ω, evalF (resS z ω) (msc z) G ∂μ₀) - (∫ ω, evalF (resS z ω) (msc z) G ∂μ₁)
        - S)‖ := by ring_nf
    _ ≤ ‖S‖ + _ := norm_add_le _ _
    _ ≤ _ := add_le_add hS h

/-- The expectation of a formal sum with nonnegative weights of words of length `s` is at most
`Σ f` times a bound for the expectations of the words. -/
private lemma iterate_norm_integral_evalF_le {N : ℕ} {μ : Measure (Entries N)} [IsFiniteMeasure μ]
    {z : ℂ} (hz : 0 < z.im) (e : Fin N ⊕ OffDiag N) {s : ℕ} {K : ℝ}
    (hK : ∀ w : Word N, w.length = s → ‖∫ ω, evalWord (resS z ω) (msc z) w ∂μ‖ ≤ K) :
    ∀ G : FSum N, (∀ cw ∈ G, 0 ≤ cw.1 ∧ cw.2.length = s) →
      ‖∫ ω, evalF (resS z ω) (msc z) G ∂μ‖ ≤ (G.map Prod.fst).sum * K
  | [], _ => by simp [evalF]
  | cw :: G, hG => by
    have hcw := hG cw List.mem_cons_self
    have ih := iterate_norm_integral_evalF_le hz e hK G fun x hx => hG x (List.mem_cons_of_mem _ hx)
    rw [iterate_integral_evalF_cons hz e]
    have h1 : ‖(cw.1 : ℂ) * ∫ ω, evalWord (resS z ω) (msc z) cw.2 ∂μ‖ ≤ cw.1 * K := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcw.1]
      exact mul_le_mul_of_nonneg_left (hK cw.2 hcw.2) hcw.1
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ cw.1 * K + (G.map Prod.fst).sum * K := add_le_add h1 ih
      _ = _ := by simp only [List.map_cons, List.sum_cons]; ring

/-- The expectation of one word of length `s` in `S` on `S(C0)`: at most `4^{s+1}` on the good
event (6.1), and at most `(N + 1)^s` off it (since `1/η ≤ N`). -/
private lemma iterate_norm_integral_evalWord_le {N : ℕ} {μ : Measure (Entries N)}
    [IsProbabilityMeasure μ] {C0 : ℝ} {z : ℂ} (hz : z ∈ specDomain N C0) (hzim : 0 < z.im)
    (hB : 1 / z.im ≤ N) (e : Fin N ⊕ OffDiag N) (w : Word N) :
    ‖∫ ω, evalWord (resS z ω) (msc z) w ∂μ‖ ≤
      4 ^ (w.length + 1) + ((N : ℝ) + 1) ^ w.length * (μ (goodEvent N C0)ᶜ).toReal := by
  refine expansion_norm_integral_le (by positivity) (Eventually.of_forall fun ω hω => ?_)
    (Eventually.of_forall fun ω => ?_)
  · have h := (norm_evalW_wordP_le_of_good hω hz e e (List.replicate w.length 0) w (by simp)).1
    rw [iterate_evalW_singleton] at h
    simpa using h
  · have h := norm_evalW_wordP_le_of_le (G := resS z ω) (m := msc z) (B := N)
      (fun i j => (norm_resolventC_apply_le (symOfEntries_isHermitian ω) hzim i j).trans hB)
      (norm_msc_eq_inv_and_lt_one hzim).2.le e (List.replicate w.length 0) w (by simp)
    rw [iterate_evalW_singleton] at h
    simpa using h

/-- The telescoping (6.4) up to `γ`: `|f(H_γ)| ≤ |f(H_0)| + Σ_e |f(H_{γ(e)}) - f(H_{γ(e)-1})|`. -/
private lemma iterate_telescope {N : ℕ} (Lv Lw : EntryLaws N) (f : EntryLaws N → ℂ) (γ : ℕ) :
    ‖f (interp (lexPos N) γ Lv Lw)‖ ≤ ‖f (interp (lexPos N) 0 Lv Lw)‖ +
      ∑ e : Fin N ⊕ OffDiag N, ‖f (interp (lexPos N) (lexPos N e) Lv Lw) -
        f (interp (lexPos N) (lexPos N e - 1) Lv Lw)‖ := by
  have hmin : interp (lexPos N) (min (N * (N + 1) / 2) γ) Lv Lw = interp (lexPos N) γ Lv Lw := by
    have h : ∀ e, (lexPos N e ≤ min (N * (N + 1) / 2) γ ↔ lexPos N e ≤ γ) := fun e => by
      rw [le_min_iff]
      exact ⟨fun h => h.2, fun h => ⟨(lexPos_mem_Icc N e).2, h⟩⟩
    simp only [interp, h]
  set g : ℕ → ℂ := fun γ' => f (interp (lexPos N) (min γ' γ) Lv Lw) with hg
  have htel := sub_eq_sum_lexPos (N := N) g
  have hg0 : g 0 = f (interp (lexPos N) 0 Lv Lw) := by simp [hg]
  have hgt : g (N * (N + 1) / 2) = f (interp (lexPos N) γ Lv Lw) := by simp only [hg, hmin]
  rw [hg0, hgt, sub_eq_iff_eq_add] at htel
  rw [htel]
  refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun e _ => ?_)) le_rfl) |>.trans (by rw [add_comm])
  by_cases he : lexPos N e ≤ γ
  · have h1 : min (lexPos N e) γ = lexPos N e := min_eq_left he
    have h2 : min (lexPos N e - 1) γ = lexPos N e - 1 := min_eq_left (by omega)
    simp only [hg, h1, h2, le_refl]
  · have h1 : min (lexPos N e) γ = γ := min_eq_right (by omega)
    have h2 : min (lexPos N e - 1) γ = γ := min_eq_right (by omega)
    simp only [hg, h1, h2, sub_self, norm_zero]
    exact norm_nonneg _

/-! ### The sums over the swaps -/

/-- With the count (6.54): `Σ_{α ∈ ℕ^s, m0 < |α| ≤ ξ} y^{|α|} ≤ 2 (t y)^{m0+1}` when `s ≤ t`
and `t y ≤ 1/2`. -/
private lemma iterate_sum_highIdx_le (s m0 ξ : ℕ) {y t : ℝ} (hy : 0 ≤ y) (ht : (s : ℝ) ≤ t)
    (hty : t * y ≤ 1 / 2) :
    ∑ α ∈ highIdx s m0 ξ, y ^ (∑ i, α i) ≤ 2 * (t * y) ^ (m0 + 1) := by
  rw [expansion_sum_highIdx]
  have ht0 : 0 ≤ t := (Nat.cast_nonneg s).trans ht
  have hty0 : 0 ≤ t * y := mul_nonneg ht0 hy
  calc ∑ k ∈ Finset.Icc (m0 + 1) ξ, ∑ α ∈ Finset.Nat.antidiagonalTuple s k, y ^ (∑ i, α i)
      = ∑ k ∈ Finset.Icc (m0 + 1) ξ, ((Finset.Nat.antidiagonalTuple s k).card : ℝ) * y ^ k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_congr rfl fun α hα => by rw [Finset.Nat.mem_antidiagonalTuple.1 hα],
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ Finset.Icc (m0 + 1) ξ, (t * y) ^ k := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [mul_pow]
        gcongr
        calc ((Finset.Nat.antidiagonalTuple s k).card : ℝ) ≤ (s : ℝ) ^ k := by
              exact_mod_cast card_antidiagonalTuple_le s k
          _ ≤ t ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _) ht k
    _ = ∑ k ∈ Finset.Ico (m0 + 1) (ξ + 1), (t * y) ^ k := by
        rw [Finset.Ico_add_one_right_eq_Icc]
    _ ≤ (t * y) ^ (m0 + 1) / (1 - t * y) := geom_sum_Ico_le_of_lt_one hty0 (by linarith)
    _ ≤ _ := by
        rw [div_le_iff₀ (by linarith)]
        have := pow_nonneg hty0 (m0 + 1)
        nlinarith

/-- The total coefficient of one step of (6.31)–(6.33), weighted by `N^{(φq/20)|α|}`: over all
`N(N+1)/2` entries and all `α` with `matchedOrder e < |α| ≤ ξ`, with `|A_α| ≤ coeffBound`
((6.22) and its diagonal analogue), it is at most `N^{-φq/5}` once `8 t^5 ≤ N^{φq/20}`, `s ≤ t`. -/
private lemma iterate_theta_le {N : ℕ} (hN : 1 ≤ N) {φq : ℝ} (s ξ : ℕ) {t : ℝ}
    (ht1 : 1 ≤ t) (hts : (s : ℝ) ≤ t) (ht : 8 * t ^ 5 ≤ (N : ℝ) ^ (φq / 20))
    (c : (Fin N ⊕ OffDiag N) → (Fin s → ℕ) → ℝ)
    (hc : ∀ e α, c e α ≤ 2 * coeffBound N φq e (∑ i, α i)) :
    ∑ e : Fin N ⊕ OffDiag N, ∑ α ∈ highIdx s (matchedOrder e) ξ,
      c e α * ((N : ℝ) ^ (φq / 20)) ^ (∑ i, α i) ≤ (N : ℝ) ^ (-(φq / 5)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set ρ := (N : ℝ) ^ (φq / 20) with hρ
  set x := (N : ℝ) ^ (-(φq / 20)) with hx
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hN0 _
  have hx0 : 0 < x := Real.rpow_pos_of_pos hN0 _
  have hxρ : x * ρ = 1 := by
    rw [hx, hρ, ← Real.rpow_add hN0, neg_add_cancel, Real.rpow_zero]
  have h8 : 8 * t ^ 5 * x ≤ 1 := by
    calc 8 * t ^ 5 * x ≤ ρ * x := mul_le_mul_of_nonneg_right ht hx0.le
      _ = 1 := by rw [mul_comm]; exact hxρ
  have ht5 : t ≤ t ^ 5 := by
    calc t = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ 5 := pow_le_pow_right₀ ht1 (by norm_num)
  have ht3 : t ^ 3 ≤ t ^ 5 := pow_le_pow_right₀ ht1 (by norm_num)
  have htx : t * x ≤ 1 / 8 := by nlinarith
  have hx1 : x ≤ 1 := by
    have : x ≤ t * x := le_mul_of_one_le_left hx0.le ht1
    linarith
  have hx4 : (N : ℝ) ^ (-(φq / 5)) = x ^ 4 := by
    rw [hx, expansion_rpow_pow hN0.le]
    congr 1
    push_cast
    ring
  -- the weighted coefficient bounds
  have hdiag : ∀ (i : Fin N) (m : ℕ),
      2 * coeffBound N φq (Sum.inl i) m * ρ ^ m = 2 * (N : ℝ)⁻¹ * (x ^ 4) ^ m := by
    intro i m
    simp only [coeffBound]
    rw [hρ, hx, ← pow_mul, expansion_rpow_pow hN0.le, expansion_rpow_pow hN0.le, mul_assoc,
      ← Real.rpow_add hN0, mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add hN0]
    congr 2
    push_cast
    ring
  have hoff : ∀ (p : OffDiag N) (m : ℕ),
      2 * coeffBound N φq (Sum.inr p) m * ρ ^ m = 2 * ((N : ℝ) ^ 2)⁻¹ * x ^ m := by
    intro p m
    simp only [coeffBound]
    rw [hρ, hx, expansion_rpow_pow hN0.le, expansion_rpow_pow hN0.le, mul_assoc,
      ← Real.rpow_add hN0, mul_assoc, ← Real.rpow_natCast, ← Real.rpow_neg hN0.le,
      ← Real.rpow_add hN0]
    congr 2
    push_cast
    ring
  have hterm : ∀ e α, c e α * ρ ^ (∑ i, α i) ≤ 2 * coeffBound N φq e (∑ i, α i) * ρ ^ (∑ i, α i) :=
    fun e α => mul_le_mul_of_nonneg_right (hc e α) (pow_nonneg hρ0.le _)
  rw [Fintype.sum_sum_type]
  have hA : ∑ i : Fin N, ∑ α ∈ highIdx s (matchedOrder (Sum.inl i : Fin N ⊕ OffDiag N)) ξ,
      c (Sum.inl i) α * ρ ^ (∑ j, α j) ≤ 4 * (t * x ^ 4) ^ 3 := by
    have h1 : ∀ i : Fin N, ∑ α ∈ highIdx s (matchedOrder (Sum.inl i : Fin N ⊕ OffDiag N)) ξ,
        c (Sum.inl i) α * ρ ^ (∑ j, α j) ≤ (N : ℝ)⁻¹ * (4 * (t * x ^ 4) ^ 3) := by
      intro i
      calc _ ≤ ∑ α ∈ highIdx s 2 ξ, 2 * (N : ℝ)⁻¹ * (x ^ 4) ^ (∑ j, α j) :=
            Finset.sum_le_sum fun α _ => (hterm _ α).trans_eq (hdiag i _)
        _ = 2 * (N : ℝ)⁻¹ * ∑ α ∈ highIdx s 2 ξ, (x ^ 4) ^ (∑ j, α j) := by
            rw [Finset.mul_sum]
        _ ≤ 2 * (N : ℝ)⁻¹ * (2 * (t * x ^ 4) ^ (2 + 1)) := by
            gcongr
            refine iterate_sum_highIdx_le s 2 ξ (by positivity) hts ?_
            have : x ^ 4 ≤ x := by
              calc x ^ 4 ≤ x ^ 1 := pow_le_pow_of_le_one hx0.le hx1 (by norm_num)
                _ = x := pow_one x
            nlinarith
        _ = _ := by ring
    calc _ ≤ ∑ i : Fin N, (N : ℝ)⁻¹ * (4 * (t * x ^ 4) ^ 3) := Finset.sum_le_sum fun i _ => h1 i
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
            mul_inv_cancel₀ hN0.ne', one_mul]
  have hB : ∑ p : OffDiag N, ∑ α ∈ highIdx s (matchedOrder (Sum.inr p : Fin N ⊕ OffDiag N)) ξ,
      c (Sum.inr p) α * ρ ^ (∑ j, α j) ≤ 4 * (t * x) ^ 5 := by
    have h1 : ∀ p : OffDiag N, ∑ α ∈ highIdx s (matchedOrder (Sum.inr p : Fin N ⊕ OffDiag N)) ξ,
        c (Sum.inr p) α * ρ ^ (∑ j, α j) ≤ ((N : ℝ) ^ 2)⁻¹ * (4 * (t * x) ^ 5) := by
      intro p
      calc _ ≤ ∑ α ∈ highIdx s 4 ξ, 2 * ((N : ℝ) ^ 2)⁻¹ * x ^ (∑ j, α j) :=
            Finset.sum_le_sum fun α _ => (hterm _ α).trans_eq (hoff p _)
        _ = 2 * ((N : ℝ) ^ 2)⁻¹ * ∑ α ∈ highIdx s 4 ξ, x ^ (∑ j, α j) := by
            rw [Finset.mul_sum]
        _ ≤ 2 * ((N : ℝ) ^ 2)⁻¹ * (2 * (t * x) ^ (4 + 1)) := by
            gcongr
            exact iterate_sum_highIdx_le s 4 ξ hx0.le hts (by linarith)
        _ = _ := by ring
    have hcard : (Fintype.card (OffDiag N) : ℝ) ≤ (N : ℝ) ^ 2 := by
      have := Fintype.card_subtype_le (fun p : Fin N × Fin N => p.1 < p.2)
      rw [Fintype.card_prod, Fintype.card_fin] at this
      rw [sq]
      exact_mod_cast this
    calc _ ≤ ∑ p : OffDiag N, ((N : ℝ) ^ 2)⁻¹ * (4 * (t * x) ^ 5) :=
          Finset.sum_le_sum fun p _ => h1 p
      _ = (Fintype.card (OffDiag N) : ℝ) * ((N : ℝ) ^ 2)⁻¹ * (4 * (t * x) ^ 5) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
      _ ≤ (N : ℝ) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * (4 * (t * x) ^ 5) := by gcongr
      _ = _ := by rw [mul_inv_cancel₀ (by positivity), one_mul]
  rw [hx4]
  have hx12 : x ^ 12 ≤ x ^ 5 := pow_le_pow_of_le_one hx0.le hx1 (by norm_num)
  have e1 : 4 * (t * x ^ 4) ^ 3 = 4 * t ^ 3 * x ^ 12 := by ring
  have e2 : 4 * (t * x) ^ 5 = (4 * t ^ 5 * x) * x ^ 4 := by ring
  have h3 : 4 * t ^ 3 * x ^ 12 ≤ 4 * t ^ 5 * x ^ 5 := by
    have := mul_le_mul ht3 hx12 (by positivity) (by positivity)
    nlinarith
  have h4 : (4 * t ^ 5 * x) * x ^ 4 ≤ 1 / 2 * x ^ 4 :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have e3 : 4 * t ^ 5 * x ^ 5 = (4 * t ^ 5 * x) * x ^ 4 := by ring
  linarith [hA, hB]

/-! ### Exponent bookkeeping -/

/-- `|Fin N ⊕ OffDiag N| ≤ 2 N²`. -/
private lemma iterate_card_entries_le (N : ℕ) :
    (Fintype.card (Fin N ⊕ OffDiag N) : ℝ) ≤ 2 * (N : ℝ) ^ 2 := by
  have h := Fintype.card_subtype_le (fun p : Fin N × Fin N => p.1 < p.2)
  rw [Fintype.card_prod, Fintype.card_fin] at h
  rw [Fintype.card_sum, Fintype.card_fin]
  have h' : ((Fintype.card (OffDiag N) : ℕ) : ℝ) ≤ (N : ℝ) * N := by exact_mod_cast h
  have h'' : (N : ℝ) ≤ (N : ℝ) * N := by exact_mod_cast Nat.le_mul_self N
  push_cast
  nlinarith

/-- Off the good event: `(N + 1)^s N^{C'} e^{-c φ³} ≤ 1` for `s ≤ K φ²` once
`((2K + C')/c) log N ≤ φ`. -/
private lemma iterate_bad_le {N : ℕ} (hN : 2 ≤ N) {s : ℕ} {K c : ℝ} {C' : ℕ} {P : ℝ}
    (hc : 0 < c) (hs : (s : ℝ) ≤ K * phi N ^ 2) (hφ1 : 1 ≤ phi N)
    (hD : (2 * K + C') / c * Real.log N ≤ phi N)
    (hP : P ≤ (N : ℝ) ^ C' * Real.exp (-c * phi N ^ 3)) (hP0 : 0 ≤ P) :
    ((N : ℝ) + 1) ^ s * P ≤ 1 := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have h1 : ((N : ℝ) + 1) ^ s ≤ (N : ℝ) ^ (2 * s) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) _
  have hpow : ∀ n : ℕ, (N : ℝ) ^ n = Real.exp (n * Real.log N) := fun n => by
    rw [← Real.exp_log hN0, ← Real.exp_nat_mul, Real.exp_log hN0]
  have hexp : ((2 * s + C' : ℕ) : ℝ) * Real.log N ≤ c * phi N ^ 3 := by
    have hφ2 : 1 ≤ phi N ^ 2 := one_le_pow₀ hφ1
    have hC0 : (0 : ℝ) ≤ C' := Nat.cast_nonneg _
    have h2 : ((2 * s + C' : ℕ) : ℝ) ≤ (2 * K + C') * phi N ^ 2 := by push_cast; nlinarith
    have h3 : (2 * K + C') * Real.log N ≤ c * phi N := by
      have := mul_le_mul_of_nonneg_left hD hc.le
      rwa [← mul_assoc, mul_div_cancel₀ _ hc.ne'] at this
    calc ((2 * s + C' : ℕ) : ℝ) * Real.log N ≤ (2 * K + C') * phi N ^ 2 * Real.log N :=
          mul_le_mul_of_nonneg_right h2 hlog0
      _ = phi N ^ 2 * ((2 * K + C') * Real.log N) := by ring
      _ ≤ phi N ^ 2 * (c * phi N) := by gcongr
      _ = c * phi N ^ 3 := by ring
  calc ((N : ℝ) + 1) ^ s * P ≤ (N : ℝ) ^ (2 * s) * ((N : ℝ) ^ C' * Real.exp (-c * phi N ^ 3)) :=
        mul_le_mul h1 hP hP0 (by positivity)
    _ = Real.exp (((2 * s + C' : ℕ) : ℝ) * Real.log N - c * phi N ^ 3) := by
        rw [← mul_assoc, ← pow_add, hpow, ← Real.exp_add]
        congr 1
        ring
    _ ≤ 1 := Real.exp_le_one_iff.2 (by linarith)

/-- The word lengths of the iteration: `s + ⌈6ζ/φq⌉ ⌈2(2ζ+3)/φq⌉ ≤ (K_s + (6/φq + 1)(10/φq + 1)) φ²`
for `1 ≤ ζ ≤ φ` and `s ≤ K_s ζ`. -/
private lemma iterate_len_le {φq ζ Ks ϕ : ℝ} (hφq : 0 < φq) (hKs : 0 < Ks) (hζ1 : 1 ≤ ζ)
    (hζ : ζ ≤ ϕ) {s : ℕ} (hs : (s : ℝ) ≤ Ks * ζ) :
    (s : ℝ) + (⌈6 * ζ / φq⌉₊ : ℝ) * (xiOf (2 * ζ + 3) φq : ℝ) ≤
      (Ks + (6 / φq + 1) * (10 / φq + 1)) * ϕ ^ 2 := by
  have hϕ1 : 1 ≤ ϕ := hζ1.trans hζ
  have hn : (⌈6 * ζ / φq⌉₊ : ℝ) ≤ (6 / φq + 1) * ϕ := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 6 * ζ / φq)
    have h2 : 6 * ζ / φq ≤ 6 / φq * ϕ := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hφq]; linarith
    nlinarith
  have hξ : (xiOf (2 * ζ + 3) φq : ℝ) ≤ (10 / φq + 1) * ϕ := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 * (2 * ζ + 3) / φq)
    have h2 : 2 * (2 * ζ + 3) / φq ≤ 10 / φq * ϕ := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hφq]; linarith
    unfold xiOf
    nlinarith
  have h1 : (⌈6 * ζ / φq⌉₊ : ℝ) * (xiOf (2 * ζ + 3) φq : ℝ) ≤
      (6 / φq + 1) * ϕ * ((10 / φq + 1) * ϕ) :=
    mul_le_mul hn hξ (Nat.cast_nonneg _) (by positivity)
  have h2 : (s : ℝ) ≤ Ks * ϕ ^ 2 := by
    have : ϕ ≤ ϕ ^ 2 := by nlinarith
    nlinarith
  nlinarith

/-- The final count: `(N^{-φq/5})^n 8·4^s + 8 N² 4^s N^{-(2ζ+3)} ≤ N^{-ζ}` for `n ≥ 6ζ/φq`,
`s ≤ K_s ζ`, `1 ≤ ζ` and `16·4^{K_s} ≤ N^{1/5}`. -/
private lemma iterate_final_le {N : ℕ} (hN : 1 ≤ N) {φq ζ Ks : ℝ} (hφq : 0 < φq) (hζ : 1 ≤ ζ)
    {s n : ℕ} (hs : (s : ℝ) ≤ Ks * ζ) (hn : 6 * ζ / φq ≤ n)
    (hK : 16 * (4 : ℝ) ^ Ks ≤ (N : ℝ) ^ (1 / 5 : ℝ)) :
    ((N : ℝ) ^ (-(φq / 5))) ^ n * (8 * 4 ^ s) +
        2 * (4 * (N : ℝ) ^ 2 * 4 ^ s * (N : ℝ) ^ (-(2 * ζ + 3))) ≤ (N : ℝ) ^ (-ζ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hY0 : (0 : ℝ) < 4 ^ s := by positivity
  have h1 : ((N : ℝ) ^ (-(φq / 5))) ^ n ≤ (N : ℝ) ^ (-(6 * ζ / 5)) := by
    rw [expansion_rpow_pow hN0.le]
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    rw [div_le_iff₀ hφq] at hn
    nlinarith
  have h2 : (N : ℝ) ^ 2 * (N : ℝ) ^ (-(2 * ζ + 3)) ≤ (N : ℝ) ^ (-(6 * ζ / 5)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hN0]
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    push_cast
    linarith
  have h3 : 16 * (4 : ℝ) ^ s ≤ (N : ℝ) ^ (ζ / 5) := by
    have a1 : (4 : ℝ) ^ s ≤ ((4 : ℝ) ^ Ks) ^ ζ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
    have a2 : (16 : ℝ) ≤ (16 : ℝ) ^ ζ := by
      calc (16 : ℝ) = 16 ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hζ
    calc 16 * (4 : ℝ) ^ s ≤ (16 : ℝ) ^ ζ * ((4 : ℝ) ^ Ks) ^ ζ :=
          mul_le_mul a2 a1 hY0.le (by positivity)
      _ = (16 * (4 : ℝ) ^ Ks) ^ ζ := (Real.mul_rpow (by norm_num) (by positivity)).symm
      _ ≤ ((N : ℝ) ^ (1 / 5 : ℝ)) ^ ζ := Real.rpow_le_rpow (by positivity) hK (by linarith)
      _ = (N : ℝ) ^ (ζ / 5) := by rw [← Real.rpow_mul hN0.le]; ring_nf
  have h4 : (N : ℝ) ^ (ζ / 5) * (N : ℝ) ^ (-(6 * ζ / 5)) = (N : ℝ) ^ (-ζ) := by
    rw [← Real.rpow_add hN0]; ring_nf
  have h5 : 0 ≤ (N : ℝ) ^ (-(6 * ζ / 5)) := by positivity
  calc _ ≤ (N : ℝ) ^ (-(6 * ζ / 5)) * (8 * 4 ^ s) + 8 * 4 ^ s * (N : ℝ) ^ (-(6 * ζ / 5)) := by
        have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 8 * 4 ^ s)
        have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 8 * 4 ^ s)
        nlinarith
    _ = 16 * 4 ^ s * (N : ℝ) ^ (-(6 * ζ / 5)) := by ring
    _ ≤ (N : ℝ) ^ (ζ / 5) * (N : ℝ) ^ (-(6 * ζ / 5)) := mul_le_mul_of_nonneg_right h3 h5
    _ = _ := h4

/-- The premise of `comparison_iterate` in the form `|E …| ≤ B N^{(φq/20) m}`. -/
private lemma iterate_premise_le {N : ℕ} (hN : (0 : ℝ) < N) {φq B X : ℝ} (m : ℕ)
    (h : (N : ℝ) ^ (-(φq / 20) * (m : ℝ)) * X ≤ B) : X ≤ B * ((N : ℝ) ^ (φq / 20)) ^ m := by
  have e : (N : ℝ) ^ (-(φq / 20) * (m : ℝ)) = (((N : ℝ) ^ (φq / 20)) ^ m)⁻¹ := by
    rw [Real.rpow_mul hN.le, Real.rpow_natCast, Real.rpow_neg hN.le, inv_pow]
  rw [e, inv_mul_le_iff₀ (by positivity)] at h
  linarith [mul_comm B (((N : ℝ) ^ (φq / 20)) ^ m)]

/-- The iteration (6.29)–(6.38), with (6.37)–(6.38) in the "max" form: if every
admissible iterate `P_{γ_n,k_n} ⋯ P_{γ_1,k_1}` (`1 ≤ n ≤ ⌈6ζ/φq⌉`, `|k_i| ≤ ⌈2(2ζ+3)/φq⌉`) of the
weighted sum `F` has `N^{-(φq/20) Σ|k_i|} |E_{H̃} …| ≤ B`, then
`|E_{H_{γ₀}} F| ≤ |E_{H̃} F| + B + N^{-ζ}`. The expansions are taken at `2ζ + 3`, which absorbs the
`N(N+1)/2` swaps. -/
theorem comparison_iterate {C1 φq Ks : ℝ} (hφq : 0 < φq) (hKs : 0 < Ks) :
    ∃ C0 > (0 : ℝ), ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (Lv Lw : EntryLaws N) (q : ℝ),
      MatchedPair C1 q Lv Lw → (N : ℝ) ^ φq ≤ q →
      ∀ (γ0 : ℕ) (ζ : ℝ), 1 ≤ ζ → ζ ≤ phi N → ∀ s : ℕ, (s : ℝ) ≤ Ks * ζ →
      ∀ z ∈ specDomain N C0, ∀ F : FSum N, (∀ cw ∈ F, 0 ≤ cw.1 ∧ cw.2.length = s) →
        (F.map Prod.fst).sum = 1 → ∀ B : ℝ, 0 ≤ B →
        (∀ d : List ((Fin N ⊕ OffDiag N) × List ℕ), d ≠ [] → d.length ≤ ⌈6 * ζ / φq⌉₊ →
          IterAdm (xiOf (2 * ζ + 3) φq) s d →
          (N : ℝ) ^ (-(φq / 20) * ((d.map fun x => x.2.sum).sum : ℝ)) *
            ‖∫ ω, evalF (resS z ω) (msc z) (iterP d F) ∂Lw.law‖ ≤ B) →
        ‖∫ ω, evalF (resS z ω) (msc z) F ∂(interp (lexPos N) γ0 Lv Lw).law‖ ≤
          ‖∫ ω, evalF (resS z ω) (msc z) F ∂Lw.law‖ + B + (N : ℝ) ^ (-ζ) := by
  set K' : ℝ := Ks + (6 / φq + 1) * (10 / φq + 1) + 1 with hK'def
  have hK'0 : 0 < K' := by positivity
  have hK'1 : 1 ≤ K' := by
    have : 0 ≤ Ks + (6 / φq + 1) * (10 / φq + 1) := by positivity
    linarith
  obtain ⟨C0s, hC0s, N0s, hswap⟩ := swap_comparison (C1 := C1) (φq := φq) (Ks := K') hφq hK'0
  obtain ⟨C0g, hC0g, c, hc, C', hC', N0g, hgood⟩ := highProb_goodEvent (C1 := C1) hφq
  have hev := (eventually_ge_atTop (max (max N0s N0g) 16)).and <|
    (expansion_eventually_le_phi (max 3 (8 * K' ^ 5))).and <|
    (phi_rpow_le_rpow 11 (by positivity : (0 : ℝ) < φq / 20)).and <|
    (((tendsto_rpow_atTop (by positivity : (0 : ℝ) < φq / 20)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 8).and <|
    (expansion_eventually_log_le ((2 * K' + C') / c)).and <|
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (16 * (4 : ℝ) ^ Ks))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨max C0s C0g, lt_max_of_lt_left hC0s, N0, fun N hN Lv Lw q hmp hq γ0 ζ hζ1 hζϕ s hs z hz
    F hF hF1 B hB hprem => ?_⟩
  obtain ⟨hNbig, hϕbig, hϕ11, hρ8, hlogϕ, hN5⟩ := hN0 N hN
  have hρ8' : (8 : ℝ) ≤ (N : ℝ) ^ (φq / 20) := hρ8
  have hN5' : 16 * (4 : ℝ) ^ Ks ≤ (N : ℝ) ^ (1 / 5 : ℝ) := hN5
  clear hρ8 hN5 hev hN0
  have hNs : N0s ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hNbig
  have hNg : N0g ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hNbig
  have hN16 : 16 ≤ N := le_trans (le_max_right _ _) hNbig
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hN0r : (0 : ℝ) < N := by linarith
  have hϕ3 : 3 ≤ phi N := le_trans (le_max_left _ _) hϕbig
  have hϕK : 8 * K' ^ 5 ≤ phi N := le_trans (le_max_right _ _) hϕbig
  have hϕ1 : 1 ≤ phi N := by linarith
  -- the spectral domain
  have hzs : z ∈ specDomain N C0s := ⟨hz.1, lt_of_le_of_lt (div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hϕ1 (le_max_left _ _)) hN0r.le) hz.2.1, hz.2.2⟩
  have hzg : z ∈ specDomain N C0g := ⟨hz.1, lt_of_le_of_lt (div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hϕ1 (le_max_right _ _)) hN0r.le) hz.2.1, hz.2.2⟩
  have hzim : 0 < z.im := lt_of_le_of_lt (by positivity) hz.2.1
  have hzB : 1 / z.im ≤ N := by
    have h1 : 1 ≤ phi N ^ (max C0s C0g) :=
      Real.one_le_rpow hϕ1 (le_trans hC0s.le (le_max_left _ _))
    have h2 : 1 / (N : ℝ) < z.im := lt_of_le_of_lt (div_le_div_of_nonneg_right h1 hN0r.le) hz.2.1
    rw [div_le_iff₀ hzim]
    rw [div_lt_iff₀ hN0r] at h2
    linarith
  have e₀ : Fin N ⊕ OffDiag N := Sum.inl ⟨0, by omega⟩
  have hμ : ∀ γ : ℕ, IsProbabilityMeasure (interp (lexPos N) γ Lv Lw).law := fun γ =>
    isProbabilityMeasure_law (hmp.interp γ).isProb_v
  have hμw : IsProbabilityMeasure Lw.law := isProbabilityMeasure_law hmp.isProb_w
  have hζ'1 : 1 ≤ 2 * ζ + 3 := by linarith
  have hζ'2 : 2 * ζ + 3 ≤ phi N ^ 2 := by nlinarith
  -- the quantities of the iteration
  set ρ : ℝ := (N : ℝ) ^ (φq / 20) with hρ
  set θ : ℝ := (N : ℝ) ^ (-(φq / 5)) with hθ
  set E0 : ℝ := 4 * (N : ℝ) ^ 2 * 4 ^ s * (N : ℝ) ^ (-(2 * ζ + 3)) with hE0
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hN0r _
  have hθ0 : 0 ≤ θ := (Real.rpow_pos_of_pos hN0r _).le
  have hE00 : 0 ≤ E0 := by positivity
  have hθ2 : θ ≤ 1 / 2 := by
    have h1 : θ * ρ ^ 4 = 1 := by
      rw [hθ, hρ, expansion_rpow_pow hN0r.le, ← Real.rpow_add hN0r]
      have : -(φq / 5) + φq / 20 * ((4 : ℕ) : ℝ) = 0 := by push_cast; ring
      rw [this, Real.rpow_zero]
    have h2 : (8 : ℝ) ^ 4 ≤ ρ ^ 4 := pow_le_pow_left₀ (by norm_num) hρ8' 4
    have h3 : θ * 8 ^ 4 ≤ θ * ρ ^ 4 := mul_le_mul_of_nonneg_left h2 hθ0
    norm_num at h3
    linarith only [h1, h3, hθ0]
  have ht8 : 8 * (K' * phi N ^ 2) ^ 5 ≤ ρ := by
    have h11 : phi N ^ (11 : ℝ) = phi N ^ (11 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (phi N) 11
    rw [h11] at hϕ11
    have hp : 0 ≤ phi N ^ 10 := by positivity
    calc 8 * (K' * phi N ^ 2) ^ 5 = 8 * K' ^ 5 * phi N ^ 10 := by ring
      _ ≤ phi N * phi N ^ 10 := mul_le_mul_of_nonneg_right hϕK hp
      _ = phi N ^ 11 := by ring
      _ ≤ ρ := hϕ11
  have ht1 : 1 ≤ K' * phi N ^ 2 := by
    exact one_le_mul_of_one_le_of_one_le hK'1 (one_le_pow₀ hϕ1)
  -- the word lengths
  have hlen : ∀ d : List ((Fin N ⊕ OffDiag N) × List ℕ), IterAdm (xiOf (2 * ζ + 3) φq) s d →
      d.length ≤ ⌈6 * ζ / φq⌉₊ → ((s + iterate_ord d : ℕ) : ℝ) ≤ (K' - 1) * phi N ^ 2 := by
    intro d hd hdl
    have h1 := iterate_ord_le d s hd
    have h2 : iterate_ord d ≤ ⌈6 * ζ / φq⌉₊ * xiOf (2 * ζ + 3) φq :=
      h1.trans (Nat.mul_le_mul_right _ hdl)
    have h3 := iterate_len_le hφq hKs hζ1 hζϕ hs
    have h4 : ((s + iterate_ord d : ℕ) : ℝ) ≤
        (s : ℝ) + (⌈6 * ζ / φq⌉₊ : ℝ) * (xiOf (2 * ζ + 3) φq : ℝ) := by
      push_cast
      exact_mod_cast Nat.add_le_add_left h2 s
    rw [hK'def]
    linarith
  -- the expectation of one word
  have hP : ∀ γ : ℕ, ((interp (lexPos N) γ Lv Lw).law (goodEvent N C0g)ᶜ).toReal ≤
      (N : ℝ) ^ C' * Real.exp (-c * phi N ^ 3) := by
    intro γ
    have h := hgood N hNg (interp (lexPos N) γ Lv Lw) ⟨Lv, Lw, q, γ, hmp, hq, rfl⟩
    have h3 : phi N ^ (3 : ℝ) = phi N ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast (phi N) 3
    rw [h3] at h
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h
  have hword : ∀ (γ : ℕ) (w : Word N), (w.length : ℝ) ≤ K' * phi N ^ 2 →
      ‖∫ ω, evalWord (resS z ω) (msc z) w ∂(interp (lexPos N) γ Lv Lw).law‖ ≤
        2 * 4 ^ (w.length + 1) := by
    intro γ w hw
    have := hμ γ
    have h1 := iterate_norm_integral_evalWord_le (μ := (interp (lexPos N) γ Lv Lw).law) hzg hzim
      hzB e₀ w
    have h2 := iterate_bad_le (by omega : 2 ≤ N) hc hw hϕ1 hlogϕ (hP γ) ENNReal.toReal_nonneg
    have h3 : (1 : ℝ) ≤ 4 ^ (w.length + 1) := one_le_pow₀ (by norm_num)
    linarith
  -- the coefficients of the swaps
  have hAex : ∀ (e : Fin N ⊕ OffDiag N) (s' : ℕ),
      ∃ A : ((Fin s' → ℕ) → ℝ) × ((Fin s' → ℕ) → ℝ), (s' : ℝ) ≤ K' * phi N ^ 2 →
      (∀ α, |A.1 α| ≤ coeffBound N φq e (∑ t, α t) ∧ |A.2 α| ≤ coeffBound N φq e (∑ t, α t)) ∧
      ∀ w : Word N, w.length = s' →
        ‖(∫ ω, evalWord (resS z ω) (msc z) w ∂(interp (lexPos N) (lexPos N e) Lv Lw).law)
          - (∫ ω, evalWord (resS z ω) (msc z) w ∂(interp (lexPos N) (lexPos N e - 1) Lv Lw).law)
          - ∑ α ∈ highIdx s' (matchedOrder e) (xiOf (2 * ζ + 3) φq),
              ((A.1 α : ℂ) * ∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) w)
                  ∂(interp (lexPos N) (lexPos N e) Lv Lw).law
                - (A.2 α : ℂ) * ∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) w)
                  ∂(interp (lexPos N) (lexPos N e - 1) Lv Lw).law)‖
          ≤ 2 * 4 ^ s' * (N : ℝ) ^ (-(2 * ζ + 3)) := by
    intro e s'
    by_cases hs' : (s' : ℝ) ≤ K' * phi N ^ 2
    · obtain ⟨A₀, A₁, h1, h2⟩ := hswap N hNs Lv Lw q hmp hq e (2 * ζ + 3) hζ'1 hζ'2 s' hs'
      exact ⟨(A₀, A₁), fun _ => ⟨h1, fun w hw => h2 z hzs w hw⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hs'⟩
  choose A hA using hAex
  -- the iteration, by induction on the remaining depth
  have key : ∀ j : ℕ, ∀ d : List ((Fin N ⊕ OffDiag N) × List ℕ),
      IterAdm (xiOf (2 * ζ + 3) φq) s d → d.length + j = ⌈6 * ζ / φq⌉₊ → ∀ γ : ℕ,
      ‖∫ ω, evalF (resS z ω) (msc z) (iterP d F) ∂(interp (lexPos N) γ Lv Lw).law‖ ≤
        ‖∫ ω, evalF (resS z ω) (msc z) (iterP d F) ∂Lw.law‖ +
          ρ ^ iterate_ord d * (B + (θ ^ j * (8 * 4 ^ s) + 2 * E0)) := by
    intro j
    induction j with
    | zero =>
      intro d hd hdl γ
      have := hμ γ
      obtain ⟨hGp, hGW⟩ := iterate_iterP_props d s F hd hF
      rw [hF1, mul_one] at hGW
      have hsd := hlen d hd (by omega)
      have hK : ∀ w : Word N, w.length = s + iterate_ord d →
          ‖∫ ω, evalWord (resS z ω) (msc z) w ∂(interp (lexPos N) γ Lv Lw).law‖ ≤
            2 * 4 ^ (s + iterate_ord d + 1) := by
        intro w hw
        have hw' : (w.length : ℝ) ≤ K' * phi N ^ 2 := by
          rw [hw]
          have : 0 ≤ phi N ^ 2 := by positivity
          linarith
        have := hword γ w hw'
        rwa [hw] at this
      have h1 := iterate_norm_integral_evalF_le hzim e₀ hK (iterP d F) hGp
      have h8 : (8 : ℝ) ^ iterate_ord d ≤ ρ ^ iterate_ord d :=
        pow_le_pow_left₀ (by norm_num) hρ8' _
      have hρo : 0 ≤ ρ ^ iterate_ord d := by positivity
      have hn := norm_nonneg (∫ ω, evalF (resS z ω) (msc z) (iterP d F) ∂Lw.law)
      calc _ ≤ ((iterP d F).map Prod.fst).sum * (2 * 4 ^ (s + iterate_ord d + 1)) := h1
        _ ≤ 2 ^ iterate_ord d * (2 * 4 ^ (s + iterate_ord d + 1)) := by gcongr
        _ = 8 ^ iterate_ord d * (8 * 4 ^ s) := by
            rw [show (8 : ℝ) ^ iterate_ord d = 2 ^ iterate_ord d * 4 ^ iterate_ord d by
              rw [← mul_pow]; norm_num, pow_succ, pow_add]
            ring
        _ ≤ ρ ^ iterate_ord d * (8 * 4 ^ s) := by gcongr
        _ ≤ _ := by
            rw [pow_zero, one_mul]
            have e : ρ ^ iterate_ord d * (B + (8 * 4 ^ s + 2 * E0)) =
                ρ ^ iterate_ord d * (8 * 4 ^ s) + ρ ^ iterate_ord d * (B + 2 * E0) := by ring
            rw [e]
            have := mul_nonneg hρo (add_nonneg hB (mul_nonneg zero_le_two hE00))
            linarith
    | succ j ih =>
      intro d hd hdl γ
      obtain ⟨hGp, hGW⟩ := iterate_iterP_props d s F hd hF
      rw [hF1, mul_one] at hGW
      have hW0 : 0 ≤ ((iterP d F).map Prod.fst).sum := List.sum_nonneg fun x hx => by
        obtain ⟨cw, hcw, rfl⟩ := List.mem_map.1 hx
        exact (hGp cw hcw).1
      have hsd := hlen d hd (by omega)
      have hsK : ((s + iterate_ord d : ℕ) : ℝ) ≤ K' * phi N ^ 2 := by
        have : 0 ≤ phi N ^ 2 := by positivity
        linarith
      set R : ℝ := ρ ^ iterate_ord d * (2 * B + (θ ^ j * (8 * 4 ^ s) + 2 * E0)) with hR
      have hρo : 0 ≤ ρ ^ iterate_ord d := by positivity
      have hR0 : 0 ≤ R := by positivity
      -- the next level
      have hnext : ∀ (e : Fin N ⊕ OffDiag N) (α : Fin (s + iterate_ord d) → ℕ),
          α ∈ highIdx (s + iterate_ord d) (matchedOrder e) (xiOf (2 * ζ + 3) φq) → ∀ γ' : ℕ,
          ‖∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) (iterP d F))
            ∂(interp (lexPos N) γ' Lv Lw).law‖ ≤ ρ ^ (∑ t, α t) * R := by
        intro e α hα γ'
        obtain ⟨hα1, hα2⟩ := (expansion_mem_highIdx α).1 hα
        have hsum : (List.ofFn α).sum = ∑ t, α t := List.sum_ofFn
        have hd' : IterAdm (xiOf (2 * ζ + 3) φq) s (d ++ [(e, List.ofFn α)]) :=
          iterate_iterAdm_append (e, List.ofFn α) d s hd (by simp) (by simpa [hsum] using hα1)
            (by simpa [hsum] using hα2)
        have hl' : (d ++ [(e, List.ofFn α)]).length + j = ⌈6 * ζ / φq⌉₊ := by
          simp only [List.length_append, List.length_singleton]
          omega
        have hiter := iterate_iterP_append (e, List.ofFn α) d F
        have hord : iterate_ord (d ++ [(e, List.ofFn α)]) = iterate_ord d + ∑ t, α t := by
          rw [iterate_ord_append, hsum]
        have h1 := ih _ hd' hl' γ'
        have h2 := hprem _ (by simp) (by
          simp only [List.length_append, List.length_singleton]
          omega) hd'
        rw [iterate_cast_ord, hord, hiter] at h2
        rw [hord, hiter] at h1
        have h2' := iterate_premise_le hN0r _ h2
        calc _ ≤ _ := h1
          _ ≤ B * ρ ^ (iterate_ord d + ∑ t, α t) +
              ρ ^ (iterate_ord d + ∑ t, α t) * (B + (θ ^ j * (8 * 4 ^ s) + 2 * E0)) := by
            linarith
          _ = ρ ^ (∑ t, α t) * R := by rw [hR, pow_add]; ring
      -- one swap for every entry
      have hent : ∀ e : Fin N ⊕ OffDiag N,
          ‖(∫ ω, evalF (resS z ω) (msc z) (iterP d F) ∂(interp (lexPos N) (lexPos N e) Lv Lw).law)
            - ∫ ω, evalF (resS z ω) (msc z) (iterP d F)
              ∂(interp (lexPos N) (lexPos N e - 1) Lv Lw).law‖ ≤
          ∑ α ∈ highIdx (s + iterate_ord d) (matchedOrder e) (xiOf (2 * ζ + 3) φq),
            (|(A e (s + iterate_ord d)).1 α| * (ρ ^ (∑ t, α t) * R) +
              |(A e (s + iterate_ord d)).2 α| * (ρ ^ (∑ t, α t) * R)) +
          ((iterP d F).map Prod.fst).sum *
            (2 * 4 ^ (s + iterate_ord d) * (N : ℝ) ^ (-(2 * ζ + 3))) := by
        intro e
        have := hμ (lexPos N e)
        have := hμ (lexPos N e - 1)
        refine (iterate_swap_sum hzim e _ (A e (s + iterate_ord d)).1 (A e (s + iterate_ord d)).2
          (hA e (s + iterate_ord d) hsK).2 (iterP d F) hGp).trans ?_
        gcongr with α hα
        · exact hnext e α hα _
        · exact hnext e α hα _
      -- the sum over the entries
      have hθsum := iterate_theta_le (by omega : 1 ≤ N) (φq := φq) (s + iterate_ord d)
        (xiOf (2 * ζ + 3) φq) ht1 hsK ht8
        (fun e α => |(A e (s + iterate_ord d)).1 α| + |(A e (s + iterate_ord d)).2 α|)
        (fun e α => by
          have := (hA e (s + iterate_ord d) hsK).1 α
          linarith [this.1, this.2])
      have hsplit : ∑ e : Fin N ⊕ OffDiag N,
          (∑ α ∈ highIdx (s + iterate_ord d) (matchedOrder e) (xiOf (2 * ζ + 3) φq),
            (|(A e (s + iterate_ord d)).1 α| * (ρ ^ (∑ t, α t) * R) +
              |(A e (s + iterate_ord d)).2 α| * (ρ ^ (∑ t, α t) * R)) +
          ((iterP d F).map Prod.fst).sum *
            (2 * 4 ^ (s + iterate_ord d) * (N : ℝ) ^ (-(2 * ζ + 3)))) =
          (∑ e : Fin N ⊕ OffDiag N,
            ∑ α ∈ highIdx (s + iterate_ord d) (matchedOrder e) (xiOf (2 * ζ + 3) φq),
              (|(A e (s + iterate_ord d)).1 α| + |(A e (s + iterate_ord d)).2 α|) *
                ρ ^ (∑ t, α t)) * R +
          (Fintype.card (Fin N ⊕ OffDiag N) : ℝ) * (((iterP d F).map Prod.fst).sum *
            (2 * 4 ^ (s + iterate_ord d) * (N : ℝ) ^ (-(2 * ζ + 3)))) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun α _ => by ring
      have htel := iterate_telescope Lv Lw
        (fun L => ∫ ω, evalF (resS z ω) (msc z) (iterP d F) ∂L.law) γ
      simp only [interp_lexPos_zero] at htel
      have hcard := iterate_card_entries_le N
      have hε0 : 0 ≤ 2 * 4 ^ (s + iterate_ord d) * (N : ℝ) ^ (-(2 * ζ + 3)) := by positivity
      have herr : (Fintype.card (Fin N ⊕ OffDiag N) : ℝ) * (((iterP d F).map Prod.fst).sum *
            (2 * 4 ^ (s + iterate_ord d) * (N : ℝ) ^ (-(2 * ζ + 3)))) ≤ ρ ^ iterate_ord d * E0 := by
        calc _ ≤ (2 * (N : ℝ) ^ 2) * (2 ^ iterate_ord d *
              (2 * 4 ^ (s + iterate_ord d) * (N : ℝ) ^ (-(2 * ζ + 3)))) := by gcongr
          _ = 8 ^ iterate_ord d * E0 := by
              rw [hE0, show (8 : ℝ) ^ iterate_ord d = 2 ^ iterate_ord d * 4 ^ iterate_ord d by
                rw [← mul_pow]; norm_num, pow_add]
              ring
          _ ≤ ρ ^ iterate_ord d * E0 := by gcongr
      have hfin : θ * R + ρ ^ iterate_ord d * E0 ≤
          ρ ^ iterate_ord d * (B + (θ ^ (j + 1) * (8 * 4 ^ s) + 2 * E0)) := by
        have h1 : 2 * θ * B ≤ B := by
          have := mul_le_mul_of_nonneg_right hθ2 hB
          linarith
        have h2 : 2 * θ * E0 ≤ E0 := by
          have := mul_le_mul_of_nonneg_right hθ2 hE00
          linarith
        have h3 : θ * R + ρ ^ iterate_ord d * E0 = ρ ^ iterate_ord d *
            (2 * θ * B + θ ^ (j + 1) * (8 * 4 ^ s) + 2 * θ * E0 + E0) := by
          rw [hR]; ring
        rw [h3]
        exact mul_le_mul_of_nonneg_left (by linarith) hρo
      calc _ ≤ _ := htel
        _ ≤ _ + _ := add_le_add le_rfl (Finset.sum_le_sum fun e _ => hent e)
        _ = _ := by rw [hsplit]
        _ ≤ ‖∫ ω, evalF (resS z ω) (msc z) (iterP d F) ∂Lw.law‖ +
            (θ * R + ρ ^ iterate_ord d * E0) := by
            have := mul_le_mul_of_nonneg_right hθsum hR0
            linarith
        _ ≤ _ := by linarith
  have hfin := key ⌈6 * ζ / φq⌉₊ [] trivial (by simp) γ0
  simp only [iterP, iterate_ord, List.map_nil, List.sum_nil, pow_zero, one_mul] at hfin
  have hf := iterate_final_le (by omega : 1 ≤ N) hφq hζ1 hs (Nat.le_ceil _) hN5'
  rw [← hθ, ← hE0] at hf
  linarith

/-! ### Compiled checks at concrete nondegenerate points -/

open private lawV lawW lawVW_matchedPair diagV diagW
  from WEdgeNS.Comparison.Classes
open private phi_sixteen_bounds from WEdgeNS.Comparison.GoodEvent

/-- The term `max` of (6.37): the largest of `N^{-(φq/20)|d|} |E_μ P_d F|` over the admissible data
`d` (`1 ≤ length ≤ ⌈6ζ/φq⌉`, `IterAdm` with `ξ = ⌈2(2ζ+3)/φq⌉`), and `0`. -/
private def iterate_maxB (N : ℕ) (φq ζ : ℝ) (s : ℕ) (z : ℂ) (μ : Measure (Entries N))
    (F : FSum N) : ℝ :=
  max 0 (sSup {x : ℝ | ∃ d : List ((Fin N ⊕ OffDiag N) × List ℕ), d ≠ [] ∧
    d.length ≤ ⌈6 * ζ / φq⌉₊ ∧ IterAdm (xiOf (2 * ζ + 3) φq) s d ∧
    x = (N : ℝ) ^ (-(φq / 20) * ((d.map fun x => x.2.sum).sum : ℝ)) *
      ‖∫ ω, evalF (resS z ω) (msc z) (iterP d F) ∂μ‖})

/-- `iterate_maxB` satisfies the premise of `comparison_iterate`: every weighted iterate over the
admissible data is at most `2^M (1/η + 1)^{s + M}`, `M = ⌈6ζ/φq⌉ ⌈2(2ζ+3)/φq⌉`, so the supremum
bounds each of them. -/
private lemma iterate_maxB_spec {N : ℕ} (hN : 1 ≤ N) {μ : Measure (Entries N)}
    [IsProbabilityMeasure μ] {φq ζ : ℝ} (hφq : 0 < φq) {s : ℕ} {z : ℂ} (hz : 0 < z.im)
    {F : FSum N} (hF : ∀ cw ∈ F, 0 ≤ cw.1 ∧ cw.2.length = s) (hF1 : (F.map Prod.fst).sum = 1) :
    0 ≤ iterate_maxB N φq ζ s z μ F ∧
      ∀ d : List ((Fin N ⊕ OffDiag N) × List ℕ), d ≠ [] → d.length ≤ ⌈6 * ζ / φq⌉₊ →
        IterAdm (xiOf (2 * ζ + 3) φq) s d →
        (N : ℝ) ^ (-(φq / 20) * ((d.map fun x => x.2.sum).sum : ℝ)) *
          ‖∫ ω, evalF (resS z ω) (msc z) (iterP d F) ∂μ‖ ≤ iterate_maxB N φq ζ s z μ F := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set M := ⌈6 * ζ / φq⌉₊ * xiOf (2 * ζ + 3) φq
  have e₀ : Fin N ⊕ OffDiag N := Sum.inl ⟨0, by omega⟩
  have hb1 : (1 : ℝ) ≤ 1 / z.im + 1 := by
    have : 0 < 1 / z.im := by positivity
    linarith
  refine ⟨le_max_left _ _, fun d hd hl ha => le_max_of_le_right (le_csSup ⟨2 ^ M *
    (1 / z.im + 1) ^ (s + M), ?_⟩ ⟨d, hd, hl, ha, rfl⟩)⟩
  rintro x ⟨d, -, hl, ha, rfl⟩
  obtain ⟨hGp, hGW⟩ := iterate_iterP_props d s F ha hF
  rw [hF1, mul_one] at hGW
  have hoM : iterate_ord d ≤ M := (iterate_ord_le d s ha).trans (Nat.mul_le_mul_right _ hl)
  have hK : ∀ w : Word N, w.length = s + iterate_ord d →
      ‖∫ ω, evalWord (resS z ω) (msc z) w ∂μ‖ ≤ (1 / z.im + 1) ^ (s + iterate_ord d) := by
    intro w hw
    have h := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun ω => evalWord (resS z ω) (msc z) w) (C := (1 / z.im + 1) ^ w.length)
      (Eventually.of_forall fun ω => by
        have h := norm_evalW_wordP_le_of_le (G := resS z ω) (m := msc z) (B := 1 / z.im)
          (fun i j => norm_resolventC_apply_le (symOfEntries_isHermitian ω) hz i j)
          (norm_msc_eq_inv_and_lt_one hz).2.le e₀ (List.replicate w.length 0) w (by simp)
        rw [iterate_evalW_singleton] at h
        simpa using h)
    rw [probReal_univ, mul_one, hw] at h
    exact h
  have h1 := iterate_norm_integral_evalF_le hz e₀ hK (iterP d F) hGp
  have h2 : (N : ℝ) ^ (-(φq / 20) * ((d.map fun x => x.2.sum).sum : ℝ)) ≤ 1 := by
    rw [iterate_cast_ord]
    exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by
      have : (0 : ℝ) ≤ iterate_ord d := Nat.cast_nonneg _
      nlinarith)
  have h3 : ((iterP d F).map Prod.fst).sum * (1 / z.im + 1) ^ (s + iterate_ord d) ≤
      2 ^ M * (1 / z.im + 1) ^ (s + M) := by
    have hW0 : 0 ≤ ((iterP d F).map Prod.fst).sum := List.sum_nonneg fun x hx => by
      obtain ⟨cw, hcw, rfl⟩ := List.mem_map.1 hx
      exact (hGp cw hcw).1
    calc _ ≤ 2 ^ iterate_ord d * (1 / z.im + 1) ^ (s + iterate_ord d) := by gcongr
      _ ≤ _ := by gcongr; first | omega | norm_num
  calc _ ≤ 1 * ‖∫ ω, evalF (resS z ω) (msc z) (iterP d F) ∂μ‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact h1.trans h3

/-- The class of `comparison_iterate` (`MatchedPair` with `q ≥ N^{φq}`) is nonempty for all large
`N`: it contains the Rademacher laws against themselves, `C1 = 2`, `φq = 2/5`, `q = N^{2/5}`. -/
example : ∀ᶠ N : ℕ in atTop, ∃ (Lv Lw : EntryLaws N) (q : ℝ),
    MatchedPair 2 q Lv Lw ∧ (N : ℝ) ^ (2 / 5 : ℝ) ≤ q := by
  filter_upwards [expansion_matchedPair_radLaws] with N h
  exact ⟨radLaws N, radLaws N, _, h, le_rfl⟩

/-- `comparison_iterate` for `C1 = 2`, `φq = 2/5`, `K_s = 2`, the Rademacher laws against
themselves with `q = N^{2/5}`, `γ₀ = N(N+1)/2`, `ζ = 1`, `z = i`, the word `|G_ij|²` (`s = 2`,
weight `1`) and `B` the maximum `iterate_maxB` over the admissible data: all hypotheses hold for
all large `N`. -/
example : ∃ C0 > (0 : ℝ), ∀ᶠ N : ℕ in atTop, Complex.I ∈ specDomain N C0 ∧ ∀ i j : Fin N,
    ‖∫ ω, evalF (resS Complex.I ω) (msc Complex.I) [(1, [⟨.g, i, j⟩, ⟨.gbar, i, j⟩])]
        ∂(interp (lexPos N) (N * (N + 1) / 2) (radLaws N) (radLaws N)).law‖ ≤
      ‖∫ ω, evalF (resS Complex.I ω) (msc Complex.I) [(1, [⟨.g, i, j⟩, ⟨.gbar, i, j⟩])]
        ∂(radLaws N).law‖ +
      iterate_maxB N (2 / 5) 1 2 Complex.I (radLaws N).law [(1, [⟨.g, i, j⟩, ⟨.gbar, i, j⟩])] +
      (N : ℝ) ^ (-(1 : ℝ)) := by
  obtain ⟨C0, hC0, N0, h⟩ := comparison_iterate (C1 := 2) (φq := 2 / 5) (Ks := 2)
    (by norm_num) (by norm_num)
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [expansion_matchedPair_radLaws, eventually_ge_atTop N0, eventually_ge_atTop 16,
    expansion_eventually_le_phi 1, phi_rpow_le_rpow C0 (by norm_num : (0 : ℝ) < 1 / 2)]
    with N hmp hN h16 hφ hφC
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast h16
  have hzI : Complex.I ∈ specDomain N C0 := by
    refine ⟨by simp, ?_, by simp⟩
    have h1 : (N : ℝ) ^ (1 / 2 : ℝ) < (N : ℝ) ^ (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
    rw [Real.rpow_one] at h1
    rw [Complex.I_im, div_lt_one (by linarith)]
    linarith
  refine ⟨hzI, fun i j => ?_⟩
  have := isProbabilityMeasure_law hmp.isProb_w
  have hFp : ∀ cw ∈ ([(1, [⟨.g, i, j⟩, ⟨.gbar, i, j⟩])] : FSum N),
      0 ≤ cw.1 ∧ cw.2.length = 2 := by simp
  obtain ⟨hB0, hBp⟩ := iterate_maxB_spec (μ := (radLaws N).law) (by omega) (φq := 2 / 5)
    (ζ := 1) (by norm_num) (z := Complex.I) (by simp) hFp (by simp)
  exact h N hN (radLaws N) (radLaws N) _ hmp le_rfl _ 1 le_rfl hφ 2 (by norm_num) Complex.I hzI _
    hFp (by simp) _ hB0 hBp

/-- The hypotheses of `comparison_iterate` other than `N ≥ N0` and `z ∈ S(C0)`, at `N = 16`,
`C1 = 2`, `φq = 1/4`, `K_s = 2`, `ζ = 1`, `s = 2`, `F = |G_12|²`, `z = i` and `B = iterate_maxB`,
for two different laws: `lawV` and `lawW` form a matched pair with `q = 16^{1/4}` and differ in the
fourth diagonal moment. The data `d = ((1, 2), (3, 3))` are admissible (`4 < 6 ≤ ⌈40⌉`, length
`1 ≤ ⌈24⌉`), so the premise is not empty. -/
example : ∃ q : ℝ, MatchedPair 2 q lawV lawW ∧ ((16 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) ≤ q ∧
    (1 : ℝ) ≤ phi 16 ∧ ((2 : ℕ) : ℝ) ≤ 2 * 1 ∧
    (∀ cw ∈ ([(1, [⟨.g, 0, 1⟩, ⟨.gbar, 0, 1⟩])] : FSum 16), 0 ≤ cw.1 ∧ cw.2.length = 2) ∧
    (([(1, [⟨.g, 0, 1⟩, ⟨.gbar, 0, 1⟩])] : FSum 16).map Prod.fst).sum = 1 ∧
    0 ≤ iterate_maxB 16 (1 / 4) 1 2 Complex.I lawW.law [(1, [⟨.g, 0, 1⟩, ⟨.gbar, 0, 1⟩])] ∧
    (∀ d : List ((Fin 16 ⊕ OffDiag 16) × List ℕ), d ≠ [] → d.length ≤ ⌈6 * 1 / (1 / 4 : ℝ)⌉₊ →
      IterAdm (xiOf (2 * 1 + 3) (1 / 4)) 2 d →
      ((16 : ℕ) : ℝ) ^ (-((1 / 4 : ℝ) / 20) * ((d.map fun x => x.2.sum).sum : ℝ)) *
        ‖∫ ω, evalF (resS Complex.I ω) (msc Complex.I) (iterP d [(1, [⟨.g, 0, 1⟩, ⟨.gbar, 0, 1⟩])])
          ∂lawW.law‖ ≤
        iterate_maxB 16 (1 / 4) 1 2 Complex.I lawW.law [(1, [⟨.g, 0, 1⟩, ⟨.gbar, 0, 1⟩])]) ∧
    IterAdm (xiOf (2 * 1 + 3) (1 / 4)) 2
      [((Sum.inr ⟨(0, 1), by decide⟩ : Fin 16 ⊕ OffDiag 16), [3, 3])] ∧
    [((Sum.inr ⟨(0, 1), by decide⟩ : Fin 16 ⊕ OffDiag 16), [3, 3])].length ≤
      ⌈6 * 1 / (1 / 4 : ℝ)⌉₊ ∧
    lawV.entryMoment (Sum.inl 0) 4 ≠ lawW.entryMoment (Sum.inl 0) 4 := by
  obtain ⟨h1, -⟩ := phi_sixteen_bounds
  have := isProbabilityMeasure_law lawVW_matchedPair.isProb_w
  have hFp : ∀ cw ∈ ([(1, [⟨.g, 0, 1⟩, ⟨.gbar, 0, 1⟩])] : FSum 16),
      0 ≤ cw.1 ∧ cw.2.length = 2 := by simp
  obtain ⟨hB0, hBp⟩ := iterate_maxB_spec (μ := lawW.law) (by norm_num) (φq := 1 / 4)
    (ζ := 1) (by norm_num) (z := Complex.I) (by simp) hFp (by simp)
  refine ⟨_, lawVW_matchedPair, le_rfl, by linarith, by norm_num, hFp, by simp, hB0, hBp,
    ⟨rfl, by decide, ?_, trivial⟩, ?_, ?_⟩
  · unfold xiOf
    exact Nat.succ_le_of_lt (Nat.lt_ceil.2 (by norm_num))
  · simp only [List.length_singleton]
    exact Nat.succ_le_of_lt (Nat.lt_ceil.2 (by norm_num))
  · simp only [EntryLaws.entryMoment, EntryLaws.entry, Sum.elim_inl, lawV, lawW]
    rw [integral_unifList, integral_unifList]
    norm_num [diagV, diagW]

#print axioms comparison_iterate

end WEdgeNS
