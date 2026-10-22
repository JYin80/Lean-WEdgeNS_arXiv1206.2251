import WEdgeNS.Comparison.Iterate

/-!
# The iteration in the sum form
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

open private iterate_opP_props iterate_telescope iterate_swap_sum iterate_theta_le
  iterate_norm_integral_evalF_le iterate_norm_integral_evalWord_le iterate_bad_le iterate_len_le
  iterate_final_le iterate_card_entries_le
  from WEdgeNS.Comparison.Iterate
open private expansion_eventually_le_phi expansion_eventually_log_le expansion_rpow_pow
  expansion_mem_highIdx from WEdgeNS.Comparison.Expansion

/-- Weight of one entry: `N^{-1}` on the diagonal, `N^{-2}` off it. -/
def entryWeight (N : ℕ) : Fin N ⊕ OffDiag N → ℝ
  | Sum.inl _ => (N : ℝ)⁻¹
  | Sum.inr _ => ((N : ℝ) ^ 2)⁻¹

/-- `w(d) = Π_t W(e_t) N^{-(φq/20)|k_t|}`. -/
def iterWeight (N : ℕ) (φq : ℝ) (d : List ((Fin N ⊕ OffDiag N) × List ℕ)) : ℝ :=
  (d.map fun x => entryWeight N x.1 * (N : ℝ) ^ (-(φq / 20) * (x.2.sum : ℝ))).prod

/-- The admissible data of (6.34) of length at most `n` (the empty data included). -/
def iterAdmSet (N ξ : ℕ) : ℕ → ℕ → Finset (List ((Fin N ⊕ OffDiag N) × List ℕ))
  | _, 0 => {[]}
  | s, n + 1 => insert [] ((Finset.univ : Finset (Fin N ⊕ OffDiag N)).biUnion fun e =>
      (highIdx s (matchedOrder e) ξ).biUnion fun α =>
        (iterAdmSet N ξ (s + ∑ t, α t) n).image fun d => (e, List.ofFn α) :: d)

/-- Membership in `iterAdmSet`. -/
theorem mem_iterAdmSet {N ξ : ℕ} :
    ∀ (n s : ℕ) (d : List ((Fin N ⊕ OffDiag N) × List ℕ)),
      d ∈ iterAdmSet N ξ s n ↔ d.length ≤ n ∧ IterAdm ξ s d := by
  intro n
  induction n with
  | zero =>
    intro s d
    cases d with
    | nil => simp [iterAdmSet, IterAdm]
    | cons x d => simp [iterAdmSet]
  | succ n ih =>
    intro s d
    cases d with
    | nil => simp [iterAdmSet, IterAdm]
    | cons x d =>
      obtain ⟨e, k⟩ := x
      simp only [iterAdmSet, Finset.mem_insert, reduceCtorEq, false_or, Finset.mem_biUnion,
        Finset.mem_univ, true_and, Finset.mem_image, List.cons.injEq, Prod.mk.injEq, ih,
        List.length_cons, IterAdm, add_le_add_iff_right]
      constructor
      · rintro ⟨e', α, hα, d', ⟨hl, hd'⟩, ⟨rfl, rfl⟩, rfl⟩
        obtain ⟨h1, h2⟩ := (expansion_mem_highIdx α).1 hα
        rw [List.sum_ofFn]
        exact ⟨hl, List.length_ofFn, h1, h2, hd'⟩
      · rintro ⟨hl, hk, h1, h2, hd⟩
        subst hk
        have hs : ∑ t, k.get t = k.sum := by
          rw [← List.sum_ofFn, List.ofFn_get]
        refine ⟨e, k.get, (expansion_mem_highIdx _).2 ⟨hs ▸ h1, hs ▸ h2⟩, d,
          ⟨hl, hs ▸ hd⟩, ⟨rfl, List.ofFn_get k⟩, rfl⟩

/-- A sum over `iterAdmSet N ξ s (n + 1)` splits into the term `d = []` and the sums over the first
step `(e, α)` and the remaining data in `iterAdmSet N ξ (s + |α|) n`. -/
private lemma iterateSum_sum_succ {N ξ : ℕ} {M : Type*} [AddCommMonoid M] (s n : ℕ)
    (g : List ((Fin N ⊕ OffDiag N) × List ℕ) → M) :
    ∑ d ∈ iterAdmSet N ξ s (n + 1), g d = g [] +
      ∑ e : Fin N ⊕ OffDiag N, ∑ α ∈ highIdx s (matchedOrder e) ξ,
        ∑ d ∈ iterAdmSet N ξ (s + ∑ t, α t) n, g ((e, List.ofFn α) :: d) := by
  have hnot : [] ∉ (Finset.univ : Finset (Fin N ⊕ OffDiag N)).biUnion fun e =>
      (highIdx s (matchedOrder e) ξ).biUnion fun α =>
        (iterAdmSet N ξ (s + ∑ t, α t) n).image fun d => (e, List.ofFn α) :: d := by
    simp
  rw [iterAdmSet, Finset.sum_insert hnot, Finset.sum_biUnion]
  · congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.sum_image]
      intro x _ y _ h
      exact (List.cons.inj h).2
    · intro α₁ _ α₂ _ hne
      refine Finset.disjoint_left.2 fun d h1 h2 => hne ?_
      simp only [Finset.mem_image] at h1 h2
      obtain ⟨d1, -, rfl⟩ := h1
      obtain ⟨d2, -, h⟩ := h2
      exact (List.ofFn_injective (Prod.mk.inj (List.cons.inj h).1).2).symm
  · intro e₁ _ e₂ _ hne
    refine Finset.disjoint_left.2 fun d h1 h2 => hne ?_
    simp only [Finset.mem_biUnion, Finset.mem_image] at h1 h2
    obtain ⟨α1, -, d1, -, rfl⟩ := h1
    obtain ⟨α2, -, d2, -, h⟩ := h2
    exact (Prod.mk.inj (List.cons.inj h).1).1.symm

/-- The weights are nonnegative. -/
private lemma iterateSum_iterWeight_nonneg (N : ℕ) (φq : ℝ)
    (d : List ((Fin N ⊕ OffDiag N) × List ℕ)) : 0 ≤ iterWeight N φq d := by
  refine List.prod_nonneg fun x hx => ?_
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
  have h1 : 0 ≤ entryWeight N y.1 := by
    rcases y with ⟨e | e, k⟩ <;> simp only [entryWeight] <;> positivity
  exact mul_nonneg h1 (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The weight of one step of (6.35): for `m ≥ 1` and `N^{φq/20} ≥ 8`, twice the coefficient bound
of (6.22) and of its diagonal analogue is at most `W(e) N^{-(φq/20) m}`. -/
private lemma iterateSum_coeff_le {N : ℕ} (hN : (0 : ℝ) < N) {φq : ℝ}
    (hρ : (8 : ℝ) ≤ (N : ℝ) ^ (φq / 20)) (e : Fin N ⊕ OffDiag N) {m : ℕ} (hm : 1 ≤ m) :
    2 * coeffBound N φq e m ≤ entryWeight N e * (N : ℝ) ^ (-(φq / 20) * (m : ℝ)) := by
  set x := (N : ℝ) ^ (-(φq / 20) * (m : ℝ)) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos hN _
  have hxρ : x * ((N : ℝ) ^ (φq / 20)) ^ m = 1 := by
    rw [hx, expansion_rpow_pow hN.le, ← Real.rpow_add hN]
    have : -(φq / 20) * (m : ℝ) + φq / 20 * (m : ℝ) = 0 := by ring
    rw [this, Real.rpow_zero]
  have hρm : (8 : ℝ) ≤ ((N : ℝ) ^ (φq / 20)) ^ m :=
    calc (8 : ℝ) ≤ (N : ℝ) ^ (φq / 20) := hρ
      _ = ((N : ℝ) ^ (φq / 20)) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) hm
  have hx8 : x ≤ 1 / 8 := by nlinarith
  have hN1 : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.2 hN
  cases e with
  | inl i =>
    have h : coeffBound N φq (Sum.inl i) m = (N : ℝ)⁻¹ * x ^ 5 := by
      simp only [coeffBound]
      rw [hx, expansion_rpow_pow hN.le, ← Real.rpow_neg_one, ← Real.rpow_add hN]
      congr 1
      push_cast
      ring
    rw [h]
    simp only [entryWeight]
    have h4 : x ^ 4 ≤ (1 / 8) ^ 4 := pow_le_pow_left₀ hx0.le hx8 4
    have h5 : 2 * x ^ 5 ≤ x := by
      have : 2 * x ^ 5 = (2 * x ^ 4) * x := by ring
      rw [this]
      have : 2 * x ^ 4 ≤ 1 := by norm_num at h4; linarith
      nlinarith
    nlinarith
  | inr p =>
    have h : coeffBound N φq (Sum.inr p) m = ((N : ℝ) ^ 2)⁻¹ * x ^ 2 := by
      simp only [coeffBound]
      rw [hx, expansion_rpow_pow hN.le, ← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_neg hN.le,
        ← Real.rpow_add hN]
      congr 1
      push_cast
      ring
    rw [h]
    simp only [entryWeight]
    have hN2 : (0 : ℝ) < ((N : ℝ) ^ 2)⁻¹ := by positivity
    have h2 : 2 * x ^ 2 ≤ x := by nlinarith
    nlinarith

/-- The iteration (6.29)–(6.35) in the sum form (6.33) with the weights of (6.35):
`|E_{H_{γ₀}} F| ≤ Σ_d w(d) |E_{H̃} P_d F| + N^{-ζ}`, the sum over the admissible data `d` of
length `≤ ⌈6ζ/φq⌉` (the term `d = []` is `|E_{H̃} F|`). -/
theorem comparison_iterate_sum {C1 φq Ks : ℝ} (hφq : 0 < φq) (hKs : 0 < Ks) :
    ∃ C0 > (0 : ℝ), ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (Lv Lw : EntryLaws N) (q : ℝ),
      MatchedPair C1 q Lv Lw → (N : ℝ) ^ φq ≤ q →
      ∀ (γ0 : ℕ) (ζ : ℝ), 1 ≤ ζ → ζ ≤ phi N → ∀ s : ℕ, (s : ℝ) ≤ Ks * ζ →
      ∀ z ∈ specDomain N C0, ∀ F : FSum N, (∀ cw ∈ F, 0 ≤ cw.1 ∧ cw.2.length = s) →
        (F.map Prod.fst).sum = 1 →
        ‖∫ ω, evalF (resS z ω) (msc z) F ∂(interp (lexPos N) γ0 Lv Lw).law‖ ≤
          ∑ d ∈ iterAdmSet N (xiOf (2 * ζ + 3) φq) s ⌈6 * ζ / φq⌉₊,
            iterWeight N φq d * ‖∫ ω, evalF (resS z ω) (msc z) (iterP d F) ∂Lw.law‖ +
          (N : ℝ) ^ (-ζ) := by
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
    F hF hF1 => ?_⟩
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
  have hζ'1 : 1 ≤ 2 * ζ + 3 := by linarith
  have hζ'2 : 2 * ζ + 3 ≤ phi N ^ 2 := by nlinarith
  -- the quantities of the iteration
  set ξ : ℕ := xiOf (2 * ζ + 3) φq with hξ
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
          - ∑ α ∈ highIdx s' (matchedOrder e) ξ,
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
  -- the iteration, by induction on the remaining depth `j`, for formal sums `G` of words of
  -- length `s' = s + o` with total weight at most `2^o`
  have key : ∀ j : ℕ, ∀ (o s' : ℕ) (G : FSum N), s' = s + o →
      (∀ cw ∈ G, 0 ≤ cw.1 ∧ cw.2.length = s') → (G.map Prod.fst).sum ≤ 2 ^ o →
      ((s' + j * ξ : ℕ) : ℝ) ≤ (K' - 1) * phi N ^ 2 → ∀ γ : ℕ,
      ‖∫ ω, evalF (resS z ω) (msc z) G ∂(interp (lexPos N) γ Lv Lw).law‖ ≤
        ∑ d ∈ iterAdmSet N ξ s' j,
          iterWeight N φq d * ‖∫ ω, evalF (resS z ω) (msc z) (iterP d G) ∂Lw.law‖ +
        ρ ^ o * (θ ^ j * (8 * 4 ^ s) + 2 * E0) := by
    have hϕ2 : 0 ≤ phi N ^ 2 := by positivity
    intro j
    induction j with
    | zero =>
      intro o s' G hs' hG hW hlen γ
      have := hμ γ
      have hsK : (s' : ℝ) ≤ K' * phi N ^ 2 := by
        have : ((s' + 0 * ξ : ℕ) : ℝ) = s' := by simp
        linarith
      have hK : ∀ w : Word N, w.length = s' →
          ‖∫ ω, evalWord (resS z ω) (msc z) w ∂(interp (lexPos N) γ Lv Lw).law‖ ≤
            2 * 4 ^ (s' + 1) := by
        intro w hw
        have := hword γ w (by rw [hw]; exact hsK)
        rwa [hw] at this
      have h1 := iterate_norm_integral_evalF_le hzim e₀ hK G hG
      have h8 : (8 : ℝ) ^ o ≤ ρ ^ o := pow_le_pow_left₀ (by norm_num) hρ8' _
      have hρo : 0 ≤ ρ ^ o := by positivity
      have hsum : ∑ d ∈ iterAdmSet N ξ s' 0,
          iterWeight N φq d * ‖∫ ω, evalF (resS z ω) (msc z) (iterP d G) ∂Lw.law‖ =
            ‖∫ ω, evalF (resS z ω) (msc z) G ∂Lw.law‖ := by
        simp [iterAdmSet, iterWeight, iterP]
      rw [hsum]
      have hn := norm_nonneg (∫ ω, evalF (resS z ω) (msc z) G ∂Lw.law)
      calc _ ≤ (G.map Prod.fst).sum * (2 * 4 ^ (s' + 1)) := h1
        _ ≤ 2 ^ o * (2 * 4 ^ (s' + 1)) := by gcongr
        _ = 8 ^ o * (8 * 4 ^ s) := by
            rw [hs', show (8 : ℝ) ^ o = 2 ^ o * 4 ^ o by rw [← mul_pow]; norm_num, pow_succ,
              pow_add]
            ring
        _ ≤ ρ ^ o * (8 * 4 ^ s) := by gcongr
        _ ≤ _ := by
            rw [pow_zero, one_mul]
            have e : ρ ^ o * (8 * 4 ^ s + 2 * E0) = ρ ^ o * (8 * 4 ^ s) + ρ ^ o * (2 * E0) := by
              ring
            rw [e]
            have := mul_nonneg hρo (mul_nonneg zero_le_two hE00)
            linarith
    | succ j ih =>
      intro o s' G hs' hG hW hlen γ
      have hsK : (s' : ℝ) ≤ K' * phi N ^ 2 := by
        have : (s' : ℝ) ≤ ((s' + (j + 1) * ξ : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right _ _
        linarith
      set R : ℝ := ρ ^ o * (θ ^ j * (8 * 4 ^ s) + 2 * E0) with hR
      have hρo : 0 ≤ ρ ^ o := by positivity
      have hR0 : 0 ≤ R := by positivity
      -- the sum over the remaining data after one step `(e, α)`
      set S : (e : Fin N ⊕ OffDiag N) → (Fin s' → ℕ) → ℝ := fun e α =>
        ∑ d ∈ iterAdmSet N ξ (s' + ∑ t, α t) j, iterWeight N φq d *
          ‖∫ ω, evalF (resS z ω) (msc z) (iterP d (opP e (List.ofFn α) G)) ∂Lw.law‖ with hS
      have hS0 : ∀ e α, 0 ≤ S e α := fun e α =>
        Finset.sum_nonneg fun d _ => mul_nonneg (iterateSum_iterWeight_nonneg N φq d)
          (norm_nonneg _)
      -- the next level
      have hnext : ∀ (e : Fin N ⊕ OffDiag N) (α : Fin s' → ℕ),
          α ∈ highIdx s' (matchedOrder e) ξ → ∀ γ' : ℕ,
          ‖∫ ω, evalF (resS z ω) (msc z) (opP e (List.ofFn α) G)
            ∂(interp (lexPos N) γ' Lv Lw).law‖ ≤ S e α + ρ ^ (∑ t, α t) * R := by
        intro e α hα γ'
        obtain ⟨hα1, hα2⟩ := (expansion_mem_highIdx α).1 hα
        have hsum : (List.ofFn α).sum = ∑ t, α t := List.sum_ofFn
        have hp := iterate_opP_props e (List.ofFn α) (s := s') (by simp) G hG
        rw [hsum] at hp
        have hW' : ((opP e (List.ofFn α) G).map Prod.fst).sum ≤ 2 ^ (o + ∑ t, α t) := by
          calc _ ≤ 2 ^ (∑ t, α t) * (G.map Prod.fst).sum := hp.2
            _ ≤ 2 ^ (∑ t, α t) * 2 ^ o := by gcongr
            _ = _ := by rw [pow_add]; ring
        have hlen' : ((s' + ∑ t, α t + j * ξ : ℕ) : ℝ) ≤ (K' - 1) * phi N ^ 2 := by
          have : s' + ∑ t, α t + j * ξ ≤ s' + (j + 1) * ξ := by
            rw [add_mul, one_mul]; omega
          have : ((s' + ∑ t, α t + j * ξ : ℕ) : ℝ) ≤ ((s' + (j + 1) * ξ : ℕ) : ℝ) := by
            exact_mod_cast this
          linarith
        have h1 := ih (o + ∑ t, α t) (s' + ∑ t, α t) (opP e (List.ofFn α) G) (by omega) hp.1
          hW' hlen' γ'
        rw [pow_add] at h1
        calc _ ≤ _ := h1
          _ = _ := by rw [hR]; ring
      -- one swap for every entry, with the weights of the first step
      have hent : ∀ e : Fin N ⊕ OffDiag N,
          ‖(∫ ω, evalF (resS z ω) (msc z) G ∂(interp (lexPos N) (lexPos N e) Lv Lw).law)
            - ∫ ω, evalF (resS z ω) (msc z) G ∂(interp (lexPos N) (lexPos N e - 1) Lv Lw).law‖ ≤
          ∑ α ∈ highIdx s' (matchedOrder e) ξ,
            (∑ d ∈ iterAdmSet N ξ (s' + ∑ t, α t) j,
                iterWeight N φq ((e, List.ofFn α) :: d) *
                  ‖∫ ω, evalF (resS z ω) (msc z) (iterP ((e, List.ofFn α) :: d) G) ∂Lw.law‖ +
              (|(A e s').1 α| + |(A e s').2 α|) * ρ ^ (∑ t, α t) * R) +
          (G.map Prod.fst).sum * (2 * 4 ^ s' * (N : ℝ) ^ (-(2 * ζ + 3))) := by
        intro e
        have := hμ (lexPos N e)
        have := hμ (lexPos N e - 1)
        refine (iterate_swap_sum hzim e _ (A e s').1 (A e s').2 (hA e s' hsK).2 G hG).trans
          (add_le_add (Finset.sum_le_sum fun α hα => ?_) le_rfl)
        have hT : ∑ d ∈ iterAdmSet N ξ (s' + ∑ t, α t) j,
              iterWeight N φq ((e, List.ofFn α) :: d) *
                ‖∫ ω, evalF (resS z ω) (msc z) (iterP ((e, List.ofFn α) :: d) G) ∂Lw.law‖ =
            entryWeight N e * (N : ℝ) ^ (-(φq / 20) * ((∑ t, α t : ℕ) : ℝ)) * S e α := by
          rw [hS, Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          simp only [iterWeight, iterP, List.map_cons, List.prod_cons, List.sum_ofFn]
          ring
        rw [hT]
        have hm : 1 ≤ ∑ t, α t := by
          have := ((expansion_mem_highIdx α).1 hα).1
          omega
        have hc := iterateSum_coeff_le hN0r hρ8' e hm
        have hAb := (hA e s' hsK).1 α
        have h0 := hnext e α hα (lexPos N e)
        have h1 := hnext e α hα (lexPos N e - 1)
        have ha0 := abs_nonneg ((A e s').1 α)
        have ha1 := abs_nonneg ((A e s').2 α)
        have hSα := hS0 e α
        have hcS : (|(A e s').1 α| + |(A e s').2 α|) * S e α ≤
            entryWeight N e * (N : ℝ) ^ (-(φq / 20) * ((∑ t, α t : ℕ) : ℝ)) * S e α :=
          mul_le_mul_of_nonneg_right (by linarith [hAb.1, hAb.2]) hSα
        calc _ ≤ |(A e s').1 α| * (S e α + ρ ^ (∑ t, α t) * R) +
              |(A e s').2 α| * (S e α + ρ ^ (∑ t, α t) * R) :=
            add_le_add (mul_le_mul_of_nonneg_left h0 ha0) (mul_le_mul_of_nonneg_left h1 ha1)
          _ = (|(A e s').1 α| + |(A e s').2 α|) * S e α +
              (|(A e s').1 α| + |(A e s').2 α|) * ρ ^ (∑ t, α t) * R := by ring
          _ ≤ _ := by linarith
      -- the sum over the entries
      have hθsum := iterate_theta_le (by omega : 1 ≤ N) (φq := φq) s' ξ ht1 hsK ht8
        (fun e α => |(A e s').1 α| + |(A e s').2 α|)
        (fun e α => by
          have := (hA e s' hsK).1 α
          linarith [this.1, this.2])
      have htel := iterate_telescope Lv Lw
        (fun L => ∫ ω, evalF (resS z ω) (msc z) G ∂L.law) γ
      simp only [interp_lexPos_zero] at htel
      have hcard := iterate_card_entries_le N
      have hW0 : 0 ≤ (G.map Prod.fst).sum := List.sum_nonneg fun x hx => by
        obtain ⟨cw, hcw, rfl⟩ := List.mem_map.1 hx
        exact (hG cw hcw).1
      have hε0 : 0 ≤ 2 * 4 ^ s' * (N : ℝ) ^ (-(2 * ζ + 3)) := by positivity
      have herr : (Fintype.card (Fin N ⊕ OffDiag N) : ℝ) * ((G.map Prod.fst).sum *
            (2 * 4 ^ s' * (N : ℝ) ^ (-(2 * ζ + 3)))) ≤ ρ ^ o * E0 := by
        calc _ ≤ (2 * (N : ℝ) ^ 2) * (2 ^ o * (2 * 4 ^ s' * (N : ℝ) ^ (-(2 * ζ + 3)))) := by
              gcongr
          _ = 8 ^ o * E0 := by
              rw [hE0, hs', show (8 : ℝ) ^ o = 2 ^ o * 4 ^ o by rw [← mul_pow]; norm_num, pow_add]
              ring
          _ ≤ ρ ^ o * E0 := by gcongr
      have hsplit : ∑ e : Fin N ⊕ OffDiag N,
          (∑ α ∈ highIdx s' (matchedOrder e) ξ,
            (∑ d ∈ iterAdmSet N ξ (s' + ∑ t, α t) j,
                iterWeight N φq ((e, List.ofFn α) :: d) *
                  ‖∫ ω, evalF (resS z ω) (msc z) (iterP ((e, List.ofFn α) :: d) G) ∂Lw.law‖ +
              (|(A e s').1 α| + |(A e s').2 α|) * ρ ^ (∑ t, α t) * R) +
          (G.map Prod.fst).sum * (2 * 4 ^ s' * (N : ℝ) ^ (-(2 * ζ + 3)))) =
          (∑ e : Fin N ⊕ OffDiag N, ∑ α ∈ highIdx s' (matchedOrder e) ξ,
            ∑ d ∈ iterAdmSet N ξ (s' + ∑ t, α t) j,
              iterWeight N φq ((e, List.ofFn α) :: d) *
                ‖∫ ω, evalF (resS z ω) (msc z) (iterP ((e, List.ofFn α) :: d) G) ∂Lw.law‖) +
          (∑ e : Fin N ⊕ OffDiag N, ∑ α ∈ highIdx s' (matchedOrder e) ξ,
            (|(A e s').1 α| + |(A e s').2 α|) * ρ ^ (∑ t, α t)) * R +
          (Fintype.card (Fin N ⊕ OffDiag N) : ℝ) * ((G.map Prod.fst).sum *
            (2 * 4 ^ s' * (N : ℝ) ^ (-(2 * ζ + 3)))) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Finset.sum_mul]
        congr 1
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      have hfin : θ * R + ρ ^ o * E0 ≤ ρ ^ o * (θ ^ (j + 1) * (8 * 4 ^ s) + 2 * E0) := by
        have h2 : 2 * θ * E0 ≤ E0 := by
          have := mul_le_mul_of_nonneg_right hθ2 hE00
          linarith
        have h3 : θ * R + ρ ^ o * E0 = ρ ^ o * (θ ^ (j + 1) * (8 * 4 ^ s) + 2 * θ * E0 + E0) := by
          rw [hR]; ring
        rw [h3]
        exact mul_le_mul_of_nonneg_left (by linarith) hρo
      have hnil : iterWeight N φq [] *
          ‖∫ ω, evalF (resS z ω) (msc z) (iterP [] G) ∂Lw.law‖ =
            ‖∫ ω, evalF (resS z ω) (msc z) G ∂Lw.law‖ := by
        simp [iterWeight, iterP]
      rw [iterateSum_sum_succ, hnil]
      calc _ ≤ _ := htel
        _ ≤ _ + _ := add_le_add le_rfl (Finset.sum_le_sum fun e _ => hent e)
        _ = _ := by rw [hsplit]
        _ ≤ ‖∫ ω, evalF (resS z ω) (msc z) G ∂Lw.law‖ +
            (∑ e : Fin N ⊕ OffDiag N, ∑ α ∈ highIdx s' (matchedOrder e) ξ,
              ∑ d ∈ iterAdmSet N ξ (s' + ∑ t, α t) j,
                iterWeight N φq ((e, List.ofFn α) :: d) *
                  ‖∫ ω, evalF (resS z ω) (msc z) (iterP ((e, List.ofFn α) :: d) G) ∂Lw.law‖) +
            (θ * R + ρ ^ o * E0) := by
            have := mul_le_mul_of_nonneg_right hθsum hR0
            linarith
        _ ≤ _ := by linarith
  have hlen0 : ((s + ⌈6 * ζ / φq⌉₊ * ξ : ℕ) : ℝ) ≤ (K' - 1) * phi N ^ 2 := by
    have h3 := iterate_len_le hφq hKs hζ1 hζϕ hs
    push_cast
    rw [hK'def]
    linarith
  have hfin := key ⌈6 * ζ / φq⌉₊ 0 s F rfl hF (by rw [hF1]; simp) hlen0 γ0
  rw [pow_zero, one_mul] at hfin
  have hf := iterate_final_le (by omega : 1 ≤ N) hφq hζ1 hs (Nat.le_ceil _) hN5'
  rw [← hθ, ← hE0] at hf
  linarith

/-! ### Compiled checks at concrete nondegenerate points -/

/-- `mem_iterAdmSet` at `N = 4`, `ξ = 6`, `s = 2`: the one-step datum along the off-diagonal entry
`{1, 2}` with `k = (3, 3)` (`4 < 6 ≤ 6`) lies in the set for `n = 2` but not for `n = 0`; the
two-step datum along the diagonal entry `1` with `k = (3, 0)` (`2 < 3 ≤ 6`), then along `{2, 3}`
with `k ∈ ℕ^5`, `|k| = 5` (`4 < 5 ≤ 6`), lies in the set for `n = 2`; the datum with `k = (2, 2)`
along `{1, 2}` does not (`4 < 4` fails). -/
example : [((Sum.inr ⟨(0, 1), by decide⟩ : Fin 4 ⊕ OffDiag 4), [3, 3])] ∈ iterAdmSet 4 6 2 2 ∧
    [((Sum.inr ⟨(0, 1), by decide⟩ : Fin 4 ⊕ OffDiag 4), [3, 3])] ∉ iterAdmSet 4 6 2 0 ∧
    [((Sum.inl 0 : Fin 4 ⊕ OffDiag 4), [3, 0]),
      ((Sum.inr ⟨(1, 2), by decide⟩ : Fin 4 ⊕ OffDiag 4), [5, 0, 0, 0, 0])] ∈
      iterAdmSet 4 6 2 2 ∧
    [((Sum.inr ⟨(0, 1), by decide⟩ : Fin 4 ⊕ OffDiag 4), [2, 2])] ∉ iterAdmSet 4 6 2 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [mem_iterAdmSet, not_and]
  · exact ⟨by simp, rfl, by decide, by decide, trivial⟩
  · simp
  · exact ⟨by simp, rfl, by decide, by decide, rfl, by decide, by decide, trivial⟩
  · intro _ h
    exact absurd h.2.1 (by decide)

/-- One admissible step is in `iterAdmSet`. -/
private lemma iterateSum_mem_single {N ξ s n : ℕ} (e : Fin N ⊕ OffDiag N) (α : Fin s → ℕ)
    (hα : α ∈ highIdx s (matchedOrder e) ξ) : [(e, List.ofFn α)] ∈ iterAdmSet N ξ s (n + 1) := by
  rw [iterAdmSet]
  refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨e, Finset.mem_univ _,
    Finset.mem_biUnion.2 ⟨α, hα, Finset.mem_image.2 ⟨[], ?_, rfl⟩⟩⟩)
  cases n <;> simp [iterAdmSet]

open private expansion_matchedPair_radLaws from WEdgeNS.Comparison.Expansion
open private lawV lawW lawVW_matchedPair diagV diagW
  from WEdgeNS.Comparison.Classes
open private phi_sixteen_bounds from WEdgeNS.Comparison.GoodEvent

/-- `comparison_iterate_sum` applied for all large `N`: `C1 = 2`, `φq = 2/5`, `K_s = 3`, the
Rademacher laws against themselves with `q = N^{2/5}`, `γ₀ = N(N+1)/2`, `ζ = 1`, `s = 2`, `z = i`,
`F = G_ij Ḡ_ij`; every hypothesis is discharged. -/
example : ∃ C0 > (0 : ℝ), ∀ᶠ N : ℕ in atTop, Complex.I ∈ specDomain N C0 ∧ ∀ i j : Fin N,
    ‖∫ ω, evalF (resS Complex.I ω) (msc Complex.I) [(1, [⟨.g, i, j⟩, ⟨.gbar, i, j⟩])]
        ∂(interp (lexPos N) (N * (N + 1) / 2) (radLaws N) (radLaws N)).law‖ ≤
      ∑ d ∈ iterAdmSet N (xiOf (2 * 1 + 3) (2 / 5)) 2 ⌈6 * 1 / (2 / 5 : ℝ)⌉₊,
        iterWeight N (2 / 5) d * ‖∫ ω, evalF (resS Complex.I ω) (msc Complex.I)
          (iterP d [(1, [⟨.g, i, j⟩, ⟨.gbar, i, j⟩])]) ∂(radLaws N).law‖ +
      (N : ℝ) ^ (-(1 : ℝ)) := by
  obtain ⟨C0, hC0, N0, h⟩ := comparison_iterate_sum (C1 := 2) (φq := 2 / 5) (Ks := 3)
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
  exact h N hN (radLaws N) (radLaws N) _ hmp le_rfl _ 1 le_rfl hφ 2 (by norm_num) Complex.I hzI _
    (by simp) (by simp)

/-- The hypotheses of `comparison_iterate_sum` other than `N ≥ N0` and `z ∈ S(C0)` at `N = 16`,
`C1 = 2`, `φq = 1/4`, `K_s = 3`, `ζ = 1`, `s = 2`, `F = G_12 Ḡ_12`, for two different laws
(`lawV ≠ lawW` in the fourth diagonal moment), and two terms of the sum: `d = [({1,2}, (3,3))]`
and `d = [({3,4}, (3,3))]`, both admissible, with the weight of the first. -/
example : ∃ q : ℝ, MatchedPair 2 q lawV lawW ∧ ((16 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) ≤ q ∧
    (1 : ℝ) ≤ phi 16 ∧ ((2 : ℕ) : ℝ) ≤ 3 * 1 ∧
    (∀ cw ∈ ([(1, [⟨.g, 0, 1⟩, ⟨.gbar, 0, 1⟩])] : FSum 16), 0 ≤ cw.1 ∧ cw.2.length = 2) ∧
    (([(1, [⟨.g, 0, 1⟩, ⟨.gbar, 0, 1⟩])] : FSum 16).map Prod.fst).sum = 1 ∧
    [((Sum.inr ⟨(0, 1), by decide⟩ : Fin 16 ⊕ OffDiag 16), [3, 3])] ∈
      iterAdmSet 16 (xiOf (2 * 1 + 3) (1 / 4)) 2 ⌈6 * 1 / (1 / 4 : ℝ)⌉₊ ∧
    [((Sum.inr ⟨(2, 3), by decide⟩ : Fin 16 ⊕ OffDiag 16), [3, 3])] ∈
      iterAdmSet 16 (xiOf (2 * 1 + 3) (1 / 4)) 2 ⌈6 * 1 / (1 / 4 : ℝ)⌉₊ ∧
    iterWeight 16 (1 / 4) [((Sum.inr ⟨(0, 1), by decide⟩ : Fin 16 ⊕ OffDiag 16), [3, 3])] =
      ((16 : ℝ) ^ 2)⁻¹ * (16 : ℝ) ^ (-((1 / 4 : ℝ) / 20) * 6) ∧
    lawV.entryMoment (Sum.inl 0) 4 ≠ lawW.entryMoment (Sum.inl 0) 4 := by
  obtain ⟨h1, -⟩ := phi_sixteen_bounds
  have hξ : 6 ≤ xiOf (2 * 1 + 3) (1 / 4 : ℝ) := by
    unfold xiOf; norm_num
  have hn : 0 < ⌈6 * 1 / (1 / 4 : ℝ)⌉₊ := by norm_num
  have hmem : ∀ p : OffDiag 16, [((Sum.inr p : Fin 16 ⊕ OffDiag 16), [3, 3])] ∈
      iterAdmSet 16 (xiOf (2 * 1 + 3) (1 / 4)) 2 ⌈6 * 1 / (1 / 4 : ℝ)⌉₊ := by
    intro p
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hn
    rw [hm, zero_add]
    have hα : (![3, 3] : Fin 2 → ℕ) ∈ highIdx 2 (matchedOrder (Sum.inr p : Fin 16 ⊕ OffDiag 16))
        (xiOf (2 * 1 + 3) (1 / 4)) := by
      simp only [highIdx, Finset.mem_biUnion, Finset.mem_Icc, Finset.Nat.mem_antidiagonalTuple,
        matchedOrder]
      exact ⟨6, ⟨by norm_num, hξ⟩, by simp⟩
    exact iterateSum_mem_single (Sum.inr p) ![3, 3] hα
  refine ⟨_, lawVW_matchedPair, le_rfl, by linarith, by norm_num, by simp, by simp, hmem _,
    hmem _, ?_, ?_⟩
  · simp [iterWeight, entryWeight]; norm_num
  · simp only [EntryLaws.entryMoment, EntryLaws.entry, Sum.elim_inl, lawV, lawW]
    rw [integral_unifList, integral_unifList]
    norm_num [diagV, diagW]

#print axioms mem_iterAdmSet
#print axioms comparison_iterate_sum

end WEdgeNS
