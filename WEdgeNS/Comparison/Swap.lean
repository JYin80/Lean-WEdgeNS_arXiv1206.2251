import WEdgeNS.Comparison.Expansion

/-!
# One swap of the comparison
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

open private expansion_matchedPair_radLaws expansion_eventually_le_phi
  from WEdgeNS.Comparison.Expansion
open private lawV lawW lawVW_matchedPair diagV diagW
  from WEdgeNS.Comparison.Classes
open private phi_sixteen_bounds from WEdgeNS.Comparison.GoodEvent

/-- The resolvent `S = (H - z)⁻¹` is measurable in the entries. -/
private lemma swap_measurable_resS {N : ℕ} (z : ℂ) :
    Measurable (fun ω : Entries N => resS z ω) := by
  have hA : Continuous fun ω : Entries N =>
      (symOfEntries ω).map (fun x : ℝ => (x : ℂ)) - z • (1 : Matrix (Fin N) (Fin N) ℂ) :=
    (((continuous_symOfEntries _).matrix_map Complex.continuous_ofReal).sub continuous_const)
  refine Measurable.of_eval_matrix _ fun i j => ?_
  have h : (fun ω : Entries N => resS z ω i j) = fun ω : Entries N =>
      ((symOfEntries ω).map (fun x : ℝ => (x : ℂ)) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det⁻¹ *
        ((symOfEntries ω).map (fun x : ℝ => (x : ℂ)) -
          z • (1 : Matrix (Fin N) (Fin N) ℂ)).adjugate i j := by
    funext ω
    simp only [resS, resolventC, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply,
      smul_eq_mul]
  rw [h]
  exact hA.matrix_det.measurable.inv.mul (hA.matrix_adjugate.matrix_elem i j).measurable

/-- A letter of a word is measurable in the entries when the matrix is. -/
private lemma swap_measurable_evalLetter {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {G : Ω → Matrix (Fin N) (Fin N) ℂ} (hG : Measurable G) (m : ℂ) (ℓ : Letter N) :
    Measurable fun ω => evalLetter (G ω) m ℓ := by
  have hij : Measurable fun ω => G ω ℓ.i ℓ.j := hG.eval_matrix
  unfold evalLetter
  cases ℓ.kind
  · exact hij
  · exact Complex.continuous_conj.measurable.comp hij
  · exact hij.sub measurable_const
  · exact Complex.continuous_conj.measurable.comp (hij.sub measurable_const)

/-- A word is measurable in the entries when the matrix is. -/
private lemma swap_measurable_evalWord {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {G : Ω → Matrix (Fin N) (Fin N) ℂ} (hG : Measurable G) (m : ℂ) (w : Word N) :
    Measurable fun ω => evalWord (G ω) m w := by
  induction w with
  | nil => simp [evalWord]
  | cons ℓ w ih =>
    simpa [evalWord] using (swap_measurable_evalLetter hG m ℓ).fun_mul ih

/-- A list of words is measurable in the entries when the matrix is. -/
private lemma swap_measurable_evalW {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {G : Ω → Matrix (Fin N) (Fin N) ℂ} (hG : Measurable G) (m : ℂ) (ws : List (Word N)) :
    Measurable fun ω => evalW (G ω) m ws := by
  induction ws with
  | nil => simp [evalW]
  | cons w ws ih =>
    simpa [evalW] using (swap_measurable_evalWord hG m w).fun_add ih

/-- The `k`-th moment of the entry `e` under `H_γ` is that of `Lv` when `e` follows `Lv`. -/
private lemma swap_entryMoment_interp_of_le {N : ℕ} {Lv Lw : EntryLaws N}
    (e : Fin N ⊕ OffDiag N) {γ : ℕ} (hγ : lexPos N e ≤ γ) (k : ℕ) :
    (interp (lexPos N) γ Lv Lw).entryMoment e k = Lv.entryMoment e k := by
  rcases e with i | p <;> simp [EntryLaws.entryMoment, EntryLaws.entry, interp, hγ]

/-- The `k`-th moment of the entry `e` under `H_γ` is that of `Lw` when `e` follows `Lw`. -/
private lemma swap_entryMoment_interp_of_not_le {N : ℕ} {Lv Lw : EntryLaws N}
    (e : Fin N ⊕ OffDiag N) {γ : ℕ} (hγ : ¬ lexPos N e ≤ γ) (k : ℕ) :
    (interp (lexPos N) γ Lv Lw).entryMoment e k = Lw.entryMoment e k := by
  rcases e with i | p <;> simp [EntryLaws.entryMoment, EntryLaws.entry, interp, hγ]

/-- One swap (6.26)–(6.28): the terms `k ≤ matchedOrder e` cancel between
`H_γ` and `H_{γ-1}`, `γ = lexPos N e`. -/
theorem swap_comparison {C1 φq Ks : ℝ} (hφq : 0 < φq) (hKs : 0 < Ks) :
    ∃ C0 > (0 : ℝ), ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (Lv Lw : EntryLaws N) (q : ℝ),
      MatchedPair C1 q Lv Lw → (N : ℝ) ^ φq ≤ q →
      ∀ (e : Fin N ⊕ OffDiag N) (ζ : ℝ), 1 ≤ ζ → ζ ≤ phi N ^ 2 →
      ∀ s : ℕ, (s : ℝ) ≤ Ks * phi N ^ 2 →
      ∃ A₀ A₁ : (Fin s → ℕ) → ℝ,
        (∀ α, |A₀ α| ≤ coeffBound N φq e (∑ t, α t) ∧ |A₁ α| ≤ coeffBound N φq e (∑ t, α t)) ∧
        ∀ z ∈ specDomain N C0, ∀ w : Word N, w.length = s →
          ‖(∫ ω, evalWord (resS z ω) (msc z) w ∂(interp (lexPos N) (lexPos N e) Lv Lw).law)
            - (∫ ω, evalWord (resS z ω) (msc z) w ∂(interp (lexPos N) (lexPos N e - 1) Lv Lw).law)
            - ∑ α ∈ highIdx s (matchedOrder e) (xiOf ζ φq),
                ((A₀ α : ℂ) * ∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) w)
                    ∂(interp (lexPos N) (lexPos N e) Lv Lw).law
                  - (A₁ α : ℂ) * ∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) w)
                    ∂(interp (lexPos N) (lexPos N e - 1) Lv Lw).law)‖
            ≤ 2 * 4 ^ s * (N : ℝ) ^ (-ζ) := by
  obtain ⟨C0, hC0, N0, h⟩ := expectation_expansion (C1 := C1) (φq := φq) (Ks := Ks) hφq hKs
  refine ⟨C0, hC0, N0, fun N hN Lv Lw q hmp hq e ζ hζ1 hζ2 s hs => ?_⟩
  obtain ⟨A₀, hA₀, h₀⟩ := h N hN (interp (lexPos N) (lexPos N e) Lv Lw)
    ⟨Lv, Lw, q, _, hmp, hq, rfl⟩ e ζ hζ1 hζ2 s hs
  obtain ⟨A₁, hA₁, h₁⟩ := h N hN (interp (lexPos N) (lexPos N e - 1) Lv Lw)
    ⟨Lv, Lw, q, _, hmp, hq, rfl⟩ e ζ hζ1 hζ2 s hs
  refine ⟨A₀, A₁, fun α => ⟨hA₀ α, hA₁ α⟩, fun z hz w hw => ?_⟩
  have e₀ := h₀ z hz w hw
  have e₁ := h₁ z hz w hw
  have hge : 1 ≤ lexPos N e := (lexPos_mem_Icc N e).1
  have hlt : ¬ lexPos N e ≤ lexPos N e - 1 := by omega
  -- the terms `k ≤ matchedOrder e` coincide
  have hK : (∑ k ∈ Finset.range (matchedOrder e + 1),
        ((interp (lexPos N) (lexPos N e) Lv Lw).entryMoment e k : ℂ) *
          ∑ κ ∈ Finset.Nat.antidiagonalTuple s k,
            ∫ ω, evalW (resR e z ω) (msc z) (wordP e (List.ofFn κ) w)
              ∂(interp (lexPos N) (lexPos N e) Lv Lw).law) =
      ∑ k ∈ Finset.range (matchedOrder e + 1),
        ((interp (lexPos N) (lexPos N e - 1) Lv Lw).entryMoment e k : ℂ) *
          ∑ κ ∈ Finset.Nat.antidiagonalTuple s k,
            ∫ ω, evalW (resR e z ω) (msc z) (wordP e (List.ofFn κ) w)
              ∂(interp (lexPos N) (lexPos N e - 1) Lv Lw).law := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ matchedOrder e := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rw [swap_entryMoment_interp_of_le e le_rfl k, swap_entryMoment_interp_of_not_le e hlt k,
      hmp.entryMoment_eq e k hk']
    congr 1
    refine Finset.sum_congr rfl fun κ _ => ?_
    exact integral_zeroEntry_interp hmp.isProb_v hmp.isProb_w e
      (fun ω' => evalW (resS z ω') (msc z) (wordP e (List.ofFn κ) w))
      (swap_measurable_evalW (swap_measurable_resS z) (msc z) _)
  rw [hK] at e₀
  rw [Finset.sum_sub_distrib]
  set E₀ := ∫ ω, evalWord (resS z ω) (msc z) w ∂(interp (lexPos N) (lexPos N e) Lv Lw).law
  set E₁ := ∫ ω, evalWord (resS z ω) (msc z) w ∂(interp (lexPos N) (lexPos N e - 1) Lv Lw).law
  set K := ∑ k ∈ Finset.range (matchedOrder e + 1),
        ((interp (lexPos N) (lexPos N e - 1) Lv Lw).entryMoment e k : ℂ) *
          ∑ κ ∈ Finset.Nat.antidiagonalTuple s k,
            ∫ ω, evalW (resR e z ω) (msc z) (wordP e (List.ofFn κ) w)
              ∂(interp (lexPos N) (lexPos N e - 1) Lv Lw).law
  set X₀ := ∑ α ∈ highIdx s (matchedOrder e) (xiOf ζ φq),
    (A₀ α : ℂ) * ∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) w)
      ∂(interp (lexPos N) (lexPos N e) Lv Lw).law
  set X₁ := ∑ α ∈ highIdx s (matchedOrder e) (xiOf ζ φq),
    (A₁ α : ℂ) * ∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) w)
      ∂(interp (lexPos N) (lexPos N e - 1) Lv Lw).law
  have hid : E₀ - E₁ - (X₀ - X₁) = (E₀ - K - X₀) - (E₁ - K - X₁) := by ring
  rw [hid]
  calc ‖(E₀ - K - X₀) - (E₁ - K - X₁)‖ ≤ ‖E₀ - K - X₀‖ + ‖E₁ - K - X₁‖ := norm_sub_le _ _
    _ ≤ 4 ^ s * (N : ℝ) ^ (-ζ) + 4 ^ s * (N : ℝ) ^ (-ζ) := add_le_add e₀ e₁
    _ = 2 * 4 ^ s * (N : ℝ) ^ (-ζ) := by ring

/-- `swap_comparison` for `C1 = 2`, `φq = 2/5`, `K_s = 1`, the Rademacher laws against themselves
with `q = N^{2/5}`, every entry `e`, `ζ = 1` and words of length `s = 2`: all hypotheses hold for
all large `N`. -/
example : ∃ C0 > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ e : Fin N ⊕ OffDiag N,
    ∃ A₀ A₁ : (Fin 2 → ℕ) → ℝ,
      (∀ α, |A₀ α| ≤ coeffBound N (2 / 5) e (∑ t, α t) ∧
        |A₁ α| ≤ coeffBound N (2 / 5) e (∑ t, α t)) ∧
      ∀ z ∈ specDomain N C0, ∀ w : Word N, w.length = 2 →
        ‖(∫ ω, evalWord (resS z ω) (msc z) w
              ∂(interp (lexPos N) (lexPos N e) (radLaws N) (radLaws N)).law)
          - (∫ ω, evalWord (resS z ω) (msc z) w
              ∂(interp (lexPos N) (lexPos N e - 1) (radLaws N) (radLaws N)).law)
          - ∑ α ∈ highIdx 2 (matchedOrder e) (xiOf 1 (2 / 5)),
              ((A₀ α : ℂ) * ∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) w)
                  ∂(interp (lexPos N) (lexPos N e) (radLaws N) (radLaws N)).law
                - (A₁ α : ℂ) * ∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) w)
                  ∂(interp (lexPos N) (lexPos N e - 1) (radLaws N) (radLaws N)).law)‖
          ≤ 2 * 4 ^ 2 * (N : ℝ) ^ (-(1 : ℝ)) := by
  obtain ⟨C0, hC0, N0, h⟩ := swap_comparison (C1 := 2) (φq := 2 / 5) (Ks := 1)
    (by norm_num) (by norm_num)
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [expansion_matchedPair_radLaws, eventually_ge_atTop N0,
    expansion_eventually_le_phi 2] with N hmp hN hφ e
  have hφ2 : (2 : ℝ) ≤ phi N ^ 2 := by nlinarith
  exact h N hN (radLaws N) (radLaws N) _ hmp le_rfl e 1 le_rfl (by linarith) 2
    (by push_cast; linarith)

/-- The hypotheses of `swap_comparison` other than `N ≥ N0`, at `N = 16`, `C1 = 2`, `φq = 1/4`,
`K_s = 1`, `ζ = 1`, `s = 2`, for two different laws: `lawV` and `lawW` form a matched pair with
`q = 16^{1/4}` and differ in the fourth diagonal moment, which is not matched. -/
example : ∃ q : ℝ, MatchedPair 2 q lawV lawW ∧ ((16 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) ≤ q ∧
    1 ≤ phi 16 ^ 2 ∧ ((2 : ℕ) : ℝ) ≤ 1 * phi 16 ^ 2 ∧
    lawV.entryMoment (Sum.inl 0) 4 ≠ lawW.entryMoment (Sum.inl 0) 4 := by
  obtain ⟨h1, -⟩ := phi_sixteen_bounds
  refine ⟨_, lawVW_matchedPair, le_rfl, by nlinarith, by norm_num; nlinarith, ?_⟩
  simp only [EntryLaws.entryMoment, EntryLaws.entry, Sum.elim_inl, lawV, lawW]
  rw [integral_unifList, integral_unifList]
  norm_num [diagV, diagW]

#print axioms swap_comparison

end WEdgeNS
