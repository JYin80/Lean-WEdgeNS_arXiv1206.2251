import WEdgeNS.Reduction.Claim426
import WEdgeNS.Reduction.CutoffProb

/-!
# The edge of the Wigner matrix against the small matrix
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-! ### Deterministic step -/

private lemma comparison_symOfEntries_smul {N : ℕ} (c : ℝ) (ω : Entries N) :
    symOfEntries (c • ω) = c • symOfEntries ω := by
  ext i j
  simp only [symOfEntries, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- `H^S = σ H̃^S` when the normalising factor of `H̃^S` is `σ⁻¹`. -/
private lemma comparison_smallMat_eq {ν : Measure ℝ} {ε σ : ℝ} {N : ℕ} (hσ : 0 < σ)
    (ht : truncNormFactor ν ε N = σ⁻¹) (u : CoupleSpace N) :
    smallMat u = σ • normSmall ν ε u := by
  unfold smallMat normSmall
  rw [← comparison_symOfEntries_smul, smul_smul, ht, mul_inv_cancel_left₀ hσ.ne']

/-- The eigenvalue bounds behind (4.17), (4.26) and the rescaling: if `λ_N(H̃ + σ⁻¹E)` is within
`B` of `λ_N(H̃)` and `|λ_N(H̃)| ≤ 3`, then `λ_N(σ H̃ + E + M)` is within
`√N|m| + |m̃ - m|/√N + σB + 3|σ - 1|` of `λ_N(H̃)`. -/
private lemma comparison_det {N : ℕ} [NeZero N] {Hs E : Matrix (Fin N) (Fin N) ℝ}
    {σ B m m' : ℝ} (hσ : 0 < σ) (hHs : Hs.IsHermitian) (hE : E.IsHermitian)
    (hB : |lambdaMax (Hs + σ⁻¹ • E) - lambdaMax Hs| ≤ B) (h3 : |lambdaMax Hs| ≤ 3) :
    |lambdaMax (σ • Hs + E + shiftMat N m m') - lambdaMax Hs| ≤
      Real.sqrt N * |m| + |m' - m| / Real.sqrt N + σ * B + 3 * |σ - 1| := by
  have hσE : (σ⁻¹ • E).IsHermitian := hE.smul (IsSelfAdjoint.all _)
  have hA : (σ • Hs + E).IsHermitian := (hHs.smul (IsSelfAdjoint.all _)).add hE
  have h1 := abs_lambdaMax_add_shiftMat_sub_le hA m m'
  have e1 : σ • Hs + E = σ • (Hs + σ⁻¹ • E) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hσ.ne', one_smul]
  have h2 : lambdaMax (σ • Hs + E) = σ * lambdaMax (Hs + σ⁻¹ • E) := by
    rw [e1]
    exact lambdaMax_smul_of_pos (hHs.add hσE) hσ
  have h5 : |σ * lambdaMax (Hs + σ⁻¹ • E) - σ * lambdaMax Hs| ≤ σ * B := by
    rw [← mul_sub, abs_mul, abs_of_pos hσ]
    exact mul_le_mul_of_nonneg_left hB hσ.le
  have h6 : |σ * lambdaMax Hs - lambdaMax Hs| ≤ 3 * |σ - 1| := by
    have : σ * lambdaMax Hs - lambdaMax Hs = (σ - 1) * lambdaMax Hs := by ring
    rw [this, abs_mul]
    nlinarith [abs_nonneg (σ - 1), abs_nonneg (lambdaMax Hs)]
  calc |lambdaMax (σ • Hs + E + shiftMat N m m') - lambdaMax Hs|
      = |(lambdaMax (σ • Hs + E + shiftMat N m m') - lambdaMax (σ • Hs + E)) +
          (σ * lambdaMax (Hs + σ⁻¹ • E) - σ * lambdaMax Hs) +
          (σ * lambdaMax Hs - lambdaMax Hs)| := by
        rw [h2]
        congr 1
        ring
    _ ≤ |lambdaMax (σ • Hs + E + shiftMat N m m') - lambdaMax (σ • Hs + E)| +
          |σ * lambdaMax (Hs + σ⁻¹ • E) - σ * lambdaMax Hs| +
          |σ * lambdaMax Hs - lambdaMax Hs| := abs_add_three _ _ _
    _ ≤ _ := by linarith

/-- If the shifts of the deterministic step fit in `N^{-1/24}`, the event
`N^{-1/24} < |N^{2/3}(λ_N(H) - 2) - N^{2/3}(λ_N(H̃^S) - 2)|` lies in the union of four events: some
`|H̃_ij H^C_ij| > 3/4` (4.21)-(4.23), `H^C` not admissible (4.24)-(4.25), the bound (4.26) for the
rescaled pair fails, and some eigenvalue of `H̃^S` exceeds `3` in absolute value. -/
private lemma comparison_subset {ν : Measure ℝ} {ε : ℝ} {N : ℕ} [NeZero N] {C σ m m' : ℝ}
    (hσ : 0 < σ) (ht : truncNormFactor ν ε N = σ⁻¹)
    (hβ : (N : ℝ) ^ ((2 : ℝ) / 3) * (Real.sqrt N * |m| + |m' - m| / Real.sqrt N +
      σ * (N : ℝ) ^ (-(3 : ℝ) / 4) + 3 * |σ - 1|) ≤ (N : ℝ) ^ (-(1 : ℝ) / 24)) :
    {u : CoupleSpace N | (N : ℝ) ^ (-(1 : ℝ) / 24) <
      |edgeScaled N (coupleMap m m' u) -
        (N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (normSmall ν ε u) - 2)|} ⊆
      {u | ∃ i j, 3 / 4 < |(largeMat u - smallMat u) i j * selMat u i j|} ∪
        {u | ¬ SelGood ε u.2.2} ∪
        {u | (N : ℝ) ^ (-(3 : ℝ) / 4) <
          |lambdaMax (normSmall ν ε u + truncNormFactor ν ε N • pertMat ε u) -
            lambdaMax (normSmall ν ε u)|} ∪
        {u | (truncNormFactor ν ε N * (Real.sqrt N)⁻¹) • u.1 ∈ (smallGood N C ε)ᶜ} := by
  intro u hu
  by_contra hnot
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_compl_iff, not_or, not_exists, not_not,
    not_lt] at hnot
  obtain ⟨⟨⟨hD, hC⟩, hlam⟩, hgood⟩ := hnot
  obtain ⟨-, -, -, -, -, hge⟩ := hgood
  obtain ⟨α, hα⟩ := (lambdaMax_isGreatest
    (symOfEntries_isHermitian ((truncNormFactor ν ε N * (Real.sqrt N)⁻¹) • u.1))).1
  have h3 : |lambdaMax (normSmall ν ε u)| ≤ 3 := by
    change |lambdaMax (symOfEntries ((truncNormFactor ν ε N * (Real.sqrt N)⁻¹) • u.1))| ≤ 3
    rw [← hα]
    exact hge α
  have hdet := comparison_det (Hs := normSmall ν ε u) (m := m) (m' := m')
    (B := (N : ℝ) ^ (-(3 : ℝ) / 4)) hσ (symOfEntries_isHermitian _) (pertMat_props ε u).1
    (by rw [← ht]; exact hlam) h3
  have hEq : edgeScaled N (coupleMap m m' u) -
      (N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (normSmall ν ε u) - 2) =
      (N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (σ • normSmall ν ε u + pertMat ε u +
        shiftMat N m m') - lambdaMax (normSmall ν ε u)) := by
    unfold edgeScaled
    rw [wignerMatrix_coupleMap_eq_of_good ε m m' u hC hD, comparison_smallMat_eq hσ ht u]
    ring
  rw [Set.mem_ofPred_eq, hEq, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    at hu
  have := mul_le_mul_of_nonneg_left hdet (Real.rpow_nonneg (Nat.cast_nonneg N) ((2 : ℝ) / 3))
  linarith

/-! ### The budget -/

/-- A sequence with `N^a |g N| → 0` is eventually at most `κ N^{-1/24}` after multiplying by
`N^p`, whenever `p + 1/24 ≤ a`. -/
private lemma comparison_rpow_mul_le {g : ℕ → ℝ} {a p : ℝ}
    (hg : Tendsto (fun N : ℕ => (N : ℝ) ^ a * |g N|) atTop (𝓝 0)) (hp : p + 1 / 24 ≤ a)
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ p * |g N| ≤ κ * (N : ℝ) ^ (-(1 : ℝ) / 24) := by
  filter_upwards [hg.eventually (ge_mem_nhds hκ), eventually_ge_atTop 1] with N hN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have h1 : (N : ℝ) ^ (p + 1 / 24) ≤ (N : ℝ) ^ a := Real.rpow_le_rpow_of_exponent_le hN1' hp
  have hX : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 24) := Real.rpow_nonneg hNpos.le _
  have e : (N : ℝ) ^ p = (N : ℝ) ^ (-(1 : ℝ) / 24) * (N : ℝ) ^ (p + 1 / 24) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have h2 : (N : ℝ) ^ (p + 1 / 24) * |g N| ≤ κ :=
    le_trans (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) hN
  calc (N : ℝ) ^ p * |g N|
      = (N : ℝ) ^ (-(1 : ℝ) / 24) * ((N : ℝ) ^ (p + 1 / 24) * |g N|) := by rw [e]; ring
    _ ≤ (N : ℝ) ^ (-(1 : ℝ) / 24) * κ := mul_le_mul_of_nonneg_left h2 hX
    _ = κ * (N : ℝ) ^ (-(1 : ℝ) / 24) := mul_comm _ _

/-- The sum of the shifts of the deterministic step is at most `N^{-1/24}`: the shift of `M`, the
rescaling `H^S → H̃^S`, and the barrier `N^{2/3} N^{-3/4} = N^{-1/12}`. -/
private lemma comparison_budget {N : ℕ} (hN : 0 < (N : ℝ)) {m m' σ d : ℝ}
    (hσ : σ ≤ 10 / 9) (hd : |σ - 1| ≤ d)
    (h1 : (N : ℝ) ^ ((7 : ℝ) / 6) * |m| ≤ 1 / 10 * (N : ℝ) ^ (-(1 : ℝ) / 24))
    (h2 : (N : ℝ) ^ ((1 : ℝ) / 6) * |m'| ≤ 1 / 10 * (N : ℝ) ^ (-(1 : ℝ) / 24))
    (h3 : (N : ℝ) ^ ((1 : ℝ) / 6) * |m| ≤ 1 / 10 * (N : ℝ) ^ (-(1 : ℝ) / 24))
    (h4 : (N : ℝ) ^ ((2 : ℝ) / 3) * d ≤ 1 / 30 * (N : ℝ) ^ (-(1 : ℝ) / 24))
    (h5 : (N : ℝ) ^ (-(1 : ℝ) / 24) ≤ 9 / 20) :
    (N : ℝ) ^ ((2 : ℝ) / 3) * (Real.sqrt N * |m| + |m' - m| / Real.sqrt N +
      σ * (N : ℝ) ^ (-(3 : ℝ) / 4) + 3 * |σ - 1|) ≤ (N : ℝ) ^ (-(1 : ℝ) / 24) := by
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hX : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 24) := Real.rpow_nonneg hN.le _
  have hp23 : 0 ≤ (N : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hN.le _
  have hp16 : 0 ≤ (N : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_nonneg hN.le _
  have e1 : (N : ℝ) ^ ((2 : ℝ) / 3) * Real.sqrt N = (N : ℝ) ^ ((7 : ℝ) / 6) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN]
    congr 1
    norm_num
  have e2 : (N : ℝ) ^ ((2 : ℝ) / 3) / Real.sqrt N = (N : ℝ) ^ ((1 : ℝ) / 6) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hN]
    congr 1
    norm_num
  have e3 : (N : ℝ) ^ ((2 : ℝ) / 3) * (N : ℝ) ^ (-(3 : ℝ) / 4) =
      (N : ℝ) ^ (-(1 : ℝ) / 24) * (N : ℝ) ^ (-(1 : ℝ) / 24) := by
    rw [← Real.rpow_add hN, ← Real.rpow_add hN]
    congr 1
    norm_num
  have hm : |m' - m| ≤ |m'| + |m| := abs_sub m' m
  have hexp : (N : ℝ) ^ ((2 : ℝ) / 3) * (Real.sqrt N * |m| + |m' - m| / Real.sqrt N +
      σ * (N : ℝ) ^ (-(3 : ℝ) / 4) + 3 * |σ - 1|) =
      (N : ℝ) ^ ((2 : ℝ) / 3) * Real.sqrt N * |m| +
        (N : ℝ) ^ ((2 : ℝ) / 3) / Real.sqrt N * |m' - m| +
        σ * ((N : ℝ) ^ ((2 : ℝ) / 3) * (N : ℝ) ^ (-(3 : ℝ) / 4)) +
        3 * ((N : ℝ) ^ ((2 : ℝ) / 3) * |σ - 1|) := by ring
  rw [hexp, e1, e2, e3]
  have h6 : (N : ℝ) ^ ((1 : ℝ) / 6) * |m' - m| ≤ 1 / 10 * (N : ℝ) ^ (-(1 : ℝ) / 24) +
      1 / 10 * (N : ℝ) ^ (-(1 : ℝ) / 24) := by
    calc (N : ℝ) ^ ((1 : ℝ) / 6) * |m' - m|
        ≤ (N : ℝ) ^ ((1 : ℝ) / 6) * (|m'| + |m|) := mul_le_mul_of_nonneg_left hm hp16
      _ = (N : ℝ) ^ ((1 : ℝ) / 6) * |m'| + (N : ℝ) ^ ((1 : ℝ) / 6) * |m| := by ring
      _ ≤ _ := add_le_add h2 h3
  have h7 : (N : ℝ) ^ ((2 : ℝ) / 3) * |σ - 1| ≤ 1 / 30 * (N : ℝ) ^ (-(1 : ℝ) / 24) :=
    le_trans (mul_le_mul_of_nonneg_left hd hp23) h4
  have h8 : σ * ((N : ℝ) ^ (-(1 : ℝ) / 24) * (N : ℝ) ^ (-(1 : ℝ) / 24)) ≤
      1 / 2 * (N : ℝ) ^ (-(1 : ℝ) / 24) := by
    set X := (N : ℝ) ^ (-(1 : ℝ) / 24)
    nlinarith [mul_nonneg hX (sub_nonneg.2 h5), mul_nonneg hX (sub_nonneg.2 hσ)]
  linarith

/-! ### Assembly -/

/-- (4.17), (4.23), (4.24), (4.26) and the rescaling `H^S → H̃^S`:
`|N^{2/3}(λ_N(H) - 2) - N^{2/3}(λ_N(H̃^S) - 2)| ≤ N^{-1/24}` with probability `1 - o(1)`. -/
theorem tendsto_coupleLaw_edge_close {ν ν' : Measure ℝ} (hW : WignerLaws ν ν')
    (h14 : TailCond ν) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 30) :
    Tendsto (fun N : ℕ => (coupleLaw ν ν' ε N {u | (N : ℝ) ^ (-(1 : ℝ) / 24) <
      |edgeScaled N (coupleMap (cutoffMean ν ((N : ℝ) ^ (1 / 2 - ε)))
          (cutoffMean ν' ((N : ℝ) ^ (1 / 2 - ε))) u) -
        (N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (normSmall ν ε u) - 2)|}).toReal) atTop (𝓝 0) := by
  have hprob := hW.prob
  have hprob' := hW.prob'
  have h1 := tendsto_coupleLaw_cutoff hW h14 hε0 (by linarith)
  have h2 := tendsto_coupleLaw_not_selGood hW h14 hε0 (by linarith)
  have h3 := tendsto_coupleLaw_claim426 hW h14 hε0 hε
  obtain ⟨C1, N0, hcl⟩ := truncLawsNorm_smallQClass hW h14 hε0 (by linarith)
  obtain ⟨C, hC, hHP⟩ := highProb_smallGood (C1 := C1) (φs := 3 * ε / 4) hε0 (by linarith)
    (by linarith)
  obtain ⟨e, he, hev⟩ := hHP.tendstoOneOn one_pos
  obtain ⟨hm, hm'⟩ := cutoffMean_bounds hW h14 hε0 (by linarith)
  have hσ := truncCentered_sq_sub_one hW h14 hε0 (by linarith)
  have hpow : ∀ r : ℝ, r < 0 → Tendsto (fun N : ℕ => (N : ℝ) ^ r) atTop (𝓝 0) := fun r hr => by
    have := (tendsto_rpow_neg_atTop (y := -r) (by linarith)).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using this
  have hevall := (eventually_cutoff_mass_ne_zero (ν := ν) (ν' := ν') (ε := ε) (by linarith)).and
    (hev.and ((eventually_ge_atTop (max N0 1)).and
    ((comparison_rpow_mul_le (g := fun N : ℕ => cutoffMean ν ((N : ℝ) ^ (1 / 2 - ε)))
        hm (p := (7 : ℝ) / 6) (by linarith) (κ := 1 / 10) (by norm_num)).and
    ((comparison_rpow_mul_le (g := fun N : ℕ => cutoffMean ν' ((N : ℝ) ^ (1 / 2 - ε)))
        hm' (p := (1 : ℝ) / 6) (by linarith) (κ := 1 / 10) (by norm_num)).and
    ((comparison_rpow_mul_le (g := fun N : ℕ => cutoffMean ν ((N : ℝ) ^ (1 / 2 - ε)))
        hm (p := (1 : ℝ) / 6) (by linarith) (κ := 1 / 10) (by norm_num)).and
    ((comparison_rpow_mul_le (g := fun N : ℕ =>
        ∫ x, x ^ 2 ∂(truncCentered ν ((N : ℝ) ^ (1 / 2 - ε))) - 1)
        hσ (p := (2 : ℝ) / 3) (by linarith) (κ := 1 / 30) (by norm_num)).and
    ((hpow (-(1 : ℝ) / 24) (by norm_num)).eventually
      (ge_mem_nhds (by norm_num : (0 : ℝ) < 9 / 20)) |>.and
    (hσ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 19 / 100))))))))))
  have hg : Tendsto (fun N : ℕ => (coupleLaw ν ν' ε N
      {u | ∃ i j, 3 / 4 < |(largeMat u - smallMat u) i j * selMat u i j|}).toReal +
      (coupleLaw ν ν' ε N {u | ¬ SelGood ε u.2.2}).toReal +
      (coupleLaw ν ν' ε N {u | (N : ℝ) ^ (-(3 : ℝ) / 4) <
        |lambdaMax (normSmall ν ε u + truncNormFactor ν ε N • pertMat ε u) -
          lambdaMax (normSmall ν ε u)|}).toReal + max (e N) 0) atTop (𝓝 0) := by
    have := ((h1.add h2).add h3).add (he.max (tendsto_const_nhds (x := (0 : ℝ))))
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun N => ENNReal.toReal_nonneg) ?_ hg
  filter_upwards [hevall] with N ⟨⟨hS, hS'⟩, hevN, hN, hA1, hA2, hA3, hA4, hA5, hA6⟩
  have := isProbabilityMeasure_coupleLaw (ε := ε) hS hS'
  have hN0 : N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have : NeZero N := ⟨by omega⟩
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  -- the normalisation `σ = √(E|x^S_12|²) ∈ [9/10, 10/9]`
  set σ2 : ℝ := ∫ x, x ^ 2 ∂(truncCentered ν ((N : ℝ) ^ (1 / 2 - ε))) with hσ2
  have hσ2' : |σ2 - 1| < 19 / 100 := by
    have hone : (1 : ℝ) ≤ (N : ℝ) ^ (1 - 2 * ε) := Real.one_le_rpow hN1' (by linarith)
    nlinarith [abs_nonneg (σ2 - 1)]
  have hσ2l : 81 / 100 ≤ σ2 := by linarith [(abs_lt.mp hσ2').1]
  have hσ2u : σ2 ≤ 119 / 100 := by linarith [(abs_lt.mp hσ2').2]
  set σ : ℝ := Real.sqrt σ2 with hσdef
  have hσpos : 0 < σ := Real.sqrt_pos.mpr (by linarith)
  have hσle : σ ≤ 10 / 9 := (Real.sqrt_le_iff).2 ⟨by norm_num, by linarith⟩
  have hσsq : σ ^ 2 = σ2 := Real.sq_sqrt (by linarith)
  have ht : truncNormFactor ν ε N = σ⁻¹ := rfl
  have hσd : |σ - 1| ≤ |σ2 - 1| := by
    have h : σ2 - 1 = (σ - 1) * (σ + 1) := by nlinarith
    rw [h, abs_mul, abs_of_pos (by linarith : 0 < σ + 1)]
    nlinarith [abs_nonneg (σ - 1)]
  have hbud := comparison_budget hNpos hσle hσd hA1 hA2 hA3 hA4 hA5
  have hsub := comparison_subset (ν := ν) (ε := ε) (N := N) (C := C) hσpos ht hbud
  set μ := coupleLaw ν ν' ε N
  have h4 : (μ {u | (truncNormFactor ν ε N * (Real.sqrt N)⁻¹) • u.1 ∈
      (smallGood N C ε)ᶜ}).toReal ≤ max (e N) 0 :=
    ENNReal.toReal_le_of_le_ofReal (le_max_right _ _)
      ((coupleLaw_normSmall_le hS hS' _).trans ((hevN _ (hcl N hN0)).trans
        (ENNReal.ofReal_le_ofReal (le_max_left _ _))))
  calc _ ≤ (μ {u | ∃ i j, 3 / 4 < |(largeMat u - smallMat u) i j * selMat u i j|} +
        μ {u | ¬ SelGood ε u.2.2} +
        μ {u | (N : ℝ) ^ (-(3 : ℝ) / 4) <
          |lambdaMax (normSmall ν ε u + truncNormFactor ν ε N • pertMat ε u) -
            lambdaMax (normSmall ν ε u)|} +
        μ {u | (truncNormFactor ν ε N * (Real.sqrt N)⁻¹) • u.1 ∈ (smallGood N C ε)ᶜ}).toReal :=
        ENNReal.toReal_mono (by finiteness)
          ((measure_mono hsub).trans ((measure_union_le _ _).trans
            (add_le_add ((measure_union_le _ _).trans
              (add_le_add_left (measure_union_le _ _) _)) le_rfl)))
    _ = _ := by
        rw [ENNReal.toReal_add (by finiteness) (by finiteness),
          ENNReal.toReal_add (by finiteness) (by finiteness),
          ENNReal.toReal_add (by finiteness) (by finiteness)]
    _ ≤ _ := by gcongr

/-! ### An instance: Rademacher off-diagonal entries, `N(0, 2)` diagonal entries, `ε = 1/100`;
at `N = 1000` the cut-off laws exist and no off-diagonal entry exceeds the cut-off -/

private lemma comparison_one_le_T : (1 : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ)) :=
  Real.one_le_rpow (by norm_num) (by norm_num)

/-- The small-mass condition for Rademacher entries. -/
private lemma comparison_hS :
    rademacher {x : ℝ | |x| ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))} ≠ 0 := by
  have h1 : Measure.dirac (1 : ℝ) {x : ℝ | |x| ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))} = 1 :=
    Measure.dirac_apply_of_mem (by simpa using comparison_one_le_T)
  simp only [rademacher, Measure.smul_apply, Measure.add_apply, h1, smul_eq_mul]
  simp

/-- The small-mass condition for `N(0, 2)` diagonal entries. -/
private lemma comparison_hS' :
    gaussianReal 0 2 {x : ℝ | |x| ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))} ≠ 0 := by
  intro h
  have h0 := gaussianReal_absolutelyContinuous' 0 (by norm_num : (2 : NNReal) ≠ 0) h
  have hsub : Set.Icc (-1 : ℝ) 1 ⊆
      {x : ℝ | |x| ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))} := fun x hx =>
    (abs_le.mpr ⟨hx.1, hx.2⟩).trans comparison_one_le_T
  have := measure_mono_null hsub h0
  rw [Real.volume_Icc] at this
  norm_num at this

/-- Degenerate large part: no Rademacher entry exceeds the cut-off, so the law of the large
entries is the junk law `δ₀`. -/
example : truncLargeCentered rademacher (((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))) =
    Measure.dirac 0 := by
  have hT' : (1 : ℝ) ≤ (1000 : ℝ) ^ ((2 : ℝ)⁻¹ - (100 : ℝ)⁻¹) :=
    Real.one_le_rpow (by norm_num) (by norm_num)
  have h0 : rademacher {x : ℝ | ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ)) < |x|} = 0 := by
    simp only [rademacher, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply,
      smul_eq_mul]
    simp [hT']
  simp only [truncLargeCentered, h0, ↓reduceIte]

/-- The probability space of (4.16) at `N = 1000`, and the law of the coupled matrix there. -/
example : IsProbabilityMeasure (coupleLaw rademacher (gaussianReal 0 2) (1 / 100) 1000) := by
  have := rademacher_wignerLaws.prob
  exact isProbabilityMeasure_coupleLaw comparison_hS comparison_hS'

/-- (4.16) at the instance: the coupled entries have the law `entryLaw` of the Wigner matrix. -/
example : (coupleLaw rademacher (gaussianReal 0 2) (1 / 100) 1000).map
    (coupleMap (cutoffMean rademacher (((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))))
      (cutoffMean (gaussianReal 0 2) (((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))))) =
    entryLaw rademacher (gaussianReal 0 2) 1000 := by
  have := rademacher_wignerLaws.prob
  exact map_coupleMap_coupleLaw comparison_hS comparison_hS'

/-- The hypotheses hold at once for Rademacher off-diagonal entries and `N(0, 2)` diagonal
entries, `ε = 1/100`, and the conclusion follows. -/
example : Tendsto (fun N : ℕ => (coupleLaw rademacher (gaussianReal 0 2) (1 / 100) N
    {u | (N : ℝ) ^ (-(1 : ℝ) / 24) <
      |edgeScaled N (coupleMap (cutoffMean rademacher ((N : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))))
          (cutoffMean (gaussianReal 0 2) ((N : ℝ) ^ (1 / 2 - (1 / 100 : ℝ)))) u) -
        (N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (normSmall rademacher (1 / 100) u) - 2)|}).toReal)
    atTop (𝓝 0) :=
  tendsto_coupleLaw_edge_close rademacher_wignerLaws rademacher_tailCond (by norm_num)
    (by norm_num)

#print axioms tendsto_coupleLaw_edge_close

end WEdgeNS
