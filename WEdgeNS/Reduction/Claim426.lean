import WEdgeNS.Reduction.InputsSmall
import WEdgeNS.Reduction.OffDiagSelector
import WEdgeNS.Reduction.SelectorProb

/-!
# The largest eigenvalue under the sparse perturbation
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-! ### Deterministic step -/

private lemma claim426_smul_ne {N : ℕ} {t : ℝ} {E : Matrix (Fin N) (Fin N) ℝ} {i j : Fin N}
    (h : (t • E) i j ≠ 0) : E i j ≠ 0 := by
  intro h0
  apply h
  simp [h0]

private lemma claim426_pairPattern_smul {N : ℕ} (t : ℝ) {E : Matrix (Fin N) (Fin N) ℝ}
    (hE : PairPattern E) : PairPattern (t • E) := fun i j k l h1 h2 =>
  hE i j k l (claim426_smul_ne h1) (claim426_smul_ne h2)

private lemma claim426_nzCount_smul_le {N : ℕ} (t : ℝ) (E : Matrix (Fin N) (Fin N) ℝ) :
    nzCount (t • E) ≤ nzCount E :=
  Finset.card_le_card fun p hp => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact claim426_smul_ne hp

/-- A nonzero entry of `E` sits at a nonzero entry of the selector matrix. -/
private lemma claim426_selMat_ne {ε : ℝ} {N : ℕ} {u : CoupleSpace N} {i k : Fin N}
    (h : pertMat ε u i k ≠ 0) : selMat u i k ≠ 0 := by
  intro h0
  apply h
  simp only [pertMat, Matrix.hadamard_apply, selCut]
  split_ifs <;> simp [h0]

/-- The deterministic part of (4.40)–(4.47): the barrier bound and the Rayleigh bound give
`|λ_N(H + tE) - λ_N(H)| ≤ N^{-3/4}` from (4.38), (4.39), (4.45), delocalization (3.5) and the
Gershgorin and Rayleigh rows of the exponents. -/
private lemma claim426_det {N : ℕ} [NeZero N] {H E : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (hE : E.IsHermitian) (hEb : ∀ i j, |E i j| ≤ 3 / 4)
    (hpat : PairPattern E) {t C X A B x : ℝ} (ht0 : 0 < t) (ht : t ≤ 10 / 9)
    (hnz : (nzCount E : ℝ) ≤ X)
    (hdeloc : ∀ (v : Fin N → ℝ) (μ : ℝ), H *ᵥ v = μ • v → ∑ i, v i ^ 2 = 1 →
      ∀ i, v i ^ 2 ≤ phi N ^ C / N)
    (hdiag : ∀ i, ‖resolventC H (edgePt N) i i + 1‖ ≤ A)
    (hoff : ∀ i j, (∃ k, E i k ≠ 0) → (∃ k, E j k ≠ 0) → i ≠ j →
      ‖resolventC H (edgePt N) i j‖ ≤ B)
    (hshift : ∀ i j, ‖resolventC H ((lambdaMax H + (N : ℝ) ^ (-(3 : ℝ) / 4) : ℝ) : ℂ) i j -
      resolventC H (edgePt N) i j‖ ≤ x)
    (hA : A ≤ 1 / 60) (hX : 1 ≤ X) (hB : 0 ≤ B) (hXB : X * B ≤ 1 / 60) (hx : 0 ≤ x)
    (hXx : X * x ≤ 1 / 60) (hφ : 0 ≤ phi N ^ C / N)
    (hray : X * (phi N ^ C / N) ≤ (N : ℝ) ^ (-(3 : ℝ) / 4)) :
    |lambdaMax (H + t • E) - lambdaMax H| ≤ (N : ℝ) ^ (-(3 : ℝ) / 4) := by
  have hE' : (t • E).IsHermitian := hE.smul (IsSelfAdjoint.all t)
  have hκ : ∀ i j, |(t • E) i j| ≤ t * (3 / 4) := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos ht0]
    exact mul_le_mul_of_nonneg_left (hEb i j) ht0.le
  have hκ0 : 0 < t * (3 / 4) := by positivity
  have hκ1 : t * (3 / 4) ≤ 5 / 6 := by linarith
  have hκinv : 6 / 5 ≤ (t * (3 / 4))⁻¹ := by
    have := inv_anti₀ hκ0 hκ1
    norm_num at this ⊢
    linarith
  have hnz' : (nzCount (t • E) : ℝ) ≤ X :=
    le_trans (by exact_mod_cast claim426_nzCount_smul_le t E) hnz
  have hnz0 : (0 : ℝ) ≤ nzCount (t • E) := Nat.cast_nonneg _
  have hxX : x ≤ X * x := le_mul_of_one_le_left hx hX
  have hBX : B ≤ X * B := le_mul_of_one_le_left hB hX
  have hupper := lambdaMax_add_lt_barrier hH hE' (claim426_pairPattern_smul t hpat) hκ0 hκ
    (a := A + x) (b := B + x) (by linarith)
    (fun i _ => by
      calc ‖resolventC H ((lambdaMax H + (N : ℝ) ^ (-(3 : ℝ) / 4) : ℝ) : ℂ) i i + 1‖
          = ‖(resolventC H ((lambdaMax H + (N : ℝ) ^ (-(3 : ℝ) / 4) : ℝ) : ℂ) i i -
              resolventC H (edgePt N) i i) + (resolventC H (edgePt N) i i + 1)‖ := by
            congr 1; ring
        _ ≤ _ := norm_add_le _ _
        _ ≤ x + A := add_le_add (hshift i i) (hdiag i)
        _ = A + x := add_comm _ _)
    (fun i j hi hj hij => by
      obtain ⟨k, hk⟩ := hi
      obtain ⟨l, hl⟩ := hj
      calc ‖resolventC H ((lambdaMax H + (N : ℝ) ^ (-(3 : ℝ) / 4) : ℝ) : ℂ) i j‖
          = ‖(resolventC H ((lambdaMax H + (N : ℝ) ^ (-(3 : ℝ) / 4) : ℝ) : ℂ) i j -
              resolventC H (edgePt N) i j) + resolventC H (edgePt N) i j‖ := by
            rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
        _ ≤ x + B := add_le_add (hshift i j)
            (hoff i j ⟨k, claim426_smul_ne hk⟩ ⟨l, claim426_smul_ne hl⟩ hij)
        _ = B + x := add_comm _ _)
    (by
      have h2 : 2 * (nzCount (t • E) : ℝ) * (B + x) ≤ 2 * X * (B + x) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      nlinarith)
  have hlower := lambdaMax_sub_le_lambdaMax_add hH hE' hdeloc hκ
  have hrayE : t * (3 / 4) * nzCount (t • E) * (phi N ^ C / N) ≤ (N : ℝ) ^ (-(3 : ℝ) / 4) := by
    refine le_trans ?_ hray
    have h1 : t * (3 / 4) * nzCount (t • E) ≤ X := by
      calc t * (3 / 4) * nzCount (t • E) ≤ 1 * nzCount (t • E) :=
            mul_le_mul_of_nonneg_right (by linarith) hnz0
        _ ≤ X := by linarith
    exact mul_le_mul_of_nonneg_right h1 hφ
  rw [abs_le]
  constructor <;> linarith

/-! ### (4.26) -/

/-- (4.26) for the rescaled pair `(H̃^S, Ẽ = E / σ_S)`: `|λ_N(H̃^S + Ẽ) - λ_N(H̃^S)| ≤ N^{-3/4}`
with probability `1 - o(1)`. -/
theorem tendsto_coupleLaw_claim426 {ν ν' : Measure ℝ} (hW : WignerLaws ν ν')
    (h14 : TailCond ν) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 30) :
    Tendsto (fun N : ℕ => (coupleLaw ν ν' ε N {u | (N : ℝ) ^ (-(3 : ℝ) / 4) <
      |lambdaMax (normSmall ν ε u + truncNormFactor ν ε N • pertMat ε u) -
        lambdaMax (normSmall ν ε u)|}).toReal) atTop (𝓝 0) := by
  have hprob := hW.prob
  have hprob' := hW.prob'
  have h1 := tendsto_coupleLaw_not_selGood hW h14 hε0 (by linarith)
  have h3 := tendsto_coupleLaw_offDiag hW h14 hε0 hε
  obtain ⟨C1, N0, hcl⟩ := truncLawsNorm_smallQClass hW h14 hε0 (by linarith)
  obtain ⟨C, hC, hHP⟩ := highProb_smallGood (C1 := C1) (φs := 3 * ε / 4) hε0 (by linarith)
    (by linarith)
  obtain ⟨e, he, hev⟩ := hHP.tendstoOneOn one_pos
  obtain ⟨Nb, hNb⟩ := norm_resolventC_barrier_sub_le hC
  have hσ := truncCentered_sq_sub_one hW h14 hε0 (by linarith)
  set δ : ℝ := (1 / 4 - 5 * ε) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hpow : ∀ r : ℝ, r < 0 → Tendsto (fun N : ℕ => (N : ℝ) ^ r) atTop (𝓝 0) := fun r hr => by
    have := (tendsto_rpow_neg_atTop (y := -r) (by linarith)).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using this
  have hsmall : ∀ r : ℝ, r < 0 → ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ r ≤ 1 / 60 := fun r hr =>
    (hpow r hr).eventually (ge_mem_nhds (by norm_num))
  have hevall := (eventually_cutoff_mass_ne_zero (ν := ν) (ν' := ν') (ε := ε) (by linarith)).and
    (hev.and ((eventually_ge_atTop (max (max N0 Nb) 1)).and
      ((phi_rpow_le_rpow (5 * C) hδ0).and
      ((phi_rpow_le_rpow C (c := 1 / 4 - 5 * ε) (by linarith)).and
      ((hsmall (-ε / 2) (by linarith)).and
      ((hsmall (5 * ε - 1 / 6) (by linarith)).and
      ((hsmall (-δ) (by linarith)).and
      (hσ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 19 / 100))))))))))
  have hg : Tendsto (fun N : ℕ => (coupleLaw ν ν' ε N {u | ¬ SelGood ε u.2.2}).toReal +
      max (e N) 0 + (coupleLaw ν ν' ε N {u | SelGood ε u.2.2 ∧ ∃ i j, i ≠ j ∧
      (∃ k, selMat u i k ≠ 0) ∧ (∃ k, selMat u j k ≠ 0) ∧
      (N : ℝ) ^ (-(1 : ℝ) / 6) < ‖resolventC (normSmall ν ε u) (edgePt N) i j‖}).toReal)
      atTop (𝓝 0) := by
    have := (h1.add (he.max (tendsto_const_nhds (x := (0 : ℝ))))).add h3
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun N => ENNReal.toReal_nonneg) ?_ hg
  filter_upwards [hevall] with N ⟨⟨hS, hS'⟩, hevN, hN, hφ5, hφ1, hA, hXB, hXx, hσN⟩
  have := isProbabilityMeasure_coupleLaw (ε := ε) hS hS'
  have hN0 : N0 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb' : Nb ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have : NeZero N := ⟨by omega⟩
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  -- the normalisation `t = σ⁻¹ ∈ (0, 10/9]`
  set σ2 : ℝ := ∫ x, x ^ 2 ∂(truncCentered ν ((N : ℝ) ^ (1 / 2 - ε))) with hσ2
  have hσ2' : 81 / 100 ≤ σ2 := by
    have hone : (1 : ℝ) ≤ (N : ℝ) ^ (1 - 2 * ε) := Real.one_le_rpow hN1' (by linarith)
    have : |σ2 - 1| < 19 / 100 := by
      nlinarith [abs_nonneg (σ2 - 1)]
    linarith [(abs_lt.mp this).1]
  have hsq : 9 / 10 ≤ Real.sqrt σ2 := (Real.le_sqrt (by norm_num) (by linarith)).2 (by linarith)
  have ht0 : 0 < truncNormFactor ν ε N := by
    unfold truncNormFactor
    rw [← hσ2]
    exact inv_pos.2 (by linarith)
  have ht : truncNormFactor ν ε N ≤ 10 / 9 := by
    unfold truncNormFactor
    rw [← hσ2]
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 9 / 10) hsq
    norm_num at this ⊢
    linarith
  -- the scales
  set X : ℝ := (N : ℝ) ^ (5 * ε) with hXdef
  have hX : 1 ≤ X := Real.one_le_rpow hN1' (by linarith)
  have hφ0 : ∀ c : ℝ, 0 ≤ phi N ^ c := fun c => by
    unfold phi
    exact Real.rpow_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg N) _) _
  have hXB' : X * (N : ℝ) ^ (-(1 : ℝ) / 6) ≤ 1 / 60 := by
    rw [hXdef, ← Real.rpow_add hNpos]
    convert hXB using 2
    ring
  have hXx' : X * (phi N ^ (5 * C) * (N : ℝ) ^ (-(1 : ℝ) / 4)) ≤ 1 / 60 := by
    refine le_trans ?_ hXx
    calc X * (phi N ^ (5 * C) * (N : ℝ) ^ (-(1 : ℝ) / 4))
        ≤ X * ((N : ℝ) ^ δ * (N : ℝ) ^ (-(1 : ℝ) / 4)) := by
          gcongr
      _ = (N : ℝ) ^ (-δ) := by
          rw [hXdef, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
          congr 1
          rw [hδ]
          ring
  have hray : X * (phi N ^ C / N) ≤ (N : ℝ) ^ (-(3 : ℝ) / 4) := by
    calc X * (phi N ^ C / N) ≤ X * ((N : ℝ) ^ (1 / 4 - 5 * ε) / N) := by
          gcongr
      _ = (N : ℝ) ^ (-(3 : ℝ) / 4) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg_one, hXdef, ← mul_assoc, ← Real.rpow_add hNpos,
            ← Real.rpow_add hNpos]
          congr 1
          ring
  -- the three bad events
  have hsub : {u : CoupleSpace N | (N : ℝ) ^ (-(3 : ℝ) / 4) <
      |lambdaMax (normSmall ν ε u + truncNormFactor ν ε N • pertMat ε u) -
        lambdaMax (normSmall ν ε u)|} ⊆
      {u | ¬ SelGood ε u.2.2} ∪
        {u | (truncNormFactor ν ε N * (Real.sqrt N)⁻¹) • u.1 ∈ (smallGood N C ε)ᶜ} ∪
        {u | SelGood ε u.2.2 ∧ ∃ i j, i ≠ j ∧
          (∃ k, selMat u i k ≠ 0) ∧ (∃ k, selMat u j k ≠ 0) ∧
          (N : ℝ) ^ (-(1 : ℝ) / 6) < ‖resolventC (normSmall ν ε u) (edgePt N) i j‖} := by
    intro u hu
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_compl_iff, not_or, not_not,
      not_and, not_exists, not_lt] at hnot
    obtain ⟨⟨hsel, hgood⟩, hoff⟩ := hnot
    obtain ⟨hg1, hg2, hg3, hg4, hg5, -⟩ := hgood
    obtain ⟨hEh, hEb, hEnz, hEpat⟩ := pertMat_props ε u
    have hH := symOfEntries_isHermitian ((truncNormFactor ν ε N * (Real.sqrt N)⁻¹) • u.1)
    have hshift := hNb N hNb' _ hH hg2 hg4 hg5 hg3
    rw [Set.mem_ofPred_eq] at hu
    refine absurd hu (not_lt.2 ?_)
    exact claim426_det (C := C) hH hEh hEb hEpat ht0 ht hEnz hg2 hg1
      (fun i j ⟨k, hk⟩ ⟨l, hl⟩ hij => hoff hsel i j hij ⟨k, claim426_selMat_ne hk⟩
        ⟨l, claim426_selMat_ne hl⟩)
      hshift hA hX (Real.rpow_nonneg hNpos.le _) hXB'
      (mul_nonneg (hφ0 _) (Real.rpow_nonneg hNpos.le _)) hXx'
      (div_nonneg (hφ0 C) hNpos.le) hray
  set μ := coupleLaw ν ν' ε N
  have h2 : (μ {u | (truncNormFactor ν ε N * (Real.sqrt N)⁻¹) • u.1 ∈
      (smallGood N C ε)ᶜ}).toReal ≤ max (e N) 0 :=
    ENNReal.toReal_le_of_le_ofReal (le_max_right _ _)
      ((coupleLaw_normSmall_le hS hS' _).trans ((hevN _ (hcl N hN0)).trans
        (ENNReal.ofReal_le_ofReal (le_max_left _ _))))
  calc _ ≤ (μ {u | ¬ SelGood ε u.2.2} +
        μ {u | (truncNormFactor ν ε N * (Real.sqrt N)⁻¹) • u.1 ∈ (smallGood N C ε)ᶜ} +
        μ {u | SelGood ε u.2.2 ∧ ∃ i j, i ≠ j ∧
          (∃ k, selMat u i k ≠ 0) ∧ (∃ k, selMat u j k ≠ 0) ∧
          (N : ℝ) ^ (-(1 : ℝ) / 6) < ‖resolventC (normSmall ν ε u) (edgePt N) i j‖}).toReal :=
        ENNReal.toReal_mono (by finiteness)
          ((measure_mono hsub).trans ((measure_union_le _ _).trans
            (add_le_add_left (measure_union_le _ _) _)))
    _ = _ := by rw [ENNReal.toReal_add (by finiteness) (by finiteness),
          ENNReal.toReal_add (by finiteness) (by finiteness)]
    _ ≤ _ := by gcongr

/-! ### Non-vacuity at Rademacher off-diagonal entries and `N(0, 2)` diagonal entries,
`ε = 1/100`; at `N = 1000` the auxiliary law is a probability measure -/

private lemma claim426_one_le_T : (1 : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ)) :=
  Real.one_le_rpow (by norm_num) (by norm_num)

/-- The small-mass condition for Rademacher entries. -/
private lemma claim426_hS :
    rademacher {x : ℝ | |x| ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))} ≠ 0 := by
  have h1 : Measure.dirac (1 : ℝ) {x : ℝ | |x| ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))} = 1 :=
    Measure.dirac_apply_of_mem (by simpa using claim426_one_le_T)
  simp only [rademacher, Measure.smul_apply, Measure.add_apply, h1, smul_eq_mul]
  simp

/-- The small-mass condition for `N(0, 2)` diagonal entries. -/
private lemma claim426_hS' :
    gaussianReal 0 2 {x : ℝ | |x| ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))} ≠ 0 := by
  intro h
  have h0 := gaussianReal_absolutelyContinuous' 0 (by norm_num : (2 : NNReal) ≠ 0) h
  have hsub : Set.Icc (-1 : ℝ) 1 ⊆
      {x : ℝ | |x| ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))} := fun x hx =>
    (abs_le.mpr ⟨hx.1, hx.2⟩).trans claim426_one_le_T
  have := measure_mono_null hsub h0
  rw [Real.volume_Icc] at this
  norm_num at this

/-- The probability space of (4.26) at `N = 1000`. -/
example : IsProbabilityMeasure (coupleLaw rademacher (gaussianReal 0 2) (1 / 100) 1000) := by
  have := rademacher_wignerLaws.prob
  exact isProbabilityMeasure_coupleLaw claim426_hS claim426_hS'

/-- (4.26) for Rademacher off-diagonal entries, `N(0, 2)` diagonal entries and `ε = 1/100`. -/
example : Tendsto (fun N : ℕ => (coupleLaw rademacher (gaussianReal 0 2) (1 / 100) N
    {u | (N : ℝ) ^ (-(3 : ℝ) / 4) <
      |lambdaMax (normSmall rademacher (1 / 100) u +
          truncNormFactor rademacher (1 / 100) N • pertMat (1 / 100) u) -
        lambdaMax (normSmall rademacher (1 / 100) u)|}).toReal) atTop (𝓝 0) :=
  tendsto_coupleLaw_claim426 rademacher_wignerLaws rademacher_tailCond (by norm_num) (by norm_num)

#print axioms tendsto_coupleLaw_claim426

end WEdgeNS
