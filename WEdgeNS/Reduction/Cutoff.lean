import WEdgeNS.Reduction.Decomp
import WEdgeNS.Reduction.Barrier

/-!
# The sparse perturbation from the large entries
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- The admissible selector patterns of (4.24)–(4.25): at most `N^{5ε}` nonzero entries
(ordered pairs), pairwise equal or disjoint. -/
def SelGood (ε : ℝ) {N : ℕ} (c : Entries N) : Prop :=
  (nzCount (symOfEntries c) : ℝ) ≤ (N : ℝ) ^ (5 * ε) ∧ PairPattern (symOfEntries c)

open Classical in
/-- `D̃_ij = 1(|H̃_ij H^C_ij| ≤ 3/4) H̃_ij` of (4.22), with the absolute value. -/
def cutDiff {N : ℕ} (u : CoupleSpace N) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if |(largeMat u - smallMat u) i j * selMat u i j| ≤ 3 / 4
    then (largeMat u - smallMat u) i j else 0

open Classical in
/-- `H̃^C` of (4.24): the selector matrix on `SelGood`, `0` otherwise. -/
def selCut (ε : ℝ) {N : ℕ} (u : CoupleSpace N) : Matrix (Fin N) (Fin N) ℝ :=
  if SelGood ε u.2.2 then selMat u else 0

/-- `E = D̃ ∘ H̃^C` (after (4.25)). -/
def pertMat (ε : ℝ) {N : ℕ} (u : CoupleSpace N) : Matrix (Fin N) (Fin N) ℝ :=
  cutDiff u ⊙ selCut ε u

private lemma cutoff_symm {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (h : A.IsHermitian) (i j : Fin N) :
    A j i = A i j := by
  simpa using h.apply i j

private lemma cutoff_largeSub_herm {N : ℕ} (u : CoupleSpace N) :
    (largeMat u - smallMat u).IsHermitian :=
  (symOfEntries_isHermitian _).sub (symOfEntries_isHermitian _)

private lemma cutDiff_herm {N : ℕ} (u : CoupleSpace N) : (cutDiff u).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, cutDiff]
  have h1 : (largeMat u - smallMat u) j i = (largeMat u - smallMat u) i j :=
    cutoff_symm (cutoff_largeSub_herm u) i j
  have h2 : selMat u j i = selMat u i j := cutoff_symm (symOfEntries_isHermitian u.2.2) i j
  rw [h1, h2]

private lemma selCut_herm (ε : ℝ) {N : ℕ} (u : CoupleSpace N) : (selCut ε u).IsHermitian := by
  unfold selCut
  split_ifs
  · exact symOfEntries_isHermitian _
  · exact Matrix.isHermitian_zero

private lemma selCut_apply_ne {N : ℕ} {ε : ℝ} {u : CoupleSpace N} {i j : Fin N}
    (h : selCut ε u i j ≠ 0) : SelGood ε u.2.2 ∧ symOfEntries u.2.2 i j ≠ 0 := by
  unfold selCut at h
  split_ifs at h with hC
  · exact ⟨hC, h⟩
  · exact absurd rfl h

/-- `E` is symmetric, `max |E_ij| ≤ 3/4`, it has at most `N^{5ε}` nonzero entries, and its
nonzero entries sit on equal or disjoint index pairs. -/
theorem pertMat_props (ε : ℝ) {N : ℕ} (u : CoupleSpace N) :
    (pertMat ε u).IsHermitian ∧ (∀ i j, |pertMat ε u i j| ≤ 3 / 4) ∧
      (nzCount (pertMat ε u) : ℝ) ≤ (N : ℝ) ^ (5 * ε) ∧ PairPattern (pertMat ε u) := by
  have hne : ∀ i j, pertMat ε u i j ≠ 0 →
      SelGood ε u.2.2 ∧ symOfEntries u.2.2 i j ≠ 0 := by
    intro i j h
    apply selCut_apply_ne
    intro h0
    apply h
    simp [pertMat, Matrix.hadamard_apply, h0]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    simp only [pertMat, Matrix.conjTranspose_apply, star_trivial, Matrix.hadamard_apply]
    rw [cutoff_symm (cutDiff_herm u) i j, cutoff_symm (selCut_herm ε u) i j]
  · intro i j
    have h0 : pertMat ε u i j = cutDiff u i j * selCut ε u i j := rfl
    by_cases hC : SelGood ε u.2.2
    · have hs : selCut ε u i j = selMat u i j := by simp only [selCut, hC, ite_true]
      by_cases hD : |(largeMat u - smallMat u) i j * selMat u i j| ≤ 3 / 4
      · have hc : cutDiff u i j = (largeMat u - smallMat u) i j := by
          simp only [cutDiff, hD, ite_true]
        rw [h0, hc, hs]
        exact hD
      · have hc : cutDiff u i j = 0 := by simp only [cutDiff, hD, ite_false]
        rw [h0, hc, zero_mul, abs_zero]
        norm_num
    · have hs : selCut ε u i j = 0 := by simp only [selCut, hC, ite_false]; rfl
      rw [h0, hs, mul_zero, abs_zero]
      norm_num
  · by_cases hC : SelGood ε u.2.2
    · refine le_trans ?_ hC.1
      exact_mod_cast Finset.card_le_card (fun p hp => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact (hne p.1 p.2 hp).2)
    · have : nzCount (pertMat ε u) = 0 := by
        unfold nzCount
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro p _ hp
        exact hC (hne p.1 p.2 hp).1
      rw [this]
      simp only [Nat.cast_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · intro i j k l hij hkl
    obtain ⟨hC, hij'⟩ := hne i j hij
    exact hC.2 i j k l hij' (hne k l hkl).2

/-- Off the events of (4.23) and (4.24), `H = H^S + E + M`. -/
theorem wignerMatrix_coupleMap_eq_of_good (ε m m' : ℝ) {N : ℕ} (u : CoupleSpace N)
    (hC : SelGood ε u.2.2)
    (hD : ∀ i j, |(largeMat u - smallMat u) i j * selMat u i j| ≤ 3 / 4) :
    wignerMatrix N (coupleMap m m' u) = smallMat u + pertMat ε u + shiftMat N m m' := by
  rw [wignerMatrix_coupleMap]
  congr 2
  ext i j
  simp only [pertMat, cutDiff, selCut, hC, hD, ite_true, Matrix.hadamard_apply]

/-! ### A nondegenerate instance: `N = 4`, `ε = 1/5`, one selected pair `{0, 1}` -/

/-- The selector block with `c_01 = 1` and all other entries `0`. -/
private def cutoffSel : Entries 4 :=
  (0, fun e => if e.1 = ((0 : Fin 4), (1 : Fin 4)) then 1 else 0)

/-- The large block with `x^L_01 = 1` and all other entries `0`. -/
private def cutoffLarge : Entries 4 := cutoffSel

/-- The point of the auxiliary space: small block `0`. -/
private def cutoffPt : CoupleSpace 4 := (0, cutoffLarge, cutoffSel)

private lemma cutoffSel_ne {i j : Fin 4} (h : symOfEntries cutoffSel i j ≠ 0) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  unfold symOfEntries cutoffSel at h
  by_cases hij : i = j
  · simp [hij] at h
  · by_cases hlt : i < j
    · simp only [hij, hlt, dite_false] at h
      by_cases hp : (i, j) = ((0 : Fin 4), (1 : Fin 4))
      · left
        exact Prod.mk.inj hp
      · exact absurd (by simp [hp]) h
    · simp only [hij, hlt, dite_false] at h
      by_cases hp : (j, i) = ((0 : Fin 4), (1 : Fin 4))
      · right
        exact ⟨(Prod.mk.inj hp).2, (Prod.mk.inj hp).1⟩
      · exact absurd (by simp [hp]) h

private lemma cutoffSel_01 : symOfEntries cutoffSel 0 1 = 1 := by
  simp [symOfEntries, cutoffSel]

private lemma cutoffSel_10 : symOfEntries cutoffSel 1 0 = 1 := by
  simp [symOfEntries, cutoffSel]

private lemma cutoffPt_selGood : SelGood (1 / 5) cutoffPt.2.2 := by
  have hsub : (Finset.univ.filter fun p : Fin 4 × Fin 4 => symOfEntries cutoffSel p.1 p.2 ≠ 0)
      ⊆ {((0 : Fin 4), (1 : Fin 4)), ((1 : Fin 4), (0 : Fin 4))} := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rcases cutoffSel_ne hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [Prod.ext_iff, h1, h2]
  refine ⟨?_, ?_⟩
  · have hc : nzCount (symOfEntries cutoffSel) ≤ 2 :=
      (Finset.card_le_card hsub).trans (Finset.card_le_two)
    have h4 : ((4 : ℕ) : ℝ) ^ (5 * (1 / 5 : ℝ)) = 4 := by
      rw [show 5 * (1 / 5 : ℝ) = 1 by norm_num, Real.rpow_one]
      norm_num
    change (nzCount (symOfEntries cutoffSel) : ℝ) ≤ ((4 : ℕ) : ℝ) ^ (5 * (1 / 5 : ℝ))
    rw [h4]
    have : (nzCount (symOfEntries cutoffSel) : ℝ) ≤ 2 := by exact_mod_cast hc
    linarith
  · intro i j k l hij hkl
    rcases cutoffSel_ne hij with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases cutoffSel_ne hkl with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      subst h1 h2 h3 h4 <;> left <;> first | rfl | exact Finset.pair_comm _ _

private lemma cutoff_symOfEntries_smul {N : ℕ} (a : ℝ) (ω : Entries N) (i j : Fin N) :
    symOfEntries (a • ω) i j = a * symOfEntries ω i j := by
  unfold symOfEntries
  split_ifs <;> simp

private lemma cutoffPt_sqrt : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
  rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

private lemma cutoffPt_diff (i j : Fin 4) :
    (largeMat cutoffPt - smallMat cutoffPt) i j = (1 / 2) * symOfEntries cutoffSel i j := by
  have hsm : smallMat cutoffPt i j = 0 := by
    simp only [smallMat, cutoffPt, cutoff_symOfEntries_smul]
    have : symOfEntries (0 : Entries 4) i j = 0 := by
      unfold symOfEntries
      split_ifs <;> simp
    rw [this, mul_zero]
  have hl : largeMat cutoffPt i j = (1 / 2) * symOfEntries cutoffSel i j := by
    simp only [largeMat, cutoffPt, cutoffLarge, cutoff_symOfEntries_smul, cutoffPt_sqrt]
    norm_num
  rw [Matrix.sub_apply, hsm, hl, sub_zero]

private lemma cutoffPt_prod (i j : Fin 4) :
    |(largeMat cutoffPt - smallMat cutoffPt) i j * selMat cutoffPt i j| ≤ 3 / 4 := by
  by_cases h : symOfEntries cutoffSel i j = 0
  · have : selMat cutoffPt i j = 0 := h
    rw [this, mul_zero, abs_zero]
    norm_num
  · have h1 : symOfEntries cutoffSel i j = 1 := by
      rcases cutoffSel_ne h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1 h2; exact cutoffSel_01
      · subst h1 h2; exact cutoffSel_10
    have : selMat cutoffPt i j = 1 := h1
    rw [cutoffPt_diff, h1, this]
    norm_num

private lemma cutoffPt_pert : pertMat (1 / 5) cutoffPt 0 1 = 1 / 2 := by
  have hs : selCut (1 / 5) cutoffPt 0 1 = 1 := by
    have hg := cutoffPt_selGood
    simp only [selCut, hg, ite_true]
    exact cutoffSel_01
  have hc : cutDiff cutoffPt 0 1 = 1 / 2 := by
    simp only [cutDiff, cutoffPt_prod, ite_true]
    rw [cutoffPt_diff, cutoffSel_01]
    norm_num
  change cutDiff cutoffPt 0 1 * selCut (1 / 5) cutoffPt 0 1 = 1 / 2
  rw [hc, hs, mul_one]

/-- A nondegenerate point at which both hypotheses of
`wignerMatrix_coupleMap_eq_of_good` hold and `E` is nonzero. -/
example (m m' : ℝ) :
    SelGood (1 / 5) cutoffPt.2.2 ∧
      (∀ i j, |(largeMat cutoffPt - smallMat cutoffPt) i j * selMat cutoffPt i j| ≤ 3 / 4) ∧
      pertMat (1 / 5) cutoffPt 0 1 = 1 / 2 ∧
      wignerMatrix 4 (coupleMap m m' cutoffPt) =
        smallMat cutoffPt + pertMat (1 / 5) cutoffPt + shiftMat 4 m m' :=
  ⟨cutoffPt_selGood, cutoffPt_prod, cutoffPt_pert,
    wignerMatrix_coupleMap_eq_of_good _ m m' _ cutoffPt_selGood cutoffPt_prod⟩

#print axioms pertMat_props
#print axioms wignerMatrix_coupleMap_eq_of_good

end WEdgeNS
