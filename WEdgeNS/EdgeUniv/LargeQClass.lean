import WEdgeNS.Model.Transfer
import WEdgeNS.Model.TestLaws

/-!
# The class of entry laws of the large-support edge universality
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- The class of Lemma 3.5 with the almost-sure support condition: Definition 2.1 with the diagonal
constant `C0`, and `|h_ij| ≤ N^{-φs}` almost surely. -/
def LargeQClass (C0 φs : ℝ) (N : ℕ) (L : EntryLaws N) : Prop :=
  L.IsGenWigner C0 ∧ L.BoundedSupportAS ((N : ℝ) ^ φs)

/-- The pairs of Lemma 3.5: a law of `LargeQClass` and the GOE. -/
def LargeQGoePair (C0 φs : ℝ) (N : ℕ) (Lv Lw : EntryLaws N) : Prop :=
  LargeQClass C0 φs N Lv ∧ Lw = goeLaws N

/-- Interpolation keeps the almost-sure support condition. -/
theorem EntryLaws.interp_boundedSupportAS {N : ℕ} {Φ : Fin N ⊕ OffDiag N → ℕ} {γ : ℕ}
    {Lv Lw : EntryLaws N} {q : ℝ} (hv : Lv.BoundedSupportAS q) (hw : Lw.BoundedSupportAS q) :
    (interp Φ γ Lv Lw).BoundedSupportAS q := by
  refine ⟨fun i => ?_, fun p => ?_⟩ <;> simp only [interp] <;> split_ifs
  exacts [hv.1 i, hw.1 i, hv.2 p, hw.2 p]

/-- The GOE is a generalized Wigner law with diagonal constant `1` (`E h_ii² = 2/N`). -/
theorem goeLaws_isGenWigner (N : ℕ) : (goeLaws N).IsGenWigner 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨⟨fun i => i.elim0, fun p => p.1.1.elim0⟩, fun i => i.elim0, fun p => p.1.1.elim0,
      fun i => i.elim0, fun p => p.1.1.elim0, fun p => p.1.1.elim0, fun i => i.elim0⟩
  · have h := ofIID_isGenWigner goe_wignerLaws hN
    have e : |∫ x, x ^ 2 ∂(gaussianReal 0 2) - 1| = 1 := by
      rw [integral_sq_gaussianReal]; norm_num
    rwa [e] at h

/-- Diagonal law at `N = 1024`: `±1/16` w.p. `1/4` each, `0` w.p. `1/2` (variance `2/N`). -/
private noncomputable def diagA : List ℝ := [1/16, -1/16, 0, 0]
/-- Off-diagonal law A: `±1/32` w.p. `1/2` each (variance `1/N`). -/
private noncomputable def offA : List ℝ := [1/32, -1/32]
/-- Off-diagonal law B: `±1/16` w.p. `1/8` each, `0` w.p. `3/4` (variance `1/N`). -/
private noncomputable def offB : List ℝ := [1/16, -1/16, 0, 0, 0, 0, 0, 0]

private noncomputable def lawA : EntryLaws 1024 := ⟨fun _ => unifList diagA, fun _ => unifList offA⟩
private noncomputable def lawB : EntryLaws 1024 := ⟨fun _ => unifList diagA, fun _ => unifList offB⟩

private lemma rpow1024 : ((1024 : ℕ) : ℝ) ^ ((2 : ℝ) / 5) = 16 := by
  rw [show ((1024 : ℕ) : ℝ) = (2 : ℝ) ^ (10 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

private lemma lawA_isGenWigner : lawA.IsGenWigner 1 := by
  refine ⟨⟨fun _ => unifList_prob _ (by simp [diagA]), fun _ => unifList_prob _ (by simp [offA])⟩,
    fun _ => integrable_unifList _ (by simp [diagA]) _,
    fun _ => integrable_unifList _ (by simp [offA]) _, fun _ => ?_, fun _ => ?_, fun _ => ?_,
    fun _ => ?_⟩
  · simp only [lawA]; rw [integral_unifList]; norm_num [diagA]
  · simp only [lawA]; rw [integral_unifList]; norm_num [offA]
  · simp only [lawA]; rw [integral_unifList]; norm_num [offA]
  · simp only [lawA]; rw [integral_unifList]; norm_num [diagA, abs_of_pos]

private lemma lawB_isGenWigner : lawB.IsGenWigner 1 := by
  refine ⟨⟨fun _ => unifList_prob _ (by simp [diagA]), fun _ => unifList_prob _ (by simp [offB])⟩,
    fun _ => integrable_unifList _ (by simp [diagA]) _,
    fun _ => integrable_unifList _ (by simp [offB]) _, fun _ => ?_, fun _ => ?_, fun _ => ?_,
    fun _ => ?_⟩
  · simp only [lawB]; rw [integral_unifList]; norm_num [diagA]
  · simp only [lawB]; rw [integral_unifList]; norm_num [offB]
  · simp only [lawB]; rw [integral_unifList]; norm_num [offB]
  · simp only [lawB]; rw [integral_unifList]; norm_num [diagA, abs_of_pos]

private lemma lawA_supp : lawA.BoundedSupportAS (((1024 : ℕ) : ℝ) ^ ((2 : ℝ) / 5)) := by
  rw [rpow1024]
  refine ⟨fun _ => unifList_tail _ _ ?_, fun _ => unifList_tail _ _ ?_⟩
  · intro a ha; simp [diagA] at ha; rcases ha with rfl | rfl | rfl <;> norm_num [abs_of_pos]
  · intro a ha; simp [offA] at ha; rcases ha with rfl | rfl <;> norm_num [abs_of_pos]

private lemma lawB_supp : lawB.BoundedSupportAS (((1024 : ℕ) : ℝ) ^ ((2 : ℝ) / 5)) := by
  rw [rpow1024]
  refine ⟨fun _ => unifList_tail _ _ ?_, fun _ => unifList_tail _ _ ?_⟩
  · intro a ha; simp [diagA] at ha; rcases ha with rfl | rfl | rfl <;> norm_num [abs_of_pos]
  · intro a ha; simp [offB] at ha; rcases ha with rfl | rfl | rfl <;> norm_num [abs_of_pos]

/-- Lemma 3.5 and Theorem 3.3 at a nondegenerate point: `N = 1024`, `φs = 2/5`,
`C0 = 1`; diagonal variance `2/N` ≠ off-diagonal variance `1/N`; the support `N^{-2/5} = 1/16` is
attained by the diagonal entries. -/
example : LargeQClass 1 (2 / 5) 1024 lawA ∧ (∀ i, ∫ x, x ^ 2 ∂(lawA.diag i) = 2 / (1024 : ℕ)) :=
  ⟨⟨lawA_isGenWigner, lawA_supp⟩, fun _ => by
    simp only [lawA]; rw [integral_unifList]; norm_num [diagA]⟩

/-- A pair of Lemma 3.5 (the GOE is the second law). -/
example : LargeQGoePair 1 (2 / 5) 1024 lawA (goeLaws 1024) :=
  ⟨⟨lawA_isGenWigner, lawA_supp⟩, rfl⟩

/-- Non-identically distributed entries in the class of Lemma 3.5: the interpolation at level
`γ = 1500` for the ordering `Φ` that lists the diagonal entries first (value `i`) and the
off-diagonal entries after them (value `2000 + i`) between laws A and B takes the diagonal laws of
A and the off-diagonal laws of B (off-diagonal laws `±1/32` and `{0, ±1/16}`). -/
example : LargeQClass (max 1 1) (2 / 5) 1024
    (interp (Sum.elim (fun i : Fin 1024 => (i : ℕ)) (fun p : OffDiag 1024 => 2000 + (p.1.1 : ℕ)))
      1500 lawA lawB) :=
  ⟨interp_isGenWigner lawA_isGenWigner lawB_isGenWigner,
    EntryLaws.interp_boundedSupportAS lawA_supp lawB_supp⟩

/-- The two off-diagonal laws differ: law A has no atom at `0`, law B has mass `3/4`. -/
example : ∫ x, x ^ 4 ∂(lawA.off ⟨(0, 1), by decide⟩) ≠
    ∫ x, x ^ 4 ∂(lawB.off ⟨(0, 1), by decide⟩) := by
  simp only [lawA, lawB]; rw [integral_unifList, integral_unifList]; norm_num [offA, offB]

#print axioms EntryLaws.interp_boundedSupportAS
#print axioms goeLaws_isGenWigner

end WEdgeNS
