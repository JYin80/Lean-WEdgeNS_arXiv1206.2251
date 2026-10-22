import WEdgeNS.LocalLaw.Class

/-!
# A polynomial lattice in the spectral domain `S(C)`
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- The cell of the square grid of mesh `(2 N³)⁻¹` containing `z`. -/
private def latticeCell (N : ℕ) (z : ℂ) : ℤ × ℤ :=
  (⌊z.re * (2 * (N : ℝ) ^ 3)⌋, ⌊z.im * (2 * (N : ℝ) ^ 3)⌋)

/-- The index set of the cells that can meet `S(C)`. -/
private def latticeIndex (N : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(10 * (N : ℤ) ^ 3)) (10 * (N : ℤ) ^ 3) ×ˢ Finset.Icc 0 (20 * (N : ℤ) ^ 3)

private lemma latticeIndex_card (N : ℕ) :
    ((latticeIndex N).card : ℝ) = (20 * (N : ℝ) ^ 3 + 1) * (20 * (N : ℝ) ^ 3 + 1) := by
  unfold latticeIndex
  rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
  have hN3 : (0 : ℤ) ≤ (N : ℤ) ^ 3 := by positivity
  have h1' : (((10 * (N : ℤ) ^ 3 + 1 - -(10 * (N : ℤ) ^ 3)).toNat : ℕ) : ℝ)
      = 20 * (N : ℝ) ^ 3 + 1 := by
    have hn : (0 : ℤ) ≤ 10 * (N : ℤ) ^ 3 + 1 - -(10 * (N : ℤ) ^ 3) := by linarith
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hn]; push_cast; ring
  have h2' : (((20 * (N : ℤ) ^ 3 + 1 - 0).toNat : ℕ) : ℝ) = 20 * (N : ℝ) ^ 3 + 1 := by
    have hn : (0 : ℤ) ≤ 20 * (N : ℤ) ^ 3 + 1 - 0 := by linarith
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hn]; push_cast; ring
  push_cast
  rw [h1', h2']

private lemma latticeCell_mem (N : ℕ) (C : ℝ) {z : ℂ} (hz : z ∈ specDomain N C) (hN : 2 ≤ N) :
    latticeCell N z ∈ latticeIndex N := by
  obtain ⟨hre, hlow, him⟩ := hz
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hphi : 0 ≤ phi N := Real.rpow_nonneg hlog _
  have hpos : 0 < z.im :=
    lt_of_le_of_lt (div_nonneg (Real.rpow_nonneg hphi _) (by positivity)) hlow
  have hM : (0 : ℝ) < 2 * (N : ℝ) ^ 3 := by positivity
  rw [abs_le] at hre
  simp only [latticeIndex, latticeCell, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have h : -(10 * (N : ℝ) ^ 3) ≤ z.re * (2 * (N : ℝ) ^ 3) := by nlinarith [hre.1]
    have h' : ((-(10 * (N : ℤ) ^ 3) : ℤ) : ℝ) ≤ z.re * (2 * (N : ℝ) ^ 3) := by
      push_cast; exact h
    exact Int.le_floor.mpr h'
  · have h : z.re * (2 * (N : ℝ) ^ 3) ≤ 10 * (N : ℝ) ^ 3 := by nlinarith [hre.2]
    have h2 : ((⌊z.re * (2 * (N : ℝ) ^ 3)⌋ : ℤ) : ℝ) ≤ ((10 * (N : ℤ) ^ 3 : ℤ) : ℝ) := by
      push_cast; exact (Int.floor_le _).trans h
    exact_mod_cast h2
  · exact Int.floor_nonneg.mpr (by positivity)
  · have h : z.im * (2 * (N : ℝ) ^ 3) ≤ 20 * (N : ℝ) ^ 3 := by nlinarith
    have h2 : ((⌊z.im * (2 * (N : ℝ) ^ 3)⌋ : ℤ) : ℝ) ≤ ((20 * (N : ℤ) ^ 3 : ℤ) : ℝ) := by
      push_cast; exact (Int.floor_le _).trans h
    exact_mod_cast h2

/-- A lattice of polynomial size that is `N⁻³`-dense in `S(C)` (Corollary 3.19
of [15]). -/
theorem exists_lattice_specDomain (C : ℝ) : ∃ K : ℝ, ∃ N0 : ℕ, ∀ N ≥ N0, ∃ Λ : Finset ℂ,
    (↑Λ : Set ℂ) ⊆ specDomain N C ∧ (Λ.card : ℝ) ≤ (N : ℝ) ^ K ∧
    ∀ z ∈ specDomain N C, ∃ w ∈ Λ, ‖z - w‖ ≤ (N : ℝ) ^ (-(3 : ℝ)) := by
  classical
  refine ⟨7, 484, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := by omega
  have hNr : (484 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set S := specDomain N C with hS
  set T : Finset (ℤ × ℤ) := (latticeIndex N).filter (fun p => p ∈ latticeCell N '' S) with hT
  have hrep : ∀ p ∈ T, Function.invFunOn (latticeCell N) S p ∈ S ∧
      latticeCell N (Function.invFunOn (latticeCell N) S p) = p := by
    intro p hp
    have hpS : p ∈ latticeCell N '' S := (Finset.mem_filter.mp hp).2
    exact ⟨Function.invFunOn_mem hpS, Function.invFunOn_eq hpS⟩
  refine ⟨T.image (Function.invFunOn (latticeCell N) S), ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw)
    exact (hrep p hp).1
  · have hcard : (T.image (Function.invFunOn (latticeCell N) S)).card ≤ (latticeIndex N).card :=
      (Finset.card_image_le).trans (Finset.card_le_card (Finset.filter_subset _ _))
    have hc : ((T.image (Function.invFunOn (latticeCell N) S)).card : ℝ)
        ≤ (20 * (N : ℝ) ^ 3 + 1) * (20 * (N : ℝ) ^ 3 + 1) := by
      rw [← latticeIndex_card]; exact_mod_cast hcard
    have h7 : (N : ℝ) ^ (7 : ℝ) = (N : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h7]
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ (by linarith)
    calc _ ≤ (20 * (N : ℝ) ^ 3 + 1) * (20 * (N : ℝ) ^ 3 + 1) := hc
      _ ≤ (21 * (N : ℝ) ^ 3) * (21 * (N : ℝ) ^ 3) := by nlinarith
      _ = 441 * (N : ℝ) ^ 6 := by ring
      _ ≤ (N : ℝ) * (N : ℝ) ^ 6 := by
          have : (0 : ℝ) ≤ (N : ℝ) ^ 6 := by positivity
          nlinarith
      _ = (N : ℝ) ^ 7 := by ring
  · intro z hz
    have hzT : latticeCell N z ∈ T :=
      Finset.mem_filter.mpr ⟨latticeCell_mem N C hz hN2, ⟨z, hz, rfl⟩⟩
    obtain ⟨hwS, hwc⟩ := hrep _ hzT
    refine ⟨_, Finset.mem_image_of_mem _ hzT, ?_⟩
    set w := Function.invFunOn (latticeCell N) S (latticeCell N z)
    have hM : (0 : ℝ) < 2 * (N : ℝ) ^ 3 := by positivity
    have hre : ⌊z.re * (2 * (N : ℝ) ^ 3)⌋ = ⌊w.re * (2 * (N : ℝ) ^ 3)⌋ :=
      (congrArg Prod.fst hwc).symm
    have him : ⌊z.im * (2 * (N : ℝ) ^ 3)⌋ = ⌊w.im * (2 * (N : ℝ) ^ 3)⌋ :=
      (congrArg Prod.snd hwc).symm
    have h1 := Int.abs_sub_lt_one_of_floor_eq_floor hre
    have h2 := Int.abs_sub_lt_one_of_floor_eq_floor him
    have e1 : |z.re * (2 * (N : ℝ) ^ 3) - w.re * (2 * (N : ℝ) ^ 3)|
        = |z.re - w.re| * (2 * (N : ℝ) ^ 3) := by
      rw [← sub_mul, abs_mul, abs_of_pos hM]
    have e2 : |z.im * (2 * (N : ℝ) ^ 3) - w.im * (2 * (N : ℝ) ^ 3)|
        = |z.im - w.im| * (2 * (N : ℝ) ^ 3) := by
      rw [← sub_mul, abs_mul, abs_of_pos hM]
    rw [e1] at h1; rw [e2] at h2
    have hr : |z.re - w.re| ≤ (1 / (2 * (N : ℝ) ^ 3)) := by
      rw [le_div_iff₀ hM]; exact h1.le
    have hi : |z.im - w.im| ≤ (1 / (2 * (N : ℝ) ^ 3)) := by
      rw [le_div_iff₀ hM]; exact h2.le
    have hn : (N : ℝ) ^ (-(3 : ℝ)) = ((N : ℝ) ^ 3)⁻¹ := by
      rw [Real.rpow_neg hNpos.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hsum : 1 / (2 * (N : ℝ) ^ 3) + 1 / (2 * (N : ℝ) ^ 3) = ((N : ℝ) ^ 3)⁻¹ := by
      field_simp; ring
    calc ‖z - w‖ ≤ |(z - w).re| + |(z - w).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |z.re - w.re| + |z.im - w.im| := by simp
      _ ≤ _ := by rw [hn, ← hsum]; linarith

/-- Non-vacuity at `C = 0`: `i ∈ S(0)` for `N ≥ 2`, so the lattice is nonempty. -/
example : ∃ K : ℝ, ∃ N0 : ℕ, ∀ N ≥ N0, ∃ Λ : Finset ℂ, Λ.Nonempty ∧
    (↑Λ : Set ℂ) ⊆ specDomain N 0 ∧ (Λ.card : ℝ) ≤ (N : ℝ) ^ K := by
  obtain ⟨K, N0, h⟩ := exists_lattice_specDomain 0
  refine ⟨K, max N0 2, fun N hN => ?_⟩
  obtain ⟨Λ, h1, h2, h3⟩ := h N (le_trans (le_max_left _ _) hN)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
  have hI : Complex.I ∈ specDomain N 0 := by
    refine ⟨by simp, ?_, by simp⟩
    simp only [Real.rpow_zero, Complex.I_im]
    rw [div_lt_one (by linarith)]; linarith
  obtain ⟨w, hw, -⟩ := h3 _ hI
  exact ⟨Λ, ⟨w, hw⟩, h1, h2⟩

#print axioms exists_lattice_specDomain

end WEdgeNS
