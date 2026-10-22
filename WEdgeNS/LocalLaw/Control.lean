import WEdgeNS.Probability.ProductSpace
import WEdgeNS.Probability.LargeDeviation
import WEdgeNS.Semicircle.Bounds

/-!
# Control parameters and the first estimates on `Ω(z)`
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- `Λ_o` of (3.9) of [15]. -/
def lamO {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : ℝ :=
  ⨆ i : Fin N, ⨆ j : Fin N, if i = j then 0 else ‖resolventC H z i j‖

/-- `Λ_d` of (3.9) of [15]. -/
def lamD {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : ℝ :=
  ⨆ i : Fin N, ‖resolventC H z i i - msc z‖

/-- `Λ` of (3.9) of [15]. -/
def lamAvg {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : ℝ := ‖stieltjesM H z - msc z‖

/-- `Ψ` of (3.26) of [15]. -/
def psiCtrl {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : ℝ :=
  Real.sqrt ((lamAvg H z + (msc z).im) / (N * z.im))

/-- `Z_i` of (3.15) of [15]. -/
def zFluct {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (i : Fin N) : ℂ :=
  ∑ k, ∑ l, if k = i ∨ l = i then 0 else
    (((H i k * H l i : ℝ) : ℂ) - if k = l then ((N : ℝ)⁻¹ : ℂ) else 0) *
      resolventC (zeroRC {i} H) z k l

/-- `[Z]` of Lemma 4.1 of [15]. -/
def zAvg {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : ℂ := (N : ℂ)⁻¹ * ∑ i, zFluct H z i

/-- `A_i` of (3.24) of [15]. -/
def aCorr {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (i : Fin N) : ℂ :=
  (N : ℂ)⁻¹ * ∑ j, resolventC H z i j * resolventC H z j i / resolventC H z i i

/-- `Υ_i` of Lemma 3.10 of [15]. -/
def upsilon {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (i : Fin N) : ℂ :=
  (H i i : ℂ) - zFluct H z i + aCorr H z i

/-! ### Basic facts on resolvents of real symmetric matrices -/

/-- For `0 < Im z` no eigenvalue of `H` equals `z`. -/
private lemma ctl_ne_eig {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (α : Fin N) : (hH.eigenvalues α : ℂ) ≠ z := by
  intro h
  have := congrArg Complex.im h
  rw [Complex.ofReal_im] at this
  linarith

/-- `G` is symmetric for a real symmetric `H`. -/
private lemma ctl_symm {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (i j : Fin N) : resolventC H z i j = resolventC H z j i := by
  rw [resolventC_apply_eq_sum hH (ctl_ne_eig hH hz) i j,
    resolventC_apply_eq_sum hH (ctl_ne_eig hH hz) j i]
  exact Finset.sum_congr rfl fun α _ => by rw [mul_comm (hH.eigenvectorBasis α i)]

/-- `Im G_ii > 0` for `0 < Im z`. -/
private lemma ctl_im_diag_pos {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (i : Fin N) : 0 < (resolventC H z i i).im := by
  have hward := sum_norm_sq_resolventC hH hz i
  have hnn : 0 ≤ (resolventC H z i i).im := by
    have : 0 ≤ ∑ j, ‖resolventC H z i j‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
    rw [hward] at this
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => by linarith [h.2])
  refine lt_of_le_of_ne hnn fun h0 => ?_
  rw [← h0, zero_div] at hward
  have hrow : ∀ j, resolventC H z i j = 0 := fun j => by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp hward j
      (Finset.mem_univ j)
    exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp this)
  have hGH : resolventC H z * (H.map (fun x : ℝ => (x : ℂ)) - z • (1 : Matrix (Fin N) (Fin N) ℂ))
      = 1 := mul_eq_one_comm.mp (resolventC_mul_eq_one hH (ctl_ne_eig hH hz))
  have h1 := congrFun (congrFun hGH i) i
  rw [Matrix.mul_apply] at h1
  simp only [hrow, zero_mul, Finset.sum_const_zero, Matrix.one_apply_eq] at h1
  exact zero_ne_one h1

/-- The diagonal entries of `G` do not vanish for `0 < Im z`. -/
private lemma ctl_diag_ne_zero {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (i : Fin N) : resolventC H z i i ≠ 0 := by
  intro h
  have := ctl_im_diag_pos hH hz i
  rw [h] at this
  simp at this

private lemma ctl_zeroRC_empty {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) : zeroRC ∅ H = H := by
  funext i j
  simp [zeroRC]

/-- (3.23) of [15] (Lemma 3.10), with `[v] = m - m_sc`. -/
theorem inv_resolventC_diag_eq {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (i : Fin N) :
    (resolventC H z i i)⁻¹ = -z - msc z - ((stieltjesM H z - msc z) - upsilon H z i) := by
  rw [resolventC_diag_eq_inv hH hz i, inv_inv]
  have hmi := minorM_insert_sub hH (T := ∅) (Finset.notMem_empty i) hz
  rw [ctl_zeroRC_empty, minorM_empty, Finset.insert_empty] at hmi
  -- the diagonal part of `Z_i`
  have hdiag : ∑ k, ∑ l, (if k = i ∨ l = i then (0 : ℂ) else
      (if k = l then ((N : ℝ)⁻¹ : ℂ) else 0) * resolventC (zeroRC {i} H) z k l) =
      (N : ℂ)⁻¹ * ∑ j ∈ ({i} : Finset (Fin N))ᶜ, resolventC (zeroRC {i} H) z j j := by
    have h1 : ∀ k, ∑ l, (if k = i ∨ l = i then (0 : ℂ) else
        (if k = l then ((N : ℝ)⁻¹ : ℂ) else 0) * resolventC (zeroRC {i} H) z k l) =
        if k = i then 0 else ((N : ℝ)⁻¹ : ℂ) * resolventC (zeroRC {i} H) z k k := by
      intro k
      by_cases hk : k = i
      · simp [hk]
      · rw [Finset.sum_eq_single k]
        · simp [hk]
        · intro l _ hl
          simp [Ne.symm hl]
        · simp
    simp only [h1]
    rw [Finset.mul_sum, ← Finset.sum_compl_add_sum {i}]
    simp [Finset.sum_ite, Finset.filter_ne', Finset.compl_eq_univ_sdiff]
  have hZ : zFluct H z i = (∑ k, ∑ l, (if k = i ∨ l = i then (0 : ℂ) else
      (H i k : ℂ) * resolventC (zeroRC {i} H) z k l * H l i)) -
      ∑ k, ∑ l, (if k = i ∨ l = i then (0 : ℂ) else
        (if k = l then ((N : ℝ)⁻¹ : ℂ) else 0) * resolventC (zeroRC {i} H) z k l) := by
    unfold zFluct
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h : k = i ∨ l = i
    · simp [h]
    · simp only [h, ite_false]
      push_cast
      ring
  have hA : aCorr H z i = stieltjesM H z - minorM {i} H z := by
    have : aCorr H z i = (N : ℂ)⁻¹ * ∑ j, resolventC H z i j ^ 2 / resolventC H z i i := by
      unfold aCorr
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ctl_symm hH hz j i, pow_two]
    rw [this]
    linear_combination hmi
  have hM : minorM {i} H z = (N : ℂ)⁻¹ * ∑ j ∈ ({i} : Finset (Fin N))ᶜ,
      resolventC (zeroRC {i} H) z j j := rfl
  unfold upsilon
  rw [hA, hZ, hdiag, ← hM]
  ring

/-! ### Elementary bounds for the control parameters -/

private lemma ctl_lamO_nonneg {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : 0 ≤ lamO H z :=
  Real.iSup_nonneg fun i => Real.iSup_nonneg fun j => by split_ifs <;> positivity

private lemma ctl_lamD_nonneg {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : 0 ≤ lamD H z :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/-- An off-diagonal entry of the resolvent is bounded in norm by `lamO H z`. -/
lemma norm_resolventC_off_le_lamO {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ} {i j : Fin N}
    (hij : i ≠ j) : ‖resolventC H z i j‖ ≤ lamO H z := by
  have h1 : ‖resolventC H z i j‖ ≤ ⨆ j', (if i = j' then 0 else ‖resolventC H z i j'‖) := by
    refine le_trans (le_of_eq ?_) (le_ciSup (f := fun j' =>
      if i = j' then (0 : ℝ) else ‖resolventC H z i j'‖) (Set.finite_range _).bddAbove j)
    simp [hij]
  exact h1.trans (le_ciSup (f := fun i' => ⨆ j', (if i' = j' then (0 : ℝ) else
    ‖resolventC H z i' j'‖)) (Set.finite_range _).bddAbove i)

private lemma ctl_lamO_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ i j, i ≠ j → ‖resolventC H z i j‖ ≤ a) : lamO H z ≤ a :=
  Real.iSup_le (fun i => Real.iSup_le (fun j => by
    split_ifs with hij
    · exact ha
    · exact h i j hij) ha) ha

/-- Each diagonal entry of the resolvent is within `lamD H z` of `m_sc(z)`. -/
lemma norm_resolventC_sub_msc_le_lamD {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ} (i : Fin N) :
    ‖resolventC H z i i - msc z‖ ≤ lamD H z :=
  le_ciSup (f := fun i => ‖resolventC H z i i - msc z‖) (Set.finite_range _).bddAbove i

private lemma ctl_lamD_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ i, ‖resolventC H z i i - msc z‖ ≤ a) : lamD H z ≤ a :=
  Real.iSup_le h ha

/-- `|m_sc|` is between `1/16` and `1` on `|E| ≤ 5`, `0 < η ≤ 10`. -/
private lemma ctl_msc_bounds {z : ℂ} (hre : |z.re| ≤ 5) (him : 0 < z.im) (hle : z.im ≤ 10) :
    1 / 16 ≤ ‖msc z‖ ∧ ‖msc z‖ ≤ 1 := by
  obtain ⟨h1, h2⟩ := norm_msc_eq_inv_and_lt_one him
  refine ⟨?_, h2.le⟩
  have hz : ‖z‖ ≤ 15 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos him] at this
    linarith
  have hsum : ‖msc z + z‖ ≤ 16 := (norm_add_le _ _).trans (by linarith)
  have hpos : 0 < ‖msc z + z‖ := by
    have hm0 : 0 < ‖msc z‖ := norm_pos_iff.mpr fun h => by
      have := im_msc_pos him
      rw [h] at this
      simp at this
    rw [h1] at hm0
    exact inv_pos.mp hm0
  rw [h1]
  rw [one_div]
  exact inv_anti₀ hpos hsum

/-- The standing deterministic hypotheses on `Ω(z)`: `H` is real symmetric, `z` lies in the upper
half plane over `|E| ≤ 5`, `η ≤ 10`, and `Λ_d + Λ_o` is small. -/
private structure CtlOmega {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : Prop where
  herm : H.IsHermitian
  im_pos : 0 < z.im
  msc_lo : 1 / 16 ≤ ‖msc z‖
  msc_hi : ‖msc z‖ ≤ 1
  small : lamD H z + lamO H z ≤ 1 / 64

namespace CtlOmega

variable {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ}

private lemma lamO_le (h : CtlOmega H z) : lamO H z ≤ 1 / 64 := by
  linarith [h.small, ctl_lamD_nonneg H z]

private lemma lamD_le (h : CtlOmega H z) : lamD H z ≤ 1 / 64 := by
  linarith [h.small, ctl_lamO_nonneg H z]

private lemma norm_diag_bounds (h : CtlOmega H z) (i : Fin N) :
    3 / 64 ≤ ‖resolventC H z i i‖ ∧ ‖resolventC H z i i‖ ≤ 5 / 4 := by
  have hd : ‖resolventC H z i i - msc z‖ ≤ 1 / 64 :=
    (norm_resolventC_sub_msc_le_lamD i).trans h.lamD_le
  have h1 := norm_sub_norm_le (msc z) (resolventC H z i i)
  have h2 := norm_sub_le (resolventC H z i i) (msc z)
  have h3 := norm_add_le (resolventC H z i i - msc z) (msc z)
  rw [norm_sub_rev] at h1
  rw [sub_add_cancel] at h3
  constructor <;> linarith [h.msc_lo, h.msc_hi]

/-- Removing one row and column changes an entry by `O(Λ_o²)`. -/
private lemma norm_minor1_sub_le (h : CtlOmega H z) {i a b : Fin N} (ha : a ≠ i) (hb : b ≠ i) :
    ‖resolventC (zeroRC {i} H) z a b - resolventC H z a b‖ ≤ 22 * lamO H z ^ 2 := by
  have e := resolventC_eq_minor_add h.herm h.im_pos ha hb
  have hii := (h.norm_diag_bounds i).1
  have h1 : ‖resolventC H z a i‖ ≤ lamO H z := norm_resolventC_off_le_lamO ha
  have h2 : ‖resolventC H z i b‖ ≤ lamO H z := norm_resolventC_off_le_lamO (Ne.symm hb)
  have hO := ctl_lamO_nonneg H z
  have hsub : resolventC (zeroRC {i} H) z a b - resolventC H z a b =
      -(resolventC H z a i * resolventC H z i b / resolventC H z i i) := by
    linear_combination (-1 : ℂ) * e
  rw [hsub, norm_neg, norm_div, norm_mul]
  calc ‖resolventC H z a i‖ * ‖resolventC H z i b‖ / ‖resolventC H z i i‖
      ≤ lamO H z * lamO H z / (3 / 64) := by gcongr
    _ ≤ 22 * lamO H z ^ 2 := by nlinarith

private lemma norm_minor1_diag (h : CtlOmega H z) {i j : Fin N} (hj : j ≠ i) :
    1 / 25 ≤ ‖resolventC (zeroRC {i} H) z j j‖ ∧ ‖resolventC (zeroRC {i} H) z j j‖ ≤ 3 / 2 := by
  have hsub := h.norm_minor1_sub_le hj hj
  have hO := ctl_lamO_nonneg H z
  have hO' := h.lamO_le
  have hsq : 22 * lamO H z ^ 2 ≤ 22 / 4096 := by nlinarith
  have hd := h.norm_diag_bounds j
  have h1 := norm_sub_norm_le (resolventC H z j j) (resolventC (zeroRC {i} H) z j j)
  have h3 := norm_add_le (resolventC (zeroRC {i} H) z j j - resolventC H z j j)
    (resolventC H z j j)
  rw [norm_sub_rev] at h1
  rw [sub_add_cancel] at h3
  constructor <;> linarith [hd.1, hd.2]

private lemma norm_minor1_offDiag (h : CtlOmega H z) {i a b : Fin N} (ha : a ≠ i) (hb : b ≠ i)
    (hab : a ≠ b) : ‖resolventC (zeroRC {i} H) z a b‖ ≤ 3 / 2 * lamO H z := by
  have hsub := h.norm_minor1_sub_le ha hb
  have hO := ctl_lamO_nonneg H z
  have hO' := h.lamO_le
  have h0 : ‖resolventC H z a b‖ ≤ lamO H z := norm_resolventC_off_le_lamO hab
  have h3 := norm_add_le (resolventC (zeroRC {i} H) z a b - resolventC H z a b)
    (resolventC H z a b)
  rw [sub_add_cancel] at h3
  nlinarith

/-- Removing two rows and columns changes an entry by `O(Λ_o²)`. -/
private lemma norm_minor2_sub_le (h : CtlOmega H z) {i j a b : Fin N} (hij : i ≠ j)
    (ha : a ∉ ({i, j} : Finset (Fin N))) (hb : b ∉ ({i, j} : Finset (Fin N))) :
    ‖resolventC (zeroRC {i, j} H) z a b - resolventC H z a b‖ ≤ 80 * lamO H z ^ 2 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb
  have hH1 := zeroRC_isHermitian h.herm {i}
  have hG2 : zeroRC {i, j} H = zeroRC {j} (zeroRC {i} H) := by
    rw [zeroRC_zeroRC, Finset.insert_eq, Finset.union_comm]
  have e := resolventC_eq_minor_add hH1 h.im_pos ha.2 hb.2
  rw [← hG2] at e
  have hO := ctl_lamO_nonneg H z
  have hO' := h.lamO_le
  have hjj := (h.norm_minor1_diag (i := i) (j := j) hij.symm).1
  have h1 := h.norm_minor1_offDiag (i := i) ha.1 hij.symm ha.2
  have h2 := h.norm_minor1_offDiag (i := i) hij.symm hb.1 (Ne.symm hb.2)
  have hsub : resolventC (zeroRC {i, j} H) z a b - resolventC (zeroRC {i} H) z a b =
      -(resolventC (zeroRC {i} H) z a j * resolventC (zeroRC {i} H) z j b /
        resolventC (zeroRC {i} H) z j j) := by
    linear_combination (-1 : ℂ) * e
  have hstep : ‖resolventC (zeroRC {i, j} H) z a b - resolventC (zeroRC {i} H) z a b‖ ≤
      57 * lamO H z ^ 2 := by
    rw [hsub, norm_neg, norm_div, norm_mul]
    calc ‖resolventC (zeroRC {i} H) z a j‖ * ‖resolventC (zeroRC {i} H) z j b‖ /
          ‖resolventC (zeroRC {i} H) z j j‖
        ≤ (3 / 2 * lamO H z) * (3 / 2 * lamO H z) / (1 / 25) := by gcongr
      _ ≤ 57 * lamO H z ^ 2 := by nlinarith
  have h22 := h.norm_minor1_sub_le (i := i) ha.1 hb.1
  have h3 := norm_add_le (resolventC (zeroRC {i, j} H) z a b - resolventC (zeroRC {i} H) z a b)
    (resolventC (zeroRC {i} H) z a b - resolventC H z a b)
  rw [sub_add_sub_cancel] at h3
  nlinarith [sq_nonneg (lamO H z)]

private lemma norm_minor2_diag_le (h : CtlOmega H z) {i j a : Fin N} (hij : i ≠ j)
    (ha : a ∉ ({i, j} : Finset (Fin N))) : ‖resolventC (zeroRC {i, j} H) z a a‖ ≤ 2 := by
  have hsub := h.norm_minor2_sub_le hij ha ha
  have hO := ctl_lamO_nonneg H z
  have hO' := h.lamO_le
  have hd := (h.norm_diag_bounds a).2
  have h3 := norm_add_le (resolventC (zeroRC {i, j} H) z a a - resolventC H z a a)
    (resolventC H z a a)
  rw [sub_add_cancel] at h3
  nlinarith

private lemma norm_minor2_offDiag_le (h : CtlOmega H z) {i j a b : Fin N} (hij : i ≠ j)
    (ha : a ∉ ({i, j} : Finset (Fin N))) (hb : b ∉ ({i, j} : Finset (Fin N))) (hab : a ≠ b) :
    ‖resolventC (zeroRC {i, j} H) z a b‖ ≤ 3 * lamO H z := by
  have hsub := h.norm_minor2_sub_le hij ha hb
  have hO := ctl_lamO_nonneg H z
  have hO' := h.lamO_le
  have h0 : ‖resolventC H z a b‖ ≤ lamO H z := norm_resolventC_off_le_lamO hab
  have h3 := norm_add_le (resolventC (zeroRC {i, j} H) z a b - resolventC H z a b)
    (resolventC H z a b)
  rw [sub_add_cancel] at h3
  nlinarith

/-- The off-diagonal Schur complement formula (3.13), as a norm bound. -/
private lemma norm_offDiag_le (h : CtlOmega H z) {i j : Fin N} (hij : i ≠ j) :
    ‖resolventC H z i j‖ ≤ 2 * (|H i j| + ‖∑ k, ∑ l, (if k = i ∨ k = j ∨ l = i ∨ l = j then
      (0 : ℂ) else (H i k : ℂ) * resolventC (zeroRC {i, j} H) z k l * H l j)‖) := by
  rw [resolventC_offDiag_eq h.herm h.im_pos hij]
  rw [norm_mul, norm_mul, norm_neg]
  have h1 := (h.norm_diag_bounds i).2
  have h2 := (h.norm_minor1_diag (i := i) (j := j) hij.symm).2
  set S := ∑ k, ∑ l, (if k = i ∨ k = j ∨ l = i ∨ l = j then
      (0 : ℂ) else (H i k : ℂ) * resolventC (zeroRC {i, j} H) z k l * H l j) with hS
  have h3 : ‖(H i j : ℂ) - S‖ ≤ |H i j| + ‖S‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
  have h4 : 0 ≤ ‖(H i j : ℂ) - S‖ := norm_nonneg _
  have h5 : 0 ≤ ‖resolventC H z i i‖ := norm_nonneg _
  have h6 : 0 ≤ ‖resolventC (zeroRC {i} H) z j j‖ := norm_nonneg _
  calc ‖resolventC H z i i‖ * ‖resolventC (zeroRC {i} H) z j j‖ * ‖(H i j : ℂ) - S‖
      ≤ (5 / 4) * (3 / 2) * (|H i j| + ‖S‖) := by gcongr
    _ ≤ 2 * (|H i j| + ‖S‖) := by
        have : 0 ≤ |H i j| + ‖S‖ := by positivity
        nlinarith

end CtlOmega

/-! ### The Hilbert–Schmidt norm of a minor -/

private lemma ctl_im_stieltjesM {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    (stieltjesM H z).im = (N : ℝ)⁻¹ * ∑ a, (resolventC H z a a).im := by
  unfold stieltjesM
  have hN : (N : ℂ)⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hN, Complex.im_ofReal_mul, Matrix.trace, Complex.im_sum]
  rfl

/-- Ward's identity (3.27) for the minor `H^{(T)}` bounds the Hilbert–Schmidt sum by the imaginary
part of `m` plus the diagonal error of the minor. -/
private lemma ctl_sum_sq_minor_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (T : Finset (Fin N)) {ε : ℝ} (hε : 0 ≤ ε)
    (hT : ∀ a ∉ T, ‖resolventC (zeroRC T H) z a a - resolventC H z a a‖ ≤ ε) :
    ∑ a ∈ Tᶜ, ∑ b ∈ Tᶜ, ‖resolventC (zeroRC T H) z a b‖ ^ 2 ≤
      (N : ℝ) * ((stieltjesM H z).im + ε) / z.im := by
  have hrow : ∀ a ∈ Tᶜ, ∑ b ∈ Tᶜ, ‖resolventC (zeroRC T H) z a b‖ ^ 2 ≤
      ((resolventC H z a a).im + ε) / z.im := by
    intro a ha
    have haT : a ∉ T := Finset.mem_compl.mp ha
    have him : (resolventC (zeroRC T H) z a a).im ≤ (resolventC H z a a).im + ε := by
      have h1 : (resolventC (zeroRC T H) z a a - resolventC H z a a).im ≤ ε :=
        ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans (hT a haT)
      rw [Complex.sub_im] at h1
      linarith
    calc ∑ b ∈ Tᶜ, ‖resolventC (zeroRC T H) z a b‖ ^ 2
        ≤ ∑ b, ‖resolventC (zeroRC T H) z a b‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => by positivity)
      _ = (resolventC (zeroRC T H) z a a).im / z.im := sum_norm_sq_resolventC_zeroRC hH T hz a
      _ ≤ ((resolventC H z a a).im + ε) / z.im := by gcongr
  calc ∑ a ∈ Tᶜ, ∑ b ∈ Tᶜ, ‖resolventC (zeroRC T H) z a b‖ ^ 2
      ≤ ∑ a ∈ Tᶜ, ((resolventC H z a a).im + ε) / z.im := Finset.sum_le_sum hrow
    _ ≤ ∑ a, ((resolventC H z a a).im + ε) / z.im :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ =>
          div_nonneg (add_nonneg (ctl_im_diag_pos hH hz a).le hε) hz.le)
    _ = (N : ℝ) * ((stieltjesM H z).im + ε) / z.im := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, ctl_im_stieltjesM, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        by_cases hN : N = 0
        · subst hN
          simp
        · have : (N : ℝ) ≠ 0 := by exact_mod_cast hN
          field_simp

private lemma ctl_sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, mul_nonneg (Real.sqrt_nonneg a)
    (Real.sqrt_nonneg b)]

/-- The Hilbert–Schmidt term of the large deviation bounds for a minor, in terms of `Ψ`. -/
private lemma ctl_hs_le {N : ℕ} (hN : 0 < N) {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (T : Finset (Fin N)) {ε : ℝ} (hε : 0 ≤ ε)
    (hT : ∀ a ∉ T, ‖resolventC (zeroRC T H) z a a - resolventC H z a a‖ ≤ ε) :
    Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∑ a ∈ Tᶜ, ∑ b ∈ Tᶜ, ‖resolventC (zeroRC T H) z a b‖ ^ 2) ≤
      psiCtrl H z + Real.sqrt (ε / (N * z.im)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNη : 0 < (N : ℝ) * z.im := mul_pos hNr hz
  have hsum := ctl_sum_sq_minor_le hH hz T hε hT
  have him : (stieltjesM H z).im ≤ (msc z).im + lamAvg H z := by
    have : (stieltjesM H z - msc z).im ≤ ‖stieltjesM H z - msc z‖ :=
      (le_abs_self _).trans (Complex.abs_im_le_norm _)
    rw [Complex.sub_im] at this
    unfold lamAvg
    linarith
  have hmsc := im_msc_pos hz
  have hA : 0 ≤ (lamAvg H z + (msc z).im) / (N * z.im) := by
    have : 0 ≤ lamAvg H z := norm_nonneg _
    positivity
  have hB : 0 ≤ ε / (N * z.im) := by positivity
  have key : ((N : ℝ) ^ 2)⁻¹ * ∑ a ∈ Tᶜ, ∑ b ∈ Tᶜ, ‖resolventC (zeroRC T H) z a b‖ ^ 2 ≤
      (lamAvg H z + (msc z).im) / (N * z.im) + ε / (N * z.im) := by
    calc ((N : ℝ) ^ 2)⁻¹ * ∑ a ∈ Tᶜ, ∑ b ∈ Tᶜ, ‖resolventC (zeroRC T H) z a b‖ ^ 2
        ≤ ((N : ℝ) ^ 2)⁻¹ * ((N : ℝ) * ((stieltjesM H z).im + ε) / z.im) := by gcongr
      _ = ((stieltjesM H z).im + ε) / (N * z.im) := by field_simp
      _ ≤ ((lamAvg H z + (msc z).im) + ε) / (N * z.im) := by
          gcongr
          linarith
      _ = _ := by rw [add_div]
  unfold psiCtrl
  exact (Real.sqrt_le_sqrt key).trans (ctl_sqrt_add_le hA hB)

/-! ### Entries as coordinates, rows and moments -/

section Coordinates

variable {N : ℕ}

/-- For `k ∈ T`, row `k` of `symOfEntries (rowsMix T ω ω')` is row `k` of `symOfEntries ω'`. -/
lemma symOfEntries_rowsMix_left_of_mem (T : Finset (Fin N)) {k : Fin N} (hk : k ∈ T)
    (l : Fin N) (ω ω' : Entries N) :
    symOfEntries (rowsMix T ω ω') k l = symOfEntries ω' k l := by
  unfold symOfEntries rowsMix
  by_cases h : k = l
  · subst h
    simp [hk]
  · by_cases h' : k < l
    · simp [h, h', hk]
    · simp [h, h', hk]

private lemma ctl_symOfEntries_rowsMix_right (T : Finset (Fin N)) (k : Fin N) {l : Fin N}
    (hl : l ∈ T) (ω ω' : Entries N) :
    symOfEntries (rowsMix T ω ω') k l = symOfEntries ω' k l := by
  unfold symOfEntries rowsMix
  by_cases h : k = l
  · subst h
    simp [hl]
  · by_cases h' : k < l
    · simp [h, h', hl]
    · simp [h, h', hl]

private lemma ctl_symOfEntries_symm (ω : Entries N) (a b : Fin N) :
    symOfEntries ω a b = symOfEntries ω b a := by
  have := (symOfEntries_isHermitian ω).apply a b
  simpa using this.symm

/-- The coordinate of `Entries N` carrying the entry `(a, b)`. -/
private def ctlIdx (a b : Fin N) : Fin N ⊕ OffDiag N :=
  if h : a = b then Sum.inl a
  else if h' : a < b then Sum.inr ⟨(a, b), h'⟩
  else Sum.inr ⟨(b, a), lt_of_le_of_ne (not_lt.mp h') (fun e => h e.symm)⟩

private lemma ctl_symOfEntries_eq_coord (ω : Entries N) (a b : Fin N) :
    symOfEntries ω a b = EntryLaws.entryCoord (ctlIdx a b) ω := by
  unfold symOfEntries ctlIdx EntryLaws.entryCoord
  split_ifs <;> simp

private lemma ctlIdx_inj {a b c d : Fin N} (h : ctlIdx a b = ctlIdx c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  unfold ctlIdx at h
  by_cases h1 : a = b <;> by_cases h2 : c = d
  · subst h1
    subst h2
    have h' : a = c := by simpa using h
    exact Or.inl ⟨h', h'⟩
  · simp [h1, h2] at h
    split_ifs at h
  · simp [h1, h2] at h
    split_ifs at h
  · simp only [h1, h2, dite_false] at h
    by_cases h3 : a < b <;> by_cases h4 : c < d
    · simp only [h3, h4, dite_true, Sum.inr.injEq, Subtype.mk.injEq, Prod.mk.injEq] at h
      exact Or.inl h
    · simp only [h3, h4, dite_true, dite_false, Sum.inr.injEq, Subtype.mk.injEq,
        Prod.mk.injEq] at h
      exact Or.inr ⟨h.1, h.2⟩
    · simp only [h3, h4, dite_true, dite_false, Sum.inr.injEq, Subtype.mk.injEq,
        Prod.mk.injEq] at h
      exact Or.inr ⟨h.2, h.1⟩
    · simp only [h3, h4, dite_false, Sum.inr.injEq, Subtype.mk.injEq, Prod.mk.injEq] at h
      exact Or.inl ⟨h.2, h.1⟩

private lemma ctlIdx_off {a b : Fin N} (hab : a ≠ b) : ∃ p : OffDiag N, ctlIdx a b = Sum.inr p := by
  unfold ctlIdx
  simp only [hab, ↓reduceDIte]
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

end Coordinates

section Moments

variable {N : ℕ} {L : EntryLaws N}

private lemma ctl_map_off (hL : L.IsProb) (p : OffDiag N) :
    L.law.map (fun ω : Entries N => ω.2 p) = L.off p := by
  have := hL.diag
  have := hL.off
  have h1 : MeasurePreserving (fun ω : Entries N => ω.2) L.law (Measure.pi L.off) :=
    measurePreserving_snd
  exact ((measurePreserving_eval L.off p).comp h1).map_eq

private lemma ctl_map_diag (hL : L.IsProb) (i : Fin N) :
    L.law.map (fun ω : Entries N => ω.1 i) = L.diag i := by
  have := hL.diag
  have := hL.off
  have h1 : MeasurePreserving (fun ω : Entries N => ω.1) L.law (Measure.pi L.diag) :=
    measurePreserving_fst
  exact ((measurePreserving_eval L.diag i).comp h1).map_eq

private lemma ctl_integral_off (hL : L.IsProb) (p : OffDiag N) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (L.off p)) :
    ∫ ω, f (ω.2 p) ∂L.law = ∫ x, f x ∂(L.off p) := by
  have hm : Measurable (fun ω : Entries N => ω.2 p) := (measurable_pi_apply p).comp measurable_snd
  have h := integral_map (μ := L.law) hm.aemeasurable (f := f) (by rw [ctl_map_off hL p]; exact hf)
  rw [ctl_map_off hL p] at h
  exact h.symm

private lemma ctl_ae_off_le (hL : L.IsProb) {q : ℝ} (hq : L.BoundedSupportAS q) (p : OffDiag N) :
    ∀ᵐ ω ∂L.law, |ω.2 p| ≤ q⁻¹ := by
  have hm : Measurable (fun ω : Entries N => ω.2 p) := (measurable_pi_apply p).comp measurable_snd
  have hA : MeasurableSet {x : ℝ | q⁻¹ < |x|} := measurableSet_lt measurable_const measurable_abs
  rw [ae_iff]
  have : {ω : Entries N | ¬ |ω.2 p| ≤ q⁻¹} =
      (fun ω : Entries N => ω.2 p) ⁻¹' {x : ℝ | q⁻¹ < |x|} := by
    ext ω
    simp
  rw [this, ← Measure.map_apply hm hA, ctl_map_off hL p]
  exact hq.2 p

private lemma ctl_ae_diag_le (hL : L.IsProb) {q : ℝ} (hq : L.BoundedSupportAS q) (i : Fin N) :
    ∀ᵐ ω ∂L.law, |ω.1 i| ≤ q⁻¹ := by
  have hm : Measurable (fun ω : Entries N => ω.1 i) := (measurable_pi_apply i).comp measurable_fst
  have hA : MeasurableSet {x : ℝ | q⁻¹ < |x|} := measurableSet_lt measurable_const measurable_abs
  rw [ae_iff]
  have : {ω : Entries N | ¬ |ω.1 i| ≤ q⁻¹} =
      (fun ω : Entries N => ω.1 i) ⁻¹' {x : ℝ | q⁻¹ < |x|} := by
    ext ω
    simp
  rw [this, ← Measure.map_apply hm hA, ctl_map_diag hL i]
  exact hq.1 i

private lemma ctl_sym_eq_off {a b : Fin N} (hab : a ≠ b) :
    ∃ p : OffDiag N, ∀ ω : Entries N, symOfEntries ω a b = ω.2 p := by
  obtain ⟨p, hp⟩ := ctlIdx_off hab
  exact ⟨p, fun ω => by rw [ctl_symOfEntries_eq_coord, hp]; rfl⟩

private lemma ctl_ae_sym_le (hL : L.IsProb) {q : ℝ} (hq : L.BoundedSupportAS q) {a b : Fin N}
    (hab : a ≠ b) : ∀ᵐ ω ∂L.law, |symOfEntries ω a b| ≤ q⁻¹ := by
  obtain ⟨p, hp⟩ := ctl_sym_eq_off hab
  simp only [hp]
  exact ctl_ae_off_le hL hq p

private lemma ctl_mean_sym {C0 : ℝ} (hL : L.IsGenWigner C0) {a b : Fin N} (hab : a ≠ b) :
    ∫ ω, symOfEntries ω a b ∂L.law = 0 := by
  obtain ⟨p, hp⟩ := ctl_sym_eq_off hab
  simp only [hp]
  rw [ctl_integral_off hL.isProb p (fun x => x) (by fun_prop)]
  exact hL.mean_off p

private lemma ctl_var_sym {C0 : ℝ} (hL : L.IsGenWigner C0) {a b : Fin N} (hab : a ≠ b) :
    ∫ ω, (symOfEntries ω a b) ^ 2 ∂L.law = (N : ℝ)⁻¹ := by
  obtain ⟨p, hp⟩ := ctl_sym_eq_off hab
  simp only [hp]
  rw [ctl_integral_off hL.isProb p (fun x => x ^ 2) (by fun_prop)]
  exact hL.var_off p

/-- Each entry of `symOfEntries ω` is a measurable function of `ω`. -/
lemma measurable_symOfEntries_at (a b : Fin N) :
    Measurable fun ω : Entries N => symOfEntries ω a b := by
  unfold symOfEntries
  by_cases h : a = b
  · simp only [h, dite_true]
    exact (measurable_pi_apply b).comp measurable_fst
  · simp only [h, dite_false]
    by_cases h' : a < b
    · simp only [h', dite_true]
      exact (measurable_pi_apply _).comp measurable_snd
    · simp only [h', dite_false]
      exact (measurable_pi_apply _).comp measurable_snd

/-- Under `(2.6)`, `N⁻¹ ≤ q⁻²`. -/
private lemma ctl_inv_le {C0 q : ℝ} (hL : L.IsGenWigner C0) (hq : L.BoundedSupportAS q)
    (hN : 2 ≤ N) : (N : ℝ)⁻¹ ≤ (q⁻¹) ^ 2 := by
  have hp : ∃ p : OffDiag N, True :=
    ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.lt_def]⟩, trivial⟩
  obtain ⟨p, -⟩ := hp
  have := hL.isProb.off p
  have hb : ∀ᵐ x ∂(L.off p), |x| ≤ q⁻¹ := by
    rw [ae_iff]
    simpa [not_le] using hq.2 p
  have hae : ∀ᵐ x ∂(L.off p), x ^ 2 ≤ (q⁻¹) ^ 2 := by
    filter_upwards [hb] with x hx
    calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ ≤ (q⁻¹) ^ 2 := by gcongr
  calc (N : ℝ)⁻¹ = ∫ x, x ^ 2 ∂(L.off p) := (hL.var_off p).symm
    _ ≤ ∫ _x, (q⁻¹) ^ 2 ∂(L.off p) :=
        integral_mono_ae (hL.sq_int_off p) (integrable_const _) hae
    _ = (q⁻¹) ^ 2 := by simp

end Moments

section Enumeration

variable {N : ℕ}

/-- An enumeration of the complement of `T` by `Fin (Tᶜ.card)`. -/
private def ctlEnum (T : Finset (Fin N)) (k : Fin (Tᶜ.card)) : Fin N :=
  ((Tᶜ.equivFin).symm k : Fin N)

private lemma ctlEnum_notMem (T : Finset (Fin N)) (k : Fin (Tᶜ.card)) : ctlEnum T k ∉ T :=
  Finset.mem_compl.mp ((Tᶜ.equivFin).symm k).2

private lemma ctlEnum_injective (T : Finset (Fin N)) : Function.Injective (ctlEnum T) :=
  fun _ _ h => (Tᶜ.equivFin).symm.injective (Subtype.ext h)

private lemma ctl_sum_enum {β : Type*} [AddCommMonoid β] (T : Finset (Fin N)) (f : Fin N → β) :
    ∑ k : Fin (Tᶜ.card), f (ctlEnum T k) = ∑ x ∈ Tᶜ, f x := by
  rw [← Finset.sum_coe_sort Tᶜ f]
  exact Equiv.sum_comp (Tᶜ.equivFin).symm (fun x : {x // x ∈ Tᶜ} => f x)

private lemma ctl_card_compl_le (T : Finset (Fin N)) : Tᶜ.card ≤ N := by
  simpa using Finset.card_le_univ Tᶜ

private lemma ctl_card_compl_pair {i j : Fin N} (hij : i ≠ j) :
    ({i, j} : Finset (Fin N))ᶜ.card = N - 2 := by
  rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hij]

private lemma ctl_card_compl_single (i : Fin N) : ({i} : Finset (Fin N))ᶜ.card = N - 1 := by
  rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton]

private lemma ctl_sum_sum_compl {β : Type*} [AddCommMonoid β] (T : Finset (Fin N))
    (f : Fin N → Fin N → β) :
    ∑ k, ∑ l, (if k ∈ T ∨ l ∈ T then 0 else f k l) =
      ∑ k : Fin (Tᶜ.card), ∑ l : Fin (Tᶜ.card), f (ctlEnum T k) (ctlEnum T l) := by
  have h1 : ∀ k, ∑ l : Fin (Tᶜ.card), f k (ctlEnum T l) = ∑ y ∈ Tᶜ, f k y :=
    fun k => ctl_sum_enum T (f k)
  simp only [h1]
  rw [ctl_sum_enum T (fun k => ∑ y ∈ Tᶜ, f k y)]
  rw [← Finset.sum_subset (Finset.subset_univ Tᶜ)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hkT : k ∉ T := Finset.mem_compl.mp hk
    simp only [hkT, false_or]
    rw [← Finset.sum_subset (Finset.subset_univ Tᶜ)]
    · refine Finset.sum_congr rfl fun l hl => ?_
      simp [Finset.mem_compl.mp hl]
    · intro l _ hl
      have : l ∈ T := by simpa using hl
      simp [this]
  · intro k _ hk
    have : k ∈ T := by simpa using hk
    simp [this]

end Enumeration

section Continuity

variable {N : ℕ}

/-- Each entry of `symOfEntries ω` is a continuous function of `ω`. -/
lemma continuous_symOfEntries_at (a b : Fin N) :
    Continuous fun ω : Entries N => symOfEntries ω a b := by
  unfold symOfEntries
  by_cases h : a = b
  · simp only [h, dite_true]
    exact (continuous_apply b).comp continuous_fst
  · simp only [h, dite_false]
    by_cases h' : a < b
    · simp only [h', dite_true]
      exact (continuous_apply _).comp continuous_snd
    · simp only [h', dite_false]
      exact (continuous_apply _).comp continuous_snd

/-- `zeroEntries T` is continuous on `Entries N`. -/
lemma continuous_zeroEntries_entries (T : Finset (Fin N)) :
    Continuous (zeroEntries T : Entries N → Entries N) := by
  refine Continuous.prodMk (continuous_pi fun k => ?_) (continuous_pi fun p => ?_)
  · by_cases hk : k ∈ T
    · simp only [hk, ite_true]
      exact continuous_const
    · simp only [hk, ite_false]
      exact (continuous_apply k).comp continuous_fst
  · by_cases hp : p.1.1 ∈ T ∨ p.1.2 ∈ T
    · simp only [hp, ite_true]
      exact continuous_const
    · simp only [hp, ite_false]
      exact (continuous_apply p).comp continuous_snd

/-- For `Im z ≠ 0`, each entry of the resolvent of the minor `zeroRC T (symOfEntries ω)` is a
continuous function of `ω`. -/
lemma continuous_resolventC_zeroRC_symOfEntries (T : Finset (Fin N)) {z : ℂ} (hz : z.im ≠ 0)
    (a b : Fin N) :
    Continuous fun ω : Entries N => resolventC (zeroRC T (symOfEntries ω)) z a b := by
  have := (continuous_resolventC_symOfEntries hz a b).comp (continuous_zeroEntries_entries T)
  convert this using 2 with ω
  simp [Function.comp, symOfEntries_zeroEntries]

end Continuity

/-! ### Conditional large deviation bound for the bilinear form (3.34) -/

section Bilinear

variable {N : ℕ} {L : EntryLaws N}

/-- The minor `G^{(T)}` restricted to the enumeration of the complement of `T`. -/
private def ctlMinor (T : Finset (Fin N)) (z : ℂ) (ω : Entries N) :
    Fin (Tᶜ.card) → Fin (Tᶜ.card) → ℂ :=
  fun k l => resolventC (zeroRC T (symOfEntries ω)) z (ctlEnum T k) (ctlEnum T l)

/-- The bracket of the large deviation bound for bilinear forms. -/
private def ctlBrkBil (N : ℕ) (q : ℝ) {n : ℕ} (B : Fin n → Fin n → ℂ) : ℝ :=
  (⨆ i, ‖B i i‖) / q ^ 2 + (⨆ i, ⨆ j, if i = j then 0 else ‖B i j‖) / q +
    Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, ‖B i j‖ ^ 2)

/-- The bilinear form `Σ_{k,l ∉ T} h_{ik} G^{(T)}_{kl} h_{lj}`. -/
private def ctlForm (T : Finset (Fin N)) (z : ℂ) (i j : Fin N) (ω : Entries N) : ℂ :=
  ∑ k : Fin (Tᶜ.card), ∑ l : Fin (Tᶜ.card), ctlMinor T z ω k l *
    (symOfEntries ω i (ctlEnum T k) : ℂ) * (symOfEntries ω (ctlEnum T l) j : ℂ)

/-- The event on which the bilinear form exceeds `s²` times its bracket. -/
private def ctlBadBil (T : Finset (Fin N)) (q s : ℝ) (z : ℂ) (i j : Fin N) : Set (Entries N) :=
  {ω | s ^ 2 * ctlBrkBil N q (ctlMinor T z ω) < ‖ctlForm T z i j ω‖}

private lemma ctl_iIndep_of_inj {ι : Type*} (hL : L.IsProb) (u : ι → Fin N × Fin N)
    (hu : Function.Injective fun x => ctlIdx (u x).1 (u x).2) :
    iIndepFun (fun x (ω : Entries N) => symOfEntries ω (u x).1 (u x).2) L.law := by
  have h := (EntryLaws.iIndepFun_entryCoord hL).precomp hu
  convert h using 2 with x
  funext ω
  exact ctl_symOfEntries_eq_coord ω _ _

private lemma ctl_measurable_brkBil (T : Finset (Fin N)) (q : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Measurable fun ω : Entries N => ctlBrkBil N q (ctlMinor T z ω) := by
  have hc : ∀ k l, Measurable fun ω : Entries N => ctlMinor T z ω k l := fun k l =>
    (continuous_resolventC_zeroRC_symOfEntries T hz _ _).measurable
  unfold ctlBrkBil
  refine (Measurable.add (Measurable.add ?_ ?_) ?_)
  · exact (Measurable.iSup fun k => (hc k k).norm).div_const _
  · refine (Measurable.iSup fun k => Measurable.iSup fun l => ?_).div_const _
    by_cases h : k = l
    · simp only [h, ite_true]
      exact measurable_const
    · simp only [h, ite_false]
      exact (hc k l).norm
  · refine Real.continuous_sqrt.measurable.comp (Measurable.const_mul ?_ _)
    exact Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ =>
      ((hc k l).norm).pow_const 2

private lemma ctl_measurable_form (T : Finset (Fin N)) {z : ℂ} (hz : z.im ≠ 0) (i j : Fin N) :
    Measurable fun ω : Entries N => ctlForm T z i j ω := by
  unfold ctlForm
  refine Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_
  have hc : Measurable fun ω : Entries N => ctlMinor T z ω k l :=
    (continuous_resolventC_zeroRC_symOfEntries T hz _ _).measurable
  exact (hc.mul (Complex.measurable_ofReal.comp (measurable_symOfEntries_at _ _))).mul
    (Complex.measurable_ofReal.comp (measurable_symOfEntries_at _ _))

private lemma ctl_measurableSet_badBil (T : Finset (Fin N)) (q s : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (i j : Fin N) : MeasurableSet (ctlBadBil T q s z i j) :=
  measurableSet_lt ((ctl_measurable_brkBil T q hz).const_mul _) (ctl_measurable_form T hz i j).norm

/-- Conditionally on the entries outside the rows `T ∋ i, j`, the bilinear form exceeds `s²` times
its bracket with probability at most `C e^{-s/C}` ((3.34) of [15], large deviation bound (3.22)
with the Hilbert–Schmidt term over all pairs). -/
private lemma ctl_pair_le :
    ∃ C > 0, ∀ {N : ℕ} {L : EntryLaws N} {C0 q : ℝ}, L.IsGenWigner C0 → L.BoundedSupportAS q →
      1 ≤ q → ∀ {z : ℂ}, 0 < z.im → ∀ (T : Finset (Fin N)) {i j : Fin N}, i ∈ T → j ∈ T →
      i ≠ j → 0 < Tᶜ.card → ∀ s : ℝ, 0 < s →
      L.law (ctlBadBil T q s z i j) ≤ ENNReal.ofReal (C * Real.exp (-s / C)) := by
  obtain ⟨C, hC, hLD⟩ := largeDev_bilinear 1 one_pos
  refine ⟨C, hC, ?_⟩
  intro N L C0 q hL hq hq1 z hz T i j hiT hjT hij hn s hs
  have hprob := EntryLaws.isProbabilityMeasure_law hL.isProb
  have hq0 : 0 < q := by linarith
  have hi_ne : ∀ k, i ≠ ctlEnum T k := fun k h => ctlEnum_notMem T k (h ▸ hiT)
  have hj_ne : ∀ k, ctlEnum T k ≠ j := fun k h => ctlEnum_notMem T k (h ▸ hjT)
  have key : ∀ ω : Entries N, L.law {ω' | rowsMix T ω ω' ∈ ctlBadBil T q s z i j} ≤
      ENNReal.ofReal (C * Real.exp (-s / C)) := by
    intro ω
    let a : Fin (Tᶜ.card) → Entries N → ℝ := fun k ω' => symOfEntries ω' i (ctlEnum T k)
    let b : Fin (Tᶜ.card) → Entries N → ℝ := fun l ω' => symOfEntries ω' (ctlEnum T l) j
    let B : Fin (Tᶜ.card) → Fin (Tᶜ.card) → ℂ := ctlMinor T z ω
    have hind : iIndepFun (Sum.elim a b) L.law := by
      let u : Fin (Tᶜ.card) ⊕ Fin (Tᶜ.card) → Fin N × Fin N :=
        Sum.elim (fun k => (i, ctlEnum T k)) (fun l => (ctlEnum T l, j))
      have hinj : Function.Injective fun x => ctlIdx (u x).1 (u x).2 := by
        intro x y hxy
        have h := ctlIdx_inj hxy
        rcases x with k | l <;> rcases y with k' | l'
        · simp only [u, Sum.elim_inl] at h
          rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
          · rw [ctlEnum_injective T h2]
          · exact absurd h1 (hi_ne k')
        · simp only [u, Sum.elim_inl, Sum.elim_inr] at h
          rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact absurd h1 (hi_ne l')
          · exact absurd h1 hij
        · simp only [u, Sum.elim_inl, Sum.elim_inr] at h
          rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact absurd h1.symm (hi_ne l)
          · exact absurd h2.symm hij
        · simp only [u, Sum.elim_inr] at h
          rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
          · rw [ctlEnum_injective T h1]
          · exact absurd h1 (hj_ne l)
      have h := ctl_iIndep_of_inj hL.isProb u hinj
      convert h using 2 with x
      funext ω'
      rcases x with k | l <;> rfl
    have ha : ∀ k, Measurable (a k) := fun k => measurable_symOfEntries_at _ _
    have hb : ∀ k, Measurable (b k) := fun k => measurable_symOfEntries_at _ _
    have ha0 : ∀ k, ∫ ω', a k ω' ∂L.law = 0 := fun k => ctl_mean_sym hL (hi_ne k)
    have hb0 : ∀ k, ∫ ω', b k ω' ∂L.law = 0 := fun k => ctl_mean_sym hL (hj_ne k)
    have hbda : ∀ k, ∀ᵐ ω' ∂L.law, |a k ω'| ≤ q⁻¹ := fun k => ctl_ae_sym_le hL.isProb hq (hi_ne k)
    have hbdb : ∀ k, ∀ᵐ ω' ∂L.law, |b k ω'| ≤ q⁻¹ := fun k => ctl_ae_sym_le hL.isProb hq (hj_ne k)
    have hvara : ∀ k, ∫ ω', a k ω' ^ 2 ∂L.law ≤ 1 / N := fun k => by
      rw [ctl_var_sym hL (hi_ne k), one_div]
    have hvarb : ∀ k, ∫ ω', b k ω' ^ 2 ∂L.law ≤ 1 / N := fun k => by
      rw [ctl_var_sym hL (hj_ne k), one_div]
    have hpos : 0 < ctlBrkBil N q B := by
      have hHerm := zeroRC_isHermitian (symOfEntries_isHermitian ω) T
      have hdiag : 0 < ⨆ k, ‖B k k‖ :=
        lt_of_lt_of_le (norm_pos_iff.mpr (ctl_diag_ne_zero hHerm hz (ctlEnum T ⟨0, hn⟩)))
          (le_ciSup (f := fun k => ‖B k k‖) (Set.finite_range _).bddAbove ⟨0, hn⟩)
      unfold ctlBrkBil
      have h1 : 0 < (⨆ k, ‖B k k‖) / q ^ 2 := by positivity
      have h2 : 0 ≤ (⨆ i, ⨆ j, if i = j then 0 else ‖B i j‖) / q :=
        div_nonneg (Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => by
          split_ifs <;> positivity) hq0.le
      have h3 := Real.sqrt_nonneg (((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, ‖B i j‖ ^ 2)
      linarith
    have hsub : {ω' | rowsMix T ω ω' ∈ ctlBadBil T q s z i j} ⊆
        {ω' | s ^ 2 * ctlBrkBil N q B ≤ ‖∑ k, ∑ l, B k l * (a k ω' : ℂ) * (b l ω' : ℂ)‖} := by
      intro ω' hω'
      have hM : ctlMinor T z (rowsMix T ω ω') = B := by
        funext k l
        exact rowIndep_iff_rowsMix.mp (rowIndep_resolventC_zeroRC (subset_refl T) z
          (ctlEnum T k) (ctlEnum T l)) ω ω'
      have hF : ctlForm T z i j (rowsMix T ω ω') =
          ∑ k, ∑ l, B k l * (a k ω' : ℂ) * (b l ω' : ℂ) := by
        unfold ctlForm
        rw [hM]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        rw [symOfEntries_rowsMix_left_of_mem T hiT, ctl_symOfEntries_rowsMix_right T _ hjT]
      have h : s ^ 2 * ctlBrkBil N q (ctlMinor T z (rowsMix T ω ω')) <
          ‖ctlForm T z i j (rowsMix T ω ω')‖ := hω'
      rw [hM, hF] at h
      exact h.le
    refine (measure_mono hsub).trans ?_
    have h := hLD L.law (Tᶜ.card) N a b hind ha hb ha0 hb0 q hq0 hq1 (ctl_card_compl_le T) hbda hbdb
      hvara hvarb B hpos (s ^ 2) (by positivity)
    rw [Real.sqrt_sq hs.le] at h
    exact h
  calc L.law (ctlBadBil T q s z i j)
      = ∫⁻ ω, L.law {ω' | rowsMix T ω ω' ∈ ctlBadBil T q s z i j} ∂L.law :=
        EntryLaws.law_eq_lintegral_rowsMix hL.isProb T (ctl_measurableSet_badBil T q s hz.ne' i j)
    _ ≤ ∫⁻ _ω, ENNReal.ofReal (C * Real.exp (-s / C)) ∂L.law := lintegral_mono key
    _ = ENNReal.ofReal (C * Real.exp (-s / C)) := by simp

/-- The bilinear form in the enumeration of the complement is the double sum of (3.13). -/
private lemma ctl_form_eq (z : ℂ) (i j : Fin N) (ω : Entries N) :
    ctlForm {i, j} z i j ω = ∑ k, ∑ l, (if k = i ∨ k = j ∨ l = i ∨ l = j then (0 : ℂ) else
      (symOfEntries ω i k : ℂ) * resolventC (zeroRC {i, j} (symOfEntries ω)) z k l *
        symOfEntries ω l j) := by
  have h := ctl_sum_sum_compl ({i, j} : Finset (Fin N)) (fun k l =>
    (symOfEntries ω i k : ℂ) * resolventC (zeroRC {i, j} (symOfEntries ω)) z k l *
      symOfEntries ω l j)
  unfold ctlForm ctlMinor
  have h2 : ∀ k l : Fin N, (k ∈ ({i, j} : Finset (Fin N)) ∨ l ∈ ({i, j} : Finset (Fin N))) ↔
      (k = i ∨ k = j ∨ l = i ∨ l = j) := by
    intro k l
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  simp only [h2] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- The bracket of the bilinear form for the minor `H^{(ij)}` in terms of `Λ_o` and `Ψ`. -/
private lemma ctl_brkBil_le {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ} (hN : 0 < N)
    (h : CtlOmega H z) {i j : Fin N} (hij : i ≠ j) {q : ℝ} (hq : 0 < q) :
    ctlBrkBil N q (fun k l : Fin (({i, j} : Finset (Fin N))ᶜ.card) =>
      resolventC (zeroRC {i, j} H) z (ctlEnum {i, j} k) (ctlEnum {i, j} l)) ≤
      2 / q ^ 2 + 3 * lamO H z / q +
        (psiCtrl H z + lamO H z * Real.sqrt (80 / (N * z.im))) := by
  have hO := ctl_lamO_nonneg H z
  have hd : (⨆ k : Fin (({i, j} : Finset (Fin N))ᶜ.card),
      ‖resolventC (zeroRC {i, j} H) z (ctlEnum {i, j} k) (ctlEnum {i, j} k)‖) ≤ 2 :=
    Real.iSup_le (fun k => h.norm_minor2_diag_le hij (ctlEnum_notMem _ k)) (by norm_num)
  have ho : (⨆ k : Fin (({i, j} : Finset (Fin N))ᶜ.card),
      ⨆ l : Fin (({i, j} : Finset (Fin N))ᶜ.card), if k = l then (0 : ℝ) else
        ‖resolventC (zeroRC {i, j} H) z (ctlEnum {i, j} k) (ctlEnum {i, j} l)‖) ≤ 3 * lamO H z :=
    Real.iSup_le (fun k => Real.iSup_le (fun l => by
      split_ifs with hkl
      · positivity
      · exact h.norm_minor2_offDiag_le hij (ctlEnum_notMem _ k) (ctlEnum_notMem _ l)
          (fun e => hkl (ctlEnum_injective _ e))) (by positivity)) (by positivity)
  have hs : Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∑ k : Fin (({i, j} : Finset (Fin N))ᶜ.card),
      ∑ l : Fin (({i, j} : Finset (Fin N))ᶜ.card),
        ‖resolventC (zeroRC {i, j} H) z (ctlEnum {i, j} k) (ctlEnum {i, j} l)‖ ^ 2) ≤
      psiCtrl H z + lamO H z * Real.sqrt (80 / (N * z.im)) := by
    have e1 : ∑ k : Fin (({i, j} : Finset (Fin N))ᶜ.card),
        ∑ l : Fin (({i, j} : Finset (Fin N))ᶜ.card),
        ‖resolventC (zeroRC {i, j} H) z (ctlEnum {i, j} k) (ctlEnum {i, j} l)‖ ^ 2 =
        ∑ a ∈ ({i, j} : Finset (Fin N))ᶜ, ∑ b ∈ ({i, j} : Finset (Fin N))ᶜ,
          ‖resolventC (zeroRC {i, j} H) z a b‖ ^ 2 := by
      have h1 : ∀ k, ∑ l : Fin (({i, j} : Finset (Fin N))ᶜ.card),
          ‖resolventC (zeroRC {i, j} H) z k (ctlEnum {i, j} l)‖ ^ 2 =
          ∑ b ∈ ({i, j} : Finset (Fin N))ᶜ, ‖resolventC (zeroRC {i, j} H) z k b‖ ^ 2 :=
        fun k => ctl_sum_enum {i, j} (fun b => ‖resolventC (zeroRC {i, j} H) z k b‖ ^ 2)
      simp only [h1]
      exact ctl_sum_enum {i, j} (fun a => ∑ b ∈ ({i, j} : Finset (Fin N))ᶜ,
        ‖resolventC (zeroRC {i, j} H) z a b‖ ^ 2)
    rw [e1]
    have hε : 0 ≤ 80 * lamO H z ^ 2 := by positivity
    have := ctl_hs_le hN h.herm h.im_pos {i, j} hε (fun a ha => by
      have ha' : a ∉ ({i, j} : Finset (Fin N)) := ha
      exact h.norm_minor2_sub_le hij ha' ha')
    have e2 : Real.sqrt (80 * lamO H z ^ 2 / (N * z.im)) =
        lamO H z * Real.sqrt (80 / (N * z.im)) := by
      rw [show 80 * lamO H z ^ 2 / (N * z.im) = lamO H z ^ 2 * (80 / (N * z.im)) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hO]
    rw [e2] at this
    exact this
  unfold ctlBrkBil
  have hq2 : 0 < q ^ 2 := by positivity
  have : (⨆ k : Fin (({i, j} : Finset (Fin N))ᶜ.card),
      ‖resolventC (zeroRC {i, j} H) z (ctlEnum {i, j} k) (ctlEnum {i, j} k)‖) / q ^ 2 ≤ 2 / q ^ 2 :=
    div_le_div_of_nonneg_right hd hq2.le
  have h2 : (⨆ k : Fin (({i, j} : Finset (Fin N))ᶜ.card),
      ⨆ l : Fin (({i, j} : Finset (Fin N))ᶜ.card), if k = l then (0 : ℝ) else
        ‖resolventC (zeroRC {i, j} H) z (ctlEnum {i, j} k) (ctlEnum {i, j} l)‖) / q ≤
      3 * lamO H z / q := div_le_div_of_nonneg_right ho hq.le
  linarith

/-- Closing the estimate of (3.32): if every pair satisfies the bound for the bilinear form, then
`Λ_o ≤ 3 (1/q + s² Ψ)`. -/
private lemma ctl_lamO_close {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ} (h : CtlOmega H z)
    {q s : ℝ} (hq : 1 ≤ q) (hsq : 48 * s ^ 2 ≤ q)
    (hρ : s ^ 2 * Real.sqrt (80 / (N * z.im)) ≤ 1 / 16)
    (hH : ∀ i j, i ≠ j → |H i j| ≤ q⁻¹)
    (hS : ∀ i j, i ≠ j → ‖∑ k, ∑ l, (if k = i ∨ k = j ∨ l = i ∨ l = j then (0 : ℂ) else
      (H i k : ℂ) * resolventC (zeroRC {i, j} H) z k l * H l j)‖ ≤
      s ^ 2 * (2 / q ^ 2 + 3 * lamO H z / q +
        (psiCtrl H z + lamO H z * Real.sqrt (80 / (N * z.im))))) :
    lamO H z ≤ 3 * (1 / q + s ^ 2 * psiCtrl H z) := by
  have hq0 : 0 < q := by linarith
  have hO := ctl_lamO_nonneg H z
  have hΨ : 0 ≤ psiCtrl H z := Real.sqrt_nonneg _
  have hρ0 : 0 ≤ Real.sqrt (80 / (N * z.im)) := Real.sqrt_nonneg _
  set Λ := lamO H z with hΛ
  set Ψ := psiCtrl H z with hΨdef
  set ρ := Real.sqrt (80 / (N * z.im)) with hρdef
  set u : ℝ := 1 / q with hu
  set a : ℝ := s ^ 2 / q with ha
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := by rw [hu]; exact (div_le_one hq0).2 hq
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 / 48 := by
    rw [ha, div_le_iff₀ hq0]
    linarith
  have e1 : s ^ 2 * (2 / q ^ 2) = 2 * (a * u) := by
    rw [ha, hu]
    field_simp
  have e2 : s ^ 2 * (3 * Λ / q) = 3 * (a * Λ) := by
    rw [ha]
    field_simp
  have hR : ∀ i j, i ≠ j → ‖resolventC H z i j‖ ≤
      2 * (u + s ^ 2 * (2 / q ^ 2 + 3 * Λ / q + (Ψ + Λ * ρ))) := by
    intro i j hij
    have h1 := h.norm_offDiag_le hij
    have h2 : |H i j| ≤ u := by rw [hu, one_div]; exact hH i j hij
    have h3 := hS i j hij
    linarith
  have hRnn : 0 ≤ 2 * (u + s ^ 2 * (2 / q ^ 2 + 3 * Λ / q + (Ψ + Λ * ρ))) := by positivity
  have hmain := ctl_lamO_le hRnn hR
  have e3 : s ^ 2 * (2 / q ^ 2 + 3 * Λ / q + (Ψ + Λ * ρ)) =
      2 * (a * u) + 3 * (a * Λ) + (s ^ 2 * Ψ + (s ^ 2 * ρ) * Λ) := by
    rw [mul_add, mul_add, mul_add, e1, e2]
    ring
  rw [e3] at hmain
  have h4 : a * u ≤ u / 48 := by nlinarith
  have h5 : a * Λ ≤ Λ / 48 := by nlinarith
  have h6 : (s ^ 2 * ρ) * Λ ≤ Λ / 16 := by nlinarith
  have h7 : s ^ 2 * Ψ ≥ 0 := by positivity
  nlinarith

end Bilinear

/-! ### Conditional large deviation bounds for the linear and quadratic forms (3.33) -/

section LinQuad

variable {N : ℕ} {L : EntryLaws N}

/-- The second moment of `h² - N⁻¹` for an off-diagonal entry. -/
private lemma ctl_centered_sq {C0 q : ℝ} (hL : L.IsGenWigner C0) (hq : L.BoundedSupportAS q)
    (hN : 2 ≤ N) {a b : Fin N} (hab : a ≠ b) :
    ∫ ω, ((symOfEntries ω a b) ^ 2 - (N : ℝ)⁻¹) ∂L.law = 0 ∧
    ∫ ω, ((symOfEntries ω a b) ^ 2 - (N : ℝ)⁻¹) ^ 2 ∂L.law ≤ (q ^ 2)⁻¹ * (N : ℝ)⁻¹ := by
  obtain ⟨p, hp⟩ := ctl_sym_eq_off hab
  have hprob := hL.isProb.off p
  have hNinv := ctl_inv_le hL hq hN
  have hb : ∀ᵐ x ∂(L.off p), |x| ≤ q⁻¹ := by
    rw [ae_iff]
    simpa [not_le] using hq.2 p
  have hx2 : ∀ᵐ x ∂(L.off p), x ^ 2 ≤ (q⁻¹) ^ 2 := by
    filter_upwards [hb] with x hx
    calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ ≤ (q⁻¹) ^ 2 := by gcongr
  have hint2 : Integrable (fun x : ℝ => x ^ 2) (L.off p) := hL.sq_int_off p
  have hint4 : Integrable (fun x : ℝ => x ^ 4) (L.off p) := by
    refine Integrable.of_bound (C := (q⁻¹) ^ 4) (by fun_prop) ?_
    filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc x ^ 4 = |x| ^ 4 := by rw [pow_abs, abs_of_nonneg (by positivity)]
      _ ≤ (q⁻¹) ^ 4 := by gcongr
  have hvar : ∫ x, x ^ 2 ∂(L.off p) = (N : ℝ)⁻¹ := hL.var_off p
  have hc1 : ∫ x, (x ^ 2 - (N : ℝ)⁻¹) ∂(L.off p) = 0 := by
    rw [integral_sub hint2 (integrable_const _), hvar]
    simp
  have hfourth : ∫ x, x ^ 4 ∂(L.off p) ≤ (q⁻¹) ^ 2 * (N : ℝ)⁻¹ := by
    calc ∫ x, x ^ 4 ∂(L.off p) ≤ ∫ x, (q⁻¹) ^ 2 * x ^ 2 ∂(L.off p) := by
          refine integral_mono_ae hint4 (hint2.const_mul _) ?_
          filter_upwards [hx2] with x hx
          nlinarith [sq_nonneg x]
      _ = (q⁻¹) ^ 2 * (N : ℝ)⁻¹ := by rw [integral_const_mul, hvar]
  have hc2 : ∫ x, (x ^ 2 - (N : ℝ)⁻¹) ^ 2 ∂(L.off p) ≤ (q⁻¹) ^ 2 * (N : ℝ)⁻¹ := by
    have e : ∀ x : ℝ, (x ^ 2 - (N : ℝ)⁻¹) ^ 2 =
        x ^ 4 - 2 * (N : ℝ)⁻¹ * x ^ 2 + ((N : ℝ)⁻¹) ^ 2 := by
      intro x; ring
    have hi : Integrable (fun x : ℝ => x ^ 4 - 2 * (N : ℝ)⁻¹ * x ^ 2) (L.off p) :=
      hint4.sub (hint2.const_mul _)
    have h1 : ∫ x, (x ^ 2 - (N : ℝ)⁻¹) ^ 2 ∂(L.off p) =
        ∫ x, x ^ 4 ∂(L.off p) - 2 * (N : ℝ)⁻¹ * ∫ x, x ^ 2 ∂(L.off p) + ((N : ℝ)⁻¹) ^ 2 := by
      simp only [e]
      rw [integral_add hi (integrable_const _), integral_sub hint4 (hint2.const_mul _),
        integral_const_mul]
      simp
    rw [h1, hvar]
    nlinarith [sq_nonneg ((N : ℝ)⁻¹)]
  have hT : ∀ f : ℝ → ℝ, AEStronglyMeasurable f (L.off p) →
      ∫ ω, f (ω.2 p) ∂L.law = ∫ x, f x ∂(L.off p) := fun f hf => ctl_integral_off hL.isProb p f hf
  simp only [hp]
  refine ⟨?_, ?_⟩
  · rw [hT (fun x => x ^ 2 - (N : ℝ)⁻¹) (by fun_prop)]
    exact hc1
  · rw [hT (fun x => (x ^ 2 - (N : ℝ)⁻¹) ^ 2) (by fun_prop)]
    simpa [inv_pow] using hc2

/-- The bracket of the large deviation bound for linear forms in `h² - N⁻¹`. -/
private def ctlBrkLin (N : ℕ) (q : ℝ) {n : ℕ} (A : Fin n → ℂ) : ℝ :=
  (⨆ k, ‖A k‖) / q ^ 2 + Real.sqrt (((q ^ 2)⁻¹ * (N : ℝ)⁻¹) * ∑ k, ‖A k‖ ^ 2)

/-- The linear form `Σ_{k ∉ T} (h_{ik}² - N⁻¹) G^{(T)}_{kk}`. -/
private def ctlLinForm (T : Finset (Fin N)) (z : ℂ) (i : Fin N) (ω : Entries N) : ℂ :=
  ∑ k : Fin (Tᶜ.card), ctlMinor T z ω k k *
    (((symOfEntries ω i (ctlEnum T k)) ^ 2 - (N : ℝ)⁻¹ : ℝ) : ℂ)

/-- The event on which the linear form exceeds `s` times its bracket. -/
private def ctlBadLin (T : Finset (Fin N)) (q s : ℝ) (z : ℂ) (i : Fin N) : Set (Entries N) :=
  {ω | s * ctlBrkLin N q (fun k => ctlMinor T z ω k k) < ‖ctlLinForm T z i ω‖}

/-- The bracket of the large deviation bound for off-diagonal quadratic forms. -/
private def ctlBrkQuad (N : ℕ) (q : ℝ) {n : ℕ} (B : Fin n → Fin n → ℂ) : ℝ :=
  (⨆ i, ⨆ j, if i = j then 0 else ‖B i j‖) / q +
    Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, if i = j then 0 else ‖B i j‖ ^ 2)

/-- The off-diagonal quadratic form `Σ_{k ≠ l ∉ T} h_{ik} G^{(T)}_{kl} h_{il}`. -/
private def ctlOffForm (T : Finset (Fin N)) (z : ℂ) (i : Fin N) (ω : Entries N) : ℂ :=
  ∑ k : Fin (Tᶜ.card), ∑ l : Fin (Tᶜ.card), (if k = l then 0 else
    ctlMinor T z ω k l * (symOfEntries ω i (ctlEnum T k) : ℂ) *
      (symOfEntries ω i (ctlEnum T l) : ℂ))

/-- The event on which the quadratic form exceeds `s²` times its bracket. -/
private def ctlBadQuad (T : Finset (Fin N)) (q s : ℝ) (z : ℂ) (i : Fin N) : Set (Entries N) :=
  {ω | s ^ 2 * ctlBrkQuad N q (ctlMinor T z ω) < ‖ctlOffForm T z i ω‖}

private lemma ctl_measurable_brkLin (T : Finset (Fin N)) (q : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Measurable fun ω : Entries N => ctlBrkLin N q (fun k => ctlMinor T z ω k k) := by
  have hc : ∀ k l, Measurable fun ω : Entries N => ctlMinor T z ω k l := fun k l =>
    (continuous_resolventC_zeroRC_symOfEntries T hz _ _).measurable
  unfold ctlBrkLin
  refine Measurable.add ?_ ?_
  · exact (Measurable.iSup fun k => (hc k k).norm).div_const _
  · refine Real.continuous_sqrt.measurable.comp (Measurable.const_mul ?_ _)
    exact Finset.measurable_sum _ fun k _ => ((hc k k).norm).pow_const 2

private lemma ctl_measurable_brkQuad (T : Finset (Fin N)) (q : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Measurable fun ω : Entries N => ctlBrkQuad N q (ctlMinor T z ω) := by
  have hc : ∀ k l, Measurable fun ω : Entries N => ctlMinor T z ω k l := fun k l =>
    (continuous_resolventC_zeroRC_symOfEntries T hz _ _).measurable
  unfold ctlBrkQuad
  refine Measurable.add ?_ ?_
  · refine (Measurable.iSup fun k => Measurable.iSup fun l => ?_).div_const _
    by_cases h : k = l
    · simp only [h, ite_true]
      exact measurable_const
    · simp only [h, ite_false]
      exact (hc k l).norm
  · refine Real.continuous_sqrt.measurable.comp (Measurable.const_mul ?_ _)
    refine Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_
    by_cases h : k = l
    · simp only [h, ite_true]
      exact measurable_const
    · simp only [h, ite_false]
      exact ((hc k l).norm).pow_const 2

private lemma ctl_measurableSet_badLin (T : Finset (Fin N)) (q s : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (i : Fin N) : MeasurableSet (ctlBadLin T q s z i) := by
  have hc : ∀ k l, Measurable fun ω : Entries N => ctlMinor T z ω k l := fun k l =>
    (continuous_resolventC_zeroRC_symOfEntries T hz _ _).measurable
  refine measurableSet_lt ((ctl_measurable_brkLin T q hz).const_mul _) ?_
  unfold ctlLinForm
  refine Measurable.norm (Finset.measurable_sum _ fun k _ => (hc k k).mul ?_)
  exact Complex.measurable_ofReal.comp
    (((measurable_symOfEntries_at _ _).pow_const 2).sub measurable_const)

private lemma ctl_measurableSet_badQuad (T : Finset (Fin N)) (q s : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (i : Fin N) : MeasurableSet (ctlBadQuad T q s z i) := by
  have hc : ∀ k l, Measurable fun ω : Entries N => ctlMinor T z ω k l := fun k l =>
    (continuous_resolventC_zeroRC_symOfEntries T hz _ _).measurable
  refine measurableSet_lt ((ctl_measurable_brkQuad T q hz).const_mul _) ?_
  unfold ctlOffForm
  refine Measurable.norm (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_)
  by_cases h : k = l
  · simp only [h, ite_true]
    exact measurable_const
  · simp only [h, ite_false]
    exact ((hc k l).mul (Complex.measurable_ofReal.comp (measurable_symOfEntries_at _ _))).mul
      (Complex.measurable_ofReal.comp (measurable_symOfEntries_at _ _))

/-- Conditionally on the entries outside the rows `T ∋ i`, the linear form in `h_{ik}² - N⁻¹`
exceeds `s` times its bracket with probability at most `C e^{-s/C}` ((3.19) of [15]). -/
private lemma ctl_lin_le :
    ∃ C > 0, ∀ {N : ℕ} {L : EntryLaws N} {C0 q : ℝ}, L.IsGenWigner C0 → L.BoundedSupportAS q →
      1 ≤ q → 2 ≤ N → ∀ {z : ℂ}, 0 < z.im → ∀ (T : Finset (Fin N)) {i : Fin N}, i ∈ T →
      0 < Tᶜ.card → ∀ s : ℝ, 0 < s →
      L.law (ctlBadLin T q s z i) ≤ ENNReal.ofReal (C * Real.exp (-s / C)) := by
  obtain ⟨C, hC, hLD⟩ := largeDev_linear
  refine ⟨C, hC, ?_⟩
  intro N L C0 q hL hq hq1 hN z hz T i hiT hn s hs
  have hprob := EntryLaws.isProbabilityMeasure_law hL.isProb
  have hq0 : 0 < q := by linarith
  have hi_ne : ∀ k, i ≠ ctlEnum T k := fun k h => ctlEnum_notMem T k (h ▸ hiT)
  have hNinv := ctl_inv_le hL hq hN
  have key : ∀ ω : Entries N, L.law {ω' | rowsMix T ω ω' ∈ ctlBadLin T q s z i} ≤
      ENNReal.ofReal (C * Real.exp (-s / C)) := by
    intro ω
    let a : Fin (Tᶜ.card) → Entries N → ℝ :=
      fun k ω' => (symOfEntries ω' i (ctlEnum T k)) ^ 2 - (N : ℝ)⁻¹
    let A : Fin (Tᶜ.card) → ℂ := fun k => ctlMinor T z ω k k
    have hind : iIndepFun a L.law := by
      have hinj : Function.Injective fun k : Fin (Tᶜ.card) =>
          ctlIdx ((i, ctlEnum T k) : Fin N × Fin N).1 ((i, ctlEnum T k) : Fin N × Fin N).2 := by
        intro k k' hkk
        rcases ctlIdx_inj hkk with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact ctlEnum_injective T h2
        · exact absurd h1 (hi_ne k')
      have h := ctl_iIndep_of_inj hL.isProb (fun k : Fin (Tᶜ.card) => (i, ctlEnum T k)) hinj
      exact h.comp (fun _ x => x ^ 2 - (N : ℝ)⁻¹) (fun _ => by fun_prop)
    have ha : ∀ k, Measurable (a k) := fun k =>
      ((measurable_symOfEntries_at _ _).pow_const 2).sub measurable_const
    have ha0 : ∀ k, ∫ ω', a k ω' ∂L.law = 0 := fun k => (ctl_centered_sq hL hq hN (hi_ne k)).1
    have hbd : ∀ k, ∀ᵐ ω' ∂L.law, |a k ω'| ≤ (q ^ 2)⁻¹ := fun k => by
      filter_upwards [ctl_ae_sym_le hL.isProb hq (hi_ne k)] with ω' hω'
      have h1 : (symOfEntries ω' i (ctlEnum T k)) ^ 2 ≤ (q⁻¹) ^ 2 := by
        calc (symOfEntries ω' i (ctlEnum T k)) ^ 2 = |symOfEntries ω' i (ctlEnum T k)| ^ 2 :=
              (sq_abs _).symm
          _ ≤ (q⁻¹) ^ 2 := by gcongr
      have h2 : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
      rw [inv_pow] at h1 hNinv
      change |(symOfEntries ω' i (ctlEnum T k)) ^ 2 - (N : ℝ)⁻¹| ≤ (q ^ 2)⁻¹
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (symOfEntries ω' i (ctlEnum T k))]
    have hvar : ∀ k, ∫ ω', a k ω' ^ 2 ∂L.law ≤ (q ^ 2)⁻¹ * (N : ℝ)⁻¹ := fun k =>
      (ctl_centered_sq hL hq hN (hi_ne k)).2
    have hpos : 0 < ctlBrkLin N q A := by
      have hHerm := zeroRC_isHermitian (symOfEntries_isHermitian ω) T
      have hdiag : 0 < ⨆ k, ‖A k‖ :=
        lt_of_lt_of_le (norm_pos_iff.mpr (ctl_diag_ne_zero hHerm hz (ctlEnum T ⟨0, hn⟩)))
          (le_ciSup (f := fun k => ‖A k‖) (Set.finite_range _).bddAbove ⟨0, hn⟩)
      unfold ctlBrkLin
      have h1 : 0 < (⨆ k, ‖A k‖) / q ^ 2 := by positivity
      have h3 := Real.sqrt_nonneg (((q ^ 2)⁻¹ * (N : ℝ)⁻¹) * ∑ k, ‖A k‖ ^ 2)
      linarith
    have hsub : {ω' | rowsMix T ω ω' ∈ ctlBadLin T q s z i} ⊆
        {ω' | s * ctlBrkLin N q A ≤ ‖∑ k, A k * (a k ω' : ℂ)‖} := by
      intro ω' hω'
      have hM : ctlMinor T z (rowsMix T ω ω') = ctlMinor T z ω := by
        funext k l
        exact rowIndep_iff_rowsMix.mp (rowIndep_resolventC_zeroRC (subset_refl T) z
          (ctlEnum T k) (ctlEnum T l)) ω ω'
      have hF : ctlLinForm T z i (rowsMix T ω ω') = ∑ k, A k * (a k ω' : ℂ) := by
        unfold ctlLinForm
        rw [hM]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [symOfEntries_rowsMix_left_of_mem T hiT]
      have h : s * ctlBrkLin N q (fun k => ctlMinor T z (rowsMix T ω ω') k k) <
          ‖ctlLinForm T z i (rowsMix T ω ω')‖ := hω'
      rw [hM, hF] at h
      exact h.le
    refine (measure_mono hsub).trans ?_
    exact hLD L.law (Tᶜ.card) a hind ha ha0 (q ^ 2) ((q ^ 2)⁻¹ * (N : ℝ)⁻¹) (by positivity) hbd
      hvar A hpos s hs
  calc L.law (ctlBadLin T q s z i)
      = ∫⁻ ω, L.law {ω' | rowsMix T ω ω' ∈ ctlBadLin T q s z i} ∂L.law :=
        EntryLaws.law_eq_lintegral_rowsMix hL.isProb T (ctl_measurableSet_badLin T q s hz.ne' i)
    _ ≤ ∫⁻ _ω, ENNReal.ofReal (C * Real.exp (-s / C)) ∂L.law := lintegral_mono key
    _ = ENNReal.ofReal (C * Real.exp (-s / C)) := by simp

/-- Conditionally on the entries outside the rows `T ∋ i`, the off-diagonal quadratic form exceeds
`s²` times its bracket with probability at most `C e^{-s/C}` ((3.22) of [15], quadratic part). -/
private lemma ctl_quad_le :
    ∃ C > 0, ∀ {N : ℕ} {L : EntryLaws N} {C0 q : ℝ}, L.IsGenWigner C0 → L.BoundedSupportAS q →
      1 ≤ q → ∀ {z : ℂ}, 0 < z.im → ∀ (T : Finset (Fin N)) {i : Fin N}, i ∈ T →
      ∀ s : ℝ, 0 < s →
      L.law (ctlBadQuad T q s z i) ≤ ENNReal.ofReal (C * Real.exp (-s / C)) := by
  obtain ⟨C, hC, hLD⟩ := largeDev_quadratic 1 one_pos
  refine ⟨C, hC, ?_⟩
  intro N L C0 q hL hq hq1 z hz T i hiT s hs
  have hprob := EntryLaws.isProbabilityMeasure_law hL.isProb
  have hq0 : 0 < q := by linarith
  have hi_ne : ∀ k, i ≠ ctlEnum T k := fun k h => ctlEnum_notMem T k (h ▸ hiT)
  have key : ∀ ω : Entries N, L.law {ω' | rowsMix T ω ω' ∈ ctlBadQuad T q s z i} ≤
      ENNReal.ofReal (C * Real.exp (-s / C)) := by
    intro ω
    let a : Fin (Tᶜ.card) → Entries N → ℝ := fun k ω' => symOfEntries ω' i (ctlEnum T k)
    let B : Fin (Tᶜ.card) → Fin (Tᶜ.card) → ℂ := ctlMinor T z ω
    have hM : ∀ ω' : Entries N, ctlMinor T z (rowsMix T ω ω') = B := fun ω' => by
      funext k l
      exact rowIndep_iff_rowsMix.mp (rowIndep_resolventC_zeroRC (subset_refl T) z
        (ctlEnum T k) (ctlEnum T l)) ω ω'
    have hF : ∀ ω' : Entries N, ctlOffForm T z i (rowsMix T ω ω') =
        ∑ k, ∑ l, (if k = l then 0 else B k l * (a k ω' : ℂ) * (a l ω' : ℂ)) := fun ω' => by
      unfold ctlOffForm
      rw [hM]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      by_cases hkl : k = l
      · simp [hkl]
      · simp only [hkl, ite_false]
        rw [symOfEntries_rowsMix_left_of_mem T hiT, symOfEntries_rowsMix_left_of_mem T hiT]
    by_cases hpos : 0 < ctlBrkQuad N q B
    · have hind : iIndepFun a L.law := by
        have hinj : Function.Injective fun k : Fin (Tᶜ.card) =>
            ctlIdx ((i, ctlEnum T k) : Fin N × Fin N).1 ((i, ctlEnum T k) : Fin N × Fin N).2 := by
          intro k k' hkk
          rcases ctlIdx_inj hkk with ⟨_, h2⟩ | ⟨h1, _⟩
          · exact ctlEnum_injective T h2
          · exact absurd h1 (hi_ne k')
        exact ctl_iIndep_of_inj hL.isProb (fun k : Fin (Tᶜ.card) => (i, ctlEnum T k)) hinj
      have hsub : {ω' | rowsMix T ω ω' ∈ ctlBadQuad T q s z i} ⊆
          {ω' | s ^ 2 * ctlBrkQuad N q B ≤
            ‖∑ k, ∑ l, (if k = l then 0 else B k l * (a k ω' : ℂ) * (a l ω' : ℂ))‖} := by
        intro ω' hω'
        have h : s ^ 2 * ctlBrkQuad N q (ctlMinor T z (rowsMix T ω ω')) <
            ‖ctlOffForm T z i (rowsMix T ω ω')‖ := hω'
        rw [hM, hF] at h
        exact h.le
      refine (measure_mono hsub).trans ?_
      have h := hLD L.law (Tᶜ.card) N a hind (fun k => measurable_symOfEntries_at _ _)
        (fun k => ctl_mean_sym hL (hi_ne k)) q hq0 hq1 (ctl_card_compl_le T)
        (fun k => ctl_ae_sym_le hL.isProb hq (hi_ne k))
        (fun k => by rw [ctl_var_sym hL (hi_ne k), one_div]) B hpos (s ^ 2) (by positivity)
      rw [Real.sqrt_sq hs.le] at h
      exact h
    · -- the bracket vanishes, so the quadratic form vanishes
      have hbr0 : ctlBrkQuad N q B = 0 := by
        refine le_antisymm (not_lt.mp hpos) ?_
        unfold ctlBrkQuad
        have h1 : 0 ≤ (⨆ i, ⨆ j, if i = j then (0 : ℝ) else ‖B i j‖) / q :=
          div_nonneg (Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => by
            split_ifs <;> positivity) hq0.le
        have h3 := Real.sqrt_nonneg
          (((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, if i = j then (0 : ℝ) else ‖B i j‖ ^ 2)
        linarith
      have hBz : ∀ k l, k ≠ l → B k l = 0 := by
        intro k l hkl
        have h1 : ‖B k l‖ ≤ ⨆ i, ⨆ j, if i = j then (0 : ℝ) else ‖B i j‖ := by
          have e : ‖B k l‖ = if k = l then (0 : ℝ) else ‖B k l‖ := by simp [hkl]
          rw [e]
          refine le_trans (le_ciSup (f := fun j => if k = j then (0 : ℝ) else ‖B k j‖)
            (Set.finite_range _).bddAbove l) ?_
          exact le_ciSup (f := fun i => ⨆ j, if i = j then (0 : ℝ) else ‖B i j‖)
            (Set.finite_range _).bddAbove k
        have h2 : (⨆ i, ⨆ j, if i = j then (0 : ℝ) else ‖B i j‖) / q ≤ 0 := by
          have : 0 ≤ Real.sqrt
              (((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, if i = j then (0 : ℝ) else ‖B i j‖ ^ 2) :=
            Real.sqrt_nonneg _
          unfold ctlBrkQuad at hbr0
          linarith
        have h3 : (⨆ i, ⨆ j, if i = j then (0 : ℝ) else ‖B i j‖) ≤ 0 := by
          by_contra hh
          exact absurd h2 (not_le.mpr (div_pos (not_le.mp hh) hq0))
        exact norm_eq_zero.mp (le_antisymm (h1.trans h3) (norm_nonneg _))
      have hempty : {ω' | rowsMix T ω ω' ∈ ctlBadQuad T q s z i} = ∅ := by
        ext ω'
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hω'
        have h : s ^ 2 * ctlBrkQuad N q (ctlMinor T z (rowsMix T ω ω')) <
            ‖ctlOffForm T z i (rowsMix T ω ω')‖ := hω'
        rw [hM, hF, hbr0] at h
        have : ∑ k : Fin (Tᶜ.card), ∑ l : Fin (Tᶜ.card), (if k = l then (0 : ℂ) else
            B k l * (a k ω' : ℂ) * (a l ω' : ℂ)) = 0 := by
          refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
          by_cases hkl : k = l
          · simp [hkl]
          · simp [hkl, hBz k l hkl]
        rw [this] at h
        simp at h
      rw [hempty]
      simp
  calc L.law (ctlBadQuad T q s z i)
      = ∫⁻ ω, L.law {ω' | rowsMix T ω ω' ∈ ctlBadQuad T q s z i} ∂L.law :=
        EntryLaws.law_eq_lintegral_rowsMix hL.isProb T (ctl_measurableSet_badQuad T q s hz.ne' i)
    _ ≤ ∫⁻ _ω, ENNReal.ofReal (C * Real.exp (-s / C)) ∂L.law := lintegral_mono key
    _ = ENNReal.ofReal (C * Real.exp (-s / C)) := by simp

/-- `Z_i` splits into the diagonal part (a linear form in `h_{ik}² - N⁻¹`) and the off-diagonal
quadratic form. -/
private lemma ctl_zFluct_eq (z : ℂ) (i : Fin N) (ω : Entries N) :
    zFluct (symOfEntries ω) z i = ctlLinForm {i} z i ω + ctlOffForm {i} z i ω := by
  unfold zFluct
  have h := ctl_sum_sum_compl ({i} : Finset (Fin N)) (fun k l =>
    (((symOfEntries ω i k * symOfEntries ω l i : ℝ) : ℂ) -
      if k = l then ((N : ℝ)⁻¹ : ℂ) else 0) *
      resolventC (zeroRC {i} (symOfEntries ω)) z k l)
  simp only [Finset.mem_singleton] at h
  rw [h]
  unfold ctlLinForm ctlOffForm ctlMinor
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsplit : ∀ l : Fin (({i} : Finset (Fin N))ᶜ.card),
      (((symOfEntries ω i (ctlEnum {i} k) * symOfEntries ω (ctlEnum {i} l) i : ℝ) : ℂ) -
        if ctlEnum {i} k = ctlEnum {i} l then ((N : ℝ)⁻¹ : ℂ) else 0) *
        resolventC (zeroRC {i} (symOfEntries ω)) z (ctlEnum {i} k) (ctlEnum {i} l) =
      (if k = l then resolventC (zeroRC {i} (symOfEntries ω)) z (ctlEnum {i} k) (ctlEnum {i} k) *
        (((symOfEntries ω i (ctlEnum {i} k)) ^ 2 - (N : ℝ)⁻¹ : ℝ) : ℂ) else 0) +
      (if k = l then 0 else
        resolventC (zeroRC {i} (symOfEntries ω)) z (ctlEnum {i} k) (ctlEnum {i} l) *
          (symOfEntries ω i (ctlEnum {i} k) : ℂ) * (symOfEntries ω i (ctlEnum {i} l) : ℂ)) := by
    intro l
    by_cases hkl : k = l
    · subst hkl
      simp only [ite_true, add_zero]
      rw [ctl_symOfEntries_symm ω (ctlEnum {i} k) i]
      push_cast
      ring
    · have hne : ctlEnum {i} k ≠ ctlEnum {i} l := fun e => hkl (ctlEnum_injective _ e)
      simp only [hkl, hne, ite_false, zero_add, sub_zero]
      rw [ctl_symOfEntries_symm ω (ctlEnum {i} l) i]
      push_cast
      ring
  rw [Finset.sum_congr rfl fun l _ => hsplit l, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq]

private lemma ctl_sum_sum_enum {β : Type*} [AddCommMonoid β] (T : Finset (Fin N))
    (f : Fin N → Fin N → β) :
    ∑ k : Fin (Tᶜ.card), ∑ l : Fin (Tᶜ.card), f (ctlEnum T k) (ctlEnum T l) =
      ∑ a ∈ Tᶜ, ∑ b ∈ Tᶜ, f a b := by
  have h1 : ∀ k, ∑ l : Fin (Tᶜ.card), f k (ctlEnum T l) = ∑ b ∈ Tᶜ, f k b :=
    fun k => ctl_sum_enum T (f k)
  simp only [h1]
  exact ctl_sum_enum T (fun a => ∑ b ∈ Tᶜ, f a b)

private lemma ctl_ne_of_notMem_single {i k : Fin N} (hk : k ∉ ({i} : Finset (Fin N))) : k ≠ i :=
  fun e => hk (by simp [e])

/-- The bracket of the linear form for the minor `H^{(i)}`. -/
private lemma ctl_brkLin_le {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ} (hN : 0 < N)
    (h : CtlOmega H z) {i : Fin N} {q : ℝ} (hq : 1 ≤ q) :
    ctlBrkLin N q (fun k : Fin (({i} : Finset (Fin N))ᶜ.card) =>
      resolventC (zeroRC {i} H) z (ctlEnum {i} k) (ctlEnum {i} k)) ≤ 2 / q ^ 2 + 2 / q := by
  have hq0 : 0 < q := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hd : ∀ k : Fin (({i} : Finset (Fin N))ᶜ.card),
      ‖resolventC (zeroRC {i} H) z (ctlEnum {i} k) (ctlEnum {i} k)‖ ≤ 2 := fun k =>
    ((h.norm_minor1_diag (ctl_ne_of_notMem_single (ctlEnum_notMem _ k))).2).trans (by norm_num)
  have hsup : (⨆ k : Fin (({i} : Finset (Fin N))ᶜ.card),
      ‖resolventC (zeroRC {i} H) z (ctlEnum {i} k) (ctlEnum {i} k)‖) ≤ 2 :=
    Real.iSup_le hd (by norm_num)
  have hsum : ∑ k : Fin (({i} : Finset (Fin N))ᶜ.card),
      ‖resolventC (zeroRC {i} H) z (ctlEnum {i} k) (ctlEnum {i} k)‖ ^ 2 ≤ 4 * N := by
    calc ∑ k : Fin (({i} : Finset (Fin N))ᶜ.card),
          ‖resolventC (zeroRC {i} H) z (ctlEnum {i} k) (ctlEnum {i} k)‖ ^ 2
        ≤ ∑ _k : Fin (({i} : Finset (Fin N))ᶜ.card), (4 : ℝ) :=
          Finset.sum_le_sum fun k _ => by
            have hk0 := norm_nonneg (resolventC (zeroRC {i} H) z (ctlEnum {i} k) (ctlEnum {i} k))
            nlinarith [hd k]
      _ = (({i} : Finset (Fin N))ᶜ.card : ℝ) * 4 := by simp
      _ ≤ 4 * N := by
          have : ((({i} : Finset (Fin N))ᶜ.card : ℕ) : ℝ) ≤ N := by
            exact_mod_cast ctl_card_compl_le _
          linarith
  unfold ctlBrkLin
  have h1 : (⨆ k : Fin (({i} : Finset (Fin N))ᶜ.card),
      ‖resolventC (zeroRC {i} H) z (ctlEnum {i} k) (ctlEnum {i} k)‖) / q ^ 2 ≤ 2 / q ^ 2 :=
    div_le_div_of_nonneg_right hsup (by positivity)
  have h2 : Real.sqrt (((q ^ 2)⁻¹ * (N : ℝ)⁻¹) * ∑ k : Fin (({i} : Finset (Fin N))ᶜ.card),
      ‖resolventC (zeroRC {i} H) z (ctlEnum {i} k) (ctlEnum {i} k)‖ ^ 2) ≤ 2 / q := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    calc ((q ^ 2)⁻¹ * (N : ℝ)⁻¹) * ∑ k : Fin (({i} : Finset (Fin N))ᶜ.card),
          ‖resolventC (zeroRC {i} H) z (ctlEnum {i} k) (ctlEnum {i} k)‖ ^ 2
        ≤ ((q ^ 2)⁻¹ * (N : ℝ)⁻¹) * (4 * N) := by gcongr
      _ = (2 / q) ^ 2 := by field_simp; ring
  linarith

/-- The bracket of the quadratic form for the minor `H^{(i)}` in terms of `Λ_o` and `Ψ`. -/
private lemma ctl_brkQuad_le {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ} (hN : 0 < N)
    (h : CtlOmega H z) {i : Fin N} {q : ℝ} (hq : 0 < q) :
    ctlBrkQuad N q (fun k l : Fin (({i} : Finset (Fin N))ᶜ.card) =>
      resolventC (zeroRC {i} H) z (ctlEnum {i} k) (ctlEnum {i} l)) ≤
      3 * lamO H z / q + (psiCtrl H z + lamO H z * Real.sqrt (80 / (N * z.im))) := by
  have hO := ctl_lamO_nonneg H z
  have ho : (⨆ k : Fin (({i} : Finset (Fin N))ᶜ.card), ⨆ l : Fin (({i} : Finset (Fin N))ᶜ.card),
      if k = l then (0 : ℝ) else
        ‖resolventC (zeroRC {i} H) z (ctlEnum {i} k) (ctlEnum {i} l)‖) ≤ 3 * lamO H z :=
    Real.iSup_le (fun k => Real.iSup_le (fun l => by
      split_ifs with hkl
      · positivity
      · have := h.norm_minor1_offDiag (ctl_ne_of_notMem_single (ctlEnum_notMem _ k))
          (ctl_ne_of_notMem_single (ctlEnum_notMem _ l)) (fun e => hkl (ctlEnum_injective _ e))
        linarith) (by positivity)) (by positivity)
  have hs : Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∑ k : Fin (({i} : Finset (Fin N))ᶜ.card),
      ∑ l : Fin (({i} : Finset (Fin N))ᶜ.card), if k = l then (0 : ℝ) else
        ‖resolventC (zeroRC {i} H) z (ctlEnum {i} k) (ctlEnum {i} l)‖ ^ 2) ≤
      psiCtrl H z + lamO H z * Real.sqrt (80 / (N * z.im)) := by
    have hle : ∑ k : Fin (({i} : Finset (Fin N))ᶜ.card),
        ∑ l : Fin (({i} : Finset (Fin N))ᶜ.card), (if k = l then (0 : ℝ) else
          ‖resolventC (zeroRC {i} H) z (ctlEnum {i} k) (ctlEnum {i} l)‖ ^ 2) ≤
        ∑ a ∈ ({i} : Finset (Fin N))ᶜ, ∑ b ∈ ({i} : Finset (Fin N))ᶜ,
          ‖resolventC (zeroRC {i} H) z a b‖ ^ 2 := by
      rw [← ctl_sum_sum_enum ({i} : Finset (Fin N)) (fun a b =>
        ‖resolventC (zeroRC {i} H) z a b‖ ^ 2)]
      exact Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => by
        split_ifs
        · positivity
        · exact le_rfl
    have hε : 0 ≤ 80 * lamO H z ^ 2 := by positivity
    have := ctl_hs_le hN h.herm h.im_pos {i} hε (fun a ha => by
      have ha' : a ≠ i := ctl_ne_of_notMem_single ha
      have := h.norm_minor1_sub_le ha' ha'
      nlinarith [sq_nonneg (lamO H z)])
    have e2 : Real.sqrt (80 * lamO H z ^ 2 / (N * z.im)) =
        lamO H z * Real.sqrt (80 / (N * z.im)) := by
      rw [show 80 * lamO H z ^ 2 / (N * z.im) = lamO H z ^ 2 * (80 / (N * z.im)) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hO]
    rw [e2] at this
    exact (Real.sqrt_le_sqrt (by gcongr)).trans this
  unfold ctlBrkQuad
  have h2 : (⨆ k : Fin (({i} : Finset (Fin N))ᶜ.card), ⨆ l : Fin (({i} : Finset (Fin N))ᶜ.card),
      if k = l then (0 : ℝ) else
        ‖resolventC (zeroRC {i} H) z (ctlEnum {i} k) (ctlEnum {i} l)‖) / q ≤
      3 * lamO H z / q := div_le_div_of_nonneg_right ho hq.le
  linarith

/-- The real-number inequality closing the estimate of (3.33). -/
private lemma ctl_real_close {q s C2 Λ Ψ ρ : ℝ} (hC2 : 0 < C2) (hq : 1 ≤ q) (hs1 : 1 ≤ s)
    (hsq : 48 * s ^ 2 ≤ q) (hρ : s ^ 2 * ρ ≤ 1 / 16) (hΛ0 : 0 ≤ Λ) (hΨ : 0 ≤ Ψ)
    (hΛ : Λ ≤ C2 * (1 / q + s ^ 2 * Ψ)) :
    s * (2 / q ^ 2 + 2 / q) + s ^ 2 * (3 * Λ / q + (Ψ + Λ * ρ)) ≤
      (5 + C2 / 8) * (s / q + s ^ 2 * Ψ) := by
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < s := by linarith
  set u : ℝ := 1 / q with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := by rw [hu]; exact (div_le_one hq0).2 hq
  have hsu : s / q = s * u := by rw [hu]; ring
  have e1 : s * (2 / q ^ 2 + 2 / q) = 2 * s * u ^ 2 + 2 * s * u := by
    rw [hu]; field_simp
  have e2 : s ^ 2 * (3 * Λ / q) = 3 * (s ^ 2 * u) * Λ := by
    rw [hu]; field_simp
  have ha : s ^ 2 * u ≤ 1 / 48 := by
    rw [hu, ← div_eq_mul_one_div, div_le_iff₀ hq0]
    linarith
  have h1 : 2 * s * u ^ 2 ≤ 2 * s * u := by nlinarith [mul_pos hs0 hu0]
  have h2 : 3 * (s ^ 2 * u) * Λ ≤ Λ / 16 := by nlinarith
  have h3 : s ^ 2 * (Λ * ρ) ≤ Λ / 16 := by
    have : s ^ 2 * (Λ * ρ) = (s ^ 2 * ρ) * Λ := by ring
    rw [this]
    nlinarith
  have h4 : Λ ≤ C2 * (s * u + s ^ 2 * Ψ) := by
    refine hΛ.trans ?_
    have : 1 / q ≤ s * u := by
      rw [← hu]; nlinarith
    nlinarith [mul_nonneg hC2.le (sub_nonneg.2 this)]
  have hsΨ : 0 ≤ s ^ 2 * Ψ := by positivity
  have hsu0 : 0 ≤ s * u := by positivity
  rw [hsu]
  nlinarith

end LinQuad

/-! ### Parameter arithmetic -/

private lemma ctl_one_le_phi {N : ℕ} (hN : 3 ≤ N) : 1 ≤ phi N := by
  rw [phi_eq_exp hN]
  exact Real.one_le_exp (sq_nonneg _)

private lemma ctl_phi_pos {N : ℕ} (hN : 3 ≤ N) : 0 < phi N :=
  lt_of_lt_of_le one_pos (ctl_one_le_phi hN)

private lemma ctl_rpow_sq {x : ℝ} (hx : 0 < x) (a : ℝ) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, mul_comm]
  norm_num

/-- `φ N → ∞`. -/
lemma tendsto_phi_atTop : Tendsto phi atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop 16] with N hN
  exact log_le_phi hN

/-- For `a > 0` and every `B`, eventually `3 ≤ N` and `φ^a` is at least `B (log N + 1)`. -/
lemma eventually_mul_log_add_one_le_phi_rpow {a : ℝ} (ha : 0 < a) (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, 3 ≤ N ∧ B * (Real.log N + 1) ≤ phi N ^ a := by
  have hloglog : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  set L0 := Real.log (2 * |B| + 1) with hL0
  filter_upwards [eventually_ge_atTop 3,
    hloglog.eventually_ge_atTop (max 1 ((1 + |L0|) / a))] with N hN hu
  refine ⟨hN, ?_⟩
  set u := Real.log (Real.log N) with hu_def
  have hN1 : (1 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlogpos : 0 < Real.log N := Real.log_pos hN1
  have hlog : Real.log N = Real.exp u := (Real.exp_log hlogpos).symm
  have hu1 : 1 ≤ u := le_trans (le_max_left _ _) hu
  have hua : 1 + |L0| ≤ u * a := by
    have := le_trans (le_max_right _ _) hu
    rwa [div_le_iff₀ ha] at this
  have hexpu : 1 ≤ Real.exp u := Real.one_le_exp (by linarith)
  have hexpL : Real.exp L0 = 2 * |B| + 1 := Real.exp_log (by positivity)
  have hexp : Real.exp (u + L0) ≤ Real.exp (u ^ 2 * a) := by
    apply Real.exp_le_exp.mpr
    have h1 : u ^ 2 * a = u * (u * a) := by ring
    rw [h1]
    have h2 : u * (1 + |L0|) ≤ u * (u * a) := mul_le_mul_of_nonneg_left hua (by linarith)
    nlinarith [abs_nonneg L0, le_abs_self L0, mul_le_mul_of_nonneg_right hu1 (abs_nonneg L0)]
  rw [phi_eq_exp hN, ← Real.exp_mul]
  calc B * (Real.log N + 1) = B * (Real.exp u + 1) := by rw [hlog]
    _ ≤ |B| * (Real.exp u + 1) := by
        gcongr
        exact le_abs_self B
    _ ≤ (2 * |B| + 1) * Real.exp u := by nlinarith [abs_nonneg B]
    _ = Real.exp (u + L0) := by rw [Real.exp_add, hexpL, mul_comm]
    _ ≤ Real.exp (u ^ 2 * a) := hexp

/-- A union bound over `M` events of probability `C e^{-s/C}`. -/
private lemma ctl_union_bound {C s M : ℝ} (hC : 0 < C) (hM : 1 ≤ M)
    (hs : 2 * C * (Real.log M + |Real.log C|) ≤ s) :
    M * (C * Real.exp (-s / C)) ≤ Real.exp (-(1 / (2 * C)) * s) := by
  have hM0 : 0 < M := by linarith
  have h1 : M * (C * Real.exp (-s / C)) = Real.exp (Real.log M + Real.log C + -s / C) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log hM0, Real.exp_log hC]
    ring
  rw [h1]
  apply Real.exp_le_exp.mpr
  have h2 : Real.log M + |Real.log C| ≤ s / (2 * C) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h3 : -s / C + s / (2 * C) = -(s / (2 * C)) := by
    field_simp
    ring
  have h4 : -(1 / (2 * C)) * s = -(s / (2 * C)) := by ring
  rw [h4]
  linarith [le_abs_self (Real.log C)]

/-- `specDomain` lies in the upper half plane for `N ≥ 3`, with `N η > φ^K`. -/
private lemma ctl_specDomain {N : ℕ} (hN : 3 ≤ N) {K : ℝ} {z : ℂ} (hz : z ∈ specDomain N K) :
    |z.re| ≤ 5 ∧ 0 < z.im ∧ z.im ≤ 10 ∧ phi N ^ K < N * z.im := by
  obtain ⟨h1, h2, h3⟩ := hz
  have hNr : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hφ : 0 < phi N ^ K := Real.rpow_pos_of_pos (ctl_phi_pos hN) K
  have h4 : phi N ^ K < N * z.im := by
    rwa [div_lt_iff₀ hNr, mul_comm] at h2
  refine ⟨h1, ?_, h3, h4⟩
  by_contra hneg
  have : N * z.im ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hNr.le (not_lt.mp hneg)
  linarith

/-- The `a.e.` bound on all off-diagonal entries. -/
private lemma ctl_ae_entries {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) {q : ℝ}
    (hq : L.BoundedSupportAS q) :
    ∀ᵐ ω ∂L.law, ∀ i j : Fin N, i ≠ j → |symOfEntries ω i j| ≤ q⁻¹ := by
  refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
  by_cases hij : i = j
  · exact ae_of_all _ fun ω h => absurd hij h
  · filter_upwards [ctl_ae_sym_le hL hq hij] with ω hω _ using hω

/-- The sum over the pairs `i ≠ j` of a constant bound. -/
private lemma ctl_pairs_sum_le (N : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    ∑ _p ∈ (Finset.univ.filter fun p : Fin N × Fin N => p.1 ≠ p.2), ENNReal.ofReal y ≤
      ENNReal.ofReal ((N : ℝ) ^ 2 * y) := by
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard :
      ((Finset.univ.filter fun p : Fin N × Fin N => p.1 ≠ p.2).card : ℝ) ≤ (N : ℝ) ^ 2 := by
    have h1 : (Finset.univ.filter fun p : Fin N × Fin N => p.1 ≠ p.2).card ≤ N * N := by
      calc (Finset.univ.filter fun p : Fin N × Fin N => p.1 ≠ p.2).card
          ≤ (Finset.univ : Finset (Fin N × Fin N)).card := Finset.card_filter_le _ _
        _ = N * N := by simp
    calc ((Finset.univ.filter fun p : Fin N × Fin N => p.1 ≠ p.2).card : ℝ) ≤ (N : ℝ) * N := by
          exact_mod_cast h1
      _ = (N : ℝ) ^ 2 := by ring
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hy)

private lemma ctl_sqrt_small {s D : ℝ} (hs : 0 < s) (hD : 20480 * s ^ 4 ≤ D) :
    s ^ 2 * Real.sqrt (80 / D) ≤ 1 / 16 := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD
  have h1 : Real.sqrt (80 / D) ≤ 1 / (16 * s ^ 2) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [div_pow, div_le_div_iff₀ hD0 (by positivity)]
    nlinarith [pow_pos hs 4]
  calc s ^ 2 * Real.sqrt (80 / D) ≤ s ^ 2 * (1 / (16 * s ^ 2)) := by gcongr
    _ = 1 / 16 := by field_simp

/-- The parameter conditions shared by (3.32), (3.33) and (3.36) at the offset `4ζ + 13`. -/
private lemma ctl_params {ζ : ℝ} (hζ : 0 < ζ) :
    ∀ᶠ N : ℕ in atTop, 3 ≤ N ∧ ∀ (q s : ℝ) (z : ℂ), phi N ^ (4 * ζ + 13) ≤ q →
      z ∈ specDomain N (4 * ζ + 13) → phi N ^ ζ ≤ s → s ≤ phi N ^ (ζ + 3) →
      64 ≤ s ∧ 1 ≤ q ∧ 48 * s ^ 2 ≤ q ∧ (|z.re| ≤ 5 ∧ 0 < z.im ∧ z.im ≤ 10) ∧
        s ^ 2 * Real.sqrt (80 / (N * z.im)) ≤ 1 / 16 := by
  filter_upwards [eventually_mul_log_add_one_le_phi_rpow hζ 64,
    eventually_mul_log_add_one_le_phi_rpow (a := 2 * ζ + 7) (by linarith) 48,
    eventually_mul_log_add_one_le_phi_rpow (a := 1) one_pos 20480] with N h1 h2 h3
  obtain ⟨hN3, hB⟩ := h1
  obtain ⟨-, h48⟩ := h2
  obtain ⟨-, h20480⟩ := h3
  refine ⟨hN3, fun q s z hqK hz hs1 hs2 => ?_⟩
  have hφ1 := ctl_one_le_phi hN3
  have hφ0 : 0 < phi N := ctl_phi_pos hN3
  have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hs64 : 64 ≤ s := by nlinarith
  have hs0 : 0 < s := by linarith
  have hKnn : 0 ≤ 4 * ζ + 13 := by positivity
  have hq1 : 1 ≤ q := le_trans (Real.one_le_rpow hφ1 hKnn) hqK
  have hX : (phi N ^ (ζ + 3)) ^ 2 = phi N ^ (2 * ζ + 6) := by
    rw [ctl_rpow_sq hφ0]
    ring_nf
  have hs2' : s ^ 2 ≤ phi N ^ (2 * ζ + 6) := by
    rw [← hX]
    exact pow_le_pow_left₀ hs0.le hs2 2
  have h48' : 48 ≤ phi N ^ (2 * ζ + 7) := by nlinarith
  have hsq : 48 * s ^ 2 ≤ q := by
    have hsplit : phi N ^ (4 * ζ + 13) = phi N ^ (2 * ζ + 7) * phi N ^ (2 * ζ + 6) := by
      rw [← Real.rpow_add hφ0]
      ring_nf
    have hpos6 : 0 ≤ phi N ^ (2 * ζ + 6) := (Real.rpow_pos_of_pos hφ0 _).le
    calc 48 * s ^ 2 ≤ 48 * phi N ^ (2 * ζ + 6) := by gcongr
      _ ≤ phi N ^ (2 * ζ + 7) * phi N ^ (2 * ζ + 6) := by gcongr
      _ = phi N ^ (4 * ζ + 13) := hsplit.symm
      _ ≤ q := hqK
  obtain ⟨hzre, hzim, hzle, hzNη⟩ := ctl_specDomain hN3 hz
  have hρ : s ^ 2 * Real.sqrt (80 / (N * z.im)) ≤ 1 / 16 := by
    refine ctl_sqrt_small hs0 ?_
    have hX4 : (phi N ^ (ζ + 3)) ^ 4 = phi N ^ (4 * ζ + 12) := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hX, ctl_rpow_sq hφ0]
      ring_nf
    have hs4 : s ^ 4 ≤ phi N ^ (4 * ζ + 12) := by
      rw [← hX4]
      exact pow_le_pow_left₀ hs0.le hs2 4
    have hsplit : phi N ^ (4 * ζ + 13) = phi N ^ (4 * ζ + 12) * phi N := by
      rw [show 4 * ζ + 13 = (4 * ζ + 12) + 1 by ring, Real.rpow_add hφ0, Real.rpow_one]
    have h20480' : 20480 ≤ phi N := by
      rw [Real.rpow_one] at h20480
      linarith
    have hpos12 : 0 ≤ phi N ^ (4 * ζ + 12) := (Real.rpow_pos_of_pos hφ0 _).le
    calc 20480 * s ^ 4 ≤ 20480 * phi N ^ (4 * ζ + 12) := by gcongr
      _ ≤ phi N ^ (4 * ζ + 12) * phi N := by
          nlinarith [mul_le_mul_of_nonneg_left h20480' hpos12]
      _ = phi N ^ (4 * ζ + 13) := hsplit.symm
      _ ≤ N * z.im := hzNη.le
  exact ⟨hs64, hq1, hsq, ⟨hzre, hzim, hzle⟩, hρ⟩

/-- Larger offsets `K` give stronger hypotheses. -/
private lemma ctl_rpow_mono {N : ℕ} (hN : 3 ≤ N) {a b : ℝ} (hab : a ≤ b) :
    phi N ^ a ≤ phi N ^ b :=
  Real.rpow_le_rpow_of_exponent_le (ctl_one_le_phi hN) hab

private lemma ctl_specDomain_mono {N : ℕ} (hN : 3 ≤ N) {K K' : ℝ} (hKK : K' ≤ K) {z : ℂ}
    (hz : z ∈ specDomain N K) : z ∈ specDomain N K' := by
  obtain ⟨h1, h2, h3⟩ := hz
  have hNr : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  refine ⟨h1, lt_of_le_of_lt ?_ h2, h3⟩
  exact div_le_div_of_nonneg_right (ctl_rpow_mono hN hKK) hNr.le

/-- (3.32) of [15] at a level `s ∈ [φ^ζ, φ^{ζ+3}]` (`s = (log N)^ξ`), constants uniform in `s`. -/
theorem lamO_le_on_omega_level {ζ C0 : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) :
    ∃ K > 0, ∃ C > 0, ∃ c > 0, ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (L : EntryLaws N) (q s : ℝ) (z : ℂ),
      L.IsGenWigner C0 → L.BoundedSupportAS q → phi N ^ K ≤ q → z ∈ specDomain N K →
      phi N ^ ζ ≤ s → s ≤ phi N ^ (ζ + 3) →
      L.law {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        C * (1 / q + s ^ 2 * psiCtrl (symOfEntries ω) z) < lamO (symOfEntries ω) z} ≤
        ENNReal.ofReal (Real.exp (-c * s)) := by
  have _ := hC0
  obtain ⟨CLD, hCLD, hpair⟩ := ctl_pair_le
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 ((ctl_params hζ).and
    (eventually_mul_log_add_one_le_phi_rpow hζ (4 * CLD + 2 * CLD * |Real.log CLD|)))
  refine ⟨4 * ζ + 13, by positivity, 3, by norm_num, 1 / (2 * CLD), by positivity, N0, ?_⟩
  intro N hN L q s z hL hq hqK hz hs1 hs2
  obtain ⟨⟨hN3, hpar⟩, -, hB⟩ := hN0 N hN
  obtain ⟨hs64, hq1, hsq, ⟨hzre, hzim, hzle⟩, hρ⟩ := hpar q s z hqK hz hs1 hs2
  have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hNpos : 0 < N := by omega
  have hs0 : 0 < s := by linarith
  have hq0 : 0 < q := by linarith
  have hunion : 2 * CLD * (Real.log ((N : ℝ) ^ 2) + |Real.log CLD|) ≤ s := by
    have e : Real.log ((N : ℝ) ^ 2) = 2 * Real.log N := by
      rw [Real.log_pow]
      norm_num
    rw [e]
    have h1 : 0 ≤ 2 * CLD * |Real.log CLD| := by positivity
    have h2 : 0 ≤ CLD := hCLD.le
    nlinarith [mul_nonneg hlog0 h1, mul_nonneg hlog0 h2]
  have hmsc := ctl_msc_bounds hzre hzim hzle
  have hs164 : s⁻¹ ≤ 1 / 64 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) hs64
  -- the covering by the bad events
  set P : Finset (Fin N × Fin N) := Finset.univ.filter fun p => p.1 ≠ p.2 with hP
  have hsub : {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
      3 * (1 / q + s ^ 2 * psiCtrl (symOfEntries ω) z) < lamO (symOfEntries ω) z} ⊆
      (⋃ p ∈ P, ctlBadBil {p.1, p.2} q s z p.1 p.2) ∪
        {ω | ¬ ∀ i j : Fin N, i ≠ j → |symOfEntries ω i j| ≤ q⁻¹} := by
    rintro ω ⟨hΩ, hbig⟩
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨hnb, hgood'⟩ := hcon
    have hgood : ∀ i j : Fin N, i ≠ j → |symOfEntries ω i j| ≤ q⁻¹ := by
      by_contra hh
      exact hgood' hh
    have hΩ' : CtlOmega (symOfEntries ω) z :=
      ⟨symOfEntries_isHermitian ω, hzim, hmsc.1, hmsc.2, by linarith⟩
    have hS : ∀ i j : Fin N, i ≠ j →
        ‖∑ k, ∑ l, (if k = i ∨ k = j ∨ l = i ∨ l = j then (0 : ℂ) else
          (symOfEntries ω i k : ℂ) * resolventC (zeroRC {i, j} (symOfEntries ω)) z k l *
            symOfEntries ω l j)‖ ≤ s ^ 2 * (2 / q ^ 2 + 3 * lamO (symOfEntries ω) z / q +
              (psiCtrl (symOfEntries ω) z + lamO (symOfEntries ω) z *
                Real.sqrt (80 / (N * z.im)))) := by
      intro i j hij
      rw [← ctl_form_eq]
      have hmem : (i, j) ∈ P := by simp [hP, hij]
      have h1 : ¬ ω ∈ ctlBadBil {i, j} q s z i j := fun h =>
        hnb (Set.mem_iUnion₂.2 ⟨(i, j), hmem, h⟩)
      have h2 : ‖ctlForm {i, j} z i j ω‖ ≤ s ^ 2 * ctlBrkBil N q (ctlMinor {i, j} z ω) :=
        not_lt.mp h1
      refine h2.trans ?_
      gcongr
      exact ctl_brkBil_le hNpos hΩ' hij hq0
    exact absurd (ctl_lamO_close hΩ' hq1 hsq hρ hgood hS) (not_le.mpr hbig)
  have hnull : L.law {ω | ¬ ∀ i j : Fin N, i ≠ j → |symOfEntries ω i j| ≤ q⁻¹} = 0 :=
    ae_iff.mp (ctl_ae_entries hL.isProb hq)
  have hbad : ∀ p ∈ P, L.law (ctlBadBil {p.1, p.2} q s z p.1 p.2) ≤
      ENNReal.ofReal (CLD * Real.exp (-s / CLD)) := by
    intro p hp
    have hp' : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hcard : 0 < (({p.1, p.2} : Finset (Fin N))ᶜ).card := by
      rw [ctl_card_compl_pair hp']
      omega
    exact hpair hL hq hq1 hzim {p.1, p.2} (by simp) (by simp) hp' hcard s hs0
  have hN1 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith
  calc L.law {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        3 * (1 / q + s ^ 2 * psiCtrl (symOfEntries ω) z) < lamO (symOfEntries ω) z}
      ≤ L.law ((⋃ p ∈ P, ctlBadBil {p.1, p.2} q s z p.1 p.2) ∪
        {ω | ¬ ∀ i j : Fin N, i ≠ j → |symOfEntries ω i j| ≤ q⁻¹}) := measure_mono hsub
    _ ≤ L.law (⋃ p ∈ P, ctlBadBil {p.1, p.2} q s z p.1 p.2) +
        L.law {ω | ¬ ∀ i j : Fin N, i ≠ j → |symOfEntries ω i j| ≤ q⁻¹} := measure_union_le _ _
    _ = L.law (⋃ p ∈ P, ctlBadBil {p.1, p.2} q s z p.1 p.2) := by rw [hnull, add_zero]
    _ ≤ ∑ p ∈ P, L.law (ctlBadBil {p.1, p.2} q s z p.1 p.2) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ P, ENNReal.ofReal (CLD * Real.exp (-s / CLD)) := Finset.sum_le_sum hbad
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ 2 * (CLD * Real.exp (-s / CLD))) :=
        ctl_pairs_sum_le N (by positivity)
    _ ≤ ENNReal.ofReal (Real.exp (-(1 / (2 * CLD)) * s)) :=
        ENNReal.ofReal_le_ofReal (ctl_union_bound hCLD hN1 hunion)

/-- Two exponentially small terms add up to a slightly weaker exponential. -/
lemma add_le_exp_neg_half_mul_of_le_exp {c s x y : ℝ} (hc : 0 < c) (hs : 2 / c ≤ s)
    (hx : x ≤ Real.exp (-c * s)) (hy : y ≤ Real.exp (-c * s)) :
    x + y ≤ Real.exp (-(c / 2) * s) := by
  have hcs : 2 ≤ c * s := by
    rw [div_le_iff₀ hc] at hs
    linarith
  have h1 : x + y ≤ Real.exp (Real.log 2) * Real.exp (-c * s) := by
    rw [Real.exp_log two_pos]
    linarith
  rw [← Real.exp_add] at h1
  refine h1.trans (Real.exp_le_exp.mpr ?_)
  have := Real.log_two_lt_d9
  nlinarith

private lemma ctl_exp_mono_C {C C' s : ℝ} (hC : 0 < C) (hCC : C ≤ C') (hs : 0 ≤ s) :
    C * Real.exp (-s / C) ≤ C' * Real.exp (-s / C') := by
  have h1 : Real.exp (-s / C) ≤ Real.exp (-s / C') := by
    apply Real.exp_le_exp.mpr
    have : s / C' ≤ s / C := div_le_div_of_nonneg_left hs hC hCC
    have e1 : -s / C = -(s / C) := by ring
    have e2 : -s / C' = -(s / C') := by ring
    rw [e1, e2]
    linarith
  exact mul_le_mul hCC h1 (Real.exp_pos _).le (by linarith)

/-- (3.33) of [15] at a level `s`. -/
theorem norm_zFluct_le_on_omega {ζ C0 : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) :
    ∃ K > 0, ∃ C > 0, ∃ c > 0, ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (L : EntryLaws N) (q s : ℝ) (z : ℂ),
      L.IsGenWigner C0 → L.BoundedSupportAS q → phi N ^ K ≤ q → z ∈ specDomain N K →
      phi N ^ ζ ≤ s → s ≤ phi N ^ (ζ + 3) →
      L.law {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        C * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) <
          ⨆ i, ‖zFluct (symOfEntries ω) z i‖} ≤ ENNReal.ofReal (Real.exp (-c * s)) := by
  obtain ⟨K2, hK2, C2, hC2, c2, hc2, N2, h2⟩ := lamO_le_on_omega_level hζ hC0
  obtain ⟨CL, hCL, hlin⟩ := ctl_lin_le
  obtain ⟨CQ, hCQ, hquad⟩ := ctl_quad_le
  set Cs : ℝ := CL + CQ with hCs
  have hCs0 : 0 < Cs := by positivity
  set c' : ℝ := min c2 (1 / (2 * Cs)) with hc'
  have hc'0 : 0 < c' := lt_min hc2 (by positivity)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 ((ctl_params hζ).and
    (eventually_mul_log_add_one_le_phi_rpow hζ (2 * Cs * (1 + |Real.log Cs|) + 2 / c')))
  refine ⟨max K2 (4 * ζ + 13), lt_max_of_lt_left hK2, 5 + C2 / 8, by positivity, c' / 2,
    by positivity, max N0 N2, ?_⟩
  intro N hN L q s z hL hq hqK hz hs1 hs2
  obtain ⟨⟨hN3, hpar⟩, -, hB⟩ := hN0 N (le_trans (le_max_left _ _) hN)
  have hN2 : N2 ≤ N := le_trans (le_max_right _ _) hN
  have hqK2 : phi N ^ K2 ≤ q := (ctl_rpow_mono hN3 (le_max_left _ _)).trans hqK
  have hqK' : phi N ^ (4 * ζ + 13) ≤ q := (ctl_rpow_mono hN3 (le_max_right _ _)).trans hqK
  have hz2 : z ∈ specDomain N K2 := ctl_specDomain_mono hN3 (le_max_left _ _) hz
  have hz' : z ∈ specDomain N (4 * ζ + 13) := ctl_specDomain_mono hN3 (le_max_right _ _) hz
  obtain ⟨hs64, hq1, hsq, ⟨hzre, hzim, hzle⟩, hρ⟩ := hpar q s z hqK' hz' hs1 hs2
  have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hs0 : 0 < s := by linarith
  have hq0 : 0 < q := by linarith
  have hT2 := h2 N hN2 L q s z hL hq hqK2 hz2 hs1 hs2
  have hmsc := ctl_msc_bounds hzre hzim hzle
  have hs164 : s⁻¹ ≤ 1 / 64 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) hs64
  -- thresholds for the exponential bounds
  have hunion : 2 * Cs * (Real.log (2 * (N : ℝ)) + |Real.log Cs|) ≤ s := by
    have e : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log N :=
      Real.log_mul (by norm_num) hNr.ne'
    have hl2 := Real.log_two_lt_d9
    rw [e]
    have h1 : 0 ≤ 2 * Cs * |Real.log Cs| := by positivity
    have h3 : 0 ≤ 2 / c' := by positivity
    nlinarith [mul_nonneg hlog0 h1, mul_nonneg hlog0 hCs0.le, mul_nonneg hlog0 h3]
  have hs2c : 2 / c' ≤ s := by
    have h1 : 0 ≤ 2 * Cs * (1 + |Real.log Cs|) := by positivity
    have h3 : 0 ≤ 2 / c' := by positivity
    nlinarith [mul_nonneg hlog0 h1, mul_nonneg hlog0 h3]
  -- the covering
  have hsub : {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
      (5 + C2 / 8) * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) <
        ⨆ i, ‖zFluct (symOfEntries ω) z i‖} ⊆
      {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        C2 * (1 / q + s ^ 2 * psiCtrl (symOfEntries ω) z) < lamO (symOfEntries ω) z} ∪
      ⋃ i ∈ (Finset.univ : Finset (Fin N)), (ctlBadLin {i} q s z i ∪ ctlBadQuad {i} q s z i) := by
    rintro ω ⟨hΩ, hbig⟩
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨hn2, hnb⟩ := hcon
    have hΛ : lamO (symOfEntries ω) z ≤ C2 * (1 / q + s ^ 2 * psiCtrl (symOfEntries ω) z) :=
      not_lt.mp fun hlt => hn2 ⟨hΩ, hlt⟩
    have hΩ' : CtlOmega (symOfEntries ω) z :=
      ⟨symOfEntries_isHermitian ω, hzim, hmsc.1, hmsc.2, by linarith⟩
    have hZ : ∀ i : Fin N, ‖zFluct (symOfEntries ω) z i‖ ≤
        (5 + C2 / 8) * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) := by
      intro i
      have hl : ω ∉ ctlBadLin {i} q s z i := fun h =>
        hnb (Set.mem_iUnion₂.2 ⟨i, Finset.mem_univ i, Or.inl h⟩)
      have hqd : ω ∉ ctlBadQuad {i} q s z i := fun h =>
        hnb (Set.mem_iUnion₂.2 ⟨i, Finset.mem_univ i, Or.inr h⟩)
      rw [ctl_zFluct_eq]
      refine (norm_add_le _ _).trans ?_
      have hlin' : ‖ctlLinForm {i} z i ω‖ ≤ s * (2 / q ^ 2 + 2 / q) :=
        (not_lt.mp hl).trans (by
          gcongr
          exact ctl_brkLin_le hNpos hΩ' hq1)
      have hquad' : ‖ctlOffForm {i} z i ω‖ ≤ s ^ 2 * (3 * lamO (symOfEntries ω) z / q +
          (psiCtrl (symOfEntries ω) z + lamO (symOfEntries ω) z *
            Real.sqrt (80 / (N * z.im)))) :=
        (not_lt.mp hqd).trans (by
          gcongr
          exact ctl_brkQuad_le hNpos hΩ' hq0)
      refine (add_le_add hlin' hquad').trans ?_
      exact ctl_real_close hC2 hq1 (by linarith) hsq hρ (ctl_lamO_nonneg _ _)
        (Real.sqrt_nonneg _) hΛ
    have : (⨆ i, ‖zFluct (symOfEntries ω) z i‖) ≤
        (5 + C2 / 8) * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) :=
      Real.iSup_le hZ (mul_nonneg (by positivity) (add_nonneg (div_nonneg hs0.le hq0.le)
        (mul_nonneg (sq_nonneg s) (Real.sqrt_nonneg _))))
    exact absurd hbig (not_lt.mpr this)
  -- the probabilities
  have hbound : ∀ i : Fin N, L.law (ctlBadLin {i} q s z i ∪ ctlBadQuad {i} q s z i) ≤
      ENNReal.ofReal (2 * (Cs * Real.exp (-s / Cs))) := by
    intro i
    have hcard : 0 < (({i} : Finset (Fin N))ᶜ).card := by
      rw [ctl_card_compl_single]
      omega
    have h1 : L.law (ctlBadLin {i} q s z i) ≤ ENNReal.ofReal (Cs * Real.exp (-s / Cs)) :=
      (hlin hL hq hq1 (by omega) hzim {i} (Finset.mem_singleton_self i) hcard s hs0).trans
        (ENNReal.ofReal_le_ofReal (ctl_exp_mono_C hCL (by linarith) hs0.le))
    have h2 : L.law (ctlBadQuad {i} q s z i) ≤ ENNReal.ofReal (Cs * Real.exp (-s / Cs)) :=
      (hquad hL hq hq1 hzim {i} (Finset.mem_singleton_self i) s hs0).trans
        (ENNReal.ofReal_le_ofReal (ctl_exp_mono_C hCQ (by linarith) hs0.le))
    calc L.law (ctlBadLin {i} q s z i ∪ ctlBadQuad {i} q s z i)
        ≤ L.law (ctlBadLin {i} q s z i) + L.law (ctlBadQuad {i} q s z i) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Cs * Real.exp (-s / Cs)) + ENNReal.ofReal (Cs * Real.exp (-s / Cs)) :=
          add_le_add h1 h2
      _ = ENNReal.ofReal (2 * (Cs * Real.exp (-s / Cs))) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf
  have hsum : L.law (⋃ i ∈ (Finset.univ : Finset (Fin N)),
      (ctlBadLin {i} q s z i ∪ ctlBadQuad {i} q s z i)) ≤
      ENNReal.ofReal (Real.exp (-(1 / (2 * Cs)) * s)) := by
    calc L.law (⋃ i ∈ (Finset.univ : Finset (Fin N)),
          (ctlBadLin {i} q s z i ∪ ctlBadQuad {i} q s z i))
        ≤ ∑ i ∈ (Finset.univ : Finset (Fin N)),
            L.law (ctlBadLin {i} q s z i ∪ ctlBadQuad {i} q s z i) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin N)), ENNReal.ofReal (2 * (Cs * Real.exp (-s / Cs))) :=
          Finset.sum_le_sum fun i _ => hbound i
      _ = ENNReal.ofReal ((N : ℝ) * (2 * (Cs * Real.exp (-s / Cs)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      _ ≤ ENNReal.ofReal (Real.exp (-(1 / (2 * Cs)) * s)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := ctl_union_bound hCs0 (M := 2 * (N : ℝ)) (by
            have : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
            linarith) hunion
          calc (N : ℝ) * (2 * (Cs * Real.exp (-s / Cs)))
              = 2 * (N : ℝ) * (Cs * Real.exp (-s / Cs)) := by
                ring
            _ ≤ _ := this
  have hexp1 : Real.exp (-c2 * s) ≤ Real.exp (-c' * s) := by
    apply Real.exp_le_exp.mpr
    nlinarith [min_le_left c2 (1 / (2 * Cs))]
  have hexp2 : Real.exp (-(1 / (2 * Cs)) * s) ≤ Real.exp (-c' * s) := by
    apply Real.exp_le_exp.mpr
    nlinarith [min_le_right c2 (1 / (2 * Cs))]
  calc L.law {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        (5 + C2 / 8) * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) <
          ⨆ i, ‖zFluct (symOfEntries ω) z i‖}
      ≤ L.law ({ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        C2 * (1 / q + s ^ 2 * psiCtrl (symOfEntries ω) z) < lamO (symOfEntries ω) z} ∪
      ⋃ i ∈ (Finset.univ : Finset (Fin N)), (ctlBadLin {i} q s z i ∪ ctlBadQuad {i} q s z i)) :=
        measure_mono hsub
    _ ≤ L.law {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        C2 * (1 / q + s ^ 2 * psiCtrl (symOfEntries ω) z) < lamO (symOfEntries ω) z} +
      L.law (⋃ i ∈ (Finset.univ : Finset (Fin N)),
        (ctlBadLin {i} q s z i ∪ ctlBadQuad {i} q s z i)) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-c2 * s)) + ENNReal.ofReal (Real.exp (-(1 / (2 * Cs)) * s)) :=
        add_le_add hT2 hsum
    _ = ENNReal.ofReal (Real.exp (-c2 * s) + Real.exp (-(1 / (2 * Cs)) * s)) :=
        (ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le).symm
    _ ≤ ENNReal.ofReal (Real.exp (-(c' / 2) * s)) :=
        ENNReal.ofReal_le_ofReal
          (add_le_exp_neg_half_mul_of_le_exp hc'0 hs2c (hexp1.trans le_rfl) hexp2)

namespace CtlOmega

variable {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ}

/-- `|A_i| ≤ C/N + C Λ_o²`. -/
private lemma norm_aCorr_le (h : CtlOmega H z) (hN : 0 < N) (i : Fin N) :
    ‖aCorr H z i‖ ≤ 5 / (4 * N) + 22 * lamO H z ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hO := ctl_lamO_nonneg H z
  have hii := h.norm_diag_bounds i
  have hgi : 0 < ‖resolventC H z i i‖ := lt_of_lt_of_le (by norm_num) hii.1
  unfold aCorr
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin N)).erase i,
      ‖resolventC H z i j * resolventC H z j i / resolventC H z i i‖ ≤ 22 * lamO H z ^ 2 := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have h1 : ‖resolventC H z i j‖ ≤ lamO H z := norm_resolventC_off_le_lamO (Ne.symm hji)
    have h2 : ‖resolventC H z j i‖ ≤ lamO H z := norm_resolventC_off_le_lamO hji
    rw [norm_div, norm_mul]
    calc ‖resolventC H z i j‖ * ‖resolventC H z j i‖ / ‖resolventC H z i i‖
        ≤ lamO H z * lamO H z / (3 / 64) := by gcongr; exact hii.1
      _ ≤ 22 * lamO H z ^ 2 := by nlinarith
  have hsum : ‖∑ j, resolventC H z i j * resolventC H z j i / resolventC H z i i‖ ≤
      5 / 4 + N * (22 * lamO H z ^ 2) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    refine (norm_add_le _ _).trans ?_
    have hdiag : ‖resolventC H z i i * resolventC H z i i / resolventC H z i i‖ ≤ 5 / 4 := by
      rw [mul_div_cancel_right₀ _ (ctl_diag_ne_zero h.herm h.im_pos i)]
      exact hii.2
    have hrest : ‖∑ j ∈ (Finset.univ : Finset (Fin N)).erase i,
        resolventC H z i j * resolventC H z j i / resolventC H z i i‖ ≤
          N * (22 * lamO H z ^ 2) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ j ∈ (Finset.univ : Finset (Fin N)).erase i,
            ‖resolventC H z i j * resolventC H z j i / resolventC H z i i‖
          ≤ ∑ _j ∈ (Finset.univ : Finset (Fin N)).erase i, 22 * lamO H z ^ 2 :=
            Finset.sum_le_sum hterm
        _ = (((Finset.univ : Finset (Fin N)).erase i).card : ℝ) * (22 * lamO H z ^ 2) := by simp
        _ ≤ N * (22 * lamO H z ^ 2) := by
            gcongr
            have : ((Finset.univ : Finset (Fin N)).erase i).card ≤ N := by
              calc _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_erase_le
                _ = N := by simp
            exact_mod_cast this
    linarith
  calc (N : ℝ)⁻¹ * ‖∑ j, resolventC H z i j * resolventC H z j i / resolventC H z i i‖
      ≤ (N : ℝ)⁻¹ * (5 / 4 + N * (22 * lamO H z ^ 2)) := by gcongr
    _ = 5 / (4 * N) + 22 * lamO H z ^ 2 := by field_simp

/-- The diagonal entries differ from their average by at most the oscillation of `Υ`. -/
private lemma norm_diag_sub_le (h : CtlOmega H z) (hN : 0 < N) {U : ℝ}
    (hU : ∀ j, ‖upsilon H z j‖ ≤ U) (i : Fin N) :
    ‖resolventC H z i i - stieltjesM H z‖ ≤ 25 / 8 * U := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU i)
  have hdiff : ∀ j, ‖resolventC H z i i - resolventC H z j j‖ ≤ 25 / 8 * U := by
    intro j
    have hi := inv_resolventC_diag_eq h.herm h.im_pos i
    have hj := inv_resolventC_diag_eq h.herm h.im_pos j
    have hgi := ctl_diag_ne_zero h.herm h.im_pos i
    have hgj := ctl_diag_ne_zero h.herm h.im_pos j
    have key : resolventC H z i i - resolventC H z j j =
        resolventC H z i i * resolventC H z j j *
          (upsilon H z j - upsilon H z i) := by
      have e : (resolventC H z j j)⁻¹ - (resolventC H z i i)⁻¹ = upsilon H z j - upsilon H z i := by
        rw [hi, hj]; ring
      rw [← e]
      field_simp
    rw [key, norm_mul, norm_mul]
    have h1 := (h.norm_diag_bounds i).2
    have h2 := (h.norm_diag_bounds j).2
    have h3 : ‖upsilon H z j - upsilon H z i‖ ≤ 2 * U := by
      refine (norm_sub_le _ _).trans ?_
      linarith [hU i, hU j]
    have h4 : 0 ≤ ‖resolventC H z i i‖ := norm_nonneg _
    have h5 : 0 ≤ ‖resolventC H z j j‖ := norm_nonneg _
    calc ‖resolventC H z i i‖ * ‖resolventC H z j j‖ * ‖upsilon H z j - upsilon H z i‖
        ≤ (5 / 4) * (5 / 4) * (2 * U) := by gcongr
      _ = 25 / 8 * U := by ring
  have hm : resolventC H z i i - stieltjesM H z =
      (N : ℂ)⁻¹ * ∑ j, (resolventC H z i i - resolventC H z j j) := by
    unfold stieltjesM
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Matrix.trace]
    simp only [Matrix.diag]
    field_simp
  rw [hm, norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ j, (resolventC H z i i - resolventC H z j j)‖
      ≤ (N : ℝ)⁻¹ * (N * (25 / 8 * U)) := by
        gcongr
        refine (norm_sum_le _ _).trans ?_
        calc ∑ j, ‖resolventC H z i i - resolventC H z j j‖
            ≤ ∑ _j : Fin N, 25 / 8 * U := Finset.sum_le_sum fun j _ => hdiff j
          _ = N * (25 / 8 * U) := by simp
    _ = 25 / 8 * U := by field_simp

end CtlOmega

/-- The `a.e.` bound on all diagonal entries. -/
private lemma ctl_ae_diag_entries {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) {q : ℝ}
    (hq : L.BoundedSupportAS q) : ∀ᵐ ω ∂L.law, ∀ i : Fin N, |symOfEntries ω i i| ≤ q⁻¹ := by
  refine ae_all_iff.2 fun i => ?_
  filter_upwards [ctl_ae_diag_le hL hq i] with ω hω
  simpa [symOfEntries] using hω

/-- Closing the estimate of (3.36) from the bounds on `Λ_o`, `Z_i` and the diagonal entries. -/
private lemma ctl_diag_close {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ} (hN : 0 < N)
    (h : CtlOmega H z) {q s C2 C3 : ℝ} (hC2 : 0 < C2) (hq0 : 0 < q) (hs1 : 1 ≤ s)
    (hdiag : ∀ i, |H i i| ≤ q⁻¹) (hNinv : (N : ℝ)⁻¹ ≤ 1 / q)
    (hΛ : lamO H z ≤ C2 * (1 / q + s ^ 2 * psiCtrl H z))
    (hZ : (⨆ i, ‖zFluct H z i‖) ≤ C3 * (s / q + s ^ 2 * psiCtrl H z)) :
    (⨆ i, ‖resolventC H z i i - stieltjesM H z‖) ≤
      25 / 8 * ((9 / 4 + C3 + C2 / 2) * (s / q + s ^ 2 * psiCtrl H z)) := by
  set X : ℝ := s / q + s ^ 2 * psiCtrl H z with hX
  have hΨ : 0 ≤ psiCtrl H z := Real.sqrt_nonneg _
  have hu : 1 / q ≤ s / q := div_le_div_of_nonneg_right hs1 hq0.le
  have hX0 : s / q ≤ X := by
    have : 0 ≤ s ^ 2 * psiCtrl H z := by positivity
    linarith
  have hΛ' : lamO H z ≤ C2 * X := by
    refine hΛ.trans ?_
    gcongr
    linarith
  have hU : ∀ j : Fin N, ‖upsilon H z j‖ ≤ (9 / 4 + C3 + C2 / 2) * X := by
    intro j
    have hO := ctl_lamO_nonneg H z
    have hO64 := h.lamO_le
    have hA := h.norm_aCorr_le hN j
    have hZj : ‖zFluct H z j‖ ≤ C3 * X :=
      (le_ciSup (f := fun i => ‖zFluct H z i‖) (Set.finite_range _).bddAbove j).trans hZ
    have hh : ‖((H j j : ℝ) : ℂ)‖ ≤ X := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have := hdiag j
      rw [← one_div] at this
      linarith
    have h5 : 5 / (4 * (N : ℝ)) ≤ 5 / 4 * X := by
      have e : 5 / (4 * (N : ℝ)) = 5 / 4 * (N : ℝ)⁻¹ := by field_simp
      rw [e]
      have : (N : ℝ)⁻¹ ≤ X := hNinv.trans (hu.trans hX0)
      linarith
    have h22 : 22 * lamO H z ^ 2 ≤ C2 / 2 * X := by
      have h1 : lamO H z ^ 2 ≤ lamO H z * (1 / 64) := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left hO64 hO
      have h2 : 22 * (lamO H z * (1 / 64)) ≤ lamO H z / 2 := by linarith
      have h3 : lamO H z / 2 ≤ C2 / 2 * X := by linarith
      linarith
    unfold upsilon
    have h6 : ‖((H j j : ℝ) : ℂ) - zFluct H z j + aCorr H z j‖ ≤
        ‖((H j j : ℝ) : ℂ)‖ + ‖zFluct H z j‖ + ‖aCorr H z j‖ := by
      refine (norm_add_le _ _).trans ?_
      have := norm_sub_le ((H j j : ℝ) : ℂ) (zFluct H z j)
      linarith
    have h7 : (9 / 4 + C3 + C2 / 2) * X = X + C3 * X + (5 / 4 * X + C2 / 2 * X) := by ring
    rw [h7]
    linarith
  have hpos : 0 ≤ 25 / 8 * ((9 / 4 + C3 + C2 / 2) * X) := by
    have h0 : 0 ≤ ‖upsilon H z ⟨0, hN⟩‖ := norm_nonneg _
    have h1 := hU ⟨0, hN⟩
    have : 0 ≤ (9 / 4 + C3 + C2 / 2) * X := h0.trans h1
    positivity
  exact Real.iSup_le (fun i => h.norm_diag_sub_le hN hU i) hpos

/-- (3.36) of [15] at a level `s`. -/
theorem norm_resolventC_diag_sub_le_on_omega {ζ C0 : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) :
    ∃ K > 0, ∃ C > 0, ∃ c > 0, ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (L : EntryLaws N) (q s : ℝ) (z : ℂ),
      L.IsGenWigner C0 → L.BoundedSupportAS q → phi N ^ K ≤ q → z ∈ specDomain N K →
      phi N ^ ζ ≤ s → s ≤ phi N ^ (ζ + 3) →
      L.law {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        C * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) <
          ⨆ i, ‖resolventC (symOfEntries ω) z i i - stieltjesM (symOfEntries ω) z‖} ≤
        ENNReal.ofReal (Real.exp (-c * s)) := by
  obtain ⟨K2, hK2, C2, hC2, c2, hc2, N2, h2⟩ := lamO_le_on_omega_level hζ hC0
  obtain ⟨K3, hK3, C3, hC3, c3, hc3, N3, h3⟩ := norm_zFluct_le_on_omega hζ hC0
  set c' : ℝ := min c2 c3 with hc'
  have hc'0 : 0 < c' := lt_min hc2 hc3
  obtain ⟨N0, hN0⟩ :=
    eventually_atTop.1 ((ctl_params hζ).and (eventually_mul_log_add_one_le_phi_rpow hζ (2 / c')))
  refine ⟨max K2 (max K3 (4 * ζ + 13)), lt_max_of_lt_left hK2, 25 / 8 * (9 / 4 + C3 + C2 / 2),
    by positivity, c' / 2, by positivity, max N0 (max N2 N3), ?_⟩
  intro N hN L q s z hL hq hqK hz hs1 hs2
  obtain ⟨⟨hN3, hpar⟩, -, hB⟩ := hN0 N (le_trans (le_max_left _ _) hN)
  have hN2 : N2 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN3' : N3 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hK2le : K2 ≤ max K2 (max K3 (4 * ζ + 13)) := le_max_left _ _
  have hK3le : K3 ≤ max K2 (max K3 (4 * ζ + 13)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hK4le : 4 * ζ + 13 ≤ max K2 (max K3 (4 * ζ + 13)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hqK2 : phi N ^ K2 ≤ q := (ctl_rpow_mono hN3 hK2le).trans hqK
  have hqK3 : phi N ^ K3 ≤ q := (ctl_rpow_mono hN3 hK3le).trans hqK
  have hqK' : phi N ^ (4 * ζ + 13) ≤ q := (ctl_rpow_mono hN3 hK4le).trans hqK
  have hz2 : z ∈ specDomain N K2 := ctl_specDomain_mono hN3 hK2le hz
  have hz3 : z ∈ specDomain N K3 := ctl_specDomain_mono hN3 hK3le hz
  have hz' : z ∈ specDomain N (4 * ζ + 13) := ctl_specDomain_mono hN3 hK4le hz
  obtain ⟨hs64, hq1, hsq, ⟨hzre, hzim, hzle⟩, hρ⟩ := hpar q s z hqK' hz' hs1 hs2
  have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hs0 : 0 < s := by linarith
  have hq0 : 0 < q := by linarith
  have hT2 := h2 N hN2 L q s z hL hq hqK2 hz2 hs1 hs2
  have hT3 := h3 N hN3' L q s z hL hq hqK3 hz3 hs1 hs2
  have hmsc := ctl_msc_bounds hzre hzim hzle
  have hs164 : s⁻¹ ≤ 1 / 64 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) hs64
  have hs2c : 2 / c' ≤ s := by
    have h3' : 0 ≤ 2 / c' := by positivity
    nlinarith [mul_nonneg hlog0 h3']
  have hnull : L.law {ω | ¬ ∀ i : Fin N, |symOfEntries ω i i| ≤ q⁻¹} = 0 :=
    ae_iff.mp (ctl_ae_diag_entries hL.isProb hq)
  have hsub : {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
      25 / 8 * (9 / 4 + C3 + C2 / 2) * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) <
        ⨆ i, ‖resolventC (symOfEntries ω) z i i - stieltjesM (symOfEntries ω) z‖} ⊆
      ({ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        C2 * (1 / q + s ^ 2 * psiCtrl (symOfEntries ω) z) < lamO (symOfEntries ω) z} ∪
      {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        C3 * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) <
          ⨆ i, ‖zFluct (symOfEntries ω) z i‖}) ∪
      {ω | ¬ ∀ i : Fin N, |symOfEntries ω i i| ≤ q⁻¹} := by
    rintro ω ⟨hΩ, hbig⟩
    by_contra hcon
    rw [Set.mem_union, Set.mem_union, not_or, not_or] at hcon
    obtain ⟨⟨hn2, hn3⟩, hnn⟩ := hcon
    have hΛ : lamO (symOfEntries ω) z ≤ C2 * (1 / q + s ^ 2 * psiCtrl (symOfEntries ω) z) :=
      not_lt.mp fun hlt => hn2 ⟨hΩ, hlt⟩
    have hZ : (⨆ i, ‖zFluct (symOfEntries ω) z i‖) ≤
        C3 * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) :=
      not_lt.mp fun hlt => hn3 ⟨hΩ, hlt⟩
    have hdiag : ∀ i : Fin N, |symOfEntries ω i i| ≤ q⁻¹ := by
      by_contra hh
      exact hnn hh
    have hΩ' : CtlOmega (symOfEntries ω) z :=
      ⟨symOfEntries_isHermitian ω, hzim, hmsc.1, hmsc.2, by linarith⟩
    have hNinv : (N : ℝ)⁻¹ ≤ 1 / q := by
      have h1 := ctl_inv_le hL hq (by omega : 2 ≤ N)
      have h2 : q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq1
      have h3 : (q⁻¹) ^ 2 ≤ q⁻¹ := by nlinarith [inv_nonneg.2 hq0.le]
      rw [one_div]
      linarith
    have hbd := ctl_diag_close hNpos hΩ' hC2 hq0 (by linarith) hdiag hNinv hΛ hZ
    exact absurd hbig (not_lt.mpr (by linarith [hbd]))
  calc L.law {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        25 / 8 * (9 / 4 + C3 + C2 / 2) * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) <
          ⨆ i, ‖resolventC (symOfEntries ω) z i i - stieltjesM (symOfEntries ω) z‖}
      ≤ L.law (({ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        C2 * (1 / q + s ^ 2 * psiCtrl (symOfEntries ω) z) < lamO (symOfEntries ω) z} ∪
      {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        C3 * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) <
          ⨆ i, ‖zFluct (symOfEntries ω) z i‖}) ∪
      {ω | ¬ ∀ i : Fin N, |symOfEntries ω i i| ≤ q⁻¹}) := measure_mono hsub
    _ ≤ L.law ({ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        C2 * (1 / q + s ^ 2 * psiCtrl (symOfEntries ω) z) < lamO (symOfEntries ω) z} ∪
      {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        C3 * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) <
          ⨆ i, ‖zFluct (symOfEntries ω) z i‖}) +
      L.law {ω | ¬ ∀ i : Fin N, |symOfEntries ω i i| ≤ q⁻¹} := measure_union_le _ _
    _ ≤ (L.law {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        C2 * (1 / q + s ^ 2 * psiCtrl (symOfEntries ω) z) < lamO (symOfEntries ω) z} +
      L.law {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        C3 * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) <
          ⨆ i, ‖zFluct (symOfEntries ω) z i‖}) +
      L.law {ω | ¬ ∀ i : Fin N, |symOfEntries ω i i| ≤ q⁻¹} :=
        add_le_add (measure_union_le _ _) le_rfl
    _ ≤ (ENNReal.ofReal (Real.exp (-c2 * s)) + ENNReal.ofReal (Real.exp (-c3 * s))) + 0 := by
        rw [hnull]
        exact add_le_add (add_le_add hT2 hT3) le_rfl
    _ = ENNReal.ofReal (Real.exp (-c2 * s) + Real.exp (-c3 * s)) := by
        rw [add_zero, ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
    _ ≤ ENNReal.ofReal (Real.exp (-(c' / 2) * s)) := by
        refine ENNReal.ofReal_le_ofReal (add_le_exp_neg_half_mul_of_le_exp hc'0 hs2c ?_ ?_)
        · apply Real.exp_le_exp.mpr
          nlinarith [min_le_left c2 c3]
        · apply Real.exp_le_exp.mpr
          nlinarith [min_le_right c2 c3]

/-- (3.32) of [15] at a fixed `z`, on `Ω(z)` of (3.25) of [15]. -/
theorem lamO_le_on_omega {ζ C0 : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) :
    ∃ K > 0, ∃ C > 0, ∃ c > 0, ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (L : EntryLaws N) (q : ℝ) (z : ℂ),
      L.IsGenWigner C0 → L.BoundedSupportAS q → phi N ^ K ≤ q → z ∈ specDomain N K →
      L.law {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ (phi N ^ ζ)⁻¹ ∧
        C * (1 / q + phi N ^ (2 * ζ) * psiCtrl (symOfEntries ω) z) <
          lamO (symOfEntries ω) z} ≤ ENNReal.ofReal (Real.exp (-c * phi N ^ ζ)) := by
  obtain ⟨K, hK, C, hC, c, hc, N0, h⟩ := lamO_le_on_omega_level hζ hC0
  refine ⟨K, hK, C, hC, c, hc, max N0 3, fun N hN L q z hL hq hqK hz => ?_⟩
  have hN3 : 3 ≤ N := le_of_max_le_right hN
  have e2 : phi N ^ (2 * ζ) = (phi N ^ ζ) ^ 2 := (ctl_rpow_sq (ctl_phi_pos hN3) ζ).symm
  rw [e2]
  exact h N (le_of_max_le_left hN) L q (phi N ^ ζ) z hL hq hqK hz le_rfl
    (ctl_rpow_mono hN3 (by linarith))

/-! ### Compiled checks -/

/-- The matrix `(1 1; 1 -1)`. -/
private def ctlTestH : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, -1]

private lemma ctlTestH_isHermitian : ctlTestH.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ctlTestH]

/-- The identity (3.23) at `N = 2`, `H = (1 1; 1 -1)`, `z = i`, `i = 0`. -/
example : (resolventC ctlTestH Complex.I 0 0)⁻¹ = -Complex.I - msc Complex.I -
    ((stieltjesM ctlTestH Complex.I - msc Complex.I) - upsilon ctlTestH Complex.I 0) :=
  inv_resolventC_diag_eq ctlTestH_isHermitian (by simp) 0

/-- If `S` contains neither `f (-1)` nor `f 1`, the image of the Rademacher law under `f`
gives `S` measure `0`. -/
lemma rademacher_map_apply_eq_zero_of_not_mem (f : ℝ → ℝ) (hf : Measurable f) {S : Set ℝ}
    (hS : MeasurableSet S) (h1 : f (-1) ∉ S) (h2 : f 1 ∉ S) : (rademacher.map f) S = 0 := by
  rw [Measure.map_apply hf hS]
  have hT : MeasurableSet (f ⁻¹' S) := hf hS
  simp [rademacher, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hT, h1, h2]

/-- If `|c| ≤ q⁻¹`, the image of the Rademacher law under `x ↦ c * x` gives measure `0` to
`{x | q⁻¹ < |x|}`. -/
lemma rademacher_map_mul_tail_eq_zero {c q : ℝ} (hc : |c| ≤ q⁻¹) :
    (rademacher.map (fun x => c * x)) {x : ℝ | q⁻¹ < |x|} = 0 := by
  have hS : MeasurableSet {x : ℝ | q⁻¹ < |x|} := measurableSet_lt measurable_const measurable_abs
  refine rademacher_map_apply_eq_zero_of_not_mem _ (by fun_prop) hS ?_ ?_
  · simpa using hc
  · simpa using hc

/-- For `N ≥ 32` the Rademacher entry laws satisfy the almost-sure form of Definition 2.4 with
`q = N^{2/5}`: every entry is bounded by `q⁻¹` almost surely, because the largest amplitude is
`(2/N)^{1/2} ≤ N^{-2/5}`. -/
lemma radLaws_boundedSupportAS {N : ℕ} (hN : 32 ≤ N) :
    (radLaws N).BoundedSupportAS ((N : ℝ) ^ (2 / 5 : ℝ)) := by
  have hx : (32 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hq2 := sqrt_two_div_le hx
  have hq1 : Real.sqrt (1 / (N : ℝ)) ≤ ((N : ℝ) ^ (2 / 5 : ℝ))⁻¹ :=
    (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hN0.le)).trans hq2
  have e1 : (Real.sqrt N)⁻¹ = Real.sqrt (1 / (N : ℝ)) := by
    rw [one_div, Real.sqrt_inv]
  have e2 : (Real.sqrt N)⁻¹ * Real.sqrt 2 = Real.sqrt (2 / (N : ℝ)) := by
    rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  refine ⟨fun i => ?_, fun p => ?_⟩
  · change ((rademacher.map (fun x => Real.sqrt 2 * x)).map
      (fun x => (Real.sqrt N)⁻¹ * x)) _ = 0
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have hcomp : ((fun x : ℝ => (Real.sqrt N)⁻¹ * x) ∘ fun x : ℝ => Real.sqrt 2 * x) =
        fun x => ((Real.sqrt N)⁻¹ * Real.sqrt 2) * x := by
      funext x
      simp only [Function.comp]
      ring
    rw [hcomp]
    refine rademacher_map_mul_tail_eq_zero ?_
    rw [abs_of_nonneg (by positivity), e2]
    exact hq2
  · change (rademacher.map (fun x => (Real.sqrt N)⁻¹ * x)) _ = 0
    refine rademacher_map_mul_tail_eq_zero ?_
    rw [abs_of_pos (inv_pos.mpr hsq), e1]
    exact hq1

/-- The smallest admissible size `N = 32`, where the diagonal amplitude `(2/32)^{1/2} = 1/4`
equals `32^{-2/5}`. -/
example : (radLaws 32).BoundedSupportAS (((32 : ℕ) : ℝ) ^ (2 / 5 : ℝ)) :=
  radLaws_boundedSupportAS le_rfl

/-- For all large `N` the hypotheses of (3.32), (3.33), (3.36) hold together for the Rademacher
entry laws, `q = N^{2/5}`, `z = i` and `s = φ^{ζ+1}`. -/
private lemma ctl_rad_instance (K ζ : ℝ) : ∀ᶠ N : ℕ in atTop,
    (radLaws N).IsGenWigner 1 ∧ (radLaws N).BoundedSupportAS ((N : ℝ) ^ (2 / 5 : ℝ)) ∧
    phi N ^ K ≤ (N : ℝ) ^ (2 / 5 : ℝ) ∧ (⟨0, 1⟩ : ℂ) ∈ specDomain N K ∧
    phi N ^ ζ ≤ phi N ^ (ζ + 1) ∧ phi N ^ (ζ + 1) ≤ phi N ^ (ζ + 3) := by
  filter_upwards [phi_rpow_le_rpow K (by norm_num : (0 : ℝ) < 2 / 5), eventually_ge_atTop 32]
    with N h1 h2
  have hN : (32 : ℝ) ≤ N := by exact_mod_cast h2
  have hlt : (N : ℝ) ^ (2 / 5 : ℝ) < N := by
    calc (N : ℝ) ^ (2 / 5 : ℝ) < (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
      _ = N := Real.rpow_one _
  refine ⟨radLaws_isGenWigner (by omega), radLaws_boundedSupportAS h2, h1,
    ⟨by simp, ?_, by simp⟩, ctl_rpow_mono (by omega) (by linarith),
    ctl_rpow_mono (by omega) (by linarith)⟩
  change phi N ^ K / N < 1
  rw [div_lt_one (by linarith)]
  linarith

/-- (3.32) at a level: the estimate applies to the Rademacher laws for all large `N`. -/
example {ζ : ℝ} (hζ : 0 < ζ) : ∃ K > (0 : ℝ), ∃ C > 0, ∃ c > 0, ∀ᶠ N : ℕ in atTop,
    (radLaws N).law {ω | lamD (symOfEntries ω) ⟨0, 1⟩ + lamO (symOfEntries ω) ⟨0, 1⟩ ≤
        (phi N ^ (ζ + 1))⁻¹ ∧
      C * (1 / ((N : ℝ) ^ (2 / 5 : ℝ)) + (phi N ^ (ζ + 1)) ^ 2 *
        psiCtrl (symOfEntries ω) ⟨0, 1⟩) < lamO (symOfEntries ω) ⟨0, 1⟩} ≤
      ENNReal.ofReal (Real.exp (-c * phi N ^ (ζ + 1))) := by
  obtain ⟨K, hK, C, hC, c, hc, N0, h⟩ := lamO_le_on_omega_level hζ (zero_le_one : (0 : ℝ) ≤ 1)
  refine ⟨K, hK, C, hC, c, hc, ?_⟩
  filter_upwards [ctl_rad_instance K ζ, eventually_ge_atTop N0] with N hi hN
  exact h N hN (radLaws N) _ _ _ hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2

/-- (3.33) at a level: the estimate applies to the Rademacher laws for all large `N`. -/
example {ζ : ℝ} (hζ : 0 < ζ) : ∃ K > (0 : ℝ), ∃ C > 0, ∃ c > 0, ∀ᶠ N : ℕ in atTop,
    (radLaws N).law {ω | lamD (symOfEntries ω) ⟨0, 1⟩ + lamO (symOfEntries ω) ⟨0, 1⟩ ≤
        (phi N ^ (ζ + 1))⁻¹ ∧
      C * (phi N ^ (ζ + 1) / ((N : ℝ) ^ (2 / 5 : ℝ)) + (phi N ^ (ζ + 1)) ^ 2 *
        psiCtrl (symOfEntries ω) ⟨0, 1⟩) < ⨆ i, ‖zFluct (symOfEntries ω) ⟨0, 1⟩ i‖} ≤
      ENNReal.ofReal (Real.exp (-c * phi N ^ (ζ + 1))) := by
  obtain ⟨K, hK, C, hC, c, hc, N0, h⟩ := norm_zFluct_le_on_omega hζ (zero_le_one : (0 : ℝ) ≤ 1)
  refine ⟨K, hK, C, hC, c, hc, ?_⟩
  filter_upwards [ctl_rad_instance K ζ, eventually_ge_atTop N0] with N hi hN
  exact h N hN (radLaws N) _ _ _ hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2

/-- (3.36) at a level: the estimate applies to the Rademacher laws for all large `N`. -/
example {ζ : ℝ} (hζ : 0 < ζ) : ∃ K > (0 : ℝ), ∃ C > 0, ∃ c > 0, ∀ᶠ N : ℕ in atTop,
    (radLaws N).law {ω | lamD (symOfEntries ω) ⟨0, 1⟩ + lamO (symOfEntries ω) ⟨0, 1⟩ ≤
        (phi N ^ (ζ + 1))⁻¹ ∧
      C * (phi N ^ (ζ + 1) / ((N : ℝ) ^ (2 / 5 : ℝ)) + (phi N ^ (ζ + 1)) ^ 2 *
        psiCtrl (symOfEntries ω) ⟨0, 1⟩) <
        ⨆ i, ‖resolventC (symOfEntries ω) ⟨0, 1⟩ i i - stieltjesM (symOfEntries ω) ⟨0, 1⟩‖} ≤
      ENNReal.ofReal (Real.exp (-c * phi N ^ (ζ + 1))) := by
  obtain ⟨K, hK, C, hC, c, hc, N0, h⟩ :=
    norm_resolventC_diag_sub_le_on_omega hζ (zero_le_one : (0 : ℝ) ≤ 1)
  refine ⟨K, hK, C, hC, c, hc, ?_⟩
  filter_upwards [ctl_rad_instance K ζ, eventually_ge_atTop N0] with N hi hN
  exact h N hN (radLaws N) _ _ _ hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2

/-- (3.32) at a fixed `z`: the estimate applies to the Rademacher laws for all large `N`. -/
example {ζ : ℝ} (hζ : 0 < ζ) : ∃ K > (0 : ℝ), ∃ C > 0, ∃ c > 0, ∀ᶠ N : ℕ in atTop,
    (radLaws N).law {ω | lamD (symOfEntries ω) ⟨0, 1⟩ + lamO (symOfEntries ω) ⟨0, 1⟩ ≤
        (phi N ^ ζ)⁻¹ ∧
      C * (1 / ((N : ℝ) ^ (2 / 5 : ℝ)) + phi N ^ (2 * ζ) * psiCtrl (symOfEntries ω) ⟨0, 1⟩) <
        lamO (symOfEntries ω) ⟨0, 1⟩} ≤ ENNReal.ofReal (Real.exp (-c * phi N ^ ζ)) := by
  obtain ⟨K, hK, C, hC, c, hc, N0, h⟩ := lamO_le_on_omega hζ (zero_le_one : (0 : ℝ) ≤ 1)
  refine ⟨K, hK, C, hC, c, hc, ?_⟩
  filter_upwards [ctl_rad_instance K ζ, eventually_ge_atTop N0] with N hi hN
  exact h N hN (radLaws N) _ _ hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1

#print axioms inv_resolventC_diag_eq
#print axioms lamO_le_on_omega_level
#print axioms norm_zFluct_le_on_omega
#print axioms norm_resolventC_diag_sub_le_on_omega
#print axioms lamO_le_on_omega

end WEdgeNS
