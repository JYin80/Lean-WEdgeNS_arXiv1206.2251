import WEdgeNS.Resolvent.Basic

/-!
# Minors of a symmetric matrix and their resolvents
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- The matrix with the rows and columns in `T` set to zero (the minor `H^{(T)}` of [15],
Definition 3.3, in the `N × N` convention of Remark 5.4 of [15]). -/
def zeroRC {N : ℕ} (T : Finset (Fin N)) (H : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i ∈ T ∨ j ∈ T then 0 else H i j

theorem zeroRC_isHermitian {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    (T : Finset (Fin N)) : (zeroRC T H).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  have h := hH.apply i j
  simp only [star_trivial] at h ⊢
  simp only [zeroRC, or_comm, h]

/-- `(H^{(V)})^{(U)} = H^{(U ∪ V)}`. -/
theorem zeroRC_zeroRC {N : ℕ} (U V : Finset (Fin N)) (H : Matrix (Fin N) (Fin N) ℝ) :
    zeroRC U (zeroRC V H) = zeroRC (U ∪ V) H := by
  funext i j
  simp only [zeroRC, Finset.mem_union]
  by_cases h : i ∈ U ∨ j ∈ U <;> by_cases h' : i ∈ V ∨ j ∈ V <;> simp_all
  tauto

/-- The complex matrix `H - z`, whose inverse is `resolventC H z`. -/
private def shiftC {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  H.map (fun x : ℝ => (x : ℂ)) - z • (1 : Matrix (Fin N) (Fin N) ℂ)

/-- Entries of `H - z`. -/
private lemma shiftC_apply {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (a b : Fin N) :
    shiftC H z a b = (H a b : ℂ) - if a = b then z else 0 := by
  by_cases h : a = b <;> simp [shiftC, h]

/-- For `0 < Im z` no eigenvalue of `H` equals `z`. -/
private lemma ne_eigenvalue {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (α : Fin N) : (hH.eigenvalues α : ℂ) ≠ z := by
  intro h
  have := congrArg Complex.im h
  rw [Complex.ofReal_im] at this
  linarith

/-- `(H - z) G = 1` for `0 < Im z`. -/
private lemma shiftC_mul_resolventC {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) : shiftC H z * resolventC H z = 1 :=
  resolventC_mul_eq_one hH (ne_eigenvalue hH hz)

/-- `G (H - z) = 1` for `0 < Im z`. -/
private lemma resolventC_mul_shiftC {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) : resolventC H z * shiftC H z = 1 :=
  mul_eq_one_comm.mp (shiftC_mul_resolventC hH hz)

/-- `G` is symmetric for a real symmetric `H`. -/
private lemma resolventC_symm {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (i j : Fin N) : resolventC H z i j = resolventC H z j i := by
  rw [resolventC_apply_eq_sum hH (ne_eigenvalue hH hz) i j,
    resolventC_apply_eq_sum hH (ne_eigenvalue hH hz) j i]
  exact Finset.sum_congr rfl fun α _ => by rw [mul_comm (hH.eigenvectorBasis α i)]

/-- Rows of `G^{(T)}` indexed by `T`. -/
private lemma resolventC_zeroRC_of_mem {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {T : Finset (Fin N)} {z : ℂ} (hz : 0 < z.im) {i : Fin N} (hi : i ∈ T)
    (j : Fin N) : resolventC (zeroRC T H) z i j = if i = j then -z⁻¹ else 0 := by
  have hH' := zeroRC_isHermitian hH T
  have h := congrFun (congrFun (shiftC_mul_resolventC hH' hz) i) j
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h
  · have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
    simp only [shiftC_apply, zeroRC, hi, true_or, ite_true, Matrix.one_apply, Complex.ofReal_zero,
      zero_sub] at h
    by_cases hij : i = j
    · simp only [hij, ↓reduceIte] at h ⊢
      field_simp
      linear_combination -h
    · simp only [hij, ↓reduceIte] at h ⊢
      rcases mul_eq_zero.mp h with h0 | h0
      · exact absurd (neg_eq_zero.mp h0) hz0
      · exact h0
  · intro c _ hc
    have hic : i ≠ c := Ne.symm hc
    simp [shiftC_apply, zeroRC, hi, hic]
  · simp

/-- Resolvent identity for the minor at one index `k`, in row form: for `b ≠ k`,
`G_ab - G^{(k)}_ab = -G_ak Σ_d H_kd G^{(k)}_db`. -/
private lemma resolventC_sub_zeroRC_single {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (k a b : Fin N) (hb : b ≠ k) :
    resolventC H z a b - resolventC (zeroRC {k} H) z a b =
      -(resolventC H z a k * ∑ d, (H k d : ℂ) * resolventC (zeroRC {k} H) z d b) := by
  have hH' := zeroRC_isHermitian hH {k}
  have key : resolventC H z - resolventC (zeroRC {k} H) z =
      resolventC H z * (shiftC (zeroRC {k} H) z - shiftC H z) * resolventC (zeroRC {k} H) z := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc (resolventC H z)
      (shiftC (zeroRC {k} H) z), shiftC_mul_resolventC hH' hz,
      resolventC_mul_shiftC hH hz]
    simp
  have hk0 : resolventC (zeroRC {k} H) z k b = 0 := by
    rw [resolventC_zeroRC_of_mem hH hz (Finset.mem_singleton_self k) b]
    simp [Ne.symm hb]
  have hD : ∀ c d, (shiftC (zeroRC {k} H) z - shiftC H z) c d =
      if c = k ∨ d = k then -(H c d : ℂ) else 0 := by
    intro c d
    simp only [Matrix.sub_apply, shiftC_apply, zeroRC, Finset.mem_singleton]
    by_cases h : c = k ∨ d = k
    · simp [h]
      ring
    · simp [h]
  have h := congrFun (congrFun key a) b
  rw [Matrix.sub_apply, Matrix.mul_apply] at h
  have hterm : ∀ d, (resolventC H z * (shiftC (zeroRC {k} H) z - shiftC H z)) a d *
      resolventC (zeroRC {k} H) z d b =
      -(resolventC H z a k * ((H k d : ℂ) * resolventC (zeroRC {k} H) z d b)) := by
    intro d
    rw [Matrix.mul_apply]
    by_cases hd : d = k
    · subst hd
      simp [hk0]
    · rw [Finset.sum_eq_single k]
      · simp [hD, hd, mul_assoc]
      · intro c _ hc
        simp [hD, hc, hd]
      · simp
  rw [h, Finset.sum_congr rfl fun d _ => hterm d, Finset.sum_neg_distrib, ← Finset.mul_sum]

/-- The Schur-complement identity in product form: `G_ii (H_ii - z - Z_ii) = 1`. -/
private lemma resolventC_diag_mul {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (i : Fin N) :
    resolventC H z i i * ((H i i : ℂ) - z - ∑ k, ∑ l,
      (if k = i ∨ l = i then 0 else (H i k : ℂ) * resolventC (zeroRC {i} H) z k l * H l i)) =
      1 := by
  have h1 := congrFun (congrFun (resolventC_mul_shiftC hH hz) i) i
  rw [Matrix.mul_apply] at h1
  simp only [shiftC_apply, Matrix.one_apply, ite_true] at h1
  have h0 : ∀ l, l ≠ i → resolventC (zeroRC {i} H) z i l = 0 := by
    intro l hl
    rw [resolventC_zeroRC_of_mem hH hz (Finset.mem_singleton_self i) l]
    simp [Ne.symm hl]
  have hp : ∀ l, resolventC H z i l * ((H l i : ℂ) - if l = i then z else 0) =
      (if l = i then resolventC H z i i * ((H i i : ℂ) - z) else 0) -
        resolventC H z i i * (if l = i then 0 else
          (∑ k, (H i k : ℂ) * resolventC (zeroRC {i} H) z k l) * H l i) := by
    intro l
    by_cases hl : l = i
    · subst hl
      simp
    · have h2 := resolventC_sub_zeroRC_single hH hz i i l hl
      rw [h0 l hl, sub_zero] at h2
      simp only [hl, ↓reduceIte, h2]
      ring
  have hZ : ∑ k, ∑ l, (if k = i ∨ l = i then 0 else
      (H i k : ℂ) * resolventC (zeroRC {i} H) z k l * H l i) =
      ∑ l, (if l = i then 0 else
        (∑ k, (H i k : ℂ) * resolventC (zeroRC {i} H) z k l) * H l i) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l = i
    · simp [hl]
    · simp only [hl, or_false, ↓reduceIte, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : k = i
      · subst hk
        simp [h0 l hl]
      · simp [hk]
  rw [hZ]
  simp only [hp, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at h1
  linear_combination h1

/-- The diagonal entries of `G` do not vanish for `0 < Im z`. -/
private lemma resolventC_diag_ne_zero {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (i : Fin N) : resolventC H z i i ≠ 0 := by
  intro h
  have := resolventC_diag_mul hH hz i
  rw [h, zero_mul] at this
  exact zero_ne_one this

/-- (3.12) of [15]. -/
theorem resolventC_eq_minor_add {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) {i j k : Fin N} (hi : i ≠ k) (hj : j ≠ k) :
    resolventC H z i j = resolventC (zeroRC {k} H) z i j +
      resolventC H z i k * resolventC H z k j / resolventC H z k k := by
  have _hi := hi
  have hk := resolventC_diag_ne_zero hH hz k
  have h1 := resolventC_sub_zeroRC_single hH hz k i j hj
  have h2 := resolventC_sub_zeroRC_single hH hz k k j hj
  have h0 : resolventC (zeroRC {k} H) z k j = 0 := by
    rw [resolventC_zeroRC_of_mem hH hz (Finset.mem_singleton_self k) j]
    simp [Ne.symm hj]
  rw [h0, sub_zero] at h2
  set S := ∑ d, (H k d : ℂ) * resolventC (zeroRC {k} H) z d j
  rw [h2, show resolventC H z i k * -(resolventC H z k k * S) / resolventC H z k k =
    -(resolventC H z i k * S) by field_simp]
  linear_combination h1

/-- (3.13) of [15], diagonal (Schur complement). -/
theorem resolventC_diag_eq_inv {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (i : Fin N) :
    resolventC H z i i = ((H i i : ℂ) - z - ∑ k, ∑ l,
      (if k = i ∨ l = i then 0 else (H i k : ℂ) * resolventC (zeroRC {i} H) z k l * H l i))⁻¹ := by
  exact eq_inv_of_mul_eq_one_left (resolventC_diag_mul hH hz i)

/-- (3.13) of [15], off-diagonal. -/
theorem resolventC_offDiag_eq {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) {i j : Fin N} (hij : i ≠ j) :
    resolventC H z i j = -resolventC H z i i * resolventC (zeroRC {i} H) z j j *
      ((H i j : ℂ) - ∑ k, ∑ l, (if k = i ∨ k = j ∨ l = i ∨ l = j then 0 else
        (H i k : ℂ) * resolventC (zeroRC {i, j} H) z k l * H l j)) := by
  have hH1 := zeroRC_isHermitian hH {i}
  have hH2 := zeroRC_isHermitian hH {i, j}
  have hHs : ∀ a b, H a b = H b a := fun a b => by simpa using (hH.apply a b).symm
  have hG'' : zeroRC {i, j} H = zeroRC {j} (zeroRC {i} H) := by
    rw [zeroRC_zeroRC, Finset.insert_eq, Finset.union_comm]
  -- vanishing of the off-diagonal entries of the rows and columns indexed by `{i, j}`
  have hz2 : ∀ a b, (a = i ∨ a = j) → a ≠ b →
      resolventC (zeroRC {i, j} H) z a b = 0 ∧ resolventC (zeroRC {i, j} H) z b a = 0 := by
    intro a b ha hab
    have hmem : a ∈ ({i, j} : Finset (Fin N)) := by
      rcases ha with rfl | rfl <;> simp
    have h := resolventC_zeroRC_of_mem hH hz hmem b
    simp only [hab, ↓reduceIte] at h
    exact ⟨h, by rw [resolventC_symm hH2 hz, h]⟩
  have hi0 : resolventC (zeroRC {i} H) z i j = 0 := by
    rw [resolventC_zeroRC_of_mem hH hz (Finset.mem_singleton_self i) j]
    simp [hij]
  have h1 := resolventC_sub_zeroRC_single hH hz i i j hij.symm
  rw [hi0, sub_zero] at h1
  have h2 : ∀ d, d ≠ j → resolventC (zeroRC {i} H) z d j =
      -(resolventC (zeroRC {i} H) z j j * ∑ e, (zeroRC {i} H j e : ℂ) *
        resolventC (zeroRC {i, j} H) z e d) := by
    intro d hd
    have h := resolventC_sub_zeroRC_single hH1 hz j j d hd
    rw [← hG'', (hz2 j d (Or.inr rfl) (Ne.symm hd)).1, sub_zero] at h
    rw [resolventC_symm hH1 hz d j, h]
  have hT : ∀ d e, (if d = j then 0 else (H i d : ℂ) *
        ((zeroRC {i} H j e : ℂ) * resolventC (zeroRC {i, j} H) z e d)) =
      (if d = i ∨ d = j ∨ e = i ∨ e = j then 0 else
        (H i d : ℂ) * resolventC (zeroRC {i, j} H) z d e * H e j) := by
    intro d e
    by_cases hd : d = j
    · simp [hd]
    by_cases he : e = j
    · subst he
      simp [hd, (hz2 e d (Or.inr rfl) (Ne.symm hd)).1]
    by_cases hei : e = i
    · subst hei
      simp [hd, zeroRC]
    by_cases hdi : d = i
    · subst hdi
      simp [hd, he, hei, (hz2 d e (Or.inl rfl) (Ne.symm hei)).2]
    · have hHje : zeroRC {i} H j e = H e j := by
        simp [zeroRC, hij.symm, hei, hHs j e]
      rw [hHje, resolventC_symm hH2 hz e d]
      simp [hd, hdi, he, hei]
      ring
  have hS : ∑ d, (H i d : ℂ) * resolventC (zeroRC {i} H) z d j =
      resolventC (zeroRC {i} H) z j j * ((H i j : ℂ) - ∑ k, ∑ l, (if k = i ∨ k = j ∨ l = i ∨ l = j
        then 0 else (H i k : ℂ) * resolventC (zeroRC {i, j} H) z k l * H l j)) := by
    have hp : ∀ d, (H i d : ℂ) * resolventC (zeroRC {i} H) z d j =
        (if d = j then (H i j : ℂ) * resolventC (zeroRC {i} H) z j j else 0) -
          resolventC (zeroRC {i} H) z j j * ∑ e, (if d = j then 0 else (H i d : ℂ) *
            ((zeroRC {i} H j e : ℂ) * resolventC (zeroRC {i, j} H) z e d)) := by
      intro d
      by_cases hd : d = j
      · subst hd
        simp
      · simp only [hd, ↓reduceIte, h2 d hd]
        rw [← Finset.mul_sum]
        ring
    have hsum : ∑ d, ∑ e, (if d = j then 0 else (H i d : ℂ) *
        ((zeroRC {i} H j e : ℂ) * resolventC (zeroRC {i, j} H) z e d)) =
        ∑ k, ∑ l, (if k = i ∨ k = j ∨ l = i ∨ l = j then 0 else
          (H i k : ℂ) * resolventC (zeroRC {i, j} H) z k l * H l j) :=
      Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => hT d e
    rw [Finset.sum_congr rfl fun d _ => hp d, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  rw [h1, hS]
  ring

/-- Lipschitz continuity of `G` in `z` ((3.56), (3.59) of [15]). -/
theorem norm_resolventC_apply_sub_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) (i j : Fin N) :
    ‖resolventC H z i j - resolventC H w i j‖ ≤ ‖z - w‖ / (z.im * w.im) := by
  have hGz := resolventC_mul_shiftC hH hz
  have hGw := shiftC_mul_resolventC hH hw
  have hsh : shiftC H w - shiftC H z = (z - w) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    unfold shiftC
    ext a b
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply]
    ring
  have key : resolventC H z - resolventC H w = (z - w) • (resolventC H z * resolventC H w) := by
    calc resolventC H z - resolventC H w
        = resolventC H z * (shiftC H w - shiftC H z) * resolventC H w := by
          rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc (resolventC H z) (shiftC H w), hGw,
            hGz]
          simp
      _ = (z - w) • (resolventC H z * resolventC H w) := by
          rw [hsh, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have hent : resolventC H z i j - resolventC H w i j =
      (z - w) * ∑ k, resolventC H z i k * resolventC H w k j := by
    have := congrFun (congrFun key i) j
    simpa [Matrix.mul_apply] using this
  have hIm : ∀ (u : ℂ) (a : Fin N), 0 < u.im →
      (resolventC H u a a).im / u.im ≤ (1 / u.im) / u.im := by
    intro u a hu
    gcongr
    exact ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans
      (norm_resolventC_apply_le hH hu a a)
  have hCS : (∑ k, ‖resolventC H z i k‖ * ‖resolventC H w k j‖) ^ 2 ≤ (1 / (z.im * w.im)) ^ 2 := by
    calc (∑ k, ‖resolventC H z i k‖ * ‖resolventC H w k j‖) ^ 2
        ≤ (∑ k, ‖resolventC H z i k‖ ^ 2) * ∑ k, ‖resolventC H w k j‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = ((resolventC H z i i).im / z.im) * ((resolventC H w j j).im / w.im) := by
          rw [sum_norm_sq_resolventC hH hz i, ← sum_norm_sq_resolventC hH hw j]
          congr 1
          exact Finset.sum_congr rfl fun k _ => by rw [resolventC_symm hH hw k j]
      _ ≤ ((1 / z.im) / z.im) * ((1 / w.im) / w.im) := by
          have h1 := hIm z i hz
          have h2 := hIm w j hw
          have h3 : 0 ≤ (resolventC H z i i).im / z.im := by
            rw [← sum_norm_sq_resolventC hH hz i]
            positivity
          have h4 : 0 ≤ (1 / z.im) / z.im := by positivity
          exact mul_le_mul h1 h2 (by
            rw [← sum_norm_sq_resolventC hH hw j]
            positivity) h4
      _ = (1 / (z.im * w.im)) ^ 2 := by field_simp
  have hS : ∑ k, ‖resolventC H z i k‖ * ‖resolventC H w k j‖ ≤ 1 / (z.im * w.im) :=
    (le_abs_self _).trans (abs_le_of_sq_le_sq hCS (by positivity))
  calc ‖resolventC H z i j - resolventC H w i j‖
      = ‖z - w‖ * ‖∑ k, resolventC H z i k * resolventC H w k j‖ := by
        rw [hent, norm_mul]
    _ ≤ ‖z - w‖ * ∑ k, ‖resolventC H z i k‖ * ‖resolventC H w k j‖ := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => (norm_mul _ _).le)
    _ ≤ ‖z - w‖ * (1 / (z.im * w.im)) := by gcongr
    _ = ‖z - w‖ / (z.im * w.im) := by rw [mul_one_div]

/-- (3.27) of [15] for the minors `H^{(T)}`. -/
theorem sum_norm_sq_resolventC_zeroRC {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (T : Finset (Fin N)) {z : ℂ} (hz : 0 < z.im) (i : Fin N) :
    ∑ j, ‖resolventC (zeroRC T H) z i j‖ ^ 2 = (resolventC (zeroRC T H) z i i).im / z.im := by
  exact sum_norm_sq_resolventC (zeroRC_isHermitian hH T) hz i

/-- Rows of `G^{(T)}` indexed by `T` in the `N × N` convention (Remark 5.4 of [15]). -/
theorem resolventC_zeroRC_apply_of_mem {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {T : Finset (Fin N)} {z : ℂ} (hz : 0 < z.im) {i : Fin N} (hi : i ∈ T)
    (j : Fin N) : resolventC (zeroRC T H) z i j = if i = j then -z⁻¹ else 0 := by
  exact resolventC_zeroRC_of_mem hH hz hi j

/-- `m^{(T)}` of (3.11) of [15] (normalisation `N⁻¹`, sum over `j ∉ T`). -/
def minorM {N : ℕ} (T : Finset (Fin N)) (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ j ∈ Tᶜ, resolventC (zeroRC T H) z j j

theorem minorM_empty {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    minorM ∅ H z = stieltjesM H z := by
  have h0 : zeroRC ∅ H = H := by
    funext i j
    simp [zeroRC]
  simp [minorM, stieltjesM, h0, Matrix.trace]

/-- (3.31) of [15], exact form (from (3.12)). -/
theorem minorM_insert_sub {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {T : Finset (Fin N)} {i : Fin N} (hi : i ∉ T) {z : ℂ} (hz : 0 < z.im) :
    minorM (insert i T) H z - minorM T H z =
      -((N : ℂ)⁻¹ * ∑ j, resolventC (zeroRC T H) z i j ^ 2 / resolventC (zeroRC T H) z i i) := by
  have hH' := zeroRC_isHermitian hH T
  have hgi := resolventC_diag_ne_zero hH' hz i
  have hz2 : zeroRC (insert i T) H = zeroRC {i} (zeroRC T H) := by
    rw [zeroRC_zeroRC, Finset.insert_eq]
  have hiTc : i ∈ Tᶜ := Finset.mem_compl.mpr hi
  have hG : ∀ j, j ≠ i → resolventC (zeroRC (insert i T) H) z j j =
      resolventC (zeroRC T H) z j j -
        resolventC (zeroRC T H) z i j ^ 2 / resolventC (zeroRC T H) z i i := by
    intro j hj
    have h := resolventC_eq_minor_add hH' hz hj hj
    rw [resolventC_symm hH' hz j i, ← hz2] at h
    linear_combination -h
  have hA : ∑ j ∈ (insert i T)ᶜ, resolventC (zeroRC (insert i T) H) z j j =
      ∑ j ∈ Tᶜ.erase i, (resolventC (zeroRC T H) z j j -
        resolventC (zeroRC T H) z i j ^ 2 / resolventC (zeroRC T H) z i i) := by
    rw [Finset.compl_insert]
    exact Finset.sum_congr rfl fun j hj => hG j (Finset.ne_of_mem_erase hj)
  have hB : ∑ j ∈ Tᶜ, resolventC (zeroRC T H) z j j =
      resolventC (zeroRC T H) z i i + ∑ j ∈ Tᶜ.erase i, resolventC (zeroRC T H) z j j :=
    (Finset.add_sum_erase _ _ hiTc).symm
  have hC : ∑ j, resolventC (zeroRC T H) z i j ^ 2 / resolventC (zeroRC T H) z i i =
      resolventC (zeroRC T H) z i i + ∑ j ∈ Tᶜ.erase i,
        resolventC (zeroRC T H) z i j ^ 2 / resolventC (zeroRC T H) z i i := by
    rw [← Finset.sum_subset (Finset.subset_univ Tᶜ), ← Finset.add_sum_erase _ _ hiTc]
    · congr 1
      field_simp
    · intro x _ hx
      have hxT : x ∈ T := by simpa using hx
      have hxi : x ≠ i := fun h => hi (h ▸ hxT)
      rw [resolventC_symm hH' hz i x, resolventC_zeroRC_of_mem hH hz hxT i]
      simp [hxi]
  unfold minorM
  rw [hA, hB, hC, Finset.sum_sub_distrib]
  ring

/-- (3.31) of [15], deterministic bound (no event `Ω(z)` needed). -/
theorem norm_minorM_insert_sub_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {T : Finset (Fin N)} {i : Fin N} (hi : i ∉ T) {z : ℂ} (hz : 0 < z.im) :
    ‖minorM (insert i T) H z - minorM T H z‖ ≤
        (resolventC (zeroRC T H) z i i).im / (N * z.im * ‖resolventC (zeroRC T H) z i i‖) ∧
      (resolventC (zeroRC T H) z i i).im / (N * z.im * ‖resolventC (zeroRC T H) z i i‖) ≤
        1 / (N * z.im) := by
  have hH' := zeroRC_isHermitian hH T
  have hg : resolventC (zeroRC T H) z i i ≠ 0 := resolventC_diag_ne_zero hH' hz i
  have hgpos : 0 < ‖resolventC (zeroRC T H) z i i‖ := norm_pos_iff.mpr hg
  have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos i
  have hIm : (resolventC (zeroRC T H) z i i).im ≤ ‖resolventC (zeroRC T H) z i i‖ :=
    (le_abs_self _).trans (Complex.abs_im_le_norm _)
  refine ⟨?_, ?_⟩
  · rw [minorM_insert_sub hH hi hz, norm_neg, norm_mul, norm_inv, Complex.norm_natCast]
    calc (N : ℝ)⁻¹ * ‖∑ j, resolventC (zeroRC T H) z i j ^ 2 / resolventC (zeroRC T H) z i i‖
        ≤ (N : ℝ)⁻¹ * ∑ j, ‖resolventC (zeroRC T H) z i j‖ ^ 2 /
            ‖resolventC (zeroRC T H) z i i‖ := by
          gcongr
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [norm_div, norm_pow]
      _ = (N : ℝ)⁻¹ * ((∑ j, ‖resolventC (zeroRC T H) z i j‖ ^ 2) /
            ‖resolventC (zeroRC T H) z i i‖) := by rw [Finset.sum_div]
      _ = (resolventC (zeroRC T H) z i i).im /
            (N * z.im * ‖resolventC (zeroRC T H) z i i‖) := by
          rw [sum_norm_sq_resolventC_zeroRC hH T hz i]
          field_simp
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hN hz]

/-! ### Compiled checks at a concrete nondegenerate point

`N = 3`, `H = [[1, 1, 0], [1, -1, 2], [0, 2, 0]]` (real symmetric), `z = i`, `w = 2i`; the
index sets are nonempty and proper, and for the off-diagonal identity the inner double sum
has the single term `k = l = 2`. -/

private def minorMatrix : Matrix (Fin 3) (Fin 3) ℝ := !![1, 1, 0; 1, -1, 2; 0, 2, 0]

private lemma minorMatrix_isHermitian : minorMatrix.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minorMatrix]

example : zeroRC {0} minorMatrix 0 1 = 0 ∧ zeroRC {0} minorMatrix 1 2 = 2 ∧
    zeroRC {0, 1} minorMatrix 2 2 = 0 := by
  simp [zeroRC, minorMatrix]

example : (zeroRC {0} minorMatrix).IsHermitian :=
  zeroRC_isHermitian minorMatrix_isHermitian {0}

example : zeroRC {1} (zeroRC {0} minorMatrix) = zeroRC ({1} ∪ {0}) minorMatrix :=
  zeroRC_zeroRC {1} {0} minorMatrix

example : resolventC minorMatrix Complex.I 1 2 =
    resolventC (zeroRC {0} minorMatrix) Complex.I 1 2 +
      resolventC minorMatrix Complex.I 1 0 * resolventC minorMatrix Complex.I 0 2 /
        resolventC minorMatrix Complex.I 0 0 :=
  resolventC_eq_minor_add minorMatrix_isHermitian (by simp) (i := 1) (j := 2) (k := 0)
    (by decide) (by decide)

example : resolventC minorMatrix Complex.I 0 0 = ((minorMatrix 0 0 : ℂ) - Complex.I - ∑ k, ∑ l,
      (if k = 0 ∨ l = 0 then 0 else (minorMatrix 0 k : ℂ) *
        resolventC (zeroRC {0} minorMatrix) Complex.I k l * minorMatrix l 0))⁻¹ :=
  resolventC_diag_eq_inv minorMatrix_isHermitian (by simp) 0

example : resolventC minorMatrix Complex.I 0 1 =
    -resolventC minorMatrix Complex.I 0 0 * resolventC (zeroRC {0} minorMatrix) Complex.I 1 1 *
      ((minorMatrix 0 1 : ℂ) - ∑ k, ∑ l, (if k = 0 ∨ k = 1 ∨ l = 0 ∨ l = 1 then 0 else
        (minorMatrix 0 k : ℂ) * resolventC (zeroRC {0, 1} minorMatrix) Complex.I k l *
          minorMatrix l 1)) :=
  resolventC_offDiag_eq minorMatrix_isHermitian (by simp) (by decide)

example : ‖resolventC minorMatrix Complex.I 0 1 - resolventC minorMatrix (2 * Complex.I) 0 1‖ ≤
    ‖Complex.I - 2 * Complex.I‖ / (Complex.I.im * (2 * Complex.I).im) :=
  norm_resolventC_apply_sub_le minorMatrix_isHermitian (by simp) (by simp) 0 1

example : ∑ j, ‖resolventC (zeroRC {0} minorMatrix) Complex.I 1 j‖ ^ 2 =
    (resolventC (zeroRC {0} minorMatrix) Complex.I 1 1).im / Complex.I.im :=
  sum_norm_sq_resolventC_zeroRC minorMatrix_isHermitian {0} (by simp) 1

example : resolventC (zeroRC {0, 1} minorMatrix) Complex.I 0 2 =
    if (0 : Fin 3) = 2 then -Complex.I⁻¹ else 0 :=
  resolventC_zeroRC_apply_of_mem minorMatrix_isHermitian (T := {0, 1}) (by simp) (i := 0)
    (by simp) 2

example : minorM ∅ minorMatrix Complex.I = stieltjesM minorMatrix Complex.I :=
  minorM_empty minorMatrix Complex.I

example : minorM {1, 0} minorMatrix Complex.I - minorM {0} minorMatrix Complex.I =
    -(((3 : ℕ) : ℂ)⁻¹ * ∑ j, resolventC (zeroRC {0} minorMatrix) Complex.I 1 j ^ 2 /
      resolventC (zeroRC {0} minorMatrix) Complex.I 1 1) :=
  minorM_insert_sub minorMatrix_isHermitian (T := {0}) (i := 1) (by decide) (by simp)

example : ‖minorM {1, 0} minorMatrix Complex.I - minorM {0} minorMatrix Complex.I‖ ≤
      (resolventC (zeroRC {0} minorMatrix) Complex.I 1 1).im /
        (((3 : ℕ) : ℝ) * Complex.I.im * ‖resolventC (zeroRC {0} minorMatrix) Complex.I 1 1‖) ∧
    (resolventC (zeroRC {0} minorMatrix) Complex.I 1 1).im /
        (((3 : ℕ) : ℝ) * Complex.I.im * ‖resolventC (zeroRC {0} minorMatrix) Complex.I 1 1‖) ≤
      1 / (((3 : ℕ) : ℝ) * Complex.I.im) :=
  norm_minorM_insert_sub_le minorMatrix_isHermitian (T := {0}) (i := 1) (by decide) (by simp)

#print axioms zeroRC
#print axioms zeroRC_isHermitian
#print axioms zeroRC_zeroRC
#print axioms resolventC_eq_minor_add
#print axioms resolventC_diag_eq_inv
#print axioms resolventC_offDiag_eq
#print axioms norm_resolventC_apply_sub_le
#print axioms sum_norm_sq_resolventC_zeroRC
#print axioms resolventC_zeroRC_apply_of_mem
#print axioms minorM
#print axioms minorM_empty
#print axioms minorM_insert_sub
#print axioms norm_minorM_insert_sub_le

end WEdgeNS
