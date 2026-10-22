import WEdgeNS.EdgeUniv.RBound
import WEdgeNS.EdgeUniv.WardReduction

/-!
# Expansion of the off-diagonal Ward sums in one entry
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- `k = |{i, j} ∩ {b, d}|` of [16] (6.57) for the off-diagonal entry `p = (b, d)` and `i ≠ j`: the
number of the indices `i`, `j` that lie in `{b, d}`. -/
def swapIdx {N : ℕ} (p : OffDiag N) (i j : Fin N) : ℕ :=
  (if i = p.1.1 ∨ i = p.1.2 then 1 else 0) + (if j = p.1.1 ∨ j = p.1.2 then 1 else 0)

/-- `(R I_e)^m R` with `R = G(H)(z)`: the coefficient of `(-v)^m` in the expansion (6.58) of `S`
around `R`, so that `R^{(m)} = (-v)^m (R I_e)^m R` in the notation of [16] (6.64). -/
def swapCoeff {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (e : Fin N ⊕ OffDiag N) (z : ℂ) (m : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (resolventC H z * (entryMat e).map (fun x : ℝ => (x : ℂ))) ^ m * resolventC H z

/-- [16] (6.58) with `V = v I_e` ((3.23)–(3.24)):
`S = Σ_{m ≤ 5} (-v)^m (R I_e)^m R + (-v)^6 (R I_e)^6 S`, `S = G(H)`, `R = G(Q)`. -/
theorem resolventC_eq_sum_swapCoeff {N : ℕ} (e : Fin N ⊕ OffDiag N) (ω : Entries N) {z : ℂ}
    (hz : 0 < z.im) :
    resolventC (symOfEntries ω) z =
      ∑ m ∈ Finset.range 6,
          (-(entryVal e ω : ℂ)) ^ m • swapCoeff (symOfEntries (zeroEntry e ω)) e z m +
        (-(entryVal e ω : ℂ)) ^ 6 • ((resolventC (symOfEntries (zeroEntry e ω)) z *
          (entryMat e).map (fun x : ℝ => (x : ℂ))) ^ 6 * resolventC (symOfEntries ω) z) := by
  have hQ := symOfEntries_isHermitian (zeroEntry e ω)
  have hsum := symOfEntries_eq_zeroEntry_add e ω
  have hV : (entryVal e ω • entryMat e).IsHermitian := by
    have h' : entryVal e ω • entryMat e = symOfEntries ω - symOfEntries (zeroEntry e ω) := by
      rw [hsum]; abel
    rw [h']; exact (symOfEntries_isHermitian ω).sub hQ
  have h := resolventC_expansion_right hQ hV hz 5
  rw [← hsum] at h
  have hmap : (entryVal e ω • entryMat e).map (fun x : ℝ => (x : ℂ)) =
      (entryVal e ω : ℂ) • (entryMat e).map (fun x : ℝ => (x : ℂ)) := by
    ext k l; simp
  conv_lhs => rw [h]
  simp_rw [hmap, Matrix.mul_smul, ← neg_smul, smul_pow, smul_mul_assoc, swapCoeff]

/-- The column weight: `1` on `{b, d}` and `P` elsewhere. -/
private def odeWt {N : ℕ} (p : OffDiag N) (P : ℝ) (i : Fin N) : ℝ :=
  if i = p.1.1 ∨ i = p.1.2 then 1 else P

private lemma ode_entryMat_mul_apply {N : ℕ} (p : OffDiag N) (M : Matrix (Fin N) (Fin N) ℂ)
    (y j : Fin N) :
    ((entryMat (Sum.inr p)).map (fun x : ℝ => (x : ℂ)) * M) y j =
      (if y = p.1.1 then M p.1.2 j else 0) + (if y = p.1.2 then M p.1.1 j else 0) := by
  have hne : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  rw [Matrix.mul_apply]
  simp only [Matrix.map_apply, entryMat, entryPairs, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq]
  by_cases h1 : y = p.1.1
  · subst h1
    have : ¬ p.1.1 = p.1.2 := hne
    simp [this, apply_ite Complex.ofReal, ite_mul]
  · by_cases h2 : y = p.1.2
    · subst h2
      simp [h1, apply_ite Complex.ofReal, ite_mul]
    · simp [h1, h2]

private lemma ode_mul_entryMat_mul_apply {N : ℕ} (p : OffDiag N) (A M : Matrix (Fin N) (Fin N) ℂ)
    (i j : Fin N) :
    ((A * (entryMat (Sum.inr p)).map (fun x : ℝ => (x : ℂ))) * M) i j =
      A i p.1.1 * M p.1.2 j + A i p.1.2 * M p.1.1 j := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp_rw [ode_entryMat_mul_apply, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private lemma ode_wt_mul {N : ℕ} (p : OffDiag N) (P : ℝ) (i j : Fin N) :
    odeWt p P i * odeWt p P j = P ^ (2 - swapIdx p i j) := by
  unfold odeWt swapIdx
  split_ifs <;> simp [sq]

private lemma ode_wt_nonneg {N : ℕ} (p : OffDiag N) {P : ℝ} (hP : 0 ≤ P) (i : Fin N) :
    0 ≤ odeWt p P i := by
  unfold odeWt; split_ifs <;> linarith

private lemma ode_le_wt_left {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} {P : ℝ}
    (hP : 0 ≤ P) (hA : ∀ k l, ‖A k l‖ ≤ 2) (hA' : ∀ k l, k ≠ l → ‖A k l‖ ≤ P)
    (p : OffDiag N) {x : Fin N} (hx : x = p.1.1 ∨ x = p.1.2) (i : Fin N) :
    ‖A i x‖ ≤ 2 * odeWt p P i := by
  unfold odeWt
  split_ifs with hi
  · linarith [hA i x]
  · have hne : i ≠ x := by rintro rfl; exact hi hx
    linarith [hA' i x hne]

private lemma ode_le_wt_right {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} {P : ℝ}
    (hP : 0 ≤ P) (hA : ∀ k l, ‖A k l‖ ≤ 2) (hA' : ∀ k l, k ≠ l → ‖A k l‖ ≤ P)
    (p : OffDiag N) {x : Fin N} (hx : x = p.1.1 ∨ x = p.1.2) (j : Fin N) :
    ‖A x j‖ ≤ 2 * odeWt p P j := by
  unfold odeWt
  split_ifs with hj
  · linarith [hA x j]
  · have hne : x ≠ j := by rintro rfl; exact hj hx
    linarith [hA' x j hne]

private lemma ode_step {N : ℕ} {A M : Matrix (Fin N) (Fin N) ℂ} {P c : ℝ}
    (hP : 0 ≤ P) (hA : ∀ k l, ‖A k l‖ ≤ 2) (hA' : ∀ k l, k ≠ l → ‖A k l‖ ≤ P)
    (p : OffDiag N)
    (hM : ∀ x, x = p.1.1 ∨ x = p.1.2 → ∀ j, ‖M x j‖ ≤ c * odeWt p P j) (i j : Fin N) :
    ‖((A * (entryMat (Sum.inr p)).map (fun x : ℝ => (x : ℂ))) * M) i j‖ ≤
      4 * c * (odeWt p P i * odeWt p P j) := by
  rw [ode_mul_entryMat_mul_apply]
  have h1 := ode_le_wt_left hP hA hA' p (Or.inl rfl) i
  have h2 := ode_le_wt_left hP hA hA' p (Or.inr rfl) i
  have h3 := hM p.1.2 (Or.inr rfl) j
  have h4 := hM p.1.1 (Or.inl rfl) j
  have hwi := ode_wt_nonneg p hP i
  have hwj := ode_wt_nonneg p hP j
  calc ‖A i p.1.1 * M p.1.2 j + A i p.1.2 * M p.1.1 j‖
      ≤ ‖A i p.1.1‖ * ‖M p.1.2 j‖ + ‖A i p.1.2‖ * ‖M p.1.1 j‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ (2 * odeWt p P i) * (c * odeWt p P j) + (2 * odeWt p P i) * (c * odeWt p P j) :=
        add_le_add (mul_le_mul h1 h3 (norm_nonneg _) (by positivity))
          (mul_le_mul h2 h4 (norm_nonneg _) (by positivity))
    _ = 4 * c * (odeWt p P i * odeWt p P j) := by ring

private lemma ode_pow_succ_le {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℂ} {P : ℝ}
    (hP : 0 ≤ P) (hA : ∀ k l, ‖A k l‖ ≤ 2) (hA' : ∀ k l, k ≠ l → ‖A k l‖ ≤ P)
    (hB : ∀ k l, ‖B k l‖ ≤ 2) (hB' : ∀ k l, k ≠ l → ‖B k l‖ ≤ P) (p : OffDiag N) (n : ℕ)
    (i j : Fin N) :
    ‖((A * (entryMat (Sum.inr p)).map (fun x : ℝ => (x : ℂ))) ^ (n + 1) * B) i j‖ ≤
      2 ^ (2 * n + 3) * (odeWt p P i * odeWt p P j) := by
  induction n generalizing i j with
  | zero =>
    rw [pow_one]
    have := ode_step hP hA hA' p (c := 2)
      (fun x hx j => ode_le_wt_right hP hB hB' p hx j) i j
    calc _ ≤ _ := this
      _ = _ := by ring
  | succ n ih =>
    rw [pow_succ', Matrix.mul_assoc]
    have hM : ∀ x, x = p.1.1 ∨ x = p.1.2 → ∀ j,
        ‖((A * (entryMat (Sum.inr p)).map (fun x : ℝ => (x : ℂ))) ^ (n + 1) * B) x j‖ ≤
          2 ^ (2 * n + 3) * odeWt p P j := by
      intro x hx j
      have hx1 : odeWt p P x = 1 := by simp [odeWt, hx]
      simpa [hx1] using ih x j
    calc _ ≤ _ := ode_step hP hA hA' p hM i j
      _ = _ := by ring

/-- [16] (6.59)–(6.60): if every entry of `A` and `B` is at most `2` and every off-diagonal entry at
most `P ≤ 2`, then for `m ≥ 1` every entry of `(A I_e)^m B`, `e = (b, d)`, is at most
`2^{2m+1} P^{2-k}`, `k = swapIdx p i j`. -/
theorem norm_mul_entryMat_pow_mul_apply_le {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℂ} {P : ℝ}
    (hP : 0 ≤ P) (hP2 : P ≤ 2) (hA : ∀ k l, ‖A k l‖ ≤ 2) (hA' : ∀ k l, k ≠ l → ‖A k l‖ ≤ P)
    (hB : ∀ k l, ‖B k l‖ ≤ 2) (hB' : ∀ k l, k ≠ l → ‖B k l‖ ≤ P) (p : OffDiag N) {m : ℕ}
    (hm : 1 ≤ m) (i j : Fin N) :
    ‖((A * (entryMat (Sum.inr p)).map (fun x : ℝ => (x : ℂ))) ^ m * B) i j‖ ≤
      2 ^ (2 * m + 1) * P ^ (2 - swapIdx p i j) := by
  have _ := hP2
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [← ode_wt_mul]
  calc _ ≤ _ := ode_pow_succ_le hP hA hA' hB hB' p n i j
    _ = _ := by ring_nf

/-- `x_k` of [16] (6.57) for the functional (6.56) written with `|G_ij|²`: the part of `offWardInt`
with `swapIdx p i j = k`. -/
def offWardIntPart {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (p : OffDiag N) (η E₁ E₂ : ℝ) (k : ℕ) :
    ℝ :=
  η * ∫ y in E₁..E₂, ∑ i, ∑ j,
    if i ≠ j ∧ swapIdx p i j = k then ‖resolventC H ⟨y, η⟩ i j‖ ^ 2 else 0

/-- The same split of `offWard` ((3.33), [16] (6.46)). -/
def offWardPart {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (p : OffDiag N) (z : ℂ) (k : ℕ) : ℝ :=
  z.im ^ 2 * ∑ i, ∑ j, if i ≠ j ∧ swapIdx p i j = k then ‖resolventC H z i j‖ ^ 2 else 0

/-- `y ↦ G(H)(y + iη)` is continuous for symmetric `H` and `η > 0`. -/
private lemma ode_continuous_resolventC {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {η : ℝ} (hη : 0 < η) :
    Continuous fun y : ℝ => resolventC H ⟨y, η⟩ := by
  have hz : Continuous fun y : ℝ => (⟨y, η⟩ : ℂ) := by
    have : (fun y : ℝ => (⟨y, η⟩ : ℂ)) = fun y : ℝ => (y : ℂ) + (η : ℂ) * Complex.I := by
      funext y; apply Complex.ext <;> simp
    rw [this]
    exact Complex.continuous_ofReal.add continuous_const
  have hM : Continuous (fun y : ℝ => H.map (fun x : ℝ => (x : ℂ)) -
      (⟨y, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) :=
    continuous_const.sub (hz.smul continuous_const)
  have hdet : ∀ y : ℝ, (H.map (fun x : ℝ => (x : ℂ)) -
      (⟨y, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).det ≠ 0 := by
    intro y
    have hne : ∀ α, (hH.eigenvalues α : ℂ) ≠ (⟨y, η⟩ : ℂ) := by
      intro α h
      have := congrArg Complex.im h
      simp at this
      linarith
    have h2 := congrArg Matrix.det (resolventC_mul_eq_one hH hne)
    rw [Matrix.det_mul, Matrix.det_one] at h2
    exact left_ne_zero_of_mul_eq_one h2
  have hinv : (fun y : ℝ => resolventC H ⟨y, η⟩) = fun y =>
      ((H.map (fun x : ℝ => (x : ℂ)) - (⟨y, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).det)⁻¹ •
      (H.map (fun x : ℝ => (x : ℂ)) - (⟨y, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).adjugate := by
    funext y
    unfold resolventC
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [hinv]
  exact (hM.matrix_det.inv₀ hdet).smul hM.matrix_adjugate

/-- `y ↦ ((G I_e)^m G)_ij(y + iη)` is continuous for symmetric `H` and `η > 0`. -/
private lemma ode_continuous_swapCoeff {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {η : ℝ} (hη : 0 < η) (e : Fin N ⊕ OffDiag N) (m : ℕ) (i j : Fin N) :
    Continuous fun y : ℝ => swapCoeff H e ⟨y, η⟩ m i j := by
  have hR := ode_continuous_resolventC hH hη
  have : Continuous fun y : ℝ => swapCoeff H e ⟨y, η⟩ m :=
    ((hR.mul continuous_const).pow m).mul hR
  exact this.matrix_elem i j

/-- `swapIdx p i j ∈ {0, 1, 2}`. -/
private lemma ode_swapIdx_le {N : ℕ} (p : OffDiag N) (i j : Fin N) : swapIdx p i j ≤ 2 := by
  unfold swapIdx; split_ifs <;> omega

/-- The split of [16] (6.57) for one pair: the summand of `i ≠ j` is the sum of its parts
`k = 0, 1, 2`. -/
private lemma ode_ite_eq_sum {M : Type*} [AddCommMonoid M] {N : ℕ} (p : OffDiag N) (i j : Fin N)
    (x : M) :
    (if i = j then 0 else x) =
      ∑ k ∈ Finset.range 3, if i ≠ j ∧ swapIdx p i j = k then x else 0 := by
  by_cases hij : i = j
  · simp [hij]
  · have hk : swapIdx p i j < 3 := Nat.lt_succ_of_le (ode_swapIdx_le p i j)
    simp [hij, Finset.sum_ite_eq, hk]

/-- The integrand of a part is continuous in `y`. -/
private lemma ode_continuous_part {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {η : ℝ} (hη : 0 < η) (p : OffDiag N) (k : ℕ) :
    Continuous fun y : ℝ => ∑ i, ∑ j,
      if i ≠ j ∧ swapIdx p i j = k then ‖resolventC H ⟨y, η⟩ i j‖ ^ 2 else 0 :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_if_const _ (fun _ => ((ode_continuous_resolventC hH hη).matrix_elem i j).norm.pow 2)
      fun _ => continuous_const

/-- [16] (6.57): `x = x_0 + x_1 + x_2`. -/
theorem offWardInt_eq_sum_part {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (hH : H.IsHermitian)
    (p : OffDiag N) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) :
    offWardInt H η E₁ E₂ = ∑ k ∈ Finset.range 3, offWardIntPart H p η E₁ E₂ k := by
  unfold offWardInt offWardIntPart
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum fun k _ =>
    (ode_continuous_part hH hη p k).intervalIntegrable _ _]
  congr 1
  refine intervalIntegral.integral_congr fun y _ => ?_
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => (ode_ite_eq_sum p i j _).symm

/--
`K^{(s,t)}_k(H) = η ∫_{E₁}^{E₂} Σ_{i ≠ j, swapIdx = k} [(R I_e)^s R]_ij conj [(R I_e)^t R]_ij dy`,
`R = G(H)(y + iη)`: [16] (6.66) for the functional (6.56) written with `|G_ij|²`, with the entry
factored out, `Q^{(s,t)}_k = (-v)^{s+t} K^{(s,t)}_k(Q)`. -/
def swapK {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (p : OffDiag N) (η E₁ E₂ : ℝ) (k s t : ℕ) : ℂ :=
  (η : ℂ) * ∫ y in E₁..E₂, ∑ i, ∑ j, if i ≠ j ∧ swapIdx p i j = k then
    swapCoeff H (Sum.inr p) ⟨y, η⟩ s i j * (starRingEnd ℂ) (swapCoeff H (Sum.inr p) ⟨y, η⟩ t i j)
    else 0

/-- The same coefficients for the functional `η² Σ_{i ≠ j} |G_ij(z)|²` of (3.20), [16] (6.46). -/
def swapKpt {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (p : OffDiag N) (z : ℂ) (k s t : ℕ) : ℂ :=
  (z.im : ℂ) ^ 2 * ∑ i, ∑ j, if i ≠ j ∧ swapIdx p i j = k then
    swapCoeff H (Sum.inr p) z s i j * (starRingEnd ℂ) (swapCoeff H (Sum.inr p) z t i j) else 0

/-! ### Deterministic bounds for one pair `(i, j)` -/

/-- (6.58) to any order `n`: `S = Σ_{m ≤ n} (-v)^m (R I_e)^m R + (-v)^{n+1} (R I_e)^{n+1} S`,
entrywise. -/
private lemma ode_apply_eq_sum {N : ℕ} (e : Fin N ⊕ OffDiag N) (ω : Entries N) {z : ℂ}
    (hz : 0 < z.im) (n : ℕ) (i j : Fin N) :
    resolventC (symOfEntries ω) z i j =
      ∑ m ∈ Finset.range (n + 1),
          (-(entryVal e ω : ℂ)) ^ m * swapCoeff (symOfEntries (zeroEntry e ω)) e z m i j +
        (-(entryVal e ω : ℂ)) ^ (n + 1) * (((resolventC (symOfEntries (zeroEntry e ω)) z *
          (entryMat e).map (fun x : ℝ => (x : ℂ))) ^ (n + 1) *
            resolventC (symOfEntries ω) z) i j) := by
  have hQ := symOfEntries_isHermitian (zeroEntry e ω)
  have hsum := symOfEntries_eq_zeroEntry_add e ω
  have hV : (entryVal e ω • entryMat e).IsHermitian := by
    have h' : entryVal e ω • entryMat e = symOfEntries ω - symOfEntries (zeroEntry e ω) := by
      rw [hsum]; abel
    rw [h']; exact (symOfEntries_isHermitian ω).sub hQ
  have h := resolventC_expansion_right hQ hV hz n
  rw [← hsum] at h
  have hmap : (entryVal e ω • entryMat e).map (fun x : ℝ => (x : ℂ)) =
      (entryVal e ω : ℂ) • (entryMat e).map (fun x : ℝ => (x : ℂ)) := by
    ext k l; simp
  have h2 : resolventC (symOfEntries ω) z =
      ∑ m ∈ Finset.range (n + 1),
          (-(entryVal e ω : ℂ)) ^ m • swapCoeff (symOfEntries (zeroEntry e ω)) e z m +
        (-(entryVal e ω : ℂ)) ^ (n + 1) • ((resolventC (symOfEntries (zeroEntry e ω)) z *
          (entryMat e).map (fun x : ℝ => (x : ℂ))) ^ (n + 1) * resolventC (symOfEntries ω) z) := by
    conv_lhs => rw [h]
    simp_rw [hmap, Matrix.mul_smul, ← neg_smul, smul_pow, smul_mul_assoc, swapCoeff]
  have h3 := congrFun (congrFun h2 i) j
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h3
  exact h3

/-- [16] (6.61) for one pair `i ≠ j`: if the entries of `S` and `R` are at most `2`, the
off-diagonal ones at most `P`, and `S = R + w (R I_e) S` with `|w| ≤ B`, then
`||S_ij|² - |R_ij|²| ≤ 16 B P^{3-k}`. -/
private lemma ode_pair_diff {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {S : Matrix (Fin N) (Fin N) ℂ}
    {p : OffDiag N} {v : ℝ} {z : ℂ} {P B : ℝ}
    (hexp : ∀ n i j, S i j = ∑ m ∈ Finset.range (n + 1),
        (-(v : ℂ)) ^ m * swapCoeff H (Sum.inr p) z m i j + (-(v : ℂ)) ^ (n + 1) *
          (((resolventC H z * (entryMat (Sum.inr p)).map (fun x : ℝ => (x : ℂ))) ^ (n + 1) *
            S) i j))
    (hv : |v| ≤ B) (hP : 0 ≤ P)
    (hS : ∀ k l, ‖S k l‖ ≤ 2) (hS' : ∀ k l, k ≠ l → ‖S k l‖ ≤ P)
    (hR : ∀ k l, ‖resolventC H z k l‖ ≤ 2) (hR' : ∀ k l, k ≠ l → ‖resolventC H z k l‖ ≤ P)
    {i j : Fin N} (hij : i ≠ j) :
    |‖S i j‖ ^ 2 - ‖resolventC H z i j‖ ^ 2| ≤ 16 * B * P ^ (3 - swapIdx p i j) := by
  have h0 := hexp 0 i j
  simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, swapCoeff] at h0
  have hD := ode_pow_succ_le hP hR hR' hS hS' p 0 i j
  simp only [zero_add, mul_zero] at hD
  rw [ode_wt_mul] at hD
  have hw : ‖-(v : ℂ)‖ = |v| := by rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have hdiff : ‖S i j - resolventC H z i j‖ ≤ B * (2 ^ 3 * P ^ (2 - swapIdx p i j)) := by
    rw [h0, add_sub_cancel_left, norm_mul, norm_pow, pow_one, hw]
    exact mul_le_mul hv hD (norm_nonneg _) ((abs_nonneg v).trans hv)
  have hsum : ‖S i j‖ + ‖resolventC H z i j‖ ≤ 2 * P := by
    linarith [hS' i j hij, hR' i j hij]
  have hk3 : P ^ (3 - swapIdx p i j) = P ^ (2 - swapIdx p i j) * P := by
    rw [← pow_succ]; congr 1; have := ode_swapIdx_le p i j; omega
  have hB : 0 ≤ B := (abs_nonneg v).trans hv
  calc |‖S i j‖ ^ 2 - ‖resolventC H z i j‖ ^ 2| =
        |‖S i j‖ - ‖resolventC H z i j‖| * (‖S i j‖ + ‖resolventC H z i j‖) := by
        rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖S i j‖ + ‖resolventC H z i j‖)]
        ring
    _ ≤ ‖S i j - resolventC H z i j‖ * (2 * P) :=
        mul_le_mul (abs_norm_sub_norm_le _ _) hsum (by positivity) (norm_nonneg _)
    _ ≤ B * (2 ^ 3 * P ^ (2 - swapIdx p i j)) * (2 * P) :=
        mul_le_mul_of_nonneg_right hdiff (by positivity)
    _ = 16 * B * P ^ (3 - swapIdx p i j) := by rw [hk3]; ring

/-- The algebra of [16] (6.62)–(6.69) for one pair: with `S_ij = a + ρ`,
`a = Σ_{m ≤ 4} w^m c_m`, `ρ = w^5 r`, `R_ij = c_0` and `conj w = w`,
`|S_ij|² - |R_ij|² - Σ_{1 ≤ s+t ≤ 4} w^{s+t} c_s conj c_t` is the sum of the terms with
`s + t ≥ 5` and of the terms containing `ρ`. -/
private lemma ode_rem_eq (c : ℕ → ℂ) (r w : ℂ) (hwc : (starRingEnd ℂ) w = w) :
    (((‖∑ m ∈ Finset.range 5, w ^ m * c m + w ^ 5 * r‖ ^ 2 - ‖c 0‖ ^ 2 : ℝ)) : ℂ) -
        ∑ s ∈ Finset.range 5, ∑ t ∈ Finset.range 5,
          (if 1 ≤ s + t ∧ s + t ≤ 4 then w ^ (s + t) else 0) * (c s * (starRingEnd ℂ) (c t)) =
      ∑ s ∈ Finset.range 5, ∑ t ∈ Finset.range 5,
          (if 5 ≤ s + t then w ^ (s + t) else 0) * (c s * (starRingEnd ℂ) (c t)) +
        ((∑ m ∈ Finset.range 5, w ^ m * c m) * (starRingEnd ℂ) (w ^ 5 * r) +
          w ^ 5 * r * (starRingEnd ℂ) (∑ m ∈ Finset.range 5, w ^ m * c m) +
          w ^ 5 * r * (starRingEnd ℂ) (w ^ 5 * r)) := by
  push_cast
  rw [← Complex.mul_conj', ← Complex.mul_conj']
  simp only [map_add, map_mul, map_pow, hwc, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

/-- The bound of [16] (6.69) for one pair: under the entry bounds `|c_m| ≤ 2^9 X` (`1 ≤ m ≤ 4`),
`|r| ≤ 2^11 X`, `|S_ij| ≤ P`, `|w| ≤ B ≤ 1`, `X² ≤ Y` and `P X ≤ Y`, the remainder of `ode_rem_eq`
is at most `2^25 B^5 Y`. -/
private lemma ode_pair_rem (c : ℕ → ℂ) (r w : ℂ) {B P X Y : ℝ} (hwc : (starRingEnd ℂ) w = w)
    (hw : ‖w‖ ≤ B) (hB1 : B ≤ 1) (hP : 0 ≤ P) (hX : 0 ≤ X)
    (hc : ∀ m, 1 ≤ m → m ≤ 4 → ‖c m‖ ≤ 2 ^ 9 * X) (hr : ‖r‖ ≤ 2 ^ 11 * X)
    (hS : ‖∑ m ∈ Finset.range 5, w ^ m * c m + w ^ 5 * r‖ ≤ P) (hXX : X * X ≤ Y)
    (hPX : P * X ≤ Y) :
    ‖(((‖∑ m ∈ Finset.range 5, w ^ m * c m + w ^ 5 * r‖ ^ 2 - ‖c 0‖ ^ 2 : ℝ)) : ℂ) -
        ∑ s ∈ Finset.range 5, ∑ t ∈ Finset.range 5,
          (if 1 ≤ s + t ∧ s + t ≤ 4 then w ^ (s + t) else 0) * (c s * (starRingEnd ℂ) (c t))‖ ≤
      2 ^ 25 * B ^ 5 * Y := by
  rw [ode_rem_eq c r w hwc]
  set a := ∑ m ∈ Finset.range 5, w ^ m * c m with ha
  set ρ := w ^ 5 * r with hρ
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hw
  have hY : 0 ≤ Y := (mul_nonneg hX hX).trans hXX
  have hB5 : B ^ 10 ≤ B ^ 5 := pow_le_pow_of_le_one hB0 hB1 (by norm_num)
  have hwn : ∀ n, ‖w‖ ^ n ≤ B ^ n := fun n => pow_le_pow_left₀ (norm_nonneg _) hw n
  have hρb : ‖ρ‖ ≤ B ^ 5 * (2 ^ 11 * X) := by
    rw [hρ, norm_mul, norm_pow]
    exact mul_le_mul (hwn 5) hr (norm_nonneg _) (by positivity)
  have hab : ‖a‖ ≤ P + ‖ρ‖ := by
    have : a = (a + ρ) - ρ := by ring
    rw [this]
    exact (norm_sub_le _ _).trans (by linarith)
  have hterm : ∀ s ∈ Finset.range 5, ∀ t ∈ Finset.range 5,
      ‖(if 5 ≤ s + t then w ^ (s + t) else 0) * (c s * (starRingEnd ℂ) (c t))‖ ≤
        2 ^ 18 * B ^ 5 * Y := by
    intro s hs t ht
    rw [Finset.mem_range] at hs ht
    split_ifs with h
    · have hs1 : 1 ≤ s := by omega
      have ht1 : 1 ≤ t := by omega
      rw [norm_mul, norm_mul, Complex.norm_conj, norm_pow]
      have h1 : ‖w‖ ^ (s + t) ≤ B ^ 5 :=
        (hwn _).trans (pow_le_pow_of_le_one hB0 hB1 h)
      have h2 := hc s hs1 (by omega)
      have h3 := hc t ht1 (by omega)
      calc ‖w‖ ^ (s + t) * (‖c s‖ * ‖c t‖) ≤ B ^ 5 * ((2 ^ 9 * X) * (2 ^ 9 * X)) :=
            mul_le_mul h1 (mul_le_mul h2 h3 (norm_nonneg _) (by positivity))
              (by positivity) (by positivity)
        _ = 2 ^ 18 * B ^ 5 * (X * X) := by ring
        _ ≤ 2 ^ 18 * B ^ 5 * Y := mul_le_mul_of_nonneg_left hXX (by positivity)
    · simp only [zero_mul, norm_zero]; positivity
  have hsum : ‖∑ s ∈ Finset.range 5, ∑ t ∈ Finset.range 5,
      (if 5 ≤ s + t then w ^ (s + t) else 0) * (c s * (starRingEnd ℂ) (c t))‖ ≤
        25 * (2 ^ 18 * B ^ 5 * Y) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun s hs => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun t ht => hterm s hs t ht)).trans ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    norm_num
    ring_nf
    exact le_rfl
  have hrest : ‖a * (starRingEnd ℂ) ρ + ρ * (starRingEnd ℂ) a + ρ * (starRingEnd ℂ) ρ‖ ≤
      2 * P * ‖ρ‖ + 3 * ‖ρ‖ ^ 2 := by
    refine (norm_add₃_le).trans ?_
    simp only [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg a, norm_nonneg ρ]
  have hρ1 : 2 * P * ‖ρ‖ ≤ 2 ^ 12 * B ^ 5 * Y := by
    calc 2 * P * ‖ρ‖ ≤ 2 * P * (B ^ 5 * (2 ^ 11 * X)) :=
          mul_le_mul_of_nonneg_left hρb (by positivity)
      _ = 2 ^ 12 * B ^ 5 * (P * X) := by ring
      _ ≤ 2 ^ 12 * B ^ 5 * Y := mul_le_mul_of_nonneg_left hPX (by positivity)
  have hρ2 : ‖ρ‖ ^ 2 ≤ 2 ^ 22 * B ^ 5 * Y := by
    calc ‖ρ‖ ^ 2 ≤ (B ^ 5 * (2 ^ 11 * X)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hρb 2
      _ = 2 ^ 22 * B ^ 10 * (X * X) := by ring
      _ ≤ 2 ^ 22 * B ^ 5 * Y :=
          mul_le_mul (mul_le_mul_of_nonneg_left hB5 (by positivity)) hXX (by positivity)
            (by positivity)
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ 25 * (2 ^ 18 * B ^ 5 * Y) + (2 * P * ‖ρ‖ + 3 * ‖ρ‖ ^ 2) := add_le_add hsum hrest
    _ ≤ 25 * (2 ^ 18 * B ^ 5 * Y) + (2 ^ 12 * B ^ 5 * Y + 3 * (2 ^ 22 * B ^ 5 * Y)) := by
        linarith
    _ ≤ 2 ^ 25 * B ^ 5 * Y := by nlinarith [pow_nonneg hB0 5]

/-- The summand of `swapK` and `swapKpt`: `Σ_{i ≠ j, swapIdx = k} c_s(i, j) conj c_t(i, j)` at
`z`. -/
private def odeInner {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (p : OffDiag N) (z : ℂ) (k s t : ℕ) :
    ℂ :=
  ∑ i, ∑ j, if i ≠ j ∧ swapIdx p i j = k then
    swapCoeff H (Sum.inr p) z s i j * (starRingEnd ℂ) (swapCoeff H (Sum.inr p) z t i j) else 0

/-- The main term of [16] (6.69) at one point `z`: `Σ_{k=0,1} Σ_{1 ≤ s+t ≤ 4} (-v)^{s+t}` times
`odeInner`. -/
private def odeMainPt {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (p : OffDiag N) (v : ℝ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range 2, ∑ s ∈ Finset.range 5, ∑ t ∈ Finset.range 5,
    (if 1 ≤ s + t ∧ s + t ≤ 4 then (-(v : ℂ)) ^ (s + t) else 0) * odeInner H p z k s t

/-- The contribution of the pair `(i, j)` to `odeMainPt`. -/
private def odePair {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (p : OffDiag N) (v : ℝ) (z : ℂ)
    (i j : Fin N) : ℂ :=
  ∑ k ∈ Finset.range 2, ∑ s ∈ Finset.range 5, ∑ t ∈ Finset.range 5,
    (if 1 ≤ s + t ∧ s + t ≤ 4 then (-(v : ℂ)) ^ (s + t) else 0) *
      (if i ≠ j ∧ swapIdx p i j = k then
        swapCoeff H (Sum.inr p) z s i j * (starRingEnd ℂ) (swapCoeff H (Sum.inr p) z t i j) else 0)

private lemma ode_mainPt_eq {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (p : OffDiag N) (v : ℝ)
    (z : ℂ) : odeMainPt H p v z = ∑ i, ∑ j, odePair H p v z i j := by
  unfold odeMainPt odePair odeInner
  simp_rw [Finset.mul_sum]
  simp only [Finset.sum_comm (s := Finset.range 5) (t := (Finset.univ : Finset (Fin N))),
    Finset.sum_comm (s := Finset.range 2) (t := (Finset.univ : Finset (Fin N)))]

/-- For `i ≠ j`, only the part `k = swapIdx p i j` contributes to `odePair`. -/
private lemma ode_pair_eq {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (p : OffDiag N) (v : ℝ)
    (z : ℂ) {i j : Fin N} (hij : i ≠ j) :
    odePair H p v z i j = if swapIdx p i j < 2 then
      ∑ s ∈ Finset.range 5, ∑ t ∈ Finset.range 5,
        (if 1 ≤ s + t ∧ s + t ≤ 4 then (-(v : ℂ)) ^ (s + t) else 0) *
          (swapCoeff H (Sum.inr p) z s i j * (starRingEnd ℂ) (swapCoeff H (Sum.inr p) z t i j))
      else 0 := by
  unfold odePair
  simp only [hij, ne_eq, not_false_eq_true, true_and, mul_ite, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_range]

/-- The bound for one pair `i ≠ j` in [16] (6.61) (`k = 2`) and (6.69) (`k = 0, 1`). -/
private def odeBeta (B P : ℝ) (k : ℕ) : ℝ :=
  if k ≤ 1 then 2 ^ 25 * B ^ 5 * P ^ (3 - k) else 16 * B * P ^ (3 - k)

private lemma ode_beta_nonneg {B P : ℝ} (hB : 0 ≤ B) (hP : 0 ≤ P) (k : ℕ) : 0 ≤ odeBeta B P k := by
  unfold odeBeta; split_ifs <;> positivity

/-- [16] (6.69) for one pair `(i, j)`: the summand of `x_S - x_R` minus its main term is at most
`odeBeta B P k`, `k = swapIdx p i j`. -/
private lemma ode_pair_bound {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {S : Matrix (Fin N) (Fin N) ℂ}
    {p : OffDiag N} {v : ℝ} {z : ℂ} {P B : ℝ}
    (hexp : ∀ n i j, S i j = ∑ m ∈ Finset.range (n + 1),
        (-(v : ℂ)) ^ m * swapCoeff H (Sum.inr p) z m i j + (-(v : ℂ)) ^ (n + 1) *
          (((resolventC H z * (entryMat (Sum.inr p)).map (fun x : ℝ => (x : ℂ))) ^ (n + 1) *
            S) i j))
    (hv : |v| ≤ B) (hB1 : B ≤ 1) (hP : 0 ≤ P) (hP1 : P ≤ 1)
    (hS : ∀ k l, ‖S k l‖ ≤ 2) (hS' : ∀ k l, k ≠ l → ‖S k l‖ ≤ P)
    (hR : ∀ k l, ‖resolventC H z k l‖ ≤ 2) (hR' : ∀ k l, k ≠ l → ‖resolventC H z k l‖ ≤ P)
    (i j : Fin N) :
    ‖((((if i = j then 0 else ‖S i j‖ ^ 2) - (if i = j then 0 else ‖resolventC H z i j‖ ^ 2) : ℝ)) :
        ℂ) - odePair H p v z i j‖ ≤ if i = j then 0 else odeBeta B P (swapIdx p i j) := by
  by_cases hij : i = j
  · subst hij
    simp [odePair]
  have hk := ode_swapIdx_le p i j
  simp only [hij, ite_false]
  rw [ode_pair_eq H p v z hij]
  by_cases hk1 : swapIdx p i j ≤ 1
  · have hlt : swapIdx p i j < 2 := by omega
    simp only [hlt, ite_true, odeBeta, hk1]
    have hS4 := hexp 4 i j
    simp only [Nat.reduceAdd] at hS4
    have hR0 : resolventC H z i j = swapCoeff H (Sum.inr p) z 0 i j := by simp [swapCoeff]
    have hSP := hS' i j hij
    rw [hS4] at hSP
    rw [hS4, hR0]
    have hwc : (starRingEnd ℂ) (-(v : ℂ)) = -(v : ℂ) := by simp
    have hw : ‖-(v : ℂ)‖ ≤ B := by rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]; exact hv
    have hwt := ode_wt_mul p P i j
    refine ode_pair_rem (fun m => swapCoeff H (Sum.inr p) z m i j) _ (-(v : ℂ))
      (X := P ^ (2 - swapIdx p i j)) hwc hw hB1 hP (by positivity) ?_ ?_ hSP ?_ ?_
    · intro m hm1 hm4
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hm1
      have h := ode_pow_succ_le hP hR hR' hR hR' p n i j
      rw [hwt] at h
      calc ‖swapCoeff H (Sum.inr p) z (n + 1) i j‖ ≤ 2 ^ (2 * n + 3) * P ^ (2 - swapIdx p i j) := h
        _ ≤ 2 ^ 9 * P ^ (2 - swapIdx p i j) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega))
              (by positivity)
    · have h := ode_pow_succ_le hP hR hR' hS hS' p 4 i j
      rw [hwt] at h
      simpa using h
    · rw [← pow_add]
      exact pow_le_pow_of_le_one hP hP1 (by omega)
    · rw [← pow_succ']
      exact le_of_eq (by congr 1; omega)
  · have hlt : ¬ swapIdx p i j < 2 := by omega
    simp only [hlt, ite_false, odeBeta, hk1, sub_zero]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact ode_pair_diff hexp hv hP hS hS' hR hR' hij

/-! ### Counting the pairs `(i, j)` with `swapIdx p i j = k` -/

/-- The indicator of `{b, d}`. -/
private def odeInd {N : ℕ} (p : OffDiag N) (i : Fin N) : ℝ :=
  if i = p.1.1 ∨ i = p.1.2 then 1 else 0

private lemma ode_sum_ind_le {N : ℕ} (p : OffDiag N) : ∑ i, odeInd p i ≤ 2 := by
  calc ∑ i, odeInd p i ≤ ∑ i, ((if i = p.1.1 then (1 : ℝ) else 0) + (if i = p.1.2 then 1 else 0)) :=
        Finset.sum_le_sum fun i _ => by
          unfold odeInd
          split_ifs <;> first | (exfalso; tauto) | norm_num
    _ = 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
        simp only [Finset.mem_univ, ite_true]
        norm_num

private lemma ode_sum_ind_nonneg {N : ℕ} (p : OffDiag N) : 0 ≤ ∑ i, odeInd p i :=
  Finset.sum_nonneg fun i _ => by unfold odeInd; split_ifs <;> norm_num

/-- `|{(i, j) : i ≠ j, swapIdx p i j = k}| ≤ 4 N^{2-k}` (`k ≤ 2`), with a weight `c ≥ 0`. -/
private lemma ode_count {N : ℕ} (p : OffDiag N) {k : ℕ} (hk : k ≤ 2) {c : ℝ} (hc : 0 ≤ c) :
    ∑ i, ∑ j, (if i ≠ j ∧ swapIdx p i j = k then c else 0) ≤ 4 * (N : ℝ) ^ (2 - k) * c := by
  have hrw : ∑ i, ∑ j, (if i ≠ j ∧ swapIdx p i j = k then c else 0) =
      c * ∑ i, ∑ j, (if i ≠ j ∧ swapIdx p i j = k then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [hrw, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ hc
  have ha := ode_sum_ind_le p
  have ha0 := ode_sum_ind_nonneg p
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  interval_cases k
  · calc ∑ i, ∑ j, (if i ≠ j ∧ swapIdx p i j = 0 then (1 : ℝ) else 0) ≤
          ∑ _i : Fin N, ∑ _j : Fin N, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by split_ifs <;> norm_num
      _ = (N : ℝ) ^ 2 := by simp [sq]
      _ ≤ 4 * (N : ℝ) ^ (2 - 0) := by norm_num; nlinarith [sq_nonneg (N : ℝ)]
  · calc ∑ i, ∑ j, (if i ≠ j ∧ swapIdx p i j = 1 then (1 : ℝ) else 0) ≤
          ∑ i, ∑ j, (odeInd p i + odeInd p j) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
            unfold odeInd swapIdx
            by_cases hij : i = j <;>
              by_cases h1 : i = p.1.1 ∨ i = p.1.2 <;> by_cases h2 : j = p.1.1 ∨ j = p.1.2 <;>
                simp only [hij, h1, h2, ne_eq, not_true_eq_false, not_false_eq_true, false_and,
                  true_and, ite_true, ite_false] <;> norm_num
      _ = (N : ℝ) * ∑ i, odeInd p i + (N : ℝ) * ∑ j, odeInd p j := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          rw [← Finset.mul_sum]
      _ ≤ 4 * (N : ℝ) ^ (2 - 1) := by norm_num; nlinarith
  · calc ∑ i, ∑ j, (if i ≠ j ∧ swapIdx p i j = 2 then (1 : ℝ) else 0) ≤
          ∑ i, ∑ j, odeInd p i * odeInd p j :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
            unfold odeInd swapIdx
            by_cases hij : i = j <;>
              by_cases h1 : i = p.1.1 ∨ i = p.1.2 <;> by_cases h2 : j = p.1.1 ∨ j = p.1.2 <;>
                simp only [hij, h1, h2, ne_eq, not_true_eq_false, not_false_eq_true, false_and,
                  true_and, ite_true, ite_false] <;> norm_num
      _ = (∑ i, odeInd p i) * ∑ j, odeInd p j := (Finset.sum_mul_sum _ _ _ _).symm
      _ ≤ 4 * (N : ℝ) ^ (2 - 2) := by norm_num; nlinarith

/-- The sum over all pairs of the bounds `odeBeta`. -/
private lemma ode_sum_bound {N : ℕ} (p : OffDiag N) {F : Fin N → Fin N → ℂ} {B P : ℝ}
    (hB : 0 ≤ B) (hP : 0 ≤ P)
    (hF : ∀ i j, ‖F i j‖ ≤ if i = j then 0 else odeBeta B P (swapIdx p i j)) :
    ‖∑ i, ∑ j, F i j‖ ≤ 4 * (N : ℝ) ^ 2 * (2 ^ 25 * B ^ 5 * P ^ 3) +
      4 * (N : ℝ) * (2 ^ 25 * B ^ 5 * P ^ 2) + 4 * (16 * B * P) := by
  calc ‖∑ i, ∑ j, F i j‖ ≤ ∑ i, ∑ j, ‖F i j‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, (if i = j then 0 else odeBeta B P (swapIdx p i j)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hF i j
    _ = ∑ k ∈ Finset.range 3, ∑ i, ∑ j,
          (if i ≠ j ∧ swapIdx p i j = k then odeBeta B P k else 0) := by
        symm
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [ode_ite_eq_sum p i j]
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs with h
        · rw [h.2]
        · rfl
    _ ≤ ∑ k ∈ Finset.range 3, 4 * (N : ℝ) ^ (2 - k) * odeBeta B P k :=
        Finset.sum_le_sum fun k hk =>
          ode_count p (by have := Finset.mem_range.1 hk; omega) (ode_beta_nonneg hB hP k)
    _ = _ := by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, odeBeta]
        norm_num

/-- [16] (6.61) summed over the pairs of one part: `|Σ_{I_k} (|S_ij|² - |R_ij|²)| ≤
4 N^{2-k} 16 B P^{3-k}`. -/
private lemma ode_part_diff {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {S : Matrix (Fin N) (Fin N) ℂ}
    {p : OffDiag N} {v : ℝ} {z : ℂ} {P B : ℝ}
    (hexp : ∀ n i j, S i j = ∑ m ∈ Finset.range (n + 1),
        (-(v : ℂ)) ^ m * swapCoeff H (Sum.inr p) z m i j + (-(v : ℂ)) ^ (n + 1) *
          (((resolventC H z * (entryMat (Sum.inr p)).map (fun x : ℝ => (x : ℂ))) ^ (n + 1) *
            S) i j))
    (hv : |v| ≤ B) (hP : 0 ≤ P)
    (hS : ∀ k l, ‖S k l‖ ≤ 2) (hS' : ∀ k l, k ≠ l → ‖S k l‖ ≤ P)
    (hR : ∀ k l, ‖resolventC H z k l‖ ≤ 2) (hR' : ∀ k l, k ≠ l → ‖resolventC H z k l‖ ≤ P)
    {k : ℕ} (hk : k ≤ 2) :
    |(∑ i, ∑ j, if i ≠ j ∧ swapIdx p i j = k then ‖S i j‖ ^ 2 else 0) -
        ∑ i, ∑ j, if i ≠ j ∧ swapIdx p i j = k then ‖resolventC H z i j‖ ^ 2 else 0| ≤
      4 * (N : ℝ) ^ (2 - k) * (16 * B * P ^ (3 - k)) := by
  have hB : 0 ≤ B := (abs_nonneg v).trans hv
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_)
    (ode_count p hk (c := 16 * B * P ^ (3 - k)) (by positivity))
  split_ifs with h
  · rw [← h.2]; exact ode_pair_diff hexp hv hP hS hS' hR hR' h.1
  · simp

/-! ### The event `Ω` and the window -/

/-- On `Ω = swapEvent` with the bound (3.27) on `R`, at every `E ∈ I_ε` the entries of `S = G(H)`
and of `R = G(Q)` are at most `2` and the off-diagonal ones at most `P = N^{-1/3+3ε}`. -/
private lemma ode_good {N : ℕ} (hN : 1 ≤ N) {ε φs : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 10)
    {ω : Entries N} {p : OffDiag N} (hω : ω ∈ swapEvent N ε φs (Sum.inr p))
    (hRb : ∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) → ∀ k l,
      ‖resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l -
          (if k = l then msc ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ else 0)‖ ≤
        (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε))
    {E : ℝ} (hE : |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) :
    (∀ k l, ‖resolventC (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l‖ ≤ 2) ∧
    (∀ k l, k ≠ l → ‖resolventC (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l‖ ≤
      (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ∧
    (∀ k l, ‖resolventC (symOfEntries (zeroEntry (Sum.inr p) ω))
      ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l‖ ≤ 2) ∧
    (∀ k l, k ≠ l → ‖resolventC (symOfEntries (zeroEntry (Sum.inr p) ω))
      ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l‖ ≤ (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hη0 : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) := Real.rpow_pos_of_pos hn0 _
  have hP1 : (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hPP : (N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε) ≤ (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hm := (norm_msc_eq_inv_and_lt_one (z := ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩) hη0).2
  have hSo : ∀ k l, k ≠ l → ‖resolventC (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l‖ ≤
      (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) := by
    intro k l hkl
    have h := hω.1 E hE k l
    simp only [hkl, ite_false, sub_zero] at h
    exact h.trans hPP
  have hRo : ∀ k l, k ≠ l → ‖resolventC (symOfEntries (zeroEntry (Sum.inr p) ω))
      ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l‖ ≤ (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) := by
    intro k l hkl
    have h := hRb E hE k l
    simp only [hkl, ite_false, sub_zero] at h
    exact h
  refine ⟨fun k l => ?_, hSo, fun k l => ?_, hRo⟩
  · by_cases hkl : k = l
    · subst hkl
      exact (aprioriEvent_bounds hN hε hε' hω.1).1 E hE k
    · linarith [hSo k l hkl]
  · by_cases hkl : k = l
    · subst hkl
      have h := hRb E hE k k
      simp only [ite_true] at h
      calc _ = ‖(resolventC (symOfEntries (zeroEntry (Sum.inr p) ω))
              ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k k - msc ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩) +
            msc ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
        _ ≤ 2 := by linarith
    · linarith [hRo k l hkl]

/-- A point between two points of `I_ε` lies in `I_ε`. -/
private lemma ode_window {E₁ E₂ y r : ℝ} (h1 : |E₁ - 2| ≤ r) (h2 : |E₂ - 2| ≤ r)
    (hy : y ∈ Set.uIoc E₁ E₂) : |y - 2| ≤ r := by
  have a1 := abs_le.1 h1
  have a2 := abs_le.1 h2
  rcases Set.mem_uIcc.1 (Set.uIoc_subset_uIcc hy) with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩ <;>
    exact abs_le.2 ⟨by linarith, by linarith⟩

/-- The weight of the integrated functional: `η |E₂ - E₁| ≤ 2 N^{-4/3}` for `E₁, E₂ ∈ I_ε`. -/
private lemma ode_weight {x ε E₁ E₂ : ℝ} (hx : 1 ≤ x) (h1 : |E₁ - 2| ≤ x ^ (-(2 : ℝ) / 3 + ε))
    (h2 : |E₂ - 2| ≤ x ^ (-(2 : ℝ) / 3 + ε)) :
    x ^ (-(2 : ℝ) / 3 - ε) * |E₂ - E₁| ≤ 2 * x ^ (-(4 : ℝ) / 3) := by
  have hx0 : 0 < x := by linarith
  have hw : |E₂ - E₁| ≤ 2 * x ^ (-(2 : ℝ) / 3 + ε) := by
    calc |E₂ - E₁| = |(E₂ - 2) - (E₁ - 2)| := by ring_nf
      _ ≤ |E₂ - 2| + |E₁ - 2| := abs_sub _ _
      _ ≤ _ := by linarith
  have he : x ^ (-(2 : ℝ) / 3 - ε) * x ^ (-(2 : ℝ) / 3 + ε) = x ^ (-(4 : ℝ) / 3) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  calc x ^ (-(2 : ℝ) / 3 - ε) * |E₂ - E₁| ≤ x ^ (-(2 : ℝ) / 3 - ε) * (2 * x ^ (-(2 : ℝ) / 3 + ε)) :=
        mul_le_mul_of_nonneg_left hw (Real.rpow_pos_of_pos hx0 _).le
    _ = 2 * x ^ (-(4 : ℝ) / 3) := by rw [← he]; ring

/-- The weight of the pointwise functional: `η² ≤ 2 N^{-4/3}`. -/
private lemma ode_weight_sq {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) :
    (x ^ (-(2 : ℝ) / 3 - ε)) ^ 2 ≤ 2 * x ^ (-(4 : ℝ) / 3) := by
  have hx0 : 0 < x := by linarith
  rw [← Real.rpow_mul_natCast hx0.le]
  have : x ^ ((-(2 : ℝ) / 3 - ε) * ((2 : ℕ) : ℝ)) ≤ x ^ (-(4 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_exponent_le hx (by push_cast; linarith)
  linarith [Real.rpow_pos_of_pos hx0 (-(4 : ℝ) / 3)]

/-- The exponent bookkeeping of [16] (6.61):
`2 N^{-4/3} 4 N^{2-k} 16 B P^{3-k} = 128 N^{2/3-k} P^{3-k} B`. -/
private lemma ode_final5 {x W B P : ℝ} (hx : 1 ≤ x) (hW : W ≤ 2 * x ^ (-(4 : ℝ) / 3))
    (hB : 0 ≤ B) (hP : 0 ≤ P) {k : ℕ} (hk : k ≤ 2) :
    W * (4 * x ^ (2 - k) * (16 * B * P ^ (3 - k))) ≤
      128 * x ^ ((2 : ℝ) / 3 - k) * P ^ (3 - k) * B := by
  have hx0 : 0 < x := by linarith
  have he : x ^ (-(4 : ℝ) / 3) * x ^ (2 - k) = x ^ ((2 : ℝ) / 3 - k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx0]
    congr 1
    push_cast [Nat.cast_sub hk]
    ring
  calc W * (4 * x ^ (2 - k) * (16 * B * P ^ (3 - k))) ≤
        2 * x ^ (-(4 : ℝ) / 3) * (4 * x ^ (2 - k) * (16 * B * P ^ (3 - k))) :=
        mul_le_mul_of_nonneg_right hW (by positivity)
    _ = 128 * (x ^ (-(4 : ℝ) / 3) * x ^ (2 - k)) * P ^ (3 - k) * B := by ring
    _ = _ := by rw [he]

/-- `|η ∫_{E₁}^{E₂} g| ≤ η |E₂ - E₁| K` when `|g| ≤ K` between `E₁` and `E₂`. -/
private lemma ode_eta_int_le {g : ℝ → ℝ} {η K : ℝ} (hη : 0 < η) {E₁ E₂ : ℝ}
    (hg : ∀ y ∈ Set.uIoc E₁ E₂, |g y| ≤ K) :
    |η * ∫ y in E₁..E₂, g y| ≤ η * |E₂ - E₁| * K := by
  rw [abs_mul, abs_of_pos hη, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hη.le
  rw [mul_comm]
  simpa [Real.norm_eq_abs] using
    intervalIntegral.norm_integral_le_of_norm_le_const (a := E₁) (b := E₂) (f := g)
      (fun y hy => by simpa [Real.norm_eq_abs] using hg y hy)

/-- [16] (6.61) on `Ω = swapEvent`: `|x^S_k - x^R_k| ≤ C N^{2/3-k} p^{-(3-k)} N^ε q⁻¹`,
`p⁻¹ = N^{-1/3+3ε}`, `k = 0, 1, 2`, for both functionals. -/
theorem abs_offWardPart_sub_le {φs : ℝ} (hφs : 1 / 3 < φs) (hφs' : φs ≤ 1 / 2) :
    ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < 1 / 10 → ∃ N0 : ℕ, ∀ N ≥ N0, ∀ ω : Entries N,
      ∀ p : OffDiag N, ω ∈ swapEvent N ε φs (Sum.inr p) → ∀ k : ℕ, k ≤ 2 →
      (∀ E₁ E₂ : ℝ, |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
        |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
        |offWardIntPart (symOfEntries ω) p ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂ k -
            offWardIntPart (symOfEntries (zeroEntry (Sum.inr p) ω)) p
              ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂ k| ≤
          C * (N : ℝ) ^ ((2 : ℝ) / 3 - k) * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ (3 - k) *
            (N : ℝ) ^ (ε - φs)) ∧
      (∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
        |offWardPart (symOfEntries ω) p ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k -
            offWardPart (symOfEntries (zeroEntry (Sum.inr p) ω)) p
              ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k| ≤
          C * (N : ℝ) ^ ((2 : ℝ) / 3 - k) * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ (3 - k) *
            (N : ℝ) ^ (ε - φs)) := by
  refine ⟨128, by norm_num, fun ε hε hε' => ?_⟩
  obtain ⟨N0, hN0⟩ := norm_resolventC_zeroEntry_sub_le hφs hφs' ε hε hε'
  refine ⟨max N0 1, fun N hN ω p hω k hk => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hRb := hN0 N (le_trans (le_max_left _ _) hN) ω (Sum.inr p) hω.1 hω.2
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < N := by linarith
  have hη : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) := Real.rpow_pos_of_pos hn0 _
  have hP0 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) := (Real.rpow_pos_of_pos hn0 _).le
  have hB0 : 0 ≤ (N : ℝ) ^ (ε - φs) := (Real.rpow_pos_of_pos hn0 _).le
  have hpt : ∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
      |(∑ i, ∑ j, if i ≠ j ∧ swapIdx p i j = k then
            ‖resolventC (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i j‖ ^ 2 else 0) -
          ∑ i, ∑ j, if i ≠ j ∧ swapIdx p i j = k then
            ‖resolventC (symOfEntries (zeroEntry (Sum.inr p) ω))
              ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i j‖ ^ 2 else 0| ≤
        4 * (N : ℝ) ^ (2 - k) * (16 * (N : ℝ) ^ (ε - φs) *
          ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ (3 - k)) := by
    intro E hE
    obtain ⟨hS, hS', hR, hR'⟩ := ode_good hN1 hε hε' hω hRb hE
    exact ode_part_diff (fun n i j => ode_apply_eq_sum (Sum.inr p) ω hη n i j) hω.2 hP0
      hS hS' hR hR' hk
  refine ⟨fun E₁ E₂ h1 h2 => ?_, fun E hE => ?_⟩
  · unfold offWardIntPart
    rw [← mul_sub, ← intervalIntegral.integral_sub
      ((ode_continuous_part (symOfEntries_isHermitian ω) hη p k).intervalIntegrable _ _)
      ((ode_continuous_part (symOfEntries_isHermitian (zeroEntry (Sum.inr p) ω)) hη p
        k).intervalIntegrable _ _)]
    refine (ode_eta_int_le hη fun y hy => hpt y (ode_window h1 h2 hy)).trans ?_
    exact ode_final5 hn1 (ode_weight hn1 h1 h2) hB0 hP0 hk
  · unfold offWardPart
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
    refine (mul_le_mul_of_nonneg_left (hpt E hE) (sq_nonneg _)).trans ?_
    exact ode_final5 hn1 (ode_weight_sq hn1 hε) hB0 hP0 hk

/-! ### The main term of (6.69) -/

/-- The off-diagonal sum `Σ_{i ≠ j} |G_ij(y + iη)|²` is continuous in `y`. -/
private lemma ode_continuous_offsum {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {η : ℝ} (hη : 0 < η) :
    Continuous fun y : ℝ => ∑ i, ∑ j, if i = j then 0 else ‖resolventC H ⟨y, η⟩ i j‖ ^ 2 :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_if_const _ (fun _ => continuous_const)
      fun _ => ((ode_continuous_resolventC hH hη).matrix_elem i j).norm.pow 2

private lemma ode_continuous_inner {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {η : ℝ} (hη : 0 < η) (p : OffDiag N) (k s t : ℕ) :
    Continuous fun y : ℝ => odeInner H p ⟨y, η⟩ k s t :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_if_const _ (fun _ => (ode_continuous_swapCoeff hH hη _ s i j).mul
      (Complex.continuous_conj.comp (ode_continuous_swapCoeff hH hη _ t i j)))
      fun _ => continuous_const

private lemma ode_continuous_mainPt {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {η : ℝ} (hη : 0 < η) (p : OffDiag N) (v : ℝ) :
    Continuous fun y : ℝ => odeMainPt H p v ⟨y, η⟩ :=
  continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun s _ => continuous_finsetSum _
    fun t _ => continuous_const.mul (ode_continuous_inner hH hη p k s t)

/-- The pointwise main term: `Σ_{k, s, t} (-v)^{s+t} swapKpt = η² odeMainPt`. -/
private lemma ode_sum_swapKpt {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (p : OffDiag N) (v : ℝ)
    (z : ℂ) :
    (∑ k ∈ Finset.range 2, ∑ s ∈ Finset.range 5, ∑ t ∈ Finset.range 5,
      if 1 ≤ s + t ∧ s + t ≤ 4 then (-(v : ℂ)) ^ (s + t) * swapKpt H p z k s t else 0) =
      (z.im : ℂ) ^ 2 * odeMainPt H p v z := by
  unfold odeMainPt
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hK : swapKpt H p z k s t = (z.im : ℂ) ^ 2 * odeInner H p z k s t := rfl
  rw [hK]
  split_ifs <;> ring

/-- The integrated main term: `Σ_{k, s, t} (-v)^{s+t} swapK = η ∫ odeMainPt`. -/
private lemma ode_sum_swapK {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    (p : OffDiag N) (v : ℝ) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) :
    (∑ k ∈ Finset.range 2, ∑ s ∈ Finset.range 5, ∑ t ∈ Finset.range 5,
      if 1 ≤ s + t ∧ s + t ≤ 4 then (-(v : ℂ)) ^ (s + t) * swapK H p η E₁ E₂ k s t else 0) =
      (η : ℂ) * ∫ y in E₁..E₂, odeMainPt H p v ⟨y, η⟩ := by
  have hc := ode_continuous_inner hH hη p
  have hc3 : ∀ k s t, Continuous fun y : ℝ =>
      (if 1 ≤ s + t ∧ s + t ≤ 4 then (-(v : ℂ)) ^ (s + t) else 0) * odeInner H p ⟨y, η⟩ k s t :=
    fun k s t => continuous_const.mul (hc k s t)
  have hc2 : ∀ k s, Continuous fun y : ℝ => ∑ t ∈ Finset.range 5,
      (if 1 ≤ s + t ∧ s + t ≤ 4 then (-(v : ℂ)) ^ (s + t) else 0) * odeInner H p ⟨y, η⟩ k s t :=
    fun k s => continuous_finsetSum _ fun t _ => hc3 k s t
  have hc1 : ∀ k, Continuous fun y : ℝ => ∑ s ∈ Finset.range 5, ∑ t ∈ Finset.range 5,
      (if 1 ≤ s + t ∧ s + t ≤ 4 then (-(v : ℂ)) ^ (s + t) else 0) * odeInner H p ⟨y, η⟩ k s t :=
    fun k => continuous_finsetSum _ fun s _ => hc2 k s
  unfold odeMainPt
  rw [intervalIntegral.integral_finsetSum fun k _ => (hc1 k).intervalIntegrable _ _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_finsetSum fun s _ => (hc2 k s).intervalIntegrable _ _,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [intervalIntegral.integral_finsetSum fun t _ => (hc3 k s t).intervalIntegrable _ _,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hK : swapK H p η E₁ E₂ k s t = (η : ℂ) * ∫ y in E₁..E₂, odeInner H p ⟨y, η⟩ k s t := rfl
  rw [hK, intervalIntegral.integral_const_mul]
  split_ifs <;> ring

/-- [16] (6.69) at one point `z` of `Ω`: `|Σ_{i ≠ j}(|S_ij|² - |R_ij|²) - main| ≤
Σ_k 4 N^{2-k} odeBeta B P k`. -/
private lemma ode_pt_bound {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {S : Matrix (Fin N) (Fin N) ℂ}
    {p : OffDiag N} {v : ℝ} {z : ℂ} {P B : ℝ}
    (hexp : ∀ n i j, S i j = ∑ m ∈ Finset.range (n + 1),
        (-(v : ℂ)) ^ m * swapCoeff H (Sum.inr p) z m i j + (-(v : ℂ)) ^ (n + 1) *
          (((resolventC H z * (entryMat (Sum.inr p)).map (fun x : ℝ => (x : ℂ))) ^ (n + 1) *
            S) i j))
    (hv : |v| ≤ B) (hB1 : B ≤ 1) (hP : 0 ≤ P) (hP1 : P ≤ 1)
    (hS : ∀ k l, ‖S k l‖ ≤ 2) (hS' : ∀ k l, k ≠ l → ‖S k l‖ ≤ P)
    (hR : ∀ k l, ‖resolventC H z k l‖ ≤ 2) (hR' : ∀ k l, k ≠ l → ‖resolventC H z k l‖ ≤ P) :
    ‖((((∑ i, ∑ j, if i = j then 0 else ‖S i j‖ ^ 2) -
          ∑ i, ∑ j, if i = j then 0 else ‖resolventC H z i j‖ ^ 2) : ℝ) : ℂ) -
        odeMainPt H p v z‖ ≤
      4 * (N : ℝ) ^ 2 * (2 ^ 25 * B ^ 5 * P ^ 3) + 4 * (N : ℝ) * (2 ^ 25 * B ^ 5 * P ^ 2) +
        4 * (16 * B * P) := by
  have hB : 0 ≤ B := (abs_nonneg v).trans hv
  rw [ode_mainPt_eq, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  push_cast
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  refine ode_sum_bound p hB hP fun i j => ?_
  have h := ode_pair_bound hexp hv hB1 hP hP1 hS hS' hR hR' i j
  push_cast at h
  exact h

/-- The exponent bookkeeping of [16] (6.69): for `N^ε ≥ 2^30` and `φs > 1/3`, the weight
`W ≤ 2 N^{-4/3}` times `4N²·2^25 B⁵P³ + 4N·2^25 B⁵P² + 4·16 BP` is at most `N^{-5/3-φs+15ε}`. -/
private lemma ode_final6 {x ε φs W : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) (hφs : 1 / 3 < φs)
    (hbig : 2 ^ 30 ≤ x ^ ε) (hW : W ≤ 2 * x ^ (-(4 : ℝ) / 3)) :
    W * (4 * x ^ 2 * (2 ^ 25 * (x ^ (ε - φs)) ^ 5 * (x ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 3) +
        4 * x * (2 ^ 25 * (x ^ (ε - φs)) ^ 5 * (x ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 2) +
        4 * (16 * x ^ (ε - φs) * x ^ (-(1 : ℝ) / 3 + 3 * ε))) ≤
      x ^ (-(5 : ℝ) / 3 - φs + 15 * ε) := by
  have hx0 : 0 < x := by linarith
  have hpow : ∀ (a : ℝ) (n : ℕ), (x ^ a) ^ n = x ^ (a * n) := fun a n =>
    (Real.rpow_mul_natCast hx0.le a n).symm
  have hmulx : ∀ a : ℝ, x * x ^ a = x ^ (1 + a) := fun a => by
    rw [Real.rpow_add hx0, Real.rpow_one]
  have hx2 : x ^ 2 = x ^ (2 : ℝ) := (Real.rpow_natCast x 2).symm
  set T := x ^ (-(5 : ℝ) / 3 - φs + 14 * ε) with hT
  have hT0 : 0 ≤ T := (Real.rpow_pos_of_pos hx0 _).le
  have e1 : x ^ (-(4 : ℝ) / 3) * (x ^ 2 * ((x ^ (ε - φs)) ^ 5 * (x ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 3)) ≤
      T := by
    rw [hpow, hpow, hx2, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx (by push_cast; nlinarith)
  have e2 : x ^ (-(4 : ℝ) / 3) * (x * ((x ^ (ε - φs)) ^ 5 * (x ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 2)) ≤
      T := by
    rw [hpow, hpow, ← Real.rpow_add hx0, hmulx, ← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx (by push_cast; nlinarith)
  have e3 : x ^ (-(4 : ℝ) / 3) * (x ^ (ε - φs) * x ^ (-(1 : ℝ) / 3 + 3 * ε)) ≤ T := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx (by nlinarith)
  have hgoal : x ^ (-(5 : ℝ) / 3 - φs + 15 * ε) = x ^ ε * T := by
    rw [hT, ← Real.rpow_add hx0]; congr 1; ring
  have hA0 : 0 ≤ 4 * x ^ 2 * (2 ^ 25 * (x ^ (ε - φs)) ^ 5 * (x ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 3) +
        4 * x * (2 ^ 25 * (x ^ (ε - φs)) ^ 5 * (x ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 2) +
        4 * (16 * x ^ (ε - φs) * x ^ (-(1 : ℝ) / 3 + 3 * ε)) := by positivity
  calc _ ≤ 2 * x ^ (-(4 : ℝ) / 3) *
        (4 * x ^ 2 * (2 ^ 25 * (x ^ (ε - φs)) ^ 5 * (x ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 3) +
          4 * x * (2 ^ 25 * (x ^ (ε - φs)) ^ 5 * (x ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 2) +
          4 * (16 * x ^ (ε - φs) * x ^ (-(1 : ℝ) / 3 + 3 * ε))) :=
        mul_le_mul_of_nonneg_right hW hA0
    _ = 2 ^ 28 * (x ^ (-(4 : ℝ) / 3) * (x ^ 2 * ((x ^ (ε - φs)) ^ 5 *
            (x ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 3))) +
          2 ^ 28 * (x ^ (-(4 : ℝ) / 3) * (x * ((x ^ (ε - φs)) ^ 5 *
            (x ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 2))) +
          128 * (x ^ (-(4 : ℝ) / 3) * (x ^ (ε - φs) * x ^ (-(1 : ℝ) / 3 + 3 * ε))) := by ring
    _ ≤ 2 ^ 28 * T + 2 ^ 28 * T + 128 * T := by gcongr
    _ ≤ 2 ^ 30 * T := by nlinarith
    _ ≤ x ^ ε * T := mul_le_mul_of_nonneg_right hbig hT0
    _ = _ := hgoal.symm

/-- [16] (6.69) on `Ω = swapEvent`, `e = (b, d)` off-diagonal:
`x_S - x_R = Σ_{k=0,1} Σ_{1 ≤ s+t ≤ 4} (-v)^{s+t} K^{(s,t)}_k(Q) + O(N^{-5/3-φs+Cε})`
(`= O(N^{-1/3+Cε} p^{-4} q⁻¹)`), for both functionals; `C` is absolute. -/
theorem offWard_sub_eq_sum_swapK {φs : ℝ} (hφs : 1 / 3 < φs) (hφs' : φs ≤ 1 / 2) :
    ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < 1 / 10 → ∃ N0 : ℕ, ∀ N ≥ N0, ∀ ω : Entries N,
      ∀ p : OffDiag N, ω ∈ swapEvent N ε φs (Sum.inr p) →
      (∀ E₁ E₂ : ℝ, |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
        |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
        ‖((offWardInt (symOfEntries ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂ -
              offWardInt (symOfEntries (zeroEntry (Sum.inr p) ω))
                ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂ : ℝ) : ℂ) -
            ∑ k ∈ Finset.range 2, ∑ s ∈ Finset.range 5, ∑ t ∈ Finset.range 5,
              if 1 ≤ s + t ∧ s + t ≤ 4 then
                (-(entryVal (Sum.inr p) ω : ℂ)) ^ (s + t) *
                  swapK (symOfEntries (zeroEntry (Sum.inr p) ω)) p
                    ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂ k s t
              else 0‖ ≤
          (N : ℝ) ^ (-(5 : ℝ) / 3 - φs + C * ε)) ∧
      (∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
        ‖((offWard (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ -
              offWard (symOfEntries (zeroEntry (Sum.inr p) ω))
                ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ : ℝ) : ℂ) -
            ∑ k ∈ Finset.range 2, ∑ s ∈ Finset.range 5, ∑ t ∈ Finset.range 5,
              if 1 ≤ s + t ∧ s + t ≤ 4 then
                (-(entryVal (Sum.inr p) ω : ℂ)) ^ (s + t) *
                  swapKpt (symOfEntries (zeroEntry (Sum.inr p) ω)) p
                    ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k s t
              else 0‖ ≤
          (N : ℝ) ^ (-(5 : ℝ) / 3 - φs + C * ε)) := by
  refine ⟨15, by norm_num, fun ε hε hε' => ?_⟩
  obtain ⟨N0, hN0⟩ := norm_resolventC_zeroEntry_sub_le hφs hφs' ε hε hε'
  obtain ⟨N1, hN1⟩ := eventually_atTop.1
    (((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop ((2 : ℝ) ^ 30))
  refine ⟨max (max N0 N1) 1, fun N hN ω p hω => ?_⟩
  have hNa : N0 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb : N1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN1' : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hbig : (2 : ℝ) ^ 30 ≤ (N : ℝ) ^ ε := hN1 N hNb
  have hRb := hN0 N hNa ω (Sum.inr p) hω.1 hω.2
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1'
  have hn0 : (0 : ℝ) < N := by linarith
  have hη : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) := Real.rpow_pos_of_pos hn0 _
  have hP0 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) := (Real.rpow_pos_of_pos hn0 _).le
  have hP1 : (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hB1 : (N : ℝ) ^ (ε - φs) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hpt : ∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
      ‖((((∑ i, ∑ j, if i = j then 0 else
              ‖resolventC (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i j‖ ^ 2) -
            ∑ i, ∑ j, if i = j then 0 else
              ‖resolventC (symOfEntries (zeroEntry (Sum.inr p) ω))
                ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i j‖ ^ 2) : ℝ) : ℂ) -
          odeMainPt (symOfEntries (zeroEntry (Sum.inr p) ω)) p (entryVal (Sum.inr p) ω)
            ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩‖ ≤
        4 * (N : ℝ) ^ 2 * (2 ^ 25 * ((N : ℝ) ^ (ε - φs)) ^ 5 *
            ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 3) +
          4 * (N : ℝ) * (2 ^ 25 * ((N : ℝ) ^ (ε - φs)) ^ 5 *
            ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 2) +
          4 * (16 * (N : ℝ) ^ (ε - φs) * (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) := by
    intro E hE
    obtain ⟨hS, hS', hR, hR'⟩ := ode_good hN1' hε hε' hω hRb hE
    exact ode_pt_bound (fun n i j => ode_apply_eq_sum (Sum.inr p) ω hη n i j) hω.2 hB1 hP0 hP1
      hS hS' hR hR'
  have hHS := symOfEntries_isHermitian ω
  have hHR := symOfEntries_isHermitian (zeroEntry (Sum.inr p) ω)
  refine ⟨fun E₁ E₂ h1 h2 => ?_, fun E hE => ?_⟩
  · rw [ode_sum_swapK hHR p _ hη E₁ E₂]
    unfold offWardInt
    rw [← mul_sub, ← intervalIntegral.integral_sub
      ((ode_continuous_offsum hHS hη).intervalIntegrable _ _)
      ((ode_continuous_offsum hHR hη).intervalIntegrable _ _),
      Complex.ofReal_mul, ← intervalIntegral.integral_ofReal, ← mul_sub,
      ← intervalIntegral.integral_sub]
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
      calc _ ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) * (_ * |E₂ - E₁|) :=
            mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_of_norm_le_const
              fun y hy => hpt y (ode_window h1 h2 hy)) hη.le
        _ = ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε) * |E₂ - E₁|) * _ := by ring
        _ ≤ _ := ode_final6 hn1 hε hφs hbig (ode_weight hn1 h1 h2)
    · exact (Complex.continuous_ofReal.comp ((ode_continuous_offsum hHS hη).sub
        (ode_continuous_offsum hHR hη))).intervalIntegrable _ _
    · exact (ode_continuous_mainPt hHR hη p _).intervalIntegrable _ _
  · rw [ode_sum_swapKpt]
    unfold offWard
    have him : (⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ : ℂ).im = (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) := rfl
    rw [him, ← mul_sub, Complex.ofReal_mul, Complex.ofReal_pow, ← mul_sub, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
    calc _ ≤ ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) ^ 2 * _ :=
          mul_le_mul_of_nonneg_left (hpt E hE) (by positivity)
      _ ≤ _ := ode_final6 hn1 hε hφs hbig (ode_weight_sq hn1 hε)

/-! ### Checks -/

/-- `M` with diagonal entries `1` and off-diagonal entries `1/4` (`N = 3`). -/
private def swapM : Matrix (Fin 3) (Fin 3) ℂ := fun k l => if k = l then 1 else 1 / 4

private lemma swapM_le (k l : Fin 3) : ‖swapM k l‖ ≤ 2 := by
  unfold swapM; split_ifs <;> norm_num

private lemma swapM_off (k l : Fin 3) (h : k ≠ l) : ‖swapM k l‖ ≤ 1 / 4 := by
  simp only [swapM, h, ite_false]; norm_num

/-- `norm_mul_entryMat_pow_mul_apply_le` at `N = 3`, `A = B = M`, `P = 1/4`, `e = (0, 1)`, `m = 1`,
`(i, j) = (2, 0)` (`k = 1`); every hypothesis is discharged. -/
example : ‖((swapM * (entryMat (Sum.inr (⟨(0, 1), by decide⟩ : OffDiag 3))).map
      (fun x : ℝ => (x : ℂ))) ^ 1 * swapM) 2 0‖ ≤
    2 ^ (2 * 1 + 1) * (1 / 4 : ℝ) ^ (2 - swapIdx (⟨(0, 1), by decide⟩ : OffDiag 3) 2 0) :=
  norm_mul_entryMat_pow_mul_apply_le (by norm_num) (by norm_num) swapM_le swapM_off swapM_le
    swapM_off _ le_rfl 2 0

/-- At this point `k = 1`, so the bound is `2³ · (1/4)`. -/
example : swapIdx (⟨(0, 1), by decide⟩ : OffDiag 3) 2 0 = 1 := by decide

/-- The entries `ω` with diagonal `1` and off-diagonal `1/4` (`N = 3`). -/
private def swapW : Entries 3 := (fun _ => 1, fun _ => 1 / 4)

/-- (6.58) at `N = 3`, `ω = swapW`, `e = (0, 1)`, `z = i`. -/
example : resolventC (symOfEntries swapW) Complex.I =
    ∑ m ∈ Finset.range 6,
        (-(entryVal (Sum.inr (⟨(0, 1), by decide⟩ : OffDiag 3)) swapW : ℂ)) ^ m •
          swapCoeff (symOfEntries (zeroEntry (Sum.inr ⟨(0, 1), by decide⟩) swapW))
            (Sum.inr ⟨(0, 1), by decide⟩) Complex.I m +
      (-(entryVal (Sum.inr (⟨(0, 1), by decide⟩ : OffDiag 3)) swapW : ℂ)) ^ 6 •
        ((resolventC (symOfEntries (zeroEntry (Sum.inr ⟨(0, 1), by decide⟩) swapW)) Complex.I *
          (entryMat (Sum.inr (⟨(0, 1), by decide⟩ : OffDiag 3))).map (fun x : ℝ => (x : ℂ))) ^ 6 *
            resolventC (symOfEntries swapW) Complex.I) :=
  resolventC_eq_sum_swapCoeff _ _ (by simp)

/-- (6.57) at `N = 3`, `H = symOfEntries swapW`, `p = (0, 1)`, `η = 1`, `[E₁, E₂] = [0, 1]`. -/
example : offWardInt (symOfEntries swapW) 1 0 1 =
    ∑ k ∈ Finset.range 3, offWardIntPart (symOfEntries swapW) ⟨(0, 1), by decide⟩ 1 0 1 k :=
  offWardInt_eq_sum_part _ (symOfEntries_isHermitian _) _ one_pos 0 1

-- The event `swapEvent N ε (2/5) e` is nonempty for all large `N` (the GOE, `γ = 0`).
open private swapEvent_nonempty from WEdgeNS.EdgeUniv.RBound

/-- The hypotheses of `abs_offWardPart_sub_le` hold together at `φs = 2/5`, `ε = 1/20`: for all
large `N ≥ 4` there are `ω` and `p = (0, 1)` with `ω ∈ swapEvent`, and the conclusion holds at
`k = 0` (a nonempty part), on the window `[E₁, E₂] = [2, 2 + N^{-2/3+ε}]` and at `E = 2`. -/
example : ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, 4 ≤ N ∧ ∃ ω : Entries N, ∃ p : OffDiag N,
    ω ∈ swapEvent N (1 / 20) (2 / 5) (Sum.inr p) ∧
    (2 : ℝ) < 2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 20) ∧
    |offWardIntPart (symOfEntries ω) p ((N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 20)) 2
          (2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 20)) 0 -
        offWardIntPart (symOfEntries (zeroEntry (Sum.inr p) ω)) p
          ((N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 20)) 2 (2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 20)) 0| ≤
      C * (N : ℝ) ^ ((2 : ℝ) / 3 - ((0 : ℕ) : ℝ)) *
        ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * (1 / 20))) ^ (3 - 0) * (N : ℝ) ^ ((1 : ℝ) / 20 - 2 / 5) ∧
    |offWardPart (symOfEntries ω) p ⟨2, (N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 20)⟩ 0 -
        offWardPart (symOfEntries (zeroEntry (Sum.inr p) ω)) p
          ⟨2, (N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 20)⟩ 0| ≤
      C * (N : ℝ) ^ ((2 : ℝ) / 3 - ((0 : ℕ) : ℝ)) *
        ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * (1 / 20))) ^ (3 - 0) * (N : ℝ) ^ ((1 : ℝ) / 20 - 2 / 5) := by
  obtain ⟨C, hC, h⟩ := abs_offWardPart_sub_le (φs := 2 / 5) (by norm_num) (by norm_num)
  obtain ⟨N0, hN0⟩ := h (1 / 20) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  filter_upwards [swapEvent_nonempty (ε := 1 / 20) (by norm_num) (by norm_num),
    eventually_ge_atTop (max N0 4)] with N ⟨ω, hω⟩ hN
  have h4 : 4 ≤ N := le_trans (le_max_right _ _) hN
  let p : OffDiag N := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.lt_def]⟩
  have hr : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 20) := Real.rpow_pos_of_pos (by positivity) _
  have hE₁ : |(2 : ℝ) - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 20) := by
    rw [sub_self, abs_zero]; exact hr.le
  have hE₂ : |(2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 20)) - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 20) := by
    rw [add_sub_cancel_left, abs_of_pos hr]
  have hk := hN0 N (le_trans (le_max_left _ _) hN) ω p (hω _) 0 (by norm_num)
  exact ⟨h4, ω, p, hω _, by linarith, hk.1 _ _ hE₁ hE₂, hk.2 _ hE₁⟩

/-- The hypotheses of `offWard_sub_eq_sum_swapK` hold together at `φs = 2/5`, `ε = 1/20`: for all
large `N ≥ 4` there are `ω` and `p = (0, 1)` with `ω ∈ swapEvent`, and the conclusion holds on the
window `[E₁, E₂] = [2, 2 + N^{-2/3+ε}]` and at `E = 2`. -/
example : ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, 4 ≤ N ∧ ∃ ω : Entries N, ∃ p : OffDiag N,
    ω ∈ swapEvent N (1 / 20) (2 / 5) (Sum.inr p) ∧
    (2 : ℝ) < 2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 20) ∧
    ‖((offWardInt (symOfEntries ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 20)) 2
            (2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 20)) -
          offWardInt (symOfEntries (zeroEntry (Sum.inr p) ω))
            ((N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 20)) 2 (2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 20)) : ℝ) :
            ℂ) -
        ∑ k ∈ Finset.range 2, ∑ s ∈ Finset.range 5, ∑ t ∈ Finset.range 5,
          if 1 ≤ s + t ∧ s + t ≤ 4 then
            (-(entryVal (Sum.inr p) ω : ℂ)) ^ (s + t) *
              swapK (symOfEntries (zeroEntry (Sum.inr p) ω)) p
                ((N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 20)) 2 (2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 20)) k s t
          else 0‖ ≤
      (N : ℝ) ^ (-(5 : ℝ) / 3 - 2 / 5 + C * (1 / 20)) ∧
    ‖((offWard (symOfEntries ω) ⟨2, (N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 20)⟩ -
          offWard (symOfEntries (zeroEntry (Sum.inr p) ω))
            ⟨2, (N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 20)⟩ : ℝ) : ℂ) -
        ∑ k ∈ Finset.range 2, ∑ s ∈ Finset.range 5, ∑ t ∈ Finset.range 5,
          if 1 ≤ s + t ∧ s + t ≤ 4 then
            (-(entryVal (Sum.inr p) ω : ℂ)) ^ (s + t) *
              swapKpt (symOfEntries (zeroEntry (Sum.inr p) ω)) p
                ⟨2, (N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 20)⟩ k s t
          else 0‖ ≤
      (N : ℝ) ^ (-(5 : ℝ) / 3 - 2 / 5 + C * (1 / 20)) := by
  obtain ⟨C, hC, h⟩ := offWard_sub_eq_sum_swapK (φs := 2 / 5) (by norm_num) (by norm_num)
  obtain ⟨N0, hN0⟩ := h (1 / 20) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  filter_upwards [swapEvent_nonempty (ε := 1 / 20) (by norm_num) (by norm_num),
    eventually_ge_atTop (max N0 4)] with N ⟨ω, hω⟩ hN
  have h4 : 4 ≤ N := le_trans (le_max_right _ _) hN
  let p : OffDiag N := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.lt_def]⟩
  have hr : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 20) := Real.rpow_pos_of_pos (by positivity) _
  have hE₁ : |(2 : ℝ) - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 20) := by
    rw [sub_self, abs_zero]; exact hr.le
  have hE₂ : |(2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 20)) - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 20) := by
    rw [add_sub_cancel_left, abs_of_pos hr]
  have hk := hN0 N (le_trans (le_max_left _ _) hN) ω p (hω _)
  exact ⟨h4, ω, p, hω _, by linarith, hk.1 _ _ hE₁ hE₂, hk.2 _ hE₁⟩

#print axioms resolventC_eq_sum_swapCoeff
#print axioms norm_mul_entryMat_pow_mul_apply_le
#print axioms offWardInt_eq_sum_part
#print axioms abs_offWardPart_sub_le
#print axioms offWard_sub_eq_sum_swapK

end WEdgeNS
