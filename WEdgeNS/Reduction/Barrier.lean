import WEdgeNS.Perturbation.FiniteRank
import WEdgeNS.Resolvent.Basic
import WEdgeNS.Model.LambdaMax
import WEdgeNS.Model.HighProb
import WEdgeNS.Model.General

/-!
# A barrier for the largest eigenvalue under a sparse perturbation
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- Number of nonzero entries `#{(i, j) : E_ij ≠ 0}`. -/
def nzCount {N : ℕ} (E : Matrix (Fin N) (Fin N) ℝ) : ℕ :=
  (Finset.univ.filter fun p : Fin N × Fin N => E p.1 p.2 ≠ 0).card

/-- The support pattern after (4.25): two nonzero entries sit on equal or disjoint index
pairs. -/
def PairPattern {N : ℕ} (E : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ i j k l, E i j ≠ 0 → E k l ≠ 0 →
    ({i, j} : Finset (Fin N)) = {k, l} ∨ Disjoint ({i, j} : Finset (Fin N)) {k, l}

/-- At a real point `μ ∉ spec(H)` the resolvent is the entrywise cast of `(H - μ)⁻¹`. -/
private lemma barrier_resolventC_eq {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {μ : ℝ}
    (hdet : (H - μ • (1 : Matrix (Fin N) (Fin N) ℝ)).det ≠ 0) :
    resolventC H (μ : ℂ) = ((H - μ • (1 : Matrix (Fin N) (Fin N) ℝ))⁻¹).map (algebraMap ℝ ℂ) := by
  unfold resolventC
  have h1 : H.map (fun x : ℝ => (x : ℂ)) - (μ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) =
      (H - μ • (1 : Matrix (Fin N) (Fin N) ℝ)).map (algebraMap ℝ ℂ) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    split_ifs <;> simp
  rw [h1]
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/-- Under `PairPattern`, a row with a nonzero entry at `j` has no other nonzero entry. -/
private lemma barrier_eq_of_ne_zero {N : ℕ} {E : Matrix (Fin N) (Fin N) ℝ}
    (hpat : PairPattern E) {k j l : Fin N} (hj : E k j ≠ 0) (hl : E k l ≠ 0) : l = j := by
  rcases hpat k j k l hj hl with h | h
  · have hl' : l ∈ ({k, j} : Finset (Fin N)) := by rw [h]; simp
    have hj' : j ∈ ({k, l} : Finset (Fin N)) := by rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl' hj'
    rcases hl' with h1 | h1
    · rcases hj' with h2 | h2
      · rw [h1, h2]
      · exact h2.symm
    · exact h1
  · exact absurd (Finset.disjoint_left.mp h (by simp : k ∈ ({k, j} : Finset (Fin N))))
      (by simp)

open Classical in
/-- The touched indices number at most `nzCount E`. -/
private lemma barrier_card_touched_le {N : ℕ} (E : Matrix (Fin N) (Fin N) ℝ) :
    (Finset.univ.filter fun i : Fin N => ∃ k, E i k ≠ 0).card ≤ nzCount E := by
  unfold nzCount
  refine (Finset.card_le_card (t := Finset.image Prod.fst _) ?_).trans Finset.card_image_le
  intro i hi
  obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hi).2
  exact Finset.mem_image.mpr ⟨(i, k), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, rfl⟩

/-- (4.27)–(4.37) and (4.46), zero entries of `E` dropped: if the resolvent of `H` at the
real point `μ` satisfies `|G_ii + 1| ≤ a` and `|G_ij| ≤ b` on the indices touched by `E`, and
the Gershgorin condition holds, then `μ ∉ spec(H + γE)` for every `γ ∈ (0, 1]`. -/
theorem not_mem_spectrum_add_smul_of_resolvent {N : ℕ} {H E : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (hE : E.IsHermitian) (hpat : PairPattern E) {μ κ a b : ℝ}
    (hμ : μ ∉ spectrum ℝ H) (hκ0 : 0 < κ) (hκ : ∀ i j, |E i j| ≤ κ) (hb : 0 ≤ b)
    (hdiag : ∀ i, (∃ k, E i k ≠ 0) → ‖resolventC H (μ : ℂ) i i + 1‖ ≤ a)
    (hoff : ∀ i j, (∃ k, E i k ≠ 0) → (∃ k, E j k ≠ 0) → i ≠ j →
      ‖resolventC H (μ : ℂ) i j‖ ≤ b)
    (hgersh : a + 2 * nzCount E * b < κ⁻¹ - 1 - a - b) :
    ∀ γ ∈ Set.Ioc (0 : ℝ) 1, μ ∉ spectrum ℝ (H + γ • E) := by
  intro γ hγ hmem
  classical
  set A := H - μ • (1 : Matrix (Fin N) (Fin N) ℝ) with hA
  have hdetA : A.det ≠ 0 := fun h => hμ (mem_spectrum_iff_det_eq_zero.mpr h)
  set G := A⁻¹ with hG
  have hGA : G * A = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdetA)
  have hres := barrier_resolventC_eq hdetA
  have hGd : ∀ i, (∃ k, E i k ≠ 0) → |G i i + 1| ≤ a := by
    intro i hi
    have h := hdiag i hi
    rw [hres, Matrix.map_apply] at h
    have h2 : (algebraMap ℝ ℂ (G i i) + 1) = ((G i i + 1 : ℝ) : ℂ) := by
      simp [Complex.ofReal_add]
    rwa [h2, Complex.norm_real, Real.norm_eq_abs] at h
  have hGo : ∀ i j, (∃ k, E i k ≠ 0) → (∃ k, E j k ≠ 0) → i ≠ j → |G i j| ≤ b := by
    intro i j hi hj hij
    have h := hoff i j hi hj hij
    rw [hres, Matrix.map_apply] at h
    rwa [Complex.coe_algebraMap, Complex.norm_real, Real.norm_eq_abs] at h
  obtain ⟨x, hx0, hx⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr (mem_spectrum_iff_det_eq_zero.mp hmem)
  set y := E *ᵥ x with hy
  have hAx : A *ᵥ x = -(γ • y) := by
    have h : (H + γ • E - μ • (1 : Matrix (Fin N) (Fin N) ℝ)) *ᵥ x = A *ᵥ x + γ • y := by
      rw [hA, hy, sub_mulVec, add_mulVec, sub_mulVec, smul_mulVec]
      abel
    rw [h] at hx
    exact eq_neg_of_add_eq_zero_left hx
  have hxG : x = -(γ • (G *ᵥ y)) := by
    have h := congrArg (G *ᵥ ·) hAx
    simp only [mulVec_mulVec, hGA, one_mulVec, mulVec_neg, mulVec_smul] at h
    exact h
  set r := (G + 1) *ᵥ y with hr
  have hyE : ∀ k, y k = -(γ * ∑ l, E k l * (r l - y l)) := by
    intro k
    have h1 : y = -(γ • (E *ᵥ (G *ᵥ y))) := by
      conv_lhs => rw [hy, hxG]
      rw [mulVec_neg, mulVec_smul]
    have h2 : G *ᵥ y = r - y := by
      rw [hr, add_mulVec, one_mulVec]; abel
    rw [h2] at h1
    have := congrFun h1 k
    simpa [mulVec, dotProduct] using this
  have hy0 : y ≠ 0 := by
    intro h
    apply hx0
    rw [hxG, h, mulVec_zero, smul_zero, neg_zero]
  obtain ⟨k0, hk0⟩ := Function.ne_iff.mp hy0
  obtain ⟨i, -, himax⟩ := Finset.exists_max_image Finset.univ (fun k => |y k|)
    ⟨k0, Finset.mem_univ _⟩
  set Mx := |y i| with hMx
  have hMpos : 0 < Mx := lt_of_lt_of_le (abs_pos.mpr hk0) (himax k0 (Finset.mem_univ _))
  have htouch : ∀ k, y k ≠ 0 → ∃ l, E k l ≠ 0 := by
    intro k hk
    by_contra hcon
    push Not at hcon
    apply hk
    rw [hy, mulVec, dotProduct]
    exact Finset.sum_eq_zero fun l _ => by rw [hcon l, zero_mul]
  have hiT : ∃ l, E i l ≠ 0 := htouch i (abs_pos.mp hMpos)
  have ha : 0 ≤ a := (abs_nonneg _).trans (hGd i hiT)
  set m : ℝ := (nzCount E : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  set ρ := a + b * m with hρ
  have hr_le : ∀ k, (∃ l, E k l ≠ 0) → |r k| ≤ ρ * Mx := by
    intro k hk
    have hterm : ∀ l, |(G + 1) k l * y l| ≤
        (if l = k then a * Mx else 0) + (if (∃ q, E l q ≠ 0) then b * Mx else 0) := by
      intro l
      rw [abs_mul]
      have hyl : |y l| ≤ Mx := himax l (Finset.mem_univ _)
      by_cases hlk : l = k
      · subst hlk
        simp only [↓reduceIte, hk, Matrix.add_apply, Matrix.one_apply_eq]
        nlinarith [hGd l hk, abs_nonneg (y l), abs_nonneg (G l l + 1), mul_nonneg hb hMpos.le]
      · simp only [hlk, ↓reduceIte, zero_add]
        by_cases hlT : ∃ q, E l q ≠ 0
        · simp only [hlT, ↓reduceIte, Matrix.add_apply, Matrix.one_apply_ne (Ne.symm hlk),
            add_zero]
          nlinarith [hGo k l hk hlT (Ne.symm hlk), abs_nonneg (y l), abs_nonneg (G k l)]
        · simp only [hlT, ↓reduceIte]
          have : y l = 0 := by
            by_contra h; exact hlT (htouch l h)
          rw [this, abs_zero, mul_zero]
    calc |r k| = |∑ l, (G + 1) k l * y l| := by rw [hr, mulVec, dotProduct]
      _ ≤ ∑ l, |(G + 1) k l * y l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l, ((if l = k then a * Mx else 0) +
            (if (∃ q, E l q ≠ 0) then b * Mx else 0)) := Finset.sum_le_sum fun l _ => hterm l
      _ = a * Mx + ((Finset.univ.filter fun l : Fin N => ∃ q, E l q ≠ 0).card : ℝ) * (b * Mx) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ k]
        simp only [Finset.mem_univ, ↓reduceIte]
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ a * Mx + m * (b * Mx) := by
        have hcard : ((Finset.univ.filter fun l : Fin N => ∃ q, E l q ≠ 0).card : ℝ) ≤ m := by
          rw [hm]; exact_mod_cast barrier_card_touched_le E
        linarith [mul_le_mul_of_nonneg_right hcard (mul_nonneg hb hMpos.le)]
      _ = ρ * Mx := by rw [hρ]; ring
  have hρ0 : 0 ≤ ρ := by positivity
  -- key inequality `1 - t ≤ t ρ` with `t = γ |E i j|`
  obtain ⟨j, hj⟩ := hiT
  have hrow : ∀ {k l}, E k l ≠ 0 → y k = -(γ * (E k l * (r l - y l))) := by
    intro k l hkl
    rw [hyE k, Finset.sum_eq_single l]
    · intro q _ hq
      by_cases hq' : E k q = 0
      · rw [hq', zero_mul]
      · exact absurd (barrier_eq_of_ne_zero hpat hkl hq') hq
    · simp
  set t := γ * |E i j| with ht
  have ht0 : 0 ≤ t := mul_nonneg hγ.1.le (abs_nonneg _)
  have htκ : t ≤ κ := by
    calc t ≤ 1 * κ := mul_le_mul hγ.2 (hκ i j) (abs_nonneg _) zero_le_one
      _ = κ := one_mul κ
  have hkey : 1 - t ≤ t * ρ := by
    have hri := hr_le i ⟨j, hj⟩
    by_cases hij : j = i
    · subst hij
      have h := hrow hj
      have h1 : y j * (1 - γ * E j j) = -(γ * E j j) * r j := by linarith
      have h2 : Mx * |1 - γ * E j j| = t * |r j| := by
        rw [hMx, ← abs_mul, h1, abs_mul, abs_neg, abs_mul, abs_of_pos hγ.1, ht]
      have h3 : 1 - t ≤ |1 - γ * E j j| := by
        have := abs_sub_abs_le_abs_sub (1 : ℝ) (γ * E j j)
        rw [abs_one, abs_mul, abs_of_pos hγ.1] at this
        linarith
      have h4 : Mx * (1 - t) ≤ Mx * (t * ρ) := by
        calc Mx * (1 - t) ≤ Mx * |1 - γ * E j j| := mul_le_mul_of_nonneg_left h3 hMpos.le
          _ = t * |r j| := h2
          _ ≤ t * (ρ * Mx) := mul_le_mul_of_nonneg_left hri ht0
          _ = Mx * (t * ρ) := by ring
      exact le_of_mul_le_mul_left h4 hMpos
    · have hji : E j i = E i j := by
        have := hE.apply i j
        simpa using this
      have hji0 : E j i ≠ 0 := by rw [hji]; exact hj
      have hrj := hr_le j ⟨i, hji0⟩
      have hyi := hrow hj
      have hyj := hrow hji0
      rw [hji] at hyj
      set e := E i j with he
      have h1 : y i * (1 - (γ * e) ^ 2) = -(γ * e) * r j - (γ * e) ^ 2 * r i := by
        rw [hyj] at hyi
        linear_combination hyi
      have hte : |γ * e| = t := by rw [abs_mul, abs_of_pos hγ.1]
      have h2 : Mx * |1 - (γ * e) ^ 2| ≤ t * |r j| + t ^ 2 * |r i| := by
        rw [hMx, ← abs_mul, h1]
        refine (abs_sub _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_neg, hte, abs_mul, abs_pow, hte]
      have h3 : 1 - t ^ 2 ≤ |1 - (γ * e) ^ 2| := by
        have := abs_sub_abs_le_abs_sub (1 : ℝ) ((γ * e) ^ 2)
        rw [abs_one, abs_pow, hte] at this
        linarith
      have h4 : Mx * (1 + t) * (1 - t) ≤ Mx * (1 + t) * (t * ρ) := by
        have e1 : Mx * (1 - t ^ 2) ≤ Mx * |1 - (γ * e) ^ 2| :=
          mul_le_mul_of_nonneg_left h3 hMpos.le
        have e2 : t * |r j| ≤ t * (ρ * Mx) := mul_le_mul_of_nonneg_left hrj ht0
        have e3 : t ^ 2 * |r i| ≤ t ^ 2 * (ρ * Mx) :=
          mul_le_mul_of_nonneg_left hri (sq_nonneg t)
        nlinarith
      exact le_of_mul_le_mul_left h4 (mul_pos hMpos (by linarith))
  have hfin : κ * (1 + ρ) < 1 := by
    have h1 : 1 + ρ < κ⁻¹ := by
      rw [hρ]
      nlinarith [mul_nonneg hb hm0]
    calc κ * (1 + ρ) < κ * κ⁻¹ := mul_lt_mul_of_pos_left h1 hκ0
      _ = 1 := mul_inv_cancel₀ hκ0.ne'
  nlinarith [mul_le_mul_of_nonneg_right htκ (by linarith : (0 : ℝ) ≤ 1 + ρ)]

/-- Upper half of (4.26) by a one-sided barrier: `λ_N(H + E) < λ_N(H) + N^{-3/4}`. -/
theorem lambdaMax_add_lt_barrier {N : ℕ} [NeZero N] {H E : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (hE : E.IsHermitian) (hpat : PairPattern E) {κ a b : ℝ}
    (hκ0 : 0 < κ) (hκ : ∀ i j, |E i j| ≤ κ) (hb : 0 ≤ b)
    (hdiag : ∀ i, (∃ k, E i k ≠ 0) →
      ‖resolventC H ((lambdaMax H + (N : ℝ) ^ (-(3 : ℝ) / 4) : ℝ) : ℂ) i i + 1‖ ≤ a)
    (hoff : ∀ i j, (∃ k, E i k ≠ 0) → (∃ k, E j k ≠ 0) → i ≠ j →
      ‖resolventC H ((lambdaMax H + (N : ℝ) ^ (-(3 : ℝ) / 4) : ℝ) : ℂ) i j‖ ≤ b)
    (hgersh : a + 2 * nzCount E * b < κ⁻¹ - 1 - a - b) :
    lambdaMax (H + E) < lambdaMax H + (N : ℝ) ^ (-(3 : ℝ) / 4) := by
  have hpos : (0 : ℝ) < (N : ℝ) ^ (-(3 : ℝ) / 4) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))) _
  have hlt : lambdaMax H < lambdaMax H + (N : ℝ) ^ (-(3 : ℝ) / 4) := by linarith
  have hμ : lambdaMax H + (N : ℝ) ^ (-(3 : ℝ) / 4) ∉ spectrum ℝ H := by
    rw [hH.spectrum_real_eq_range_eigenvalues]
    rintro ⟨α, hα⟩
    have := (lambdaMax_isGreatest hH).2 ⟨α, rfl⟩
    linarith
  exact lambdaMax_add_lt_of_barrier hH hE hlt
    (not_mem_spectrum_add_smul_of_resolvent hH hE hpat hμ hκ0 hκ hb hdiag hoff hgersh)

/-- Rayleigh bound with delocalization (3.5): `λ_N(H + E) ≥ λ_N(H) - κ · #supp(E) · φ^C/N`. -/
theorem lambdaMax_sub_le_lambdaMax_add {N : ℕ} [NeZero N] {H E : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (hE : E.IsHermitian) {C κ : ℝ}
    (hdeloc : ∀ (v : Fin N → ℝ) (μ : ℝ), H *ᵥ v = μ • v → ∑ i, v i ^ 2 = 1 →
      ∀ i, v i ^ 2 ≤ phi N ^ C / N)
    (hκ : ∀ i j, |E i j| ≤ κ) :
    lambdaMax H - κ * nzCount E * (phi N ^ C / N) ≤ lambdaMax (H + E) := by
  obtain ⟨α, hα⟩ := (lambdaMax_isGreatest hH).1
  set u : Fin N → ℝ := ⇑(hH.eigenvectorBasis α) with hu
  have hHu : H *ᵥ u = lambdaMax H • u := by
    rw [← hα]; exact hH.mulVec_eigenvectorBasis α
  have hnorm := hH.eigenvectorBasis.orthonormal.1 α
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at hnorm
  have hu1 : ∑ i, u i ^ 2 = 1 := by
    rw [← hnorm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
  have huu : u ⬝ᵥ u = 1 := by
    rw [← hu1, dotProduct]
    exact Finset.sum_congr rfl fun i _ => (sq (u i)).symm
  have h1 := lambdaMax_add_dotProduct_le hH hE huu hHu
  have h2 := neg_le_dotProduct_mulVec hκ (hdeloc u (lambdaMax H) hHu hu1)
  unfold nzCount
  linarith

/-! ### Compiled checks at concrete nondegenerate points

Barrier: `N = 2`, `H = [[0, 1/4], [1/4, 0]]`, `E = [[0, 1/3], [1/3, 0]]` (one off-diagonal pair),
`μ = 1`, `κ = 1/3`, `a = 1/15`, `b = 4/15`, where `(H - 1)⁻¹ = [[-16/15, -4/15], [-4/15, -16/15]]`.
Rayleigh bound: `N = 2`, `H = [[0, 1], [1, 0]]`, `E = [[0, -1/2], [-1/2, 0]]`, `κ = 1/2`, `C = 0`;
every unit eigenvector of `H` has `v_i² = 1/2`. -/

private def barrierH : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1 / 4; 1 / 4, 0]

private def barrierE : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1 / 3; 1 / 3, 0]

private lemma barrierH_isHermitian : barrierH.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [barrierH]

private lemma barrierE_isHermitian : barrierE.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [barrierE]

private lemma barrierE_pairPattern : PairPattern barrierE := by
  intro i j k l hij hkl
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [barrierE] at hij hkl ⊢ <;> decide

private lemma barrierE_nzCount : nzCount barrierE = 2 := by
  unfold nzCount
  have h : (Finset.univ.filter fun p : Fin 2 × Fin 2 => barrierE p.1 p.2 ≠ 0) =
      {((0 : Fin 2), (1 : Fin 2)), ((1 : Fin 2), (0 : Fin 2))} := by
    ext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [barrierE]
  rw [h]
  decide

private lemma barrierH_not_mem_spectrum : (1 : ℝ) ∉ spectrum ℝ barrierH := by
  rw [mem_spectrum_iff_det_eq_zero, Matrix.det_fin_two]
  simp [barrierH]
  norm_num

private lemma resolventC_barrierH :
    resolventC barrierH ((1 : ℝ) : ℂ) = !![-16 / 15, -4 / 15; -4 / 15, -16 / 15] := by
  unfold resolventC
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [barrierH, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> norm_num

example : ∀ γ ∈ Set.Ioc (0 : ℝ) 1, (1 : ℝ) ∉ spectrum ℝ (barrierH + γ • barrierE) := by
  refine not_mem_spectrum_add_smul_of_resolvent (κ := 1 / 3) (a := 1 / 15) (b := 4 / 15)
    barrierH_isHermitian barrierE_isHermitian barrierE_pairPattern barrierH_not_mem_spectrum
    (by norm_num) ?_ (by norm_num) ?_ ?_ ?_
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [barrierE]
  · intro i _
    rw [resolventC_barrierH]
    have h : (-16 / 15 + 1 : ℂ) = ((-1 / 15 : ℝ) : ℂ) := by push_cast; ring
    fin_cases i <;> simp <;> rw [h, Complex.norm_real] <;> norm_num [abs_of_neg]
  · intro i j _ _ hij
    rw [resolventC_barrierH]
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · rw [barrierE_nzCount]
    norm_num

private def rayleighH : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

private def rayleighE : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1 / 2; -1 / 2, 0]

private lemma rayleighH_isHermitian : rayleighH.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rayleighH]

private lemma rayleighE_isHermitian : rayleighE.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rayleighE]

private lemma rayleighH_deloc : ∀ (v : Fin 2 → ℝ) (μ : ℝ), rayleighH *ᵥ v = μ • v →
    ∑ i, v i ^ 2 = 1 → ∀ i, v i ^ 2 ≤ phi 2 ^ (0 : ℝ) / (2 : ℕ) := by
  intro v μ hv hsum i
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  simp [rayleighH, mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  rw [Fin.sum_univ_two] at hsum
  have hsq : v 0 ^ 2 = v 1 ^ 2 := by linear_combination (-v 1) * h0 + v 0 * h1
  rw [Real.rpow_zero]
  fin_cases i <;> simp <;> nlinarith

example : lambdaMax rayleighH - 1 / 2 * nzCount rayleighE * (phi 2 ^ (0 : ℝ) / (2 : ℕ)) ≤
    lambdaMax (rayleighH + rayleighE) := by
  refine lambdaMax_sub_le_lambdaMax_add rayleighH_isHermitian rayleighE_isHermitian
    rayleighH_deloc ?_
  intro i j
  fin_cases i <;> fin_cases j <;> simp [rayleighE] <;> norm_num

/-! Barrier at the edge point: `N = 2`, `H = 0` (so `λ_N(H) = 0` and `G = -2^{3/4}`),
`E = [[0, 1/10], [1/10, 0]]`, `κ = 1/10`, `a = 1`, `b = 1/10`, where the Gershgorin condition
reads `1.4 < 7.9`. -/

private def barrierMaxE : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1 / 10; 1 / 10, 0]

private lemma barrierMaxE_isHermitian : barrierMaxE.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [barrierMaxE]

private lemma barrierMaxE_pairPattern : PairPattern barrierMaxE := by
  intro i j k l hij hkl
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [barrierMaxE] at hij hkl ⊢ <;> decide

private lemma barrierMaxE_nzCount : nzCount barrierMaxE = 2 := by
  unfold nzCount
  have h : (Finset.univ.filter fun p : Fin 2 × Fin 2 => barrierMaxE p.1 p.2 ≠ 0) =
      {((0 : Fin 2), (1 : Fin 2)), ((1 : Fin 2), (0 : Fin 2))} := by
    ext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [barrierMaxE]
  rw [h]
  decide

private lemma barrier_lambdaMax_zero_two : lambdaMax (0 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  unfold lambdaMax
  rw [spectrum.zero_eq, csSup_singleton]

private lemma barrier_resolventC_zero_two {t : ℝ} (ht : t ≠ 0) :
    resolventC (0 : Matrix (Fin 2) (Fin 2) ℝ) (t : ℂ) = (-(t : ℂ)⁻¹) • 1 := by
  unfold resolventC
  apply Matrix.inv_eq_right_inv
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have h0 : (0 : Matrix (Fin 2) (Fin 2) ℝ).map (fun x : ℝ => (x : ℂ)) = 0 := by
    ext i j
    simp
  rw [h0, zero_sub, ← neg_smul, smul_mul_smul_comm, mul_one, neg_mul_neg,
    mul_inv_cancel₀ ht', one_smul]

example : lambdaMax ((0 : Matrix (Fin 2) (Fin 2) ℝ) + barrierMaxE) <
    lambdaMax (0 : Matrix (Fin 2) (Fin 2) ℝ) + ((2 : ℕ) : ℝ) ^ (-(3 : ℝ) / 4) := by
  have ht0 : (0 : ℝ) < (2 : ℝ) ^ (-(3 : ℝ) / 4) := by positivity
  have ht1 : (2 : ℝ) ^ (-(3 : ℝ) / 4) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have ht2 : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(3 : ℝ) / 4) := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
      (show (-1 : ℝ) ≤ -(3 : ℝ) / 4 by norm_num)
    rwa [Real.rpow_neg_one, ← one_div] at h
  have hG : resolventC (0 : Matrix (Fin 2) (Fin 2) ℝ)
      ((lambdaMax (0 : Matrix (Fin 2) (Fin 2) ℝ) + ((2 : ℕ) : ℝ) ^ (-(3 : ℝ) / 4) : ℝ) : ℂ) =
      (-(((2 : ℝ) ^ (-(3 : ℝ) / 4) : ℝ) : ℂ)⁻¹) • 1 := by
    rw [barrier_lambdaMax_zero_two, zero_add, Nat.cast_ofNat]
    exact barrier_resolventC_zero_two ht0.ne'
  refine lambdaMax_add_lt_barrier (κ := 1 / 10) (a := 1) (b := 1 / 10)
    (isHermitian_zero) barrierMaxE_isHermitian barrierMaxE_pairPattern
    (by norm_num) ?_ (by norm_num) ?_ ?_ ?_
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [barrierMaxE]
  · intro i _
    rw [hG]
    have h : (-(((2 : ℝ) ^ (-(3 : ℝ) / 4) : ℝ) : ℂ)⁻¹ + 1 : ℂ) =
        ((1 - ((2 : ℝ) ^ (-(3 : ℝ) / 4))⁻¹ : ℝ) : ℂ) := by push_cast; ring
    have hinv1 : 1 ≤ ((2 : ℝ) ^ (-(3 : ℝ) / 4))⁻¹ := one_le_inv_iff₀.mpr ⟨ht0, ht1⟩
    have hinv2 : ((2 : ℝ) ^ (-(3 : ℝ) / 4))⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ ht0 (by norm_num)]
      linarith
    simp only [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]
    rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  · intro i j _ _ hij
    rw [hG]
    simp [one_apply_ne hij]
  · rw [barrierMaxE_nzCount]
    norm_num

#print axioms nzCount
#print axioms PairPattern
#print axioms not_mem_spectrum_add_smul_of_resolvent
#print axioms lambdaMax_add_lt_barrier
#print axioms lambdaMax_sub_le_lambdaMax_add

end WEdgeNS
