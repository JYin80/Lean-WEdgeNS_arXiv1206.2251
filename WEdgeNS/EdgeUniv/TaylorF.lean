import WEdgeNS.EdgeUniv.Smoothing

/-!
# Taylor expansions of test functions with polynomially bounded derivatives
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- Taylor's theorem with the Lagrange remainder in `iteratedDeriv` form: for `F` of class
`C^{n+1}` there is `ζ` between `x` and `y` with
`F y = Σ_{k ≤ n} F^{(k)}(x)(y - x)^k/k! + F^{(n+1)}(ζ)(y - x)^{n+1}/(n+1)!`. -/
theorem taylor_iteratedDeriv_lagrange {F : ℝ → ℝ} {n : ℕ} (hF : ContDiff ℝ (n + 1) F) (x y : ℝ) :
    ∃ ζ ∈ Set.uIcc x y, F y =
      (∑ k ∈ Finset.range (n + 1), iteratedDeriv k F x * (y - x) ^ k / (k.factorial : ℝ)) +
        iteratedDeriv (n + 1) F ζ * (y - x) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  rcases eq_or_ne x y with rfl | hxy
  · refine ⟨x, Set.left_mem_uIcc, ?_⟩
    rw [Finset.sum_eq_single_of_mem 0 (by simp)]
    · simp
    · intro k _ hk
      simp [zero_pow hk]
  · obtain ⟨ζ, hζ, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (f := F) (x := y) (x₀ := x)
      (n := n) hxy hF.contDiffOn
    refine ⟨ζ, Set.uIoo_subset_uIcc_self hζ, ?_⟩
    rw [taylor_within_apply] at h
    have hk : ∀ k : ℕ, k ≤ n → iteratedDerivWithin k F (Set.uIcc x y) x = iteratedDeriv k F x :=
      fun k hkn => iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hxy)
        ((hF.contDiffAt).of_le (by exact_mod_cast Nat.le_succ_of_le hkn)) Set.left_mem_uIcc
    have hsum : ∑ k ∈ Finset.range (n + 1),
        (((k.factorial : ℝ)⁻¹ * (y - x) ^ k) • iteratedDerivWithin k F (Set.uIcc x y) x) =
        ∑ k ∈ Finset.range (n + 1), iteratedDeriv k F x * (y - x) ^ k / (k.factorial : ℝ) := by
      refine Finset.sum_congr rfl fun k hk' => ?_
      rw [hk k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk')), smul_eq_mul]
      ring
    rw [hsum] at h
    linarith

/-- (3.35): `F y = F x + F′(x)(y - x) + ½ F″(ζ)(y - x)²` for `F ∈ C⁴`. -/
theorem taylor_second {F : ℝ → ℝ} (hF : ContDiff ℝ 4 F) (x y : ℝ) :
    ∃ ζ ∈ Set.uIcc x y, F y =
      F x + iteratedDeriv 1 F x * (y - x) + iteratedDeriv 2 F ζ * (y - x) ^ 2 / 2 := by
  obtain ⟨ζ, hζ, h⟩ := taylor_iteratedDeriv_lagrange (n := 1) (hF.of_le (by norm_cast)) x y
  refine ⟨ζ, hζ, ?_⟩
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  rw [iteratedDeriv_one]
  linarith

/-- [16] (6.48): `F y = F x + F′(x)(y - x) + ½ F″(x)(y - x)² + (1/6) F‴(ζ)(y - x)³` for `F ∈ C⁴`. -/
theorem taylor_third {F : ℝ → ℝ} (hF : ContDiff ℝ 4 F) (x y : ℝ) :
    ∃ ζ ∈ Set.uIcc x y, F y =
      F x + iteratedDeriv 1 F x * (y - x) + iteratedDeriv 2 F x * (y - x) ^ 2 / 2 +
        iteratedDeriv 3 F ζ * (y - x) ^ 3 / 6 := by
  obtain ⟨ζ, hζ, h⟩ := taylor_iteratedDeriv_lagrange (n := 2) (hF.of_le (by norm_cast)) x y
  refine ⟨ζ, hζ, ?_⟩
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  rw [iteratedDeriv_one]
  linarith

/-- Third-order Taylor polynomial with the remainder `F⁗(ζ)(y - x)⁴/24`, `F ∈ C⁴`. -/
theorem taylor_fourth {F : ℝ → ℝ} (hF : ContDiff ℝ 4 F) (x y : ℝ) :
    ∃ ζ ∈ Set.uIcc x y, F y =
      F x + iteratedDeriv 1 F x * (y - x) + iteratedDeriv 2 F x * (y - x) ^ 2 / 2 +
        iteratedDeriv 3 F x * (y - x) ^ 3 / 6 + iteratedDeriv 4 F ζ * (y - x) ^ 4 / 24 := by
  obtain ⟨ζ, hζ, h⟩ := taylor_iteratedDeriv_lagrange (n := 3) (hF.of_le (by norm_cast)) x y
  refine ⟨ζ, hζ, ?_⟩
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  rw [iteratedDeriv_one]
  linarith

/-- Growth of the derivatives at an intermediate point, from the form (3.16)/(5.12) of the
hypothesis: `|F^{(n)}| ≤ CF (1 + |x|)^CF` for `n = 1, …, 4` and `|ζ| ≤ B` give
`|F^{(n)}(ζ)| ≤ CF (1 + B)^CF`. -/
theorem abs_iteratedDeriv_le_of_abs_le {F : ℝ → ℝ} {CF : ℝ}
    (hF : ∀ n ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF)
    {B ζ : ℝ} (hζ : |ζ| ≤ B) :
    ∀ n ∈ Finset.Icc 1 4, |iteratedDeriv n F ζ| ≤ CF * (1 + B) ^ CF := by
  intro n hn
  have h0 : 0 ≤ CF := by
    have := hF 1 (by simp) 0
    simpa using (abs_nonneg _).trans this
  calc |iteratedDeriv n F ζ| ≤ CF * (1 + |ζ|) ^ CF := hF n hn ζ
    _ ≤ CF * (1 + B) ^ CF := by gcongr

/-- The same bound for `B = r^a` (`r ≥ 1` stands for `N`): `|F^{(n)}(ζ)| ≤ CF 2^CF r^{a CF}`. -/
theorem abs_iteratedDeriv_le_rpow {F : ℝ → ℝ} {CF a r : ℝ}
    (hF : ∀ n ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF)
    (ha : 0 ≤ a) (hr : 1 ≤ r) {ζ : ℝ} (hζ : |ζ| ≤ r ^ a) :
    ∀ n ∈ Finset.Icc 1 4, |iteratedDeriv n F ζ| ≤ CF * 2 ^ CF * r ^ (a * CF) := by
  intro n hn
  have h0 : 0 ≤ CF := by
    have := hF 1 (by simp) 0
    simpa using (abs_nonneg _).trans this
  have hr0 : 0 < r := by linarith
  have hra : 1 ≤ r ^ a := Real.one_le_rpow hr ha
  calc |iteratedDeriv n F ζ| ≤ CF * (1 + r ^ a) ^ CF := (abs_iteratedDeriv_le_of_abs_le hF hζ) n hn
    _ ≤ CF * (2 * r ^ a) ^ CF := by gcongr; linarith
    _ = CF * 2 ^ CF * r ^ (a * CF) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hr0.le]; ring

/-- The `N^{Cε}` form of (3.36) and [16] (6.48): for `|ζ| ≤ N^{aε}` the derivatives are at most
`N^{(a CF + 1) ε}` once `N ≥ N0(CF, a, ε)`; `N0` does not depend on `F`. -/
theorem abs_iteratedDeriv_le_rpow_eps {CF a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ F : ℝ → ℝ,
      (∀ n ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF) →
      ∀ ζ : ℝ, |ζ| ≤ (N : ℝ) ^ (a * ε) →
        ∀ n ∈ Finset.Icc 1 4, |iteratedDeriv n F ζ| ≤ (N : ℝ) ^ ((a * CF + 1) * ε) := by
  refine ⟨⌈(CF * 2 ^ CF) ^ (1 / ε)⌉₊ + 1, fun N hN F hF ζ hζ n hn => ?_⟩
  have h0 : 0 ≤ CF := by
    have := hF 1 (by simp) 0
    simpa using (abs_nonneg _).trans this
  have hNr : (⌈(CF * 2 ^ CF) ^ (1 / ε)⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by
    have := Nat.cast_nonneg (α := ℝ) ⌈(CF * 2 ^ CF) ^ (1 / ε)⌉₊
    linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hM0 : 0 ≤ CF * 2 ^ CF := by positivity
  have hM : CF * 2 ^ CF ≤ (N : ℝ) ^ ε := by
    have h1 : (CF * 2 ^ CF) ^ (1 / ε) ≤ N := by
      have := Nat.le_ceil ((CF * 2 ^ CF) ^ (1 / ε))
      linarith
    have h2 := Real.rpow_le_rpow (by positivity) h1 hε.le
    rwa [← Real.rpow_mul hM0, one_div, inv_mul_cancel₀ hε.ne', Real.rpow_one] at h2
  have hb := abs_iteratedDeriv_le_rpow hF (mul_nonneg ha hε.le) hN1 hζ n hn
  calc |iteratedDeriv n F ζ| ≤ CF * 2 ^ CF * (N : ℝ) ^ (a * ε * CF) := hb
    _ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ (a * ε * CF) := by gcongr
    _ = (N : ℝ) ^ ((a * CF + 1) * ε) := by
      rw [← Real.rpow_add hN0]; congr 1; ring

/-- Taylor remainder bound under (3.16): for `|x|, |y| ≤ B` and `n ≤ 3`,
`|F y - Σ_{k ≤ n} F^{(k)}(x)(y - x)^k/k!| ≤ CF (1 + B)^CF |y - x|^{n+1}/(n+1)!`. -/
theorem taylor_remainder_le {F : ℝ → ℝ} {CF B : ℝ} (hF4 : ContDiff ℝ 4 F)
    (hF : ∀ n ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF)
    {x y : ℝ} (hx : |x| ≤ B) (hy : |y| ≤ B) {n : ℕ} (hn : n ≤ 3) :
    |F y - ∑ k ∈ Finset.range (n + 1), iteratedDeriv k F x * (y - x) ^ k / (k.factorial : ℝ)| ≤
      CF * (1 + B) ^ CF * |y - x| ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  obtain ⟨ζ, hζ, h⟩ := taylor_iteratedDeriv_lagrange (n := n)
    (hF4.of_le (by exact_mod_cast (show n + 1 ≤ 4 by omega))) x y
  have hζB : |ζ| ≤ B := by
    have hx' := abs_le.1 hx
    have hy' := abs_le.1 hy
    rcases Set.mem_uIcc.1 hζ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact abs_le.2 ⟨by linarith, by linarith⟩
  have hb := abs_iteratedDeriv_le_of_abs_le hF hζB (n + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have hfac : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
  rw [h, add_sub_cancel_left, abs_div, abs_mul, abs_pow, abs_of_pos hfac]
  gcongr

/-- The derivatives of `F = K(·/π)` at points `|ζ| ≤ B`: `|F^{(n)}(ζ)| ≤ CF (1 + B)^CF`,
`n = 1, …, 4`. -/
example : ∃ CF > 0, ∀ B : ℝ, ∀ ζ : ℝ, |ζ| ≤ B →
    ∀ n ∈ Finset.Icc 1 4, |iteratedDeriv n (fun x => edgeCutoff (x / Real.pi)) ζ| ≤
      CF * (1 + B) ^ CF := by
  obtain ⟨CF, hCF, h⟩ := edgeCutoff_deriv_le
  exact ⟨CF, hCF, fun B ζ hζ => abs_iteratedDeriv_le_of_abs_le h hζ⟩

/-- (3.35)-(3.36) for `F = K(·/π)`: for `|y_S|, |y_R| ≤ B`,
`|F(y_S) - F(y_R) - F′(y_R)(y_S - y_R)| ≤ CF (1 + B)^CF (y_S - y_R)²/2`. -/
example : ∃ CF > 0, ∀ B yS yR : ℝ, |yS| ≤ B → |yR| ≤ B →
    |edgeCutoff (yS / Real.pi) - edgeCutoff (yR / Real.pi) -
        iteratedDeriv 1 (fun x => edgeCutoff (x / Real.pi)) yR * (yS - yR)| ≤
      CF * (1 + B) ^ CF * |yS - yR| ^ 2 / 2 := by
  obtain ⟨CF, hCF, h⟩ := edgeCutoff_deriv_le
  have hF4 : ContDiff ℝ 4 (fun x => edgeCutoff (x / Real.pi)) :=
    (edgeBump.contDiff (n := 4)).comp (contDiff_id.div_const _)
  refine ⟨CF, hCF, fun B yS yR hS hR => ?_⟩
  have := taylor_remainder_le hF4 h hR hS (n := 1) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
  norm_num at this
  rw [iteratedDeriv_one, sq_abs]
  have e : edgeCutoff (yS / Real.pi) - edgeCutoff (yR / Real.pi) -
      deriv (fun x => edgeCutoff (x / Real.pi)) yR * (yS - yR) =
      edgeCutoff (yS / Real.pi) - (edgeCutoff (yR / Real.pi) +
        deriv (fun x => edgeCutoff (x / Real.pi)) yR * (yS - yR)) := by ring
  rw [e]
  exact this

/-- Taylor's formula with Lagrange remainder for `F x = x ^ 4` at `x = 1`, `y = 2`, `n = 3`. -/
example : ∃ ζ ∈ Set.uIcc (1 : ℝ) 2, (fun x : ℝ => x ^ 4) 2 =
    (fun x : ℝ => x ^ 4) 1 + iteratedDeriv 1 (fun x : ℝ => x ^ 4) 1 * (2 - 1) +
      iteratedDeriv 2 (fun x : ℝ => x ^ 4) 1 * (2 - 1) ^ 2 / 2 +
        iteratedDeriv 3 (fun x : ℝ => x ^ 4) 1 * (2 - 1) ^ 3 / 6 +
          iteratedDeriv 4 (fun x : ℝ => x ^ 4) ζ * (2 - 1) ^ 4 / 24 :=
  taylor_fourth (F := fun x : ℝ => x ^ 4) (by fun_prop) 1 2

/-- Taylor (`n = 3`, remainder `F⁗`) for `F(x) = x⁴` at `x = 1`, `y = 2` (every term nonzero). -/
example : ∃ ζ ∈ Set.uIcc (1 : ℝ) 2, (2 : ℝ) ^ 4 =
    (∑ k ∈ Finset.range 4, iteratedDeriv k (fun x : ℝ => x ^ 4) 1 * (2 - 1) ^ k / (k.factorial : ℝ)) +
      iteratedDeriv 4 (fun x : ℝ => x ^ 4) ζ * (2 - 1) ^ 4 / (4 : ℕ).factorial :=
  taylor_iteratedDeriv_lagrange (n := 3) (F := fun x : ℝ => x ^ 4)
    (by exact (contDiff_id.pow 4).of_le le_rfl) 1 2

/-- (3.35) for `F x = x ^ 4` at `x = 1`, `y = 2`. -/
example : ∃ ζ ∈ Set.uIcc (1 : ℝ) 2, (fun x : ℝ => x ^ 4) 2 =
    (fun x : ℝ => x ^ 4) 1 + iteratedDeriv 1 (fun x : ℝ => x ^ 4) 1 * (2 - 1) +
      iteratedDeriv 2 (fun x : ℝ => x ^ 4) ζ * (2 - 1) ^ 2 / 2 :=
  taylor_second (F := fun x : ℝ => x ^ 4) (by fun_prop) 1 2

/-- [16] (6.48) for `F x = x ^ 4` at `x = 1`, `y = 2`. -/
example : ∃ ζ ∈ Set.uIcc (1 : ℝ) 2, (fun x : ℝ => x ^ 4) 2 =
    (fun x : ℝ => x ^ 4) 1 + iteratedDeriv 1 (fun x : ℝ => x ^ 4) 1 * (2 - 1) +
      iteratedDeriv 2 (fun x : ℝ => x ^ 4) 1 * (2 - 1) ^ 2 / 2 +
        iteratedDeriv 3 (fun x : ℝ => x ^ 4) ζ * (2 - 1) ^ 3 / 6 :=
  taylor_third (F := fun x : ℝ => x ^ 4) (by fun_prop) 1 2

/-- The derivatives of `F = K(·/π)` at points `|ζ| ≤ 2^1`: `|F^{(n)}(ζ)| ≤ CF 2^CF 2^{1·CF}`,
`n = 1, …, 4`. -/
example : ∃ CF > 0, ∀ ζ : ℝ, |ζ| ≤ (2 : ℝ) ^ (1 : ℝ) →
    ∀ n ∈ Finset.Icc 1 4, |iteratedDeriv n (fun x => edgeCutoff (x / Real.pi)) ζ| ≤
      CF * 2 ^ CF * (2 : ℝ) ^ ((1 : ℝ) * CF) := by
  obtain ⟨CF, hCF, h⟩ := edgeCutoff_deriv_le
  exact ⟨CF, hCF, fun ζ hζ => abs_iteratedDeriv_le_rpow h (by norm_num) (by norm_num) hζ⟩

#print axioms taylor_iteratedDeriv_lagrange
#print axioms taylor_second
#print axioms taylor_third
#print axioms taylor_fourth
#print axioms abs_iteratedDeriv_le_of_abs_le
#print axioms abs_iteratedDeriv_le_rpow
#print axioms abs_iteratedDeriv_le_rpow_eps
#print axioms taylor_remainder_le

end WEdgeNS
