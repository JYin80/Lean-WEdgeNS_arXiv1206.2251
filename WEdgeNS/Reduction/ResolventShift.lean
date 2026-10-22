import WEdgeNS.Resolvent.Basic
import WEdgeNS.Semicircle.Density
import WEdgeNS.Model.HighProb
import WEdgeNS.Model.LambdaMax

/-!
# The resolvent near the edge point
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- The point `z̃ = 2 + i N^{-2/3}` of (4.38). -/
def edgePt (N : ℕ) : ℂ := ⟨2, (N : ℝ) ^ (-(2 : ℝ) / 3)⟩

/-! ### The semicircle law near the upper edge -/

private lemma continuous_rhoSc' : Continuous rhoSc := by
  unfold rhoSc
  fun_prop

private lemma integrable_rhoSc' : Integrable rhoSc := by
  refine continuous_rhoSc'.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) fun x hx => ?_)
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  unfold rhoSc
  have : 4 - x ^ 2 ≤ 0 := by rcases hx with h | h <;> nlinarith
  rw [Real.sqrt_eq_zero'.mpr this, zero_div]

/-- `n_sc(b) - n_sc(a) = ∫_a^b ρ_sc`. -/
private lemma nsc_sub_nsc' (a b : ℝ) : nsc b - nsc a = ∫ x in a..b, rhoSc x :=
  intervalIntegral.integral_Iic_sub_Iic integrable_rhoSc'.integrableOn
    integrable_rhoSc'.integrableOn

/-- Near the upper edge, `1 - n_sc(γ) ≤ (2 - γ)^{3/2}`, from `ρ_sc(x) ≤ √(2 - γ)/π` for `x ≥ γ`. -/
private lemma one_sub_nsc_le {γ : ℝ} (hγ : γ ≤ 2) :
    1 - nsc γ ≤ (2 - γ) * Real.sqrt (2 - γ) := by
  have h := nsc_sub_nsc' γ 2
  rw [nsc_eq_one le_rfl] at h
  have hb : ∀ x ∈ Set.uIoc γ 2, ‖rhoSc x‖ ≤ Real.sqrt (2 - γ) := by
    intro x hx
    rw [Set.uIoc_of_le hγ] at hx
    have hpi := Real.pi_gt_three
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold rhoSc; positivity)]
    unfold rhoSc
    rw [div_le_iff₀ (by positivity)]
    have h1 : Real.sqrt (4 - x ^ 2) ≤ Real.sqrt (4 * (2 - γ)) :=
      Real.sqrt_le_sqrt (by nlinarith [hx.1, hx.2, sq_nonneg (x - 2)])
    have h2 : Real.sqrt (4 * (2 - γ)) = 2 * Real.sqrt (2 - γ) := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    have h3 := Real.sqrt_nonneg (2 - γ)
    nlinarith
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [← h, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 - γ)] at this
  linarith [le_abs_self (1 - nsc γ)]

/-- The classical locations lie at or below the upper edge. -/
private lemma gammaLoc_le_two {N k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) : gammaLoc N k ≤ 2 := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 := nsc_gammaLoc hk hkN
  rw [nsc_eq_one hlt.le] at h1
  have hN : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hk hkN)
  have hkN' : (k : ℝ) = N := by
    rw [eq_comm, div_eq_one_iff_eq hN.ne'] at h1
    exact h1
  have hkk : k = N := by exact_mod_cast hkN'
  subst hkk
  rw [gammaLoc_self hk] at hlt
  exact lt_irrefl _ hlt

/-- Edge asymptotics of the classical locations: with `m = N - (j + 1)` and
`g = 2 - γ_{j+1}`, `0 ≤ g` and `m / N ≤ g^{3/2}`. -/
private lemma edge_gap {N : ℕ} (j : Fin N) :
    0 ≤ 2 - gammaLoc N ((j : ℕ) + 1) ∧
      ((N - 1 - (j : ℕ) : ℕ) : ℝ) / N ≤
        (2 - gammaLoc N ((j : ℕ) + 1)) * Real.sqrt (2 - gammaLoc N ((j : ℕ) + 1)) := by
  have hj := j.isLt
  have hk : 1 ≤ (j : ℕ) + 1 := by omega
  have hkN : (j : ℕ) + 1 ≤ N := by omega
  have hg := gammaLoc_le_two hk hkN
  refine ⟨by linarith, ?_⟩
  have h1 := one_sub_nsc_le hg
  rw [nsc_gammaLoc hk hkN] at h1
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm : ((N - 1 - (j : ℕ) : ℕ) : ℝ) = N - (((j : ℕ) + 1 : ℕ) : ℝ) := by
    rw [show N - 1 - (j : ℕ) = N - ((j : ℕ) + 1) by omega, Nat.cast_sub hkN]
  rw [hm, sub_div, div_self hN.ne']
  exact h1

/-- Sums over the unordered eigenvalues equal sums over the increasing ones. -/
private lemma sum_eigenvalues_eq_sum_eigAsc {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (f : ℝ → ℝ) :
    ∑ α, f (hH.eigenvalues α) = ∑ j, f (eigAsc hH j) := by
  have e1 : ∑ α, f (hH.eigenvalues α) = ∑ k, f (hH.eigenvalues₀ k) :=
    Fintype.sum_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm _ _ (fun _ => rfl)
  rw [e1]
  exact (Fintype.sum_equiv (Fin.revPerm.trans (finCongr (Fintype.card_fin N).symm))
    (fun j => f (eigAsc hH j)) _ (fun _ => rfl)).symm

/-- `Σ_m (1 + m^{4/3})⁻¹ < ∞`. -/
private lemma summable_inv_one_add_rpow :
    Summable (fun m : ℕ => (1 + (m : ℝ) ^ ((4 : ℝ) / 3))⁻¹) := by
  rw [← summable_nat_add_iff 1]
  have hs : Summable (fun m : ℕ => (((m + 1 : ℕ) : ℝ) ^ ((4 : ℝ) / 3))⁻¹) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr (by norm_num))
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hs
  have hp : 0 < (((m + 1 : ℕ) : ℝ) ^ ((4 : ℝ) / 3)) := Real.rpow_pos_of_pos (by positivity) _
  exact inv_anti₀ hp (by linarith)

/-! ### Bounds on one term of (4.44)

Below, `u = N^{-1/12}`, so that `N^{-2/3} = u^8`, `N^{-3/4} = u^9`, `N^{-1/4} = u^3` and
`N⁻¹ = u^{12}`; `a = φ^C`. -/

/-- The bulk weight `(2 - x)^{-2}`, set to `0` on the window `|x - 2| ≤ b`. -/
private def bulkWt (b x : ℝ) : ℝ := if |x - 2| ≤ b then 0 else ((2 - x) ^ 2)⁻¹

/-- Below `λ_N ≤ 2 + a u^8`, a point outside the window `|x - 2| ≤ 2 a u^8` satisfies
`2 - x > 2 a u^8`. -/
private lemma two_sub_gt_of_not_near {a u lam l : ℝ} (hlam : lam - 2 ≤ a * u ^ 8)
    (hau : 0 < a * u ^ 8) (hl : l ≤ lam) (hnear : ¬ |l - 2| ≤ 2 * a * u ^ 8) :
    2 * a * u ^ 8 < 2 - l := by
  rw [not_le, lt_abs] at hnear
  rcases hnear with h | h
  · exfalso
    linarith
  · linarith

/-- One term of (4.44) at `μ̃ = λ_N + u^9`, `z̃ = 2 + i u^8`: it is at most `3 a² u³` in the
window `|λ_α - 2| ≤ 2 a u^8`, and at most `6 a² u^{20} (2 - λ_α)^{-2}` outside it. -/
private lemma norm_term_le {a u lam l w : ℝ} (ha1 : 1 ≤ a) (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hlam : |lam - 2| ≤ a * u ^ 8) (hl : l ≤ lam) (hw : |w| ≤ a * u ^ 12) :
    ‖(w : ℂ) * (((lam + u ^ 9 : ℝ) : ℂ) - ⟨2, u ^ 8⟩) /
        (((l : ℂ) - ((lam + u ^ 9 : ℝ) : ℂ)) * ((l : ℂ) - ⟨2, u ^ 8⟩))‖ ≤
      (if |l - 2| ≤ 2 * a * u ^ 8 then 3 * a ^ 2 * u ^ 3 else 0) +
        6 * a ^ 2 * u ^ 20 * bulkWt (2 * a * u ^ 8) l := by
  have hu8 : 0 < u ^ 8 := by positivity
  have hu9 : 0 < u ^ 9 := by positivity
  have hau8 : u ^ 8 ≤ a * u ^ 8 := le_mul_of_one_le_left hu8.le ha1
  have hlam' := abs_le.mp hlam
  have hX : ‖((lam + u ^ 9 : ℝ) : ℂ) - ⟨2, u ^ 8⟩‖ ≤ 3 * a * u ^ 8 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub,
      abs_neg, abs_of_pos hu8]
    have h98 : u ^ 9 ≤ u ^ 8 := pow_le_pow_of_le_one hu0.le hu1 (by norm_num)
    have : |lam + u ^ 9 - 2| ≤ |lam - 2| + u ^ 9 := by
      rw [show lam + u ^ 9 - 2 = (lam - 2) + u ^ 9 by ring]
      exact (abs_add_le _ _).trans (by rw [abs_of_pos hu9])
    linarith
  have hd : ‖(l : ℂ) - ((lam + u ^ 9 : ℝ) : ℂ)‖ = lam + u ^ 9 - l := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
      abs_of_pos (by linarith)]
  have hY1 : u ^ 8 ≤ ‖(l : ℂ) - ⟨2, u ^ 8⟩‖ := by
    have := Complex.abs_im_le_norm ((l : ℂ) - ⟨2, u ^ 8⟩)
    simpa [abs_of_pos hu8] using this
  have hY2 : |l - 2| ≤ ‖(l : ℂ) - ⟨2, u ^ 8⟩‖ := by
    have := Complex.abs_re_le_norm ((l : ℂ) - ⟨2, u ^ 8⟩)
    simpa using this
  rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hd]
  have hnum : |w| * ‖((lam + u ^ 9 : ℝ) : ℂ) - ⟨2, u ^ 8⟩‖ ≤ a * u ^ 12 * (3 * a * u ^ 8) :=
    mul_le_mul hw hX (norm_nonneg _) (by positivity)
  have hμl : u ^ 9 ≤ lam + u ^ 9 - l := by linarith
  unfold bulkWt
  split_ifs with hnear
  · rw [mul_zero, add_zero]
    calc _ ≤ a * u ^ 12 * (3 * a * u ^ 8) / (u ^ 9 * u ^ 8) :=
          div_le_div₀ (by positivity) hnum (by positivity)
            (mul_le_mul hμl hY1 hu8.le (by linarith))
      _ = 3 * a ^ 2 * u ^ 3 := by field_simp
  · have hs := two_sub_gt_of_not_near hlam'.2 (by positivity) hl hnear
    have h2a : 0 < 2 * a * u ^ 8 := by positivity
    have hs0 : 0 < 2 - l := by linarith
    have hdl : (2 - l) / 2 ≤ lam + u ^ 9 - l := by linarith
    have hY : 2 - l ≤ ‖(l : ℂ) - ⟨2, u ^ 8⟩‖ := by
      rw [abs_sub_comm, abs_of_pos hs0] at hY2
      exact hY2
    rw [zero_add]
    calc _ ≤ a * u ^ 12 * (3 * a * u ^ 8) / ((2 - l) / 2 * (2 - l)) :=
          div_le_div₀ (by positivity) hnum (by positivity)
            (mul_le_mul hdl hY hs0.le (by linarith))
      _ = 6 * a ^ 2 * u ^ 20 * ((2 - l) ^ 2)⁻¹ := by field_simp; ring

/-- The bulk weight of `λ_{k+1}`, from rigidity `|λ_{k+1} - γ_{k+1}| ≤ a u^8` and the edge
asymptotics of `γ_{k+1}`: with `m = N - (k + 1)`, it is at most `4 u^{-16} (1 + m^{4/3})⁻¹`. -/
private lemma bulkWt_eigAsc_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    (k : Fin N) {a u lam : ℝ} (ha1 : 1 ≤ a) (hu0 : 0 < u) (eN : (N : ℝ) * u ^ 12 = 1)
    (hlam : lam - 2 ≤ a * u ^ 8) (hlk : eigAsc hH k ≤ lam)
    (hr : |eigAsc hH k - gammaLoc N ((k : ℕ) + 1)| ≤ a * u ^ 8) :
    bulkWt (2 * a * u ^ 8) (eigAsc hH k) ≤
      4 / u ^ 16 * (1 + ((N - 1 - (k : ℕ) : ℕ) : ℝ) ^ ((4 : ℝ) / 3))⁻¹ := by
  have hu8 : 0 < u ^ 8 := by positivity
  have hau8 : u ^ 8 ≤ a * u ^ 8 := le_mul_of_one_le_left hu8.le ha1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N from Nat.zero_lt_of_lt k.isLt)
  unfold bulkWt
  split_ifs with hnear
  · positivity
  · have hs := two_sub_gt_of_not_near hlam (by positivity) hlk hnear
    have hr' := (abs_le.mp hr).2
    obtain ⟨hg0, hgm⟩ := edge_gap k
    set l := eigAsc hH k with hl_def
    set g := 2 - gammaLoc N ((k : ℕ) + 1) with hg_def
    set m := N - 1 - (k : ℕ) with hm_def
    set q := (m : ℝ) ^ ((2 : ℝ) / 3) with hq_def
    have hq0 : 0 ≤ q := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hq3 : q ^ 3 = (m : ℝ) ^ 2 := by
      rw [hq_def, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      norm_num
    have hq2 : q ^ 2 = (m : ℝ) ^ ((4 : ℝ) / 3) := by
      rw [hq_def, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      norm_num
    have hmN : (m : ℝ) / N = m * u ^ 12 := by
      rw [div_eq_iff hNpos.ne']
      calc (m : ℝ) = m * ((N : ℝ) * u ^ 12) := by rw [eN, mul_one]
        _ = m * u ^ 12 * N := by ring
    rw [hmN] at hgm
    have hcube : (q * u ^ 8) ^ 3 ≤ g ^ 3 := by
      have h1 : ((m : ℝ) * u ^ 12) ^ 2 ≤ (g * Real.sqrt g) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hgm 2
      calc (q * u ^ 8) ^ 3 = q ^ 3 * u ^ 24 := by ring
        _ = ((m : ℝ) * u ^ 12) ^ 2 := by rw [hq3]; ring
        _ ≤ (g * Real.sqrt g) ^ 2 := h1
        _ = g ^ 3 := by rw [mul_pow, Real.sq_sqrt hg0]; ring
    have hqg : q * u ^ 8 ≤ g :=
      (pow_le_pow_iff_left₀ (by positivity) hg0 (by norm_num)).mp hcube
    have hs1 : (1 + q) * u ^ 8 / 2 ≤ 2 - l := by
      have h1 : g ≤ (2 - l) + a * u ^ 8 := by rw [hg_def]; linarith
      have h2 : (1 + q) * u ^ 8 / 2 = u ^ 8 / 2 + q * u ^ 8 / 2 := by ring
      rw [h2]
      linarith
    have hpos : 0 < (1 + q) * u ^ 8 / 2 := by positivity
    rw [← hq2]
    calc ((2 - l) ^ 2)⁻¹ ≤ (((1 + q) * u ^ 8 / 2) ^ 2)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le hs1 2)
      _ = 4 / u ^ 16 * ((1 + q) ^ 2)⁻¹ := by field_simp; ring
      _ ≤ 4 / u ^ 16 * (1 + q ^ 2)⁻¹ := by
          gcongr
          nlinarith

/-- `x² ≤ c` and `y² ≤ c` give `|x y| ≤ c`. -/
private lemma abs_mul_le_of_sq_le {x y c : ℝ} (hx : x ^ 2 ≤ c) (hy : y ^ 2 ≤ c) :
    |x * y| ≤ c := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (x + y), sq_nonneg (x - y)]

/-- Each eigenvector `u_α` is a unit vector: `Σ_k u_α(k)² = 1`. -/
private lemma sum_sq_eigenvectorBasis_eq_one {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (α : Fin N) : ∑ k, hH.eigenvectorBasis α k ^ 2 = 1 := by
  have h1 := hH.eigenvectorBasis.orthonormal.1 α
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h1
  simpa [Real.norm_eq_abs, sq_abs] using h1

/-! ### (4.43)–(4.45) -/

/-- (4.44)–(4.45): under delocalization, the edge inputs (5.25)–(5.26) and
rigidity (3.12), `|G_ij(μ̃) - G_ij(z̃)| ≤ φ^{5C} N^{-1/4}` at `μ̃ = λ_N + N^{-3/4}`. -/
theorem norm_resolventC_barrier_sub_le {C : ℝ} (hC : 0 < C) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ H : Matrix (Fin N) (Fin N) ℝ, ∀ hH : H.IsHermitian,
      (∀ (v : Fin N → ℝ) (μ : ℝ), H *ᵥ v = μ • v → ∑ i, v i ^ 2 = 1 →
        ∀ i, v i ^ 2 ≤ phi N ^ C / N) →
      |(N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax H - 2)| ≤ phi N ^ C →
      ((Finset.univ.filter fun α => |hH.eigenvalues α - 2| ≤
          2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)).card : ℝ) ≤ phi N ^ (2 * C) →
      (∀ j : Fin N, |eigAsc hH j - gammaLoc N ((j : ℕ) + 1)| ≤
        phi N ^ C * (min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ))) ^ (-(1 : ℝ) / 3) *
          (N : ℝ) ^ (-(2 : ℝ) / 3)) →
      ∀ i j, ‖resolventC H ((lambdaMax H + (N : ℝ) ^ (-(3 : ℝ) / 4) : ℝ) : ℂ) i j -
        resolventC H (edgePt N) i j‖ ≤ phi N ^ (5 * C) * (N : ℝ) ^ (-(1 : ℝ) / 4) := by
  obtain ⟨K, hK0, hK⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ∑ m ∈ Finset.range n, (1 + (m : ℝ) ^ ((4 : ℝ) / 3))⁻¹ ≤ K :=
    ⟨_, tsum_nonneg (fun _ => by positivity),
      fun n => summable_inv_one_add_rpow.sum_le_tsum _ (fun _ _ => by positivity)⟩
  have hev1 : ∀ᶠ N : ℕ in atTop, 4 ≤ phi N ^ C := by
    have hll : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
      Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    filter_upwards [eventually_ge_atTop 3, hll.eventually_ge_atTop (max 1 (4 / C))] with N hN hv
    rw [phi_eq_exp hN, ← Real.exp_mul]
    set v := Real.log (Real.log N)
    have h1 : 1 ≤ v := le_trans (le_max_left _ _) hv
    have h2 : 4 / C ≤ v := le_trans (le_max_right _ _) hv
    have h3 : 4 ≤ v * C := by rwa [div_le_iff₀ hC] at h2
    have h4 : 4 ≤ v ^ 2 * C := by nlinarith
    linarith [Real.add_one_le_exp (v ^ 2 * C)]
  have hev2 : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(1 : ℝ) / 12) * (96 * K + 1) ≤ 1 := by
    have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (-((1 : ℝ) / 12))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    have := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (96 * K + 1) by positivity))
    filter_upwards [this] with N hN
    rw [neg_div, ← le_div_iff₀ (by positivity)]
    exact hN.le
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 ((hev1.and hev2).and (eventually_ge_atTop 3))
  refine ⟨N0, fun N hN H hH hdeloc h525 h526 hrig i j => ?_⟩
  obtain ⟨⟨ha4, hu1⟩, hN3⟩ := hN0 N hN
  have : NeZero N := ⟨by omega⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hphi : 0 < phi N := by rw [phi_eq_exp hN3]; exact Real.exp_pos _
  have ha5 : phi N ^ (5 * C) = (phi N ^ C) ^ 5 := by
    rw [mul_comm, Real.rpow_mul hphi.le]; norm_num
  have ha2 : phi N ^ (2 * C) = (phi N ^ C) ^ 2 := by
    rw [mul_comm, Real.rpow_mul hphi.le]; norm_num
  rw [ha5]
  rw [ha2] at h526
  generalize ha_def : phi N ^ C = a at hdeloc h525 h526 hrig ha4 ⊢
  generalize hu_def : (N : ℝ) ^ (-(1 : ℝ) / 12) = u at hu1
  have hu0 : 0 < u := hu_def ▸ Real.rpow_pos_of_pos hNpos _
  have ha1 : 1 ≤ a := by linarith
  have hu1' : u ≤ 1 := by nlinarith
  have hpow : ∀ k : ℕ, u ^ k = (N : ℝ) ^ (-(1 : ℝ) / 12 * k) := fun k => by
    rw [← hu_def, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
  have e8 : (N : ℝ) ^ (-(2 : ℝ) / 3) = u ^ 8 := by rw [hpow]; norm_num
  have e9 : (N : ℝ) ^ (-(3 : ℝ) / 4) = u ^ 9 := by rw [hpow]; norm_num
  have e3 : (N : ℝ) ^ (-(1 : ℝ) / 4) = u ^ 3 := by rw [hpow]; norm_num
  have e23 : (N : ℝ) ^ ((2 : ℝ) / 3) * u ^ 8 = 1 := by
    rw [← e8, ← Real.rpow_add hNpos]; norm_num
  have eN : (N : ℝ) * u ^ 12 = 1 := by
    rw [hpow, show -(1 : ℝ) / 12 * ((12 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one,
      mul_inv_cancel₀ hNpos.ne']
  rw [e8] at h526 hrig
  rw [e9, e3]
  have hE : edgePt N = ⟨2, u ^ 8⟩ := by rw [← e8]; rfl
  have hle : ∀ α, hH.eigenvalues α ≤ lambdaMax H :=
    fun α => (lambdaMax_isGreatest hH).2 ⟨α, rfl⟩
  have hlam : |lambdaMax H - 2| ≤ a * u ^ 8 := by
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hNpos _)] at h525
    calc |lambdaMax H - 2| = ((N : ℝ) ^ ((2 : ℝ) / 3) * u ^ 8) * |lambdaMax H - 2| := by
          rw [e23, one_mul]
      _ = ((N : ℝ) ^ ((2 : ℝ) / 3) * |lambdaMax H - 2|) * u ^ 8 := by ring
      _ ≤ a * u ^ 8 := by gcongr
  have hu9 : 0 < u ^ 9 := by positivity
  have hz : ∀ α, (hH.eigenvalues α : ℂ) ≠ ((lambdaMax H + u ^ 9 : ℝ) : ℂ) := by
    intro α h
    have h1 := Complex.ofReal_injective h
    have h2 := hle α
    linarith
  have hw : ∀ α, (hH.eigenvalues α : ℂ) ≠ edgePt N := by
    intro α h
    have h1 := congrArg Complex.im h
    rw [hE] at h1
    simp only [Complex.ofReal_im] at h1
    have : 0 < u ^ 8 := by positivity
    linarith
  rw [resolventC_sub_apply_eq_sum hH hz hw, hE]
  have haN : a / N = a * u ^ 12 := by
    rw [div_eq_iff hNpos.ne']
    calc a = a * ((N : ℝ) * u ^ 12) := by rw [eN, mul_one]
      _ = a * u ^ 12 * N := by ring
  -- (4.44) term by term
  have hterm : ∀ α, ‖((hH.eigenvectorBasis α i * hH.eigenvectorBasis α j : ℝ) : ℂ) *
        (((lambdaMax H + u ^ 9 : ℝ) : ℂ) - ⟨2, u ^ 8⟩) /
          (((hH.eigenvalues α : ℂ) - ((lambdaMax H + u ^ 9 : ℝ) : ℂ)) *
            ((hH.eigenvalues α : ℂ) - ⟨2, u ^ 8⟩))‖ ≤
      (if |hH.eigenvalues α - 2| ≤ 2 * a * u ^ 8 then 3 * a ^ 2 * u ^ 3 else 0) +
        6 * a ^ 2 * u ^ 20 * bulkWt (2 * a * u ^ 8) (hH.eigenvalues α) := by
    intro α
    have hv := hdeloc _ _ (hH.mulVec_eigenvectorBasis α) (sum_sq_eigenvectorBasis_eq_one hH α)
    have hvi := hv i
    have hvj := hv j
    rw [haN] at hvi hvj
    exact norm_term_le ha1 hu0 hu1' hlam (hle α) (abs_mul_le_of_sq_le hvi hvj)
  -- the bulk sum `Σ_α (2 - λ_α)^{-2} ≤ 4 K N^{4/3}`
  have hFsum : ∑ α, bulkWt (2 * a * u ^ 8) (hH.eigenvalues α) ≤ 4 / u ^ 16 * K := by
    rw [sum_eigenvalues_eq_sum_eigAsc hH (bulkWt (2 * a * u ^ 8))]
    have hFj : ∀ k : Fin N, bulkWt (2 * a * u ^ 8) (eigAsc hH k) ≤
        4 / u ^ 16 * (1 + ((N - 1 - (k : ℕ) : ℕ) : ℝ) ^ ((4 : ℝ) / 3))⁻¹ := by
      intro k
      have hk := k.isLt
      have hlk : eigAsc hH k ≤ lambdaMax H := by
        rw [lambdaMax_eq_eigAsc_last hH]
        exact monotone_eigAsc hH (Fin.le_def.mpr (by simp only; omega))
      have hmin : 1 ≤ min (((k : ℕ) : ℝ) + 1) ((N : ℝ) - (k : ℕ)) := by
        have h1 : ((k : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast hk
        refine le_min (by linarith [(Nat.cast_nonneg (k : ℕ) : (0 : ℝ) ≤ (k : ℕ))]) ?_
        linarith
      have hrp : min (((k : ℕ) : ℝ) + 1) ((N : ℝ) - (k : ℕ)) ^ (-(1 : ℝ) / 3) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hmin (by norm_num)
      have hr : |eigAsc hH k - gammaLoc N ((k : ℕ) + 1)| ≤ a * u ^ 8 := by
        refine (hrig k).trans ?_
        calc a * min (((k : ℕ) : ℝ) + 1) ((N : ℝ) - (k : ℕ)) ^ (-(1 : ℝ) / 3) * u ^ 8
            ≤ a * 1 * u ^ 8 := by gcongr
          _ = a * u ^ 8 := by ring
      exact bulkWt_eigAsc_le hH k ha1 hu0 eN (abs_le.mp hlam).2 hlk hr
    refine (Finset.sum_le_sum fun k _ => hFj k).trans ?_
    rw [← Finset.mul_sum]
    gcongr
    rw [Fin.sum_univ_eq_sum_range (fun m => (1 + ((N - 1 - m : ℕ) : ℝ) ^ ((4 : ℝ) / 3))⁻¹) N,
      Finset.sum_range_reflect (fun m => (1 + (m : ℝ) ^ ((4 : ℝ) / 3))⁻¹) N]
    exact hK N
  -- the window `|λ_α - 2| ≤ 2 a u^8` holds at most `a²` eigenvalues (5.26)
  have hnear : ∑ α, (if |hH.eigenvalues α - 2| ≤ 2 * a * u ^ 8 then 3 * a ^ 2 * u ^ 3 else 0)
      ≤ a ^ 2 * (3 * a ^ 2 * u ^ 3) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right h526 (by positivity)
  have hfin : a ^ 2 * (3 * a ^ 2 * u ^ 3) + 6 * a ^ 2 * u ^ 20 * (4 / u ^ 16 * K) ≤
      a ^ 5 * u ^ 3 := by
    have hsplit : a ^ 2 * (3 * a ^ 2 * u ^ 3) + 6 * a ^ 2 * u ^ 20 * (4 / u ^ 16 * K) =
        3 * a ^ 4 * u ^ 3 + (24 * K * u) * (a ^ 2 * u ^ 3) := by field_simp; ring
    rw [hsplit]
    have hKu : 24 * K * u ≤ 1 / 4 := by nlinarith
    have ha25 : a ^ 2 ≤ a ^ 5 := pow_le_pow_right₀ ha1 (by norm_num)
    have ha45 : 4 * a ^ 4 ≤ a ^ 5 := by
      rw [pow_succ]
      nlinarith [pow_pos (by linarith : (0 : ℝ) < a) 4]
    have hu3 : 0 < u ^ 3 := by positivity
    have h1 : (24 * K * u) * (a ^ 2 * u ^ 3) ≤ 1 / 4 * (a ^ 5 * u ^ 3) := by
      calc (24 * K * u) * (a ^ 2 * u ^ 3) ≤ 1 / 4 * (a ^ 2 * u ^ 3) := by gcongr
        _ ≤ 1 / 4 * (a ^ 5 * u ^ 3) := by gcongr
    nlinarith
  calc _ ≤ _ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum fun α _ => hterm α
    _ = ∑ α, (if |hH.eigenvalues α - 2| ≤ 2 * a * u ^ 8 then 3 * a ^ 2 * u ^ 3 else 0) +
        6 * a ^ 2 * u ^ 20 * ∑ α, bulkWt (2 * a * u ^ 8) (hH.eigenvalues α) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ a ^ 2 * (3 * a ^ 2 * u ^ 3) + 6 * a ^ 2 * u ^ 20 * (4 / u ^ 16 * K) := by
          gcongr
    _ ≤ a ^ 5 * u ^ 3 := hfin

/-! ### Compiled checks at a concrete nondegenerate point

`N = 2`, `H = [[0, 1], [1, 0]]` (eigenvalues `-1` and `1`, every unit eigenvector has
`v_i² = 1/2`), and `C = log(7/4) / (log log 2)²`, so that `φ^C = 7/4`. All four hypotheses of
`norm_resolventC_barrier_sub_le` hold at once: `v_i² = 1/2 ≤ 7/8`, `2^{2/3} ≤ 7/4`, at most
`2 ≤ 49/16` eigenvalues in the window, and `|λ_j - γ_j| ≤ 1 ≤ (7/4) 2^{-2/3}` (`γ_1 ∈ [-2, 0]`,
`γ_2 = 2`). -/

/-- `z̃` satisfies `|Re z̃| ≤ 5` and `Im z̃ ≥ N^{-1+1/3}`. -/
example (N : ℕ) : |(edgePt N).re| ≤ 5 ∧ (N : ℝ) ^ (-1 + (1 : ℝ) / 3) ≤ (edgePt N).im := by
  refine ⟨by norm_num [edgePt], le_of_eq ?_⟩
  simp only [edgePt]
  norm_num

private def wMat : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

private lemma wMat_isHermitian : wMat.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat]

/-- Every unit eigenvector of `[[0, 1], [1, 0]]` has eigenvalue `±1` and `v_0² = v_1² = 1/2`. -/
private lemma wMat_eigen {v : Fin 2 → ℝ} {μ : ℝ} (h : wMat *ᵥ v = μ • v)
    (hv : ∑ i, v i ^ 2 = 1) : μ ^ 2 = 1 ∧ v 0 ^ 2 = 1 / 2 ∧ v 1 ^ 2 = 1 / 2 := by
  have h0 : v 1 = μ * v 0 := by
    simpa [wMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h 0
  have h1 : v 0 = μ * v 1 := by
    simpa [wMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h 1
  rw [Fin.sum_univ_two] at hv
  have hμ : μ ^ 2 = 1 := by
    have : μ ^ 2 * (v 0 ^ 2 + v 1 ^ 2) = v 0 ^ 2 + v 1 ^ 2 := by
      linear_combination (-(v 1 + μ * v 0)) * h0 + (-(v 0 + μ * v 1)) * h1
    rw [hv, mul_one] at this
    exact this
  have h01 : v 1 ^ 2 = v 0 ^ 2 := by
    rw [h0, mul_pow, hμ, one_mul]
  exact ⟨hμ, by linarith, by linarith⟩

/-- `C = log(7/4) / (log log 2)²`. -/
private def wC : ℝ := Real.log (7 / 4) / Real.log (Real.log 2) ^ 2

private lemma log_log_two_ne_zero : Real.log (Real.log 2) ≠ 0 := by
  have h1 := Real.log_two_lt_d9
  have h2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  exact Real.log_ne_zero_of_pos_of_ne_one h2 (by linarith)

private lemma wC_pos : 0 < wC := by
  unfold wC
  have := log_log_two_ne_zero
  have h7 : 0 < Real.log (7 / 4) := Real.log_pos (by norm_num)
  positivity

private lemma phi_two_rpow_wC : phi 2 ^ wC = 7 / 4 := by
  have hL := log_log_two_ne_zero
  unfold phi wC
  rw [Nat.cast_ofNat, Real.rpow_def_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)),
    ← Real.exp_mul]
  rw [show Real.log (Real.log 2) * Real.log (Real.log 2) *
      (Real.log (7 / 4) / Real.log (Real.log 2) ^ 2) = Real.log (7 / 4) by field_simp]
  exact Real.exp_log (by norm_num)

private lemma phi_two_rpow_two_wC : phi 2 ^ (2 * wC) = (7 / 4) ^ 2 := by
  have hphi : 0 ≤ phi 2 := by
    unfold phi
    exact Real.rpow_nonneg (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le _
  rw [mul_comm, Real.rpow_mul hphi, phi_two_rpow_wC]
  norm_num

/-- `n_sc(0) = 1/2`, by the symmetry of `ρ_sc`. -/
private lemma nsc_zero : nsc 0 = 1 / 2 := by
  have h1 := nsc_sub_nsc' (-2) 0
  have h2 := nsc_sub_nsc' 0 2
  rw [nsc_eq_zero le_rfl] at h1
  rw [nsc_eq_one le_rfl] at h2
  have hsymm : (∫ x in (0 : ℝ)..2, rhoSc x) = ∫ x in (-2 : ℝ)..0, rhoSc x := by
    have h3 := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 2) rhoSc
    rw [neg_zero] at h3
    rw [← h3]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [rhoSc, neg_sq]
  linarith

private lemma gammaLoc_two_one : -2 ≤ gammaLoc 2 1 ∧ gammaLoc 2 1 ≤ 0 := by
  constructor
  · have h := nsc_gammaLoc (N := 2) (j := 1) le_rfl (by norm_num)
    by_contra hlt
    rw [not_le] at hlt
    rw [nsc_eq_zero hlt.le] at h
    norm_num at h
  · unfold gammaLoc
    refine csInf_le ⟨-2, fun x hx => ?_⟩ ?_
    · by_contra hlt
      rw [not_le] at hlt
      simp only [Set.mem_ofPred_eq] at hx
      rw [nsc_eq_zero hlt.le] at hx
      norm_num at hx
    · simp only [Set.mem_ofPred_eq, nsc_zero]
      norm_num

private lemma wMat_eigAsc : eigAsc wMat_isHermitian 0 = -1 ∧ eigAsc wMat_isHermitian 1 = 1 := by
  have hsq : ∀ k : Fin 2, eigAsc wMat_isHermitian k ^ 2 = 1 := by
    intro k
    obtain ⟨α, hα⟩ : ∃ α, eigAsc wMat_isHermitian k = wMat_isHermitian.eigenvalues α :=
      ⟨(Fintype.equivOfCardEq (Fintype.card_fin _))
        (Fin.cast (Fintype.card_fin 2).symm (Fin.rev k)),
        by simp [Matrix.IsHermitian.eigenvalues, eigAsc]⟩
    rw [hα]
    exact (wMat_eigen (wMat_isHermitian.mulVec_eigenvectorBasis α)
      (sum_sq_eigenvectorBasis_eq_one wMat_isHermitian α)).1
  have htr : ∑ k, eigAsc wMat_isHermitian k = 0 := by
    have h := wMat_isHermitian.trace_eq_sum_eigenvalues
    have h0 : wMat.trace = 0 := by simp [Matrix.trace, Fin.sum_univ_two, wMat]
    rw [h0] at h
    have := sum_eigenvalues_eq_sum_eigAsc wMat_isHermitian id
    simp only [id] at this
    rw [← this]
    simpa using h.symm
  rw [Fin.sum_univ_two] at htr
  have hmono : eigAsc wMat_isHermitian 0 ≤ eigAsc wMat_isHermitian 1 :=
    monotone_eigAsc wMat_isHermitian (by decide)
  have h0 := hsq 0
  have h1 := hsq 1
  have hx : eigAsc wMat_isHermitian 0 = -1 := by
    have hneg : eigAsc wMat_isHermitian 0 ≤ 0 := by linarith
    have : (eigAsc wMat_isHermitian 0 + 1) * (eigAsc wMat_isHermitian 0 - 1) = 0 := by
      ring_nf; linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exfalso; linarith
  exact ⟨hx, by linarith⟩

private lemma two_rpow_two_thirds_le : (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 7 / 4 := by
  have h3 : ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ 3 = 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h0 : 0 ≤ (2 : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg (by norm_num) _
  refine (pow_le_pow_iff_left₀ h0 (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)).mp ?_
  rw [h3]
  norm_num

private lemma one_le_rig_two : 1 ≤ 7 / 4 * (2 : ℝ) ^ (-(2 : ℝ) / 3) := by
  have h := two_rpow_two_thirds_le
  have hpos : 0 < (2 : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos (by norm_num) _
  rw [neg_div, Real.rpow_neg (by norm_num), ← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]
  exact h

/-- All hypotheses of `norm_resolventC_barrier_sub_le` hold at `N = 2`, `H = [[0, 1], [1, 0]]`,
`C = log(7/4) / (log log 2)²`, where `φ^C = 7/4`. -/
example : 0 < wC ∧
    (∀ (v : Fin 2 → ℝ) (μ : ℝ), wMat *ᵥ v = μ • v → ∑ i, v i ^ 2 = 1 →
      ∀ i, v i ^ 2 ≤ phi 2 ^ wC / ((2 : ℕ) : ℝ)) ∧
    |((2 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax wMat - 2)| ≤ phi 2 ^ wC ∧
    ((Finset.univ.filter fun α => |wMat_isHermitian.eigenvalues α - 2| ≤
        2 * phi 2 ^ wC * ((2 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3)).card : ℝ) ≤ phi 2 ^ (2 * wC) ∧
    (∀ j : Fin 2, |eigAsc wMat_isHermitian j - gammaLoc 2 ((j : ℕ) + 1)| ≤
      phi 2 ^ wC * (min (((j : ℕ) : ℝ) + 1) (((2 : ℕ) : ℝ) - (j : ℕ))) ^ (-(1 : ℝ) / 3) *
        ((2 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3)) := by
  obtain ⟨he0, he1⟩ := wMat_eigAsc
  have hlam : lambdaMax wMat = 1 := by
    rw [lambdaMax_eq_eigAsc_last (N := 2) wMat_isHermitian]
    exact he1
  have hγ := gammaLoc_two_one
  have hrig := one_le_rig_two
  refine ⟨wC_pos, ?_, ?_, ?_, ?_⟩
  · intro v μ h hv i
    obtain ⟨-, h0, h1⟩ := wMat_eigen h hv
    rw [phi_two_rpow_wC]
    fin_cases i
    · simp only [Fin.zero_eta, h0]; norm_num
    · simp only [Fin.mk_one, h1]; norm_num
  · rw [hlam, phi_two_rpow_wC, Nat.cast_ofNat]
    rw [show (1 : ℝ) - 2 = -1 by norm_num, mul_neg_one, abs_neg,
      abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
    exact two_rpow_two_thirds_le
  · rw [phi_two_rpow_two_wC]
    refine (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans ?_
    simp only [Finset.card_univ, Fintype.card_fin]
    norm_num
  · rw [phi_two_rpow_wC]
    intro j
    fin_cases j
    · simp only [Fin.zero_eta, Nat.cast_zero, zero_add, he0, Nat.cast_ofNat,
        sub_zero]
      rw [min_eq_left (by norm_num), Real.one_rpow, mul_one]
      refine le_trans ?_ hrig
      rw [abs_le]
      constructor <;> linarith [hγ.1, hγ.2]
    · simp only [Fin.mk_one, Nat.cast_one, he1, Nat.cast_ofNat]
      rw [show (1 : ℕ) + 1 = 2 by rfl, gammaLoc_self (by norm_num)]
      rw [min_eq_right (by norm_num), show (2 : ℝ) - 1 = 1 by norm_num, Real.one_rpow, mul_one]
      refine le_trans ?_ hrig
      norm_num

#print axioms edgePt
#print axioms norm_resolventC_barrier_sub_le

end WEdgeNS
