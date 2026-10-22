import WEdgeNS.EdgeUniv.OffDiagSwap

/-!
# The Claim of the proof of Lemma 3.5
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- The telescoping sum (3.39) over the `N` diagonal and the `|OffDiag N| ≤ N²` off-diagonal
replacements `H_{γ-1} → H_γ`, `γ = lexPos N e`: if one replacement changes the expectation of `G`
by at most `a` on the diagonal and `b ≥ 0` off the diagonal, then `H_{N(N+1)/2} = L` and `H_0` (the
GOE) differ by at most `N a + N² b`. -/
private lemma clm_telescope_le {N : ℕ} (L : EntryLaws N) (G : Entries N → ℝ) {a b : ℝ}
    (hb : 0 ≤ b)
    (h : ∀ e : Fin N ⊕ OffDiag N,
      |∫ ω, G ω ∂(interp (lexPos N) (lexPos N e) L (goeLaws N)).law -
          ∫ ω, G ω ∂(interp (lexPos N) (lexPos N e - 1) L (goeLaws N)).law| ≤
        Sum.elim (fun _ => a) (fun _ => b) e) :
    |∫ ω, G ω ∂L.law - ∫ ω, G ω ∂(goeLaws N).law| ≤ N * a + (N : ℝ) ^ 2 * b := by
  set g : ℕ → ℝ := fun γ => ∫ ω, G ω ∂(interp (lexPos N) γ L (goeLaws N)).law with hg
  have h1 := sub_eq_sum_lexPos (N := N) (fun γ => ((g γ : ℝ) : ℂ))
  have h2 : g (N * (N + 1) / 2) - g 0 =
      ∑ e : Fin N ⊕ OffDiag N, (g (lexPos N e) - g (lexPos N e - 1)) := by
    have h3 : (((g (N * (N + 1) / 2) - g 0 : ℝ)) : ℂ) =
        ((∑ e : Fin N ⊕ OffDiag N, (g (lexPos N e) - g (lexPos N e - 1)) : ℝ) : ℂ) := by
      push_cast
      exact h1
    exact_mod_cast h3
  have h4 : |g (N * (N + 1) / 2) - g 0| ≤ N * a + (N : ℝ) ^ 2 * b := by
    rw [h2]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun e _ => h e).trans ?_)
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_fin]
    have hcard : (Fintype.card (OffDiag N) : ℝ) ≤ (N : ℝ) ^ 2 := by
      have h5 : Fintype.card (OffDiag N) ≤ N * N := by
        calc Fintype.card (OffDiag N) ≤ Fintype.card (Fin N × Fin N) := Fintype.card_subtype_le _
          _ = N * N := by simp
      calc (Fintype.card (OffDiag N) : ℝ) ≤ (N : ℝ) * N := by exact_mod_cast h5
        _ = (N : ℝ) ^ 2 := by ring
    have := mul_le_mul_of_nonneg_right hcard hb
    linarith
  simpa only [hg, interp_lexPos_top, interp_lexPos_zero] using h4

/-- The off-diagonal comparison of the Claim ((3.20) and the off-diagonal form of (3.19)):
the functionals `offWard` and `offWardInt` have the same expectation under a law of Lemma 3.5 and
under the GOE, up to `N^{1/3-φs+Cε}`; `ε₀` and `C` depend only on `(CF, C0, φs)`. -/
theorem green_comparison_offDiag_largeQ {CF C0 φs : ℝ} (hC0 : 0 ≤ C0) (hφs : 1 / 3 < φs)
    (hφs' : φs ≤ 1 / 2) :
    ∃ ε₀ > (0 : ℝ), ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ N0 : ℕ, ∀ N ≥ N0,
      ∀ L : EntryLaws N, LargeQClass C0 φs N L →
      ∀ F : ℝ → ℝ, ContDiff ℝ 4 F →
        (∀ n ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF) →
        (∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |∫ ω, F (offWard (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩) ∂L.law -
            ∫ ω, F (offWard (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩)
              ∂(goeLaws N).law| ≤ (N : ℝ) ^ ((1 : ℝ) / 3 - φs + C * ε)) ∧
        (∀ E₁ E₂ : ℝ, |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |∫ ω, F (offWardInt (symOfEntries ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂) ∂L.law -
            ∫ ω, F (offWardInt (symOfEntries ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂)
              ∂(goeLaws N).law| ≤ (N : ℝ) ^ ((1 : ℝ) / 3 - φs + C * ε)) := by
  obtain ⟨ε₀, hε₀, Cs, hCs, hS⟩ := swap_comparison_largeQ (CF := CF) hC0 hφs hφs'
  refine ⟨ε₀, hε₀, Cs + 1, by positivity, fun ε hε hε' => ?_⟩
  obtain ⟨Ns, hNs⟩ := hS ε hε hε'
  refine ⟨max Ns ⌈(2 : ℝ) ^ (1 / ε)⌉₊, fun N hN L hL F hF4 hF => ?_⟩
  have hNs' : Ns ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : (2 : ℝ) ^ (1 / ε) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
  have h21 : (1 : ℝ) ≤ (2 : ℝ) ^ (1 / ε) := Real.one_le_rpow (by norm_num) (by positivity)
  have hNr : (1 : ℝ) ≤ N := h21.trans hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hNε : (2 : ℝ) ≤ (N : ℝ) ^ ε := by
    have h := Real.rpow_le_rpow (by positivity) hN2 hε.le
    rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one] at h
  set Z := (N : ℝ) ^ ((1 : ℝ) / 3 - φs + Cs * ε) with hZ
  have hZ0 : 0 < Z := Real.rpow_pos_of_pos hN0 _
  have ha : (N : ℝ) * (N : ℝ) ^ (-(1 : ℝ) / 3 + Cs * ε - 2 * φs) ≤ Z := by
    rw [hZ]
    calc (N : ℝ) * (N : ℝ) ^ (-(1 : ℝ) / 3 + Cs * ε - 2 * φs)
        = (N : ℝ) ^ (1 + (-(1 : ℝ) / 3 + Cs * ε - 2 * φs)) := by
          rw [Real.rpow_add hN0, Real.rpow_one]
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 3 - φs + Cs * ε) :=
          Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
  have hb : (N : ℝ) ^ 2 * (N : ℝ) ^ (-(5 : ℝ) / 3 + Cs * ε - φs) = Z := by
    rw [hZ, show (N : ℝ) ^ 2 = (N : ℝ) ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hN0]
    congr 1; ring
  have hb0 : 0 ≤ (N : ℝ) ^ (-(5 : ℝ) / 3 + Cs * ε - φs) := (Real.rpow_pos_of_pos hN0 _).le
  have hfin : Z + Z ≤ (N : ℝ) ^ ((1 : ℝ) / 3 - φs + (Cs + 1) * ε) := by
    rw [show (1 : ℝ) / 3 - φs + (Cs + 1) * ε = ((1 : ℝ) / 3 - φs + Cs * ε) + ε by ring,
      Real.rpow_add hN0]
    have := mul_le_mul_of_nonneg_left hNε hZ0.le
    rw [← hZ]
    linarith
  constructor
  · intro E hE
    have key := clm_telescope_le L
      (fun ω => F (offWard (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩)) hb0
      (fun e => (hNs N hNs' L hL e F hF4 hF).1 E hE)
    exact key.trans (by linarith)
  · intro E₁ E₂ h1 h2
    have key := clm_telescope_le L
      (fun ω => F (offWardInt (symOfEntries ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂)) hb0
      (fun e => (hNs N hNs' L hL e F hF4 hF).2 E₁ E₂ h1 h2)
    exact key.trans (by linarith)

/-- The Claim of the proof of Lemma 3.5, (3.16)–(3.19) ([16] Proposition 6.6 with
`f = 0`): `ε₀` and `C` depend only on `(CF, C0, φs)`. -/
theorem green_comparison_largeQ {CF C0 φs : ℝ} (hC0 : 0 ≤ C0) (hφs : 1 / 3 < φs)
    (hφs' : φs ≤ 1 / 2) :
    ∃ ε₀ > (0 : ℝ), ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ N0 : ℕ, ∀ N ≥ N0,
      ∀ L : EntryLaws N, LargeQClass C0 φs N L →
      ∀ F : ℝ → ℝ, ContDiff ℝ 4 F →
        (∀ n ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF) →
        (∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |∫ ω, F (((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) ^ 2 * ∑ i, ∑ j,
                ‖resolventC (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i j‖ ^ 2) ∂L.law -
            ∫ ω, F (((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) ^ 2 * ∑ i, ∑ j,
                ‖resolventC (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i j‖ ^ 2)
              ∂(goeLaws N).law| ≤
            (N : ℝ) ^ ((1 : ℝ) / 3 - φs + C * ε)) ∧
        (∀ E₁ E₂ : ℝ, |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |∫ ω, F (N * ∫ y in E₁..E₂,
                (stieltjesM (symOfEntries ω) ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩).im) ∂L.law -
            ∫ ω, F (N * ∫ y in E₁..E₂,
                (stieltjesM (symOfEntries ω) ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩).im)
              ∂(goeLaws N).law| ≤
            (N : ℝ) ^ ((1 : ℝ) / 3 - φs + C * ε)) := by
  obtain ⟨C₁, hC₁, hW⟩ := ward_reduction_largeQInterp (CF := CF) hC0 hφs hφs'
  obtain ⟨ε₀, hε₀, C₂, hC₂, hO⟩ := green_comparison_offDiag_largeQ (CF := CF) hC0 hφs hφs'
  refine ⟨min ε₀ (1 / 10), lt_min hε₀ (by norm_num), max C₁ C₂ + 1, by positivity,
    fun ε hε hε' => ?_⟩
  obtain ⟨N1, hN1⟩ := hW ε hε (lt_of_lt_of_le hε' (min_le_right _ _))
  obtain ⟨N2, hN2⟩ := hO ε hε (lt_of_lt_of_le hε' (min_le_left _ _))
  refine ⟨max (max N1 N2) ⌈(3 : ℝ) ^ (1 / ε)⌉₊, fun N hN L hL F hF hF' => ?_⟩
  have hN1' : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2' : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : (3 : ℝ) ^ (1 / ε) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
  have h31 : (1 : ℝ) ≤ (3 : ℝ) ^ (1 / ε) := Real.one_le_rpow (by norm_num) (by positivity)
  have hNr : (1 : ℝ) ≤ N := h31.trans hN3
  have hN0 : (0 : ℝ) < N := by linarith
  have hNε : (3 : ℝ) ≤ (N : ℝ) ^ ε := by
    have h := Real.rpow_le_rpow (by positivity) hN3 hε.le
    rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one] at h
  set M := max C₁ C₂
  have hle1 : (N : ℝ) ^ (-(1 : ℝ) / 3 + C₁ * ε) ≤ (N : ℝ) ^ ((1 : ℝ) / 3 - φs + M * ε) :=
    Real.rpow_le_rpow_of_exponent_le hNr (by
      have := mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hε.le; linarith)
  have hle2 : (N : ℝ) ^ ((1 : ℝ) / 3 - φs + C₂ * ε) ≤ (N : ℝ) ^ ((1 : ℝ) / 3 - φs + M * ε) :=
    Real.rpow_le_rpow_of_exponent_le hNr (by
      have := mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hε.le; linarith)
  have hfin : 3 * (N : ℝ) ^ ((1 : ℝ) / 3 - φs + M * ε) ≤
      (N : ℝ) ^ ((1 : ℝ) / 3 - φs + (M + 1) * ε) := by
    rw [show (1 : ℝ) / 3 - φs + (M + 1) * ε = ((1 : ℝ) / 3 - φs + M * ε) + ε by ring,
      Real.rpow_add hN0 ((1 : ℝ) / 3 - φs + M * ε) ε]
    have h0 := Real.rpow_pos_of_pos hN0 ((1 : ℝ) / 3 - φs + M * ε)
    have := mul_le_mul_of_nonneg_left hNε h0.le
    linarith
  have hcl : ∃ Lv γ, LargeQClass C0 φs N Lv ∧ L = interp (lexPos N) γ Lv (goeLaws N) :=
    ⟨L, N * (N + 1) / 2, hL, (interp_lexPos_top L (goeLaws N)).symm⟩
  have hcg : ∃ Lv γ, LargeQClass C0 φs N Lv ∧ goeLaws N = interp (lexPos N) γ Lv (goeLaws N) :=
    ⟨L, 0, hL, (interp_lexPos_zero L (goeLaws N)).symm⟩
  obtain ⟨hWL1, hWL2⟩ := hN1 N hN1' L hcl F hF hF'
  obtain ⟨hWG1, hWG2⟩ := hN1 N hN1' (goeLaws N) hcg F hF hF'
  obtain ⟨hO1, hO2⟩ := hN2 N hN2' L hL F hF hF'
  constructor
  · intro E hE
    have a := abs_le.1 (hWL1 E hE)
    have b := abs_le.1 (hO1 E hE)
    have c := abs_le.1 (hWG1 E hE)
    refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [a.1, a.2, b.1, b.2, c.1, c.2, hle1, hle2, hfin]
  · intro E₁ E₂ h1 h2
    have a := abs_le.1 (hWL2 E₁ E₂ h1 h2)
    have b := abs_le.1 (hO2 E₁ E₂ h1 h2)
    have c := abs_le.1 (hWG2 E₁ E₂ h1 h2)
    refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [a.1, a.2, b.1, b.2, c.1, c.2, hle1, hle2, hfin]

/-! ### Checks -/

-- The entry law of Lemma 3.5 at `N = 1024` with diagonal values `±1/16, 0, 0` (variance `2/N`)
-- and off-diagonal values `±1/32` (variance `1/N`), in `LargeQClass 1 (2/5) 1024`.
open private lawA lawA_isGenWigner lawA_supp from WEdgeNS.EdgeUniv.LargeQClass

/-- Every hypothesis of `green_comparison_offDiag_largeQ` and `green_comparison_largeQ` that is not
existential holds at one point: `N = 1024`, `C0 = 1`, `φs = 2/5`, `ε = 1/15` (the window `I_ε` is
`|E - 2| ≤ 1/64`), `L` the law above, `F = K(·/π)` for the edge cutoff `K`, `E = 2` and
`E₁ = 2 - 1/100 < E₂ = 2 + 1/100`. The interpolations `H_γ` between this law and the GOE, at
`γ = N(N+1)/2`, `γ = 0` and `γ = 5000`, satisfy the class hypothesis of
`ward_reduction_largeQInterp`. -/
example : ∃ CF : ℝ, 0 < CF ∧ (0 : ℝ) ≤ 1 ∧ (1 / 3 : ℝ) < 2 / 5 ∧ (2 / 5 : ℝ) ≤ 1 / 2 ∧
    (0 : ℝ) < 1 / 15 ∧ (1 / 15 : ℝ) < 1 / 10 ∧
    LargeQClass 1 (2 / 5) 1024 lawA ∧
    (∃ Lv γ, LargeQClass 1 (2 / 5) 1024 Lv ∧ lawA = interp (lexPos 1024) γ Lv (goeLaws 1024)) ∧
    (∃ Lv γ, LargeQClass 1 (2 / 5) 1024 Lv ∧
      goeLaws 1024 = interp (lexPos 1024) γ Lv (goeLaws 1024)) ∧
    (∃ Lv γ, LargeQClass 1 (2 / 5) 1024 Lv ∧
      interp (lexPos 1024) 5000 lawA (goeLaws 1024) = interp (lexPos 1024) γ Lv (goeLaws 1024)) ∧
    ContDiff ℝ 4 (fun x => edgeCutoff (x / Real.pi)) ∧
    (∀ n ∈ Finset.Icc 1 4, ∀ x : ℝ,
      |iteratedDeriv n (fun x => edgeCutoff (x / Real.pi)) x| ≤ CF * (1 + |x|) ^ CF) ∧
    |(2 - 1 / 100 : ℝ) - 2| ≤ ((1024 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) ∧
    |(2 + 1 / 100 : ℝ) - 2| ≤ ((1024 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) ∧
    (2 - 1 / 100 : ℝ) < 2 + 1 / 100 ∧
    |(2 : ℝ) - 2| ≤ ((1024 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) := by
  obtain ⟨CF, hCF, h⟩ := edgeCutoff_deriv_le
  refine ⟨CF, hCF, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    ⟨lawA_isGenWigner, lawA_supp⟩,
    ⟨lawA, 1024 * (1024 + 1) / 2, ⟨lawA_isGenWigner, lawA_supp⟩,
      (interp_lexPos_top lawA (goeLaws 1024)).symm⟩,
    ⟨lawA, 0, ⟨lawA_isGenWigner, lawA_supp⟩, (interp_lexPos_zero lawA (goeLaws 1024)).symm⟩,
    ⟨lawA, 5000, ⟨lawA_isGenWigner, lawA_supp⟩, rfl⟩,
    (edgeCutoff_props.1 4).comp (contDiff_id.div_const _), h, ?_, ?_, by norm_num, ?_⟩
  all_goals
    rw [rpow_1024_window]; norm_num [abs_of_nonneg, abs_of_nonpos]

/-- The conclusion of `green_comparison_largeQ` at `C0 = 1`, `φs = 2/5`, for every `ε ∈ (0, ε₀)` and
all large `N`: the Rademacher law against the GOE, `F = K(·/π)`, `E = 2` and
`[E₁, E₂] = [2 - N^{-2/3+ε}, 2 + N^{-2/3+ε}]`. -/
example : ∃ ε₀ > (0 : ℝ), ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ᶠ N : ℕ in atTop,
    32 ≤ N ∧ (2 : ℝ) - (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) < 2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) ∧
    |∫ ω, edgeCutoff ((((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) ^ 2 * ∑ i, ∑ j,
          ‖resolventC (symOfEntries ω) ⟨2, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i j‖ ^ 2) / Real.pi)
          ∂(radLaws N).law -
        ∫ ω, edgeCutoff ((((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) ^ 2 * ∑ i, ∑ j,
          ‖resolventC (symOfEntries ω) ⟨2, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i j‖ ^ 2) / Real.pi)
          ∂(goeLaws N).law| ≤ (N : ℝ) ^ ((1 : ℝ) / 3 - 2 / 5 + C * ε) ∧
    |∫ ω, edgeCutoff ((N * ∫ y in (2 - (N : ℝ) ^ (-(2 : ℝ) / 3 + ε))..
              (2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)),
          (stieltjesM (symOfEntries ω) ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩).im) / Real.pi)
          ∂(radLaws N).law -
        ∫ ω, edgeCutoff ((N * ∫ y in (2 - (N : ℝ) ^ (-(2 : ℝ) / 3 + ε))..
              (2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)),
          (stieltjesM (symOfEntries ω) ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩).im) / Real.pi)
          ∂(goeLaws N).law| ≤ (N : ℝ) ^ ((1 : ℝ) / 3 - 2 / 5 + C * ε) := by
  obtain ⟨CF, hCF, hFd⟩ := edgeCutoff_deriv_le
  obtain ⟨ε₀, hε₀, C, hC, h⟩ := green_comparison_largeQ (CF := CF) (C0 := 1) (φs := 2 / 5)
    zero_le_one (by norm_num) (by norm_num)
  refine ⟨ε₀, hε₀, C, hC, fun ε hε hε' => ?_⟩
  obtain ⟨N0, hN0⟩ := h ε hε hε'
  filter_upwards [eventually_ge_atTop (max N0 32)] with N hN
  have h32 : 32 ≤ N := le_trans (le_max_right _ _) hN
  have hr : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) := Real.rpow_pos_of_pos (by positivity) _
  have hE₁ : |(2 - (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) := by
    rw [sub_sub_cancel_left, abs_neg, abs_of_pos hr]
  have hE₂ : |(2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) := by
    rw [add_sub_cancel_left, abs_of_pos hr]
  have hE : |(2 : ℝ) - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) := by
    rw [sub_self, abs_zero]; exact hr.le
  have hk := hN0 N (le_trans (le_max_left _ _) hN) (radLaws N)
    ⟨radLaws_isGenWigner (by omega), radLaws_boundedSupportAS h32⟩
    (fun x => edgeCutoff (x / Real.pi)) ((edgeCutoff_props.1 4).comp (contDiff_id.div_const _))
    hFd
  exact ⟨h32, by linarith, hk.1 2 hE, hk.2 _ _ hE₁ hE₂⟩

#print axioms green_comparison_offDiag_largeQ
#print axioms green_comparison_largeQ

end WEdgeNS
