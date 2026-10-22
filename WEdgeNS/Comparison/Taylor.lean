import WEdgeNS.Comparison.PairMoments
import WEdgeNS.Comparison.LocalSmallQ

/-!
# One swap of the Green function comparison for small support
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

open private expansion_evalW_wordP_zero expansion_continuous_evalW expansion_continuous_zeroEntry
  expansion_ae_entryVal_le expansion_eventually_log_le from WEdgeNS.Comparison.Expansion
open private starExpansion_isHermitian_smul_entryMat from WEdgeNS.Comparison.StarExpansion
open private tilde_pos from WEdgeNS.Comparison.Classes
open private interp_isProb from WEdgeNS.Comparison.Telescope
open private lawV lawW lawV_momentCond lawV_supp lawVW_isMomentMatch
  from WEdgeNS.Comparison.Classes


/-- Taylor's theorem at order two with the Lagrange remainder. -/
private lemma taylor_lagrange_two {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F) (x y : ℝ) :
    ∃ ζ ∈ Set.uIcc x y, F y = F x + iteratedDeriv 1 F x * (y - x) +
      iteratedDeriv 2 F x * (y - x) ^ 2 / 2 + iteratedDeriv 3 F ζ * (y - x) ^ 3 / 6 := by
  rcases eq_or_ne x y with rfl | hxy
  · exact ⟨x, Set.left_mem_uIcc, by ring⟩
  · obtain ⟨ζ, hζ, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (f := F) (x := y) (x₀ := x)
      (n := 2) hxy hF.contDiffOn
    refine ⟨ζ, Set.uIoo_subset_uIcc_self hζ, ?_⟩
    rw [taylor_within_apply] at h
    have hk : ∀ k : ℕ, k ≤ 2 → iteratedDerivWithin k F (Set.uIcc x y) x = iteratedDeriv k F x :=
      fun k hkn => iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hxy)
        ((hF.contDiffAt).of_le (by exact_mod_cast (show k ≤ 3 by omega))) Set.left_mem_uIcc
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hk 0 (by norm_num),
      hk 1 (by norm_num), hk 2 (by norm_num), smul_eq_mul, Nat.factorial] at h
    simp only [iteratedDeriv_zero] at h
    norm_num at h
    rw [iteratedDeriv_one]
    linarith

/-- (6.86) with the bound (5.12) in place of the intermediate point: the third-order
Taylor remainder of `F` between `x` and `y` is at most
`C_F (1 + max(|x|, |y|))^{C_F} |y - x|³ / 6`. -/
theorem abs_taylor_three_le {CF : ℝ} {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    (hFd : ∀ n ∈ Finset.Icc 1 3, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF) (x y : ℝ) :
    |F y - F x - iteratedDeriv 1 F x * (y - x) - iteratedDeriv 2 F x * (y - x) ^ 2 / 2| ≤
      CF * (1 + max |x| |y|) ^ CF * |y - x| ^ 3 / 6 := by
  have hCF : 0 ≤ CF := by
    have h := hFd 1 (by simp) 0
    simp only [abs_zero, add_zero, Real.one_rpow, mul_one] at h
    exact (abs_nonneg _).trans h
  obtain ⟨ζ, hζ, h⟩ := taylor_lagrange_two hF x y
  have hζm : |ζ| ≤ max |x| |y| := by
    rcases Set.mem_uIcc.1 hζ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact abs_le.2 ⟨by linarith [neg_abs_le x, le_max_left |x| |y|],
        by linarith [le_abs_self y, le_max_right |x| |y|]⟩
    · exact abs_le.2 ⟨by linarith [neg_abs_le y, le_max_right |x| |y|],
        by linarith [le_abs_self x, le_max_left |x| |y|]⟩
  have h3 : |iteratedDeriv 3 F ζ| ≤ CF * (1 + max |x| |y|) ^ CF :=
    (hFd 3 (by simp) ζ).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by linarith) hCF) hCF)
  have he : F y - F x - iteratedDeriv 1 F x * (y - x) - iteratedDeriv 2 F x * (y - x) ^ 2 / 2 =
      iteratedDeriv 3 F ζ * (y - x) ^ 3 / 6 := by rw [h]; ring
  rw [he, abs_div, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  gcongr

/-- `Σ_{ij} P_{γ,k}(G_ij conj G_ij)` of (6.87)–(6.90) (no centred letters, `m = 0`). -/
def opPPair {N : ℕ} (e : Fin N ⊕ OffDiag N) (k : List ℕ) (G : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  ∑ i, ∑ j, evalW G 0 (wordP e k [⟨.g, i, j⟩, ⟨.gbar, i, j⟩])

/-- The word `G_ij conj G_ij` evaluates to `|G_ij|²`. -/
private lemma taylor_evalWord_pair {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    evalWord G 0 [⟨.g, i, j⟩, ⟨.gbar, i, j⟩] = ((‖G i j‖ ^ 2 : ℝ) : ℂ) := by
  simp only [evalWord, evalLetter, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Splitting off the term `c = 0` of a sum over `0 ≤ c ≤ n`. -/
private lemma taylor_sum_range_succ_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ c ∈ Finset.range (n + 1), f c = f 0 + ∑ c ∈ Finset.Icc 1 n, f c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega), add_assoc]

/-- Moving two outer finite sums inside two inner ones. -/
private lemma taylor_sum_comm4 {α β γ δ M : Type*} [AddCommMonoid M] (u : Finset α) (v : Finset β)
    (s : Finset γ) (t : γ → Finset δ) (X : α → β → γ → δ → M) :
    ∑ i ∈ u, ∑ j ∈ v, ∑ c ∈ s, ∑ κ ∈ t c, X i j c κ =
      ∑ c ∈ s, ∑ κ ∈ t c, ∑ i ∈ u, ∑ j ∈ v, X i j c κ := by
  calc ∑ i ∈ u, ∑ j ∈ v, ∑ c ∈ s, ∑ κ ∈ t c, X i j c κ =
        ∑ i ∈ u, ∑ c ∈ s, ∑ j ∈ v, ∑ κ ∈ t c, X i j c κ :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ c ∈ s, ∑ i ∈ u, ∑ j ∈ v, ∑ κ ∈ t c, X i j c κ := Finset.sum_comm
    _ = ∑ c ∈ s, ∑ i ∈ u, ∑ κ ∈ t c, ∑ j ∈ v, X i j c κ :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- (6.87)–(6.88) on the good event (6.1): with `η = Im z`,
`x_S = η² Σ_{ij} |S_ij|²` equals `x_R + Σ_{1 ≤ c ≤ ξ} (-v)^c Σ_{k ∈ ℕ², |k| = c} η² Σ_{ij}
P_{γ,k}(R_ij conj R_ij)` up to `η² N² 4⁴ (8|v|)^{ξ+1}`, for `16 |v| ≤ 1`. -/
theorem norm_sq_sum_sub_expansion_le_of_good {N : ℕ} {C0 : ℝ} {ω : Entries N}
    (hω : ω ∈ goodEvent N C0) {z : ℂ} (hz : z ∈ specDomain N C0) (e : Fin N ⊕ OffDiag N)
    (hv : 16 * |entryVal e ω| ≤ 1) (ξ : ℕ) :
    ‖((z.im ^ 2 * ∑ i, ∑ j, ‖resS z ω i j‖ ^ 2 : ℝ) : ℂ) -
        ((z.im ^ 2 * ∑ i, ∑ j, ‖resR e z ω i j‖ ^ 2 : ℝ) : ℂ) -
        ∑ c ∈ Finset.Icc 1 ξ, (((-entryVal e ω) ^ c : ℝ) : ℂ) *
          ∑ k ∈ Finset.Nat.antidiagonalTuple 2 c,
            ((z.im ^ 2 : ℝ) : ℂ) * opPPair e (List.ofFn k) (resR e z ω)‖ ≤
      z.im ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * |entryVal e ω|) ^ (ξ + 1) := by
  set v := entryVal e ω with hvdef
  -- the word `G_ij conj G_ij` and its expansion
  set w : Fin N → Fin N → Word N := fun i j => [⟨.g, i, j⟩, ⟨.gbar, i, j⟩] with hw
  set D : Fin N → Fin N → ℂ := fun i j => evalWord (resS z ω) 0 (w i j) -
    ∑ c ∈ Finset.range (ξ + 1), (((-v) ^ c : ℝ) : ℂ) *
      ∑ κ ∈ Finset.Nat.antidiagonalTuple 2 c, evalW (resR e z ω) 0 (wordP e (List.ofFn κ) (w i j))
    with hD
  have hDle : ∀ i j, ‖D i j‖ ≤ 4 ^ 4 * (8 * |v|) ^ (ξ + 1) := by
    intro i j
    rcases eq_or_ne v 0 with h0 | h0
    · have hSR : resS z ω = resR e z ω := by
        simp only [resS, resR]
        rw [symOfEntries_eq_zeroEntry_add e ω, ← hvdef, h0, zero_smul, add_zero]
      have h1 : ∀ c ∈ Finset.Icc 1 ξ, (((-v) ^ c : ℝ) : ℂ) *
          ∑ κ ∈ Finset.Nat.antidiagonalTuple 2 c,
            evalW (resR e z ω) 0 (wordP e (List.ofFn κ) (w i j)) = 0 := by
        intro c hc
        rw [h0, neg_zero, zero_pow (by simp at hc; omega)]
        simp
      have h2 : ∑ κ ∈ Finset.Nat.antidiagonalTuple 2 0,
          evalW (resR e z ω) 0 (wordP e (List.ofFn κ) (w i j)) =
            evalWord (resR e z ω) 0 (w i j) := by
        rw [Finset.Nat.antidiagonalTuple_zero_right, Finset.sum_singleton]
        exact expansion_evalW_wordP_zero _ 0 e (w i j) rfl
      simp only [hD, taylor_sum_range_succ_eq, Finset.sum_eq_zero h1, h2, pow_zero,
        Complex.ofReal_one, one_mul, add_zero, hSR, sub_self, norm_zero]
      positivity
    · have hq : 0 < |v|⁻¹ := inv_pos.2 (abs_pos.2 h0)
      have h := norm_evalWord_sub_expansion_le_of_good hω hz e (m := 0) (by simp) hq
        (by rw [inv_inv]) (s := 2) (w i j) (by simp [w]) (by
          rw [le_inv_comm₀ (by norm_num) (abs_pos.2 h0)]
          push_cast; linarith) ξ
      refine h.trans (le_of_eq ?_)
      rw [div_inv_eq_mul]
      push_cast
      ring
  -- rewriting the left side as `η² Σ_{ij} D_ij`
  have hsum : ∀ G : Matrix (Fin N) (Fin N) ℂ, ((z.im ^ 2 * ∑ i, ∑ j, ‖G i j‖ ^ 2 : ℝ) : ℂ) =
      ((z.im ^ 2 : ℝ) : ℂ) * ∑ i, ∑ j, evalWord G 0 (w i j) := by
    intro G
    simp only [hw, taylor_evalWord_pair]
    push_cast
    ring
  have hexp : ∀ i j, ∑ c ∈ Finset.range (ξ + 1), (((-v) ^ c : ℝ) : ℂ) *
      ∑ κ ∈ Finset.Nat.antidiagonalTuple 2 c, evalW (resR e z ω) 0 (wordP e (List.ofFn κ) (w i j))
      = evalWord (resR e z ω) 0 (w i j) + ∑ c ∈ Finset.Icc 1 ξ, (((-v) ^ c : ℝ) : ℂ) *
      ∑ κ ∈ Finset.Nat.antidiagonalTuple 2 c, evalW (resR e z ω) 0 (wordP e (List.ofFn κ) (w i j))
      := by
    intro i j
    rw [taylor_sum_range_succ_eq, Finset.Nat.antidiagonalTuple_zero_right, Finset.sum_singleton,
      expansion_evalW_wordP_zero _ 0 e (w i j) rfl]
    simp
  have heq : ((z.im ^ 2 * ∑ i, ∑ j, ‖resS z ω i j‖ ^ 2 : ℝ) : ℂ) -
        ((z.im ^ 2 * ∑ i, ∑ j, ‖resR e z ω i j‖ ^ 2 : ℝ) : ℂ) -
        ∑ c ∈ Finset.Icc 1 ξ, (((-v) ^ c : ℝ) : ℂ) *
          ∑ k ∈ Finset.Nat.antidiagonalTuple 2 c,
            ((z.im ^ 2 : ℝ) : ℂ) * opPPair e (List.ofFn k) (resR e z ω) =
      ((z.im ^ 2 : ℝ) : ℂ) * ∑ i, ∑ j, D i j := by
    have hswap : ((z.im ^ 2 : ℝ) : ℂ) * ∑ i, ∑ j, ∑ c ∈ Finset.Icc 1 ξ, (((-v) ^ c : ℝ) : ℂ) *
        ∑ κ ∈ Finset.Nat.antidiagonalTuple 2 c,
          evalW (resR e z ω) 0 (wordP e (List.ofFn κ) (w i j)) =
        ∑ c ∈ Finset.Icc 1 ξ, (((-v) ^ c : ℝ) : ℂ) *
          ∑ k ∈ Finset.Nat.antidiagonalTuple 2 c,
            ((z.im ^ 2 : ℝ) : ℂ) * opPPair e (List.ofFn k) (resR e z ω) := by
      simp only [opPPair, Finset.mul_sum]
      rw [taylor_sum_comm4]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun κ _ =>
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsum, hsum, ← hswap]
    simp only [hD, hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have : ‖∑ i, ∑ j, D i j‖ ≤ (N : ℝ) ^ 2 * (4 ^ 4 * (8 * |v|) ^ (ξ + 1)) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hDle i j).trans ?_
    simp [Finset.sum_const, Finset.card_univ]
    ring_nf; rfl
  calc z.im ^ 2 * ‖∑ i, ∑ j, D i j‖ ≤ z.im ^ 2 * ((N : ℝ) ^ 2 * (4 ^ 4 * (8 * |v|) ^ (ξ + 1))) :=
        mul_le_mul_of_nonneg_left this (sq_nonneg _)
    _ = _ := by ring

/-! ### Continuity in the entries and the spectral parameter -/

/-- Resolvent entries at `g(x) + iη`, `η ≠ 0`, of the sample `f(x)` are continuous in `x` when
`f` and `g` are. -/
private lemma taylor_continuous_resolvent {N : ℕ} {X : Type*} [TopologicalSpace X]
    {f : X → Entries N} {g : X → ℝ} (hf : Continuous f) (hg : Continuous g) {η : ℝ}
    (hη : η ≠ 0) (i j : Fin N) :
    Continuous (fun x => resolventC (symOfEntries (f x)) ⟨g x, η⟩ i j) := by
  have hz : Continuous (fun x => (⟨g x, η⟩ : ℂ)) := by
    have : (fun x => (⟨g x, η⟩ : ℂ)) = fun x => (g x : ℂ) + (η : ℂ) * Complex.I := by
      funext x; apply Complex.ext <;> simp
    rw [this]; fun_prop
  have hM : Continuous (fun x => (symOfEntries (f x)).map (fun x : ℝ => (x : ℂ)) -
      (⟨g x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) :=
    (((continuous_symOfEntries _).comp hf).matrix_map
      Complex.continuous_ofReal).sub (hz.smul continuous_const)
  have hdet : ∀ x, ((symOfEntries (f x)).map (fun x : ℝ => (x : ℂ)) -
      (⟨g x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).det ≠ 0 := by
    intro x
    have hH := symOfEntries_isHermitian (f x)
    have hne : ∀ α, (hH.eigenvalues α : ℂ) ≠ ⟨g x, η⟩ := by
      intro α h
      apply hη
      have := congrArg Complex.im h
      simpa using this.symm
    have h1 := resolventC_mul_eq_one hH hne
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_one] at h2
    exact left_ne_zero_of_mul_eq_one h2
  have hinv : (fun x => resolventC (symOfEntries (f x)) ⟨g x, η⟩) = fun x =>
      (((symOfEntries (f x)).map (fun x : ℝ => (x : ℂ)) -
        (⟨g x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).det)⁻¹ •
      ((symOfEntries (f x)).map (fun x : ℝ => (x : ℂ)) -
        (⟨g x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).adjugate := by
    funext x
    unfold resolventC
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  have : Continuous (fun x => resolventC (symOfEntries (f x)) ⟨g x, η⟩) := by
    rw [hinv]
    exact (hM.matrix_det.inv₀ hdet).smul hM.matrix_adjugate
  exact this.matrix_elem i j

/-- `opPPair` of a matrix with continuous entries is continuous. -/
private lemma taylor_continuous_opPPair {N : ℕ} {X : Type*} [TopologicalSpace X]
    (G : X → Matrix (Fin N) (Fin N) ℂ) (hG : ∀ i j, Continuous fun x => G x i j)
    (e : Fin N ⊕ OffDiag N) (k : List ℕ) : Continuous fun x => opPPair e k (G x) := by
  unfold opPPair
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    expansion_continuous_evalW G hG 0 _

/-- `opPPair` of the resolvent of the sample `f(x)` at `g(x) + iη` is continuous in `x`. -/
private lemma taylor_continuous_opPPair_res {N : ℕ} {η : ℝ} (hη : η ≠ 0) {X : Type*}
    [TopologicalSpace X] {f : X → Entries N} {g : X → ℝ} (hf : Continuous f) (hg : Continuous g)
    (e : Fin N ⊕ OffDiag N) (k : List ℕ) :
    Continuous (fun x => opPPair e k (resolventC (symOfEntries (f x)) ⟨g x, η⟩)) :=
  taylor_continuous_opPPair (fun x => resolventC (symOfEntries (f x)) ⟨g x, η⟩)
    (fun i j => taylor_continuous_resolvent hf hg hη i j) e k

/-- `η > 0`. -/
private lemma taylor_eta_pos (N : ℕ) (ε : ℝ) (hN : 0 < N) : 0 < etaEdge N ε :=
  Real.rpow_pos_of_pos (Nat.cast_pos.2 hN) _

/-- Entries of resolvents are at most `1/η`, so `|opPPair| ≤ N² 2^{|k|} (1/η + 1)^{2+|k|}`. -/
private lemma taylor_norm_opPPair_le {N : ℕ} {G : Matrix (Fin N) (Fin N) ℂ} {B : ℝ}
    (hG : ∀ i j, ‖G i j‖ ≤ B) (e : Fin N ⊕ OffDiag N) (k : List ℕ) (hk : k.length = 2) :
    ‖opPPair e k G‖ ≤ (N : ℝ) ^ 2 * (2 ^ k.sum * (B + 1) ^ (2 + k.sum)) := by
  unfold opPPair
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    norm_evalW_wordP_le_of_le hG (by simp) e k _ (by simpa using hk)).trans ?_
  simp only [List.length_cons, List.length_nil, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring_nf
  rfl

/-- Resolvent entries at `y + iη` of a sample are at most `η⁻¹`. -/
private lemma taylor_norm_res_le {N : ℕ} {η : ℝ} (hη : 0 < η) (ω : Entries N) (y : ℝ)
    (i j : Fin N) : ‖resolventC (symOfEntries ω) ⟨y, η⟩ i j‖ ≤ η⁻¹ := by
  have := norm_resolventC_apply_le (symOfEntries_isHermitian ω) (z := ⟨y, η⟩) hη i j
  simpa [one_div] using this

/-- `1 ≤ N^a` for `a ≥ 0`. -/
private lemma taylor_one_le_rpow {N : ℕ} (hN : 0 < N) {a : ℝ} (ha : 0 ≤ a) : 1 ≤ (N : ℝ) ^ a :=
  Real.one_le_rpow (by exact_mod_cast hN) ha

/-- Points between two points of `I_ε` lie in `I_ε`. -/
private lemma taylor_mem_window {r E₁ E₂ y : ℝ} (h₁ : |E₁ - 2| ≤ r) (h₂ : |E₂ - 2| ≤ r)
    (hy : y ∈ Set.uIcc E₁ E₂) : |y - 2| ≤ r := by
  rw [abs_le] at h₁ h₂ ⊢
  rcases Set.mem_uIcc.1 hy with ⟨a, b⟩ | ⟨a, b⟩ <;> constructor <;> linarith

/-- `r / η = N^{2ε}` for `r = N^{-2/3+ε}`, `η = N^{-2/3-ε}`. -/
private lemma taylor_window_div_eta {N : ℕ} (hN : 0 < N) (ε : ℝ) :
    (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) / etaEdge N ε = (N : ℝ) ^ (2 * ε) := by
  unfold etaEdge
  rw [← Real.rpow_sub (Nat.cast_pos.2 hN)]
  congr 1
  ring

/-- Jensen's inequality for `x ↦ x^p` on an interval: `(∫_a^b g)^p ≤ (b - a)^{p-1} ∫_a^b g^p`. -/
private lemma taylor_pow_setIntegral_le {g : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hg0 : ∀ y, 0 ≤ g y)
    (hgi : IntegrableOn g (Set.Ioc a b)) {p : ℕ}
    (hgpi : IntegrableOn (fun y => g y ^ p) (Set.Ioc a b)) (hp : 1 ≤ p) :
    (∫ y in Set.Ioc a b, g y) ^ p ≤ (b - a) ^ (p - 1) * ∫ y in Set.Ioc a b, g y ^ p := by
  have hvol : volume.real (Set.Ioc a b) = b - a := by
    rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
  have h0 : volume (Set.Ioc a b) ≠ 0 := by rw [Real.volume_Ioc]; simp [hab]
  have ht : volume (Set.Ioc a b) ≠ ⊤ := by rw [Real.volume_Ioc]; simp
  have hJ := (convexOn_pow p).map_set_average_le (continuous_pow p).continuousOn isClosed_Ici h0 ht
    (Eventually.of_forall fun y => Set.mem_Ici.2 (hg0 y)) hgi hgpi
  simp only [setAverage_eq, hvol, smul_eq_mul] at hJ
  have hba : 0 < b - a := by linarith
  rw [mul_pow] at hJ
  have hpp : (b - a) ^ p = (b - a) ^ (p - 1) * (b - a) := by
    rw [← pow_succ, Nat.sub_add_cancel hp]
  have key : ((b - a)⁻¹) ^ p * (∫ y in Set.Ioc a b, g y) ^ p * (b - a) ^ p ≤
      (b - a)⁻¹ * (∫ y in Set.Ioc a b, g y ^ p) * (b - a) ^ p :=
    mul_le_mul_of_nonneg_right hJ (by positivity)
  rw [mul_comm ((b - a)⁻¹ ^ p), mul_assoc, ← mul_pow, inv_mul_cancel₀ hba.ne', one_pow,
    mul_one] at key
  calc (∫ y in Set.Ioc a b, g y) ^ p ≤ (b - a)⁻¹ * (∫ y in Set.Ioc a b, g y ^ p) * (b - a) ^ p :=
        key
    _ = (b - a) ^ (p - 1) * ∫ y in Set.Ioc a b, g y ^ p := by
        rw [hpp]; field_simp

/-- Moments of an interval integral of a bounded jointly measurable random function:
`E |∫_a^b f(y) dy|^p ≤ (b - a)^p sup_{y ∈ [a, b]} E |f(y)|^p`. -/
private lemma taylor_integral_norm_intervalIntegral_pow_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ → ℂ}
    (hf : StronglyMeasurable (Function.uncurry f)) {K : ℝ} (hK : ∀ ω y, ‖f ω y‖ ≤ K)
    {a b : ℝ} (hab : a ≤ b) {p : ℕ} (hp : 1 ≤ p) {B : ℝ}
    (hB : ∀ y ∈ Set.Icc a b, ∫ ω, ‖f ω y‖ ^ p ∂μ ≤ B) :
    ∫ ω, ‖∫ y in a..b, f ω y‖ ^ p ∂μ ≤ (b - a) ^ p * B := by
  rcases hab.eq_or_lt with rfl | hab'
  · simp [zero_pow (by omega : p ≠ 0)]
  have hB0 : 0 ≤ B := (integral_nonneg fun _ => by positivity).trans (hB a ⟨le_rfl, hab⟩)
  set t := Set.Ioc a b
  have hvol : volume.real t = b - a := by
    rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
  have htf : volume t < ⊤ := by rw [Real.volume_Ioc]; simp
  have hfm : ∀ ω, StronglyMeasurable (f ω) := fun ω => hf.comp_measurable measurable_prodMk_left
  have hint : ∀ ω (q : ℕ), IntegrableOn (fun y => ‖f ω y‖ ^ q) t := by
    intro ω q
    have : IsFiniteMeasure (volume.restrict t) := ⟨by rw [Measure.restrict_apply_univ]; exact htf⟩
    refine Integrable.of_bound ((hfm ω).norm.pow q).aestronglyMeasurable (K ^ q)
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hK ω y) q
  -- the pointwise bound
  have hpt : ∀ ω, ‖∫ y in a..b, f ω y‖ ^ p ≤ (b - a) ^ (p - 1) * ∫ y in t, ‖f ω y‖ ^ p := by
    intro ω
    have h1 : ‖∫ y in a..b, f ω y‖ ≤ ∫ y in t, ‖f ω y‖ := by
      have := intervalIntegral.norm_integral_le_integral_norm_uIoc (f := f ω) (a := a) (b := b)
        (μ := volume)
      rwa [Set.uIoc_of_le hab] at this
    calc ‖∫ y in a..b, f ω y‖ ^ p ≤ (∫ y in t, ‖f ω y‖) ^ p :=
          pow_le_pow_left₀ (norm_nonneg _) h1 p
      _ ≤ _ := taylor_pow_setIntegral_le hab' (fun y => norm_nonneg _)
          (by simpa using hint ω 1) (hint ω p) hp
  -- measurability and integrability of the bound
  have hG : StronglyMeasurable (Function.uncurry fun ω y => ‖f ω y‖ ^ p) :=
    hf.norm.pow p
  have hGm : StronglyMeasurable (fun ω => ∫ y in t, ‖f ω y‖ ^ p) :=
    hG.integral_prod_right (ν := volume.restrict t)
  have hGb : ∀ ω, ‖∫ y in t, ‖f ω y‖ ^ p‖ ≤ K ^ p * volume.real t := by
    intro ω
    refine norm_setIntegral_le_of_norm_le_const htf fun y _ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hK ω y) p
  have hGi : Integrable (fun ω => (b - a) ^ (p - 1) * ∫ y in t, ‖f ω y‖ ^ p) μ :=
    (Integrable.of_bound hGm.aestronglyMeasurable _ (Eventually.of_forall hGb)).const_mul _
  have hprod : Integrable (Function.uncurry fun ω y => ‖f ω y‖ ^ p)
      (μ.prod (volume.restrict t)) := by
    have : IsFiniteMeasure (volume.restrict t) := ⟨by rw [Measure.restrict_apply_univ]; exact htf⟩
    refine Integrable.of_bound hG.aestronglyMeasurable (K ^ p) (Eventually.of_forall fun x => ?_)
    change ‖‖f x.1 x.2‖ ^ p‖ ≤ K ^ p
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hK _ _) p
  calc ∫ ω, ‖∫ y in a..b, f ω y‖ ^ p ∂μ
      ≤ ∫ ω, (b - a) ^ (p - 1) * (∫ y in t, ‖f ω y‖ ^ p) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => by positivity) hGi
          (Eventually.of_forall hpt)
    _ = (b - a) ^ (p - 1) * ∫ y in t, (∫ ω, ‖f ω y‖ ^ p ∂μ) := by
        rw [integral_const_mul, integral_integral_swap hprod]
    _ ≤ (b - a) ^ (p - 1) * (B * (b - a)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := norm_setIntegral_le_of_norm_le_const (f := fun y => ∫ ω, ‖f ω y‖ ^ p ∂μ) htf
          (C := B) fun y hy => by
            rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => by positivity)]
            exact hB y ⟨hy.1.le, hy.2⟩
        rw [hvol] at this
        exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ this)
    _ = (b - a) ^ p * B := by
        rw [show (b - a) ^ p = (b - a) ^ (p - 1) * (b - a) by
          rw [← pow_succ, Nat.sub_add_cancel hp]]
        ring

/-- (6.89) integrated over `[E₁, E₂]`: `E |η ∫_{E₁}^{E₂} P_{γ,k}(R_ij conj R_ij)|^p ≤
(η |E₂ - E₁| B)^p` when `E |P_{γ,k}(R_ij conj R_ij)(y + iη)|^p ≤ B^p` on `I_ε`. -/
private lemma taylor_obsInt_moment {N : ℕ} {ε E₁ E₂ : ℝ} (hN : 0 < N)
    (hE₁ : |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) (hE₂ : |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε))
    (e : Fin N ⊕ OffDiag N) (μ : Measure (Entries N)) [IsProbabilityMeasure μ] (k : List ℕ)
    (hk : k.length = 2) {p : ℕ} (hp : 1 ≤ p) {B : ℝ}
    (h : ∀ y, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
      ∫ ω, ‖opPPair e k (resR e ⟨y, etaEdge N ε⟩ ω)‖ ^ p ∂μ ≤ B ^ p) :
    ∫ ω, ‖((etaEdge N ε : ℝ) : ℂ) * ∫ y in E₁..E₂, opPPair e k
        (resolventC (symOfEntries (zeroEntry e ω)) ⟨y, etaEdge N ε⟩)‖ ^ p ∂μ ≤
      (|E₂ - E₁| / etaEdge N ε * etaEdge N ε ^ 2 * B) ^ p := by
  have hη := taylor_eta_pos N ε hN
  set η := etaEdge N ε with hηdef
  set f : Entries N → ℝ → ℂ := fun ω y => opPPair e k (resR e ⟨y, η⟩ ω) with hf
  have hfc : Continuous (Function.uncurry f) :=
    taylor_continuous_opPPair_res hη.ne' ((expansion_continuous_zeroEntry e).comp continuous_fst)
      continuous_snd e k
  have hK : ∀ ω y, ‖f ω y‖ ≤ (N : ℝ) ^ 2 * (2 ^ k.sum * (η⁻¹ + 1) ^ (2 + k.sum)) :=
    fun ω y => taylor_norm_opPPair_le (taylor_norm_res_le hη _ y) e k hk
  have hJ : ∫ ω, ‖∫ y in E₁..E₂, f ω y‖ ^ p ∂μ ≤ (|E₂ - E₁| * B) ^ p := by
    rcases le_total E₁ E₂ with h12 | h21
    · have := taylor_integral_norm_intervalIntegral_pow_le hfc.stronglyMeasurable hK h12 hp
        (B := B ^ p) fun y hy => h y (taylor_mem_window hE₁ hE₂ (Set.Icc_subset_uIcc hy))
      rwa [abs_of_nonneg (by linarith), mul_pow]
    · have := taylor_integral_norm_intervalIntegral_pow_le hfc.stronglyMeasurable hK h21 hp
        (B := B ^ p) fun y hy => h y (taylor_mem_window hE₁ hE₂ (Set.Icc_subset_uIcc' hy))
      simp only [intervalIntegral.integral_symm E₂ E₁, norm_neg]
      rwa [abs_sub_comm, abs_of_nonneg (by linarith), mul_pow]
  have heq : ∀ ω, ‖((η : ℝ) : ℂ) * ∫ y in E₁..E₂, opPPair e k
      (resolventC (symOfEntries (zeroEntry e ω)) ⟨y, η⟩)‖ ^ p =
      η ^ p * ‖∫ y in E₁..E₂, f ω y‖ ^ p := by
    intro ω
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hη.le, mul_pow]
    rfl
  simp only [heq]
  rw [integral_const_mul]
  calc η ^ p * ∫ ω, ‖∫ y in E₁..E₂, f ω y‖ ^ p ∂μ ≤ η ^ p * (|E₂ - E₁| * B) ^ p :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = _ := by
        rw [← mul_pow]
        congr 1
        field_simp

/-! ### Asymptotic bookkeeping -/

/-- Polylogarithmic factors are below any power of `N`. -/
private lemma taylor_ev_log (A : ℝ) (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, A * (1 + Real.log N) ^ k ≤ (N : ℝ) ^ δ := by
  have hb := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hδ).bound
    (show (0 : ℝ) < 1 / (|A| * 2 ^ k + 1) by positivity)
  have hb' := tendsto_natCast_atTop_atTop.eventually hb
  filter_upwards [hb', eventually_ge_atTop 3] with N h h3
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast h3
  have hlog1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hN3
  have hNδ : 0 ≤ (N : ℝ) ^ δ := by positivity
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
    Real.norm_of_nonneg hNδ, Real.rpow_natCast] at h
  have h2 : (1 + Real.log N) ^ k ≤ 2 ^ k * Real.log N ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) k
  calc A * (1 + Real.log N) ^ k ≤ |A| * (1 + Real.log N) ^ k :=
        mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
    _ ≤ |A| * (2 ^ k * Real.log N ^ k) := mul_le_mul_of_nonneg_left h2 (abs_nonneg A)
    _ = (|A| * 2 ^ k) * Real.log N ^ k := by ring
    _ ≤ (|A| * 2 ^ k + 1) * (1 / (|A| * 2 ^ k + 1) * (N : ℝ) ^ δ) := by
        gcongr; linarith
    _ = (N : ℝ) ^ δ := by field_simp

/-- A ζ-high probability bound is below any power `N^{-D}`. -/
private lemma taylor_ev_highProb (C c D ζ : ℝ) (hc : 0 < c) (hζ : 1 ≤ ζ) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ C * Real.exp (-c * phi N ^ ζ) ≤ (N : ℝ) ^ (-D) := by
  filter_upwards [expansion_eventually_log_le ((C + D) / c), eventually_ge_atTop 3] with N h h3
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast h3
  have hN0 : (0 : ℝ) < N := by linarith
  have hφ1 : 1 ≤ phi N := by
    rw [phi_eq_exp h3]; exact Real.one_le_exp (sq_nonneg _)
  have hφζ : phi N ≤ phi N ^ ζ := by
    calc phi N = phi N ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ phi N ^ ζ := Real.rpow_le_rpow_of_exponent_le hφ1 hζ
  have key : (C + D) * Real.log N ≤ c * phi N ^ ζ := by
    have := mul_le_mul_of_nonneg_left (h.trans hφζ) hc.le
    rwa [← mul_assoc, mul_div_cancel₀ _ hc.ne'] at this
  rw [Real.rpow_def_of_pos hN0, Real.rpow_def_of_pos hN0, ← Real.exp_add]
  exact Real.exp_le_exp.2 (by nlinarith)

/-- Every constant is eventually below `N^δ`, `δ > 0`. -/
private lemma taylor_ev_const (A : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, A ≤ (N : ℝ) ^ δ :=
  (tendsto_natCast_atTop_atTop.eventually ((tendsto_rpow_atTop hδ).eventually_ge_atTop A))

/-! ### Markov's inequality for the expanded terms -/

/-- `η² = N^{-4/3-2ε}`. -/
private lemma taylor_eta_sq (N : ℕ) (ε : ℝ) :
    etaEdge N ε ^ 2 = (N : ℝ) ^ (-(4 : ℝ) / 3 - 2 * ε) := by
  unfold etaEdge
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  congr 1; push_cast; ring

/-- `M η² N^{1+Cε} ≤ 2 N^{-1/3+Cε}` for `M ≤ 2 N^{2ε}`. -/
private lemma taylor_mass_rate {N : ℕ} (hN : 0 < N) {ε C M : ℝ} (hM : M ≤ 2 * (N : ℝ) ^ (2 * ε)) :
    M * etaEdge N ε ^ 2 * (N : ℝ) ^ (1 + C * ε) ≤ 2 * (N : ℝ) ^ (-(1 : ℝ) / 3 + C * ε) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  rw [taylor_eta_sq N]
  calc M * (N : ℝ) ^ (-(4 : ℝ) / 3 - 2 * ε) * (N : ℝ) ^ (1 + C * ε) ≤
      2 * (N : ℝ) ^ (2 * ε) * (N : ℝ) ^ (-(4 : ℝ) / 3 - 2 * ε) * (N : ℝ) ^ (1 + C * ε) := by
        gcongr
    _ = 2 * (N : ℝ) ^ (-(1 : ℝ) / 3 + C * ε) := by
        rw [mul_assoc 2, ← Real.rpow_add hN0, mul_assoc, ← Real.rpow_add hN0]
        congr 2; ring

/-- Markov's inequality at a power `p`: `P(‖Y‖ > t) ≤ (A / t)^p` when `E ‖Y‖^p ≤ A^p`, for a
bounded measurable `Y`. -/
private lemma taylor_markov {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℂ} (hY : Measurable Y) {K : ℝ} (hK : ∀ ω, ‖Y ω‖ ≤ K) {p : ℕ} {A t : ℝ}
    (ht : 0 < t) (hA : ∫ ω, ‖Y ω‖ ^ p ∂μ ≤ A ^ p) :
    μ.real {ω | t < ‖Y ω‖} ≤ (A / t) ^ p := by
  have hint : Integrable (fun ω => ‖Y ω‖ ^ p) μ := by
    refine Integrable.of_bound (hY.norm.pow_const p).aestronglyMeasurable (K ^ p)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hK ω) p
  have hm := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω => by positivity)
    hint (t ^ p)
  have hsub : {ω | t < ‖Y ω‖} ⊆ {ω | t ^ p ≤ ‖Y ω‖ ^ p} :=
    fun ω hω => pow_le_pow_left₀ ht.le (le_of_lt hω) p
  have htp : 0 < t ^ p := pow_pos ht p
  calc μ.real {ω | t < ‖Y ω‖} ≤ μ.real {ω | t ^ p ≤ ‖Y ω‖ ^ p} := measureReal_mono hsub
    _ ≤ A ^ p / t ^ p := by rw [le_div_iff₀ htp, mul_comm]; exact hm.trans hA
    _ = _ := by rw [div_pow]

/-- The rate of (6.90): `(M η² N^{1+Cε} / N^{-1/3+(C+1)ε})^p ≤ N^{-D}` once `N^{ε/2} ≥ 2` and
`εp/2 ≥ D`. -/
private lemma taylor_rate_pow {N : ℕ} (hN : 0 < N) {ε C M D : ℝ} {p : ℕ} (hM0 : 0 ≤ M)
    (hM : M ≤ 2 * (N : ℝ) ^ (2 * ε)) (h2 : 2 ≤ (N : ℝ) ^ (ε / 2)) (hpD : D ≤ ε / 2 * p) :
    (M * etaEdge N ε ^ 2 * (N : ℝ) ^ (1 + C * ε) / (N : ℝ) ^ (-(1 : ℝ) / 3 + (C + 1) * ε)) ^ p ≤
      (N : ℝ) ^ (-D) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 ≤ M * etaEdge N ε ^ 2 * (N : ℝ) ^ (1 + C * ε) /
      (N : ℝ) ^ (-(1 : ℝ) / 3 + (C + 1) * ε) := by
    have := taylor_eta_pos N ε hN; positivity
  have hx : M * etaEdge N ε ^ 2 * (N : ℝ) ^ (1 + C * ε) /
      (N : ℝ) ^ (-(1 : ℝ) / 3 + (C + 1) * ε) ≤ (N : ℝ) ^ (-(ε / 2)) := by
    rw [div_le_iff₀ (by positivity)]
    refine (taylor_mass_rate hN hM).trans ?_
    calc 2 * (N : ℝ) ^ (-(1 : ℝ) / 3 + C * ε) ≤
        (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (-(1 : ℝ) / 3 + C * ε) := by gcongr
      _ = (N : ℝ) ^ (-(ε / 2)) * (N : ℝ) ^ (-(1 : ℝ) / 3 + (C + 1) * ε) := by
        rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; congr 1; ring
  calc _ ≤ ((N : ℝ) ^ (-(ε / 2))) ^ p := pow_le_pow_left₀ hx0 hx p
    _ = (N : ℝ) ^ (-(ε / 2) * p) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    _ ≤ (N : ℝ) ^ (-D) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)

/-- (6.90) from (6.89) by Markov's inequality, and its integrated form for (5.15):
for `k ∈ ℕ²` with `1 ≤ |k| ≤ ⌈3/φs⌉`, `|η² Σ_{ij} P_{γ,k}(R_ij conj R_ij)| ≤ N^{-1/3+Cε}` at every
`E ∈ I_ε`, and `|η ∫_{E₁}^{E₂} Σ_{ij} P_{γ,k}(R_ij conj R_ij)(y + iη) dy| ≤ N^{-1/3+Cε}` for
`E₁, E₂ ∈ I_ε`, each outside a set of probability at most `N^{-D}`, for every `D > 0`. -/
theorem law_opPPair_gt_le {C1 φs : ℝ} (hφs : 0 < φs) :
    ∃ ε₀ > (0 : ℝ), ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ D > (0 : ℝ), ∃ N0 : ℕ,
      ∀ N ≥ N0, ∀ (Lv Lw : EntryLaws N) (γ : ℕ), SmallQClass C1 φs N Lv → Lv.IsMomentMatch Lw C1 →
      ∀ (e : Fin N ⊕ OffDiag N) (k : List ℕ), k.length = 2 → 1 ≤ k.sum → k.sum ≤ ⌈3 / φs⌉₊ →
        (∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          (interp (lexPos N) γ Lv Lw).law {ω | (N : ℝ) ^ (-(1 : ℝ) / 3 + C * ε) <
            ‖((etaEdge N ε ^ 2 : ℝ) : ℂ) * opPPair e k (resR e ⟨E, etaEdge N ε⟩ ω)‖} ≤
            ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
        (∀ E₁ E₂ : ℝ, |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          (interp (lexPos N) γ Lv Lw).law {ω | (N : ℝ) ^ (-(1 : ℝ) / 3 + C * ε) <
            ‖((etaEdge N ε : ℝ) : ℂ) *
              ∫ y in E₁..E₂, opPPair e k (resR e ⟨y, etaEdge N ε⟩ ω)‖} ≤
            ENNReal.ofReal ((N : ℝ) ^ (-D))) := by
  obtain ⟨ε₁, hε₁, Cp, hCp, hpm⟩ := moment_opP_pair_le (C1 := C1) hφs
  refine ⟨ε₁, hε₁, Cp + 1, by positivity, fun ε hε hεε₁ D hD => ?_⟩
  set p : ℕ := 2 * (⌈D / ε⌉₊ + 1) with hp
  have hpe : Even p := ⟨⌈D / ε⌉₊ + 1, by omega⟩
  have hp1 : 1 ≤ p := by omega
  have hpD : D ≤ ε / 2 * p := by
    have h1 : D / ε ≤ ⌈D / ε⌉₊ := Nat.le_ceil _
    rw [div_le_iff₀ hε] at h1
    have h2 : (p : ℝ) = 2 * ((⌈D / ε⌉₊ : ℝ) + 1) := by rw [hp]; push_cast; ring
    rw [h2]; nlinarith
  obtain ⟨N1, hN1⟩ := hpm ε hε hεε₁ p hpe
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 (taylor_ev_const 2 (half_pos hε))
  refine ⟨max (max N1 N2) 3, fun N hN Lv Lw γ hv hw e k hk hk1 hk2 => ?_⟩
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : 0 < N := by omega
  have h2 : 2 ≤ (N : ℝ) ^ (ε / 2) := hN2 N (le_trans (le_trans (le_max_right _ _)
    (le_max_left _ _)) hN)
  have hmp := (MatchedPair.of_smallQ hN3 hv hw).interp γ
  have hprob := isProbabilityMeasure_law hmp.isProb_v
  have hη := taylor_eta_pos N ε hNpos
  have hB : ∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
      ∫ ω, ‖opPPair e k (resR e ⟨E, etaEdge N ε⟩ ω)‖ ^ p ∂(interp (lexPos N) γ Lv Lw).law ≤
        ((N : ℝ) ^ (1 + Cp * ε)) ^ p :=
    fun E hE => hN1 N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN) Lv Lw γ hv hw
      e k hk hk1 hk2 E hE
  have hreal : ∀ S : Set (Entries N), (interp (lexPos N) γ Lv Lw).law.real S ≤ (N : ℝ) ^ (-D) →
      (interp (lexPos N) γ Lv Lw).law S ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := fun S h => by
    rw [← ofReal_measureReal]; exact ENNReal.ofReal_le_ofReal h
  have ht : 0 < (N : ℝ) ^ (-(1 : ℝ) / 3 + (Cp + 1) * ε) := by positivity
  have hcF : Continuous fun p : Entries N × ℝ => opPPair e k (resR e ⟨p.2, etaEdge N ε⟩ p.1) :=
    taylor_continuous_opPPair_res hη.ne' ((expansion_continuous_zeroEntry e).comp continuous_fst)
      continuous_snd e k
  constructor
  · intro E hE
    apply hreal
    have hY : Continuous fun ω => ((etaEdge N ε ^ 2 : ℝ) : ℂ) *
        opPPair e k (resR e ⟨E, etaEdge N ε⟩ ω) :=
      continuous_const.mul (taylor_continuous_opPPair_res hη.ne'
        (expansion_continuous_zeroEntry e) continuous_const e k)
    have hK : ∀ ω, ‖((etaEdge N ε ^ 2 : ℝ) : ℂ) * opPPair e k (resR e ⟨E, etaEdge N ε⟩ ω)‖ ≤
        etaEdge N ε ^ 2 * ((N : ℝ) ^ 2 * (2 ^ k.sum * ((etaEdge N ε)⁻¹ + 1) ^ (2 + k.sum))) := by
      intro ω
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left
        (taylor_norm_opPPair_le (taylor_norm_res_le hη _ E) e k hk) (by positivity)
    have hA : ∫ ω, ‖((etaEdge N ε ^ 2 : ℝ) : ℂ) * opPPair e k (resR e ⟨E, etaEdge N ε⟩ ω)‖ ^ p
        ∂(interp (lexPos N) γ Lv Lw).law ≤ (1 * etaEdge N ε ^ 2 * (N : ℝ) ^ (1 + Cp * ε)) ^ p := by
      have heq : ∀ ω, ‖((etaEdge N ε ^ 2 : ℝ) : ℂ) * opPPair e k (resR e ⟨E, etaEdge N ε⟩ ω)‖ ^ p
          = (etaEdge N ε ^ 2) ^ p * ‖opPPair e k (resR e ⟨E, etaEdge N ε⟩ ω)‖ ^ p := by
        intro ω
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow]
      simp only [heq]
      rw [integral_const_mul, one_mul, mul_pow]
      exact mul_le_mul_of_nonneg_left (hB E hE) (by positivity)
    exact (taylor_markov hY.measurable hK ht hA).trans
      (taylor_rate_pow hNpos zero_le_one (by
        have := taylor_one_le_rpow hNpos (a := 2 * ε) (by linarith); linarith) h2 hpD)
  · intro E₁ E₂ hE₁ hE₂
    apply hreal
    have hY : Continuous fun ω => ((etaEdge N ε : ℝ) : ℂ) *
        ∫ y in E₁..E₂, opPPair e k (resR e ⟨y, etaEdge N ε⟩ ω) :=
      continuous_const.mul
        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          (f := fun ω y => opPPair e k (resR e ⟨y, etaEdge N ε⟩ ω)) hcF continuous_const)
    have hK : ∀ ω, ‖((etaEdge N ε : ℝ) : ℂ) *
        ∫ y in E₁..E₂, opPPair e k (resR e ⟨y, etaEdge N ε⟩ ω)‖ ≤ etaEdge N ε *
          ((N : ℝ) ^ 2 * (2 ^ k.sum * ((etaEdge N ε)⁻¹ + 1) ^ (2 + k.sum)) * |E₂ - E₁|) := by
      intro ω
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hη.le]
      exact mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_of_norm_le_const
        fun y _ => taylor_norm_opPPair_le (taylor_norm_res_le hη _ y) e k hk) hη.le
    have hA := taylor_obsInt_moment hNpos hE₁ hE₂ e (interp (lexPos N) γ Lv Lw).law k hk hp1 hB
    have hM : |E₂ - E₁| / etaEdge N ε ≤ 2 * (N : ℝ) ^ (2 * ε) := by
      rw [← taylor_window_div_eta hNpos ε, mul_div_assoc']
      refine div_le_div_of_nonneg_right ?_ hη.le
      have := abs_sub_le E₂ 2 E₁
      rw [abs_sub_comm 2 E₁] at this
      linarith
    exact (taylor_markov hY.measurable hK ht hA).trans
      (taylor_rate_pow hNpos (by positivity) hM h2 hpD)

/-- The observable `x = η² Σ_{ij} |G_ij|²` of (5.14), (6.80) at `z = E + iη`,
`η = N^{-2/3-ε}`. -/
def obsPoint (N : ℕ) (ε E : ℝ) (H : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  etaEdge N ε ^ 2 * ∑ i, ∑ j, ‖resolventC H ⟨E, etaEdge N ε⟩ i j‖ ^ 2

/-- The observable `N ∫_{E₁}^{E₂} Im m(y + iη) dy` of (5.15), `η = N^{-2/3-ε}`. -/
def obsInt (N : ℕ) (ε E₁ E₂ : ℝ) (H : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  N * ∫ y in E₁..E₂, (stieltjesM H ⟨y, etaEdge N ε⟩).im

/-- The observables of Lemma 5.5: (5.14) at `E ∈ I_ε` and (5.15) for `E₁, E₂ ∈ I_ε`. -/
def edgeObs (N : ℕ) (ε : ℝ) : Set (Matrix (Fin N) (Fin N) ℝ → ℝ) :=
  {X | (∃ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) ∧ X = obsPoint N ε E) ∨
    ∃ E₁ E₂ : ℝ, |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) ∧
      |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) ∧ X = obsInt N ε E₁ E₂}

/-! ### Ward identities and deterministic bounds -/

/-- Ward form of `x` (6.80): `x = η Im Tr G`. -/
private lemma taylor_obsPoint_eq {N : ℕ} {ε : ℝ} (hN : 0 < N) (E : ℝ)
    (H : Matrix (Fin N) (Fin N) ℝ) (hH : H.IsHermitian) :
    obsPoint N ε E H = etaEdge N ε * ((resolventC H ⟨E, etaEdge N ε⟩).trace).im := by
  have hη := taylor_eta_pos N ε hN
  unfold obsPoint
  rw [show etaEdge N ε = (⟨E, etaEdge N ε⟩ : ℂ).im from rfl,
    sq_sum_norm_resolventC_eq hH (z := ⟨E, etaEdge N ε⟩) hη]
  unfold stieltjesM
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hc : (N : ℂ)⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, Complex.im_ofReal_mul]
  field_simp

/-- `0 ≤ x`. -/
private lemma taylor_obsPoint_nonneg {N : ℕ} (ε E : ℝ) (H : Matrix (Fin N) (Fin N) ℝ) :
    0 ≤ obsPoint N ε E H := by
  unfold obsPoint; positivity

/-- `x ≤ N`: every entry of `G` is at most `η⁻¹`. -/
private lemma taylor_obsPoint_le {N : ℕ} {ε : ℝ} (hN : 0 < N) (E : ℝ)
    (H : Matrix (Fin N) (Fin N) ℝ) (hH : H.IsHermitian) : obsPoint N ε E H ≤ N := by
  have hη := taylor_eta_pos N ε hN
  rw [taylor_obsPoint_eq hN E H hH]
  have htr : ‖(resolventC H ⟨E, etaEdge N ε⟩).trace‖ ≤ N * (1 / etaEdge N ε) := by
    unfold Matrix.trace
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => norm_resolventC_apply_le hH (z := ⟨E, etaEdge N ε⟩)
      hη i i).trans ?_
    simp
  calc etaEdge N ε * ((resolventC H ⟨E, etaEdge N ε⟩).trace).im
      ≤ etaEdge N ε * ‖(resolventC H ⟨E, etaEdge N ε⟩).trace‖ :=
        mul_le_mul_of_nonneg_left (Complex.im_le_norm _) hη.le
    _ ≤ etaEdge N ε * (N * (1 / etaEdge N ε)) := mul_le_mul_of_nonneg_left htr hη.le
    _ = N := by field_simp

/-- (6.81): the rank-two swap moves `x` by at most `2`. -/
private lemma taylor_abs_obsPoint_sub_le {N : ℕ} {ε : ℝ} (hN : 0 < N) (E : ℝ)
    (e : Fin N ⊕ OffDiag N) (ω : Entries N) :
    |obsPoint N ε E (symOfEntries ω) - obsPoint N ε E (symOfEntries (zeroEntry e ω))| ≤ 2 := by
  have hη := taylor_eta_pos N ε hN
  have hQ := symOfEntries_isHermitian (zeroEntry e ω)
  have hV := starExpansion_isHermitian_smul_entryMat e (entryVal e ω)
  obtain ⟨a, b, hab⟩ : ∃ a b : Fin N, ∀ k l, (entryVal e ω • entryMat e) k l ≠ 0 →
      (k = a ∧ l = b) ∨ (k = b ∧ l = a) := by
    rcases e with i | p
    · refine ⟨i, i, fun k l h => ?_⟩
      by_contra hc
      apply h
      simp only [Matrix.smul_apply, entryMat, entryPairs, List.mem_singleton, Prod.mk.injEq,
        smul_eq_mul]
      split_ifs <;> first | (exfalso; tauto) | ring
    · refine ⟨p.1.1, p.1.2, fun k l h => ?_⟩
      by_contra hc
      apply h
      simp only [Matrix.smul_apply, entryMat, entryPairs, List.mem_cons, Prod.mk.injEq,
        List.not_mem_nil, or_false, smul_eq_mul]
      simp [hc]
  have htr := norm_trace_resolventC_sub_le_two hQ hV a b hab (z := ⟨E, etaEdge N ε⟩) hη
  rw [← symOfEntries_eq_zeroEntry_add] at htr
  rw [taylor_obsPoint_eq hN E _ (symOfEntries_isHermitian ω), taylor_obsPoint_eq hN E _ hQ,
    ← mul_sub, ← Complex.sub_im, abs_mul, abs_of_pos hη]
  calc etaEdge N ε * |((resolventC (symOfEntries ω) ⟨E, etaEdge N ε⟩).trace -
        (resolventC (symOfEntries (zeroEntry e ω)) ⟨E, etaEdge N ε⟩).trace).im|
      ≤ etaEdge N ε * (2 / etaEdge N ε) :=
        mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans htr) hη.le
    _ = 2 := by field_simp

/-- `N Im m(y + iη) = η⁻¹ x(y)`, so `X = ∫_{E₁}^{E₂} η⁻¹ x(y) dy` for (5.15). -/
private lemma taylor_obsInt_eq {N : ℕ} {ε : ℝ} (hN : 0 < N) (E₁ E₂ : ℝ)
    (H : Matrix (Fin N) (Fin N) ℝ) (hH : H.IsHermitian) :
    obsInt N ε E₁ E₂ H = ∫ y in E₁..E₂, (etaEdge N ε)⁻¹ * obsPoint N ε y H := by
  have hη := taylor_eta_pos N ε hN
  unfold obsInt
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun y _ => ?_
  rw [taylor_obsPoint_eq hN y H hH]
  unfold stieltjesM
  have hc : (N : ℂ)⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, Complex.im_ofReal_mul]
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  field_simp

/-- `x(g(t))` at the sample `f(t)` is continuous in `t` when `f` and `g` are. -/
private lemma taylor_continuous_obsPoint {N : ℕ} {ε : ℝ} (hN : 0 < N) {X : Type*}
    [TopologicalSpace X] {f : X → Entries N} {g : X → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => obsPoint N ε (g x) (symOfEntries (f x))) := by
  have hη := taylor_eta_pos N ε hN
  unfold obsPoint
  exact continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((taylor_continuous_resolvent hf hg hη.ne' i j).norm).pow 2)

/-- Weight of one swap in (6.102)–(6.103): `N⁻²` off the diagonal and `N⁻¹` on it. -/
def swapWeight (N : ℕ) : Fin N ⊕ OffDiag N → ℝ
  | Sum.inl _ => (N : ℝ)⁻¹
  | Sum.inr _ => ((N : ℝ) ^ 2)⁻¹

/-- There are at most `N²/2` upper index pairs. -/
private lemma taylor_two_mul_card_offDiag_le (N : ℕ) : 2 * Fintype.card (OffDiag N) ≤ N ^ 2 := by
  let f : OffDiag N ⊕ OffDiag N → Fin N × Fin N := fun x => Sum.elim (fun p => p.1)
    (fun p => (p.1.2, p.1.1)) x
  have hf : Function.Injective f := by
    rintro (p | p) (q | q) h <;> simp only [f, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at h
    · exact congrArg Sum.inl (Subtype.ext h)
    · have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only at h1 h2
      have := p.2
      rw [h1, h2] at this
      exact absurd this (not_lt.2 q.2.le)
    · have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only at h1 h2
      have := q.2
      rw [← h1, ← h2] at this
      exact absurd this (not_lt.2 p.2.le)
    · exact congrArg Sum.inr (Subtype.ext (Prod.ext h.2 h.1))
  have := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at this
  nlinarith

/-- The swap weights sum to `1 + (N - 1)/(2N) ≤ 3/2`. -/
theorem sum_swapWeight_le (N : ℕ) : ∑ e : Fin N ⊕ OffDiag N, swapWeight N e ≤ 3 / 2 := by
  rw [Fintype.sum_sum_type]
  simp only [swapWeight, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · norm_num
  · have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
    have h1 : (N : ℝ) * (N : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hN'.ne'
    have h2 : (2 * Fintype.card (OffDiag N) : ℝ) ≤ (N : ℝ) ^ 2 := by
      exact_mod_cast taylor_two_mul_card_offDiag_le N
    have h3 : (Fintype.card (OffDiag N) : ℝ) * ((N : ℝ) ^ 2)⁻¹ ≤ 1 / 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]; linarith
    linarith

/-! ### The two observables as data for one swap -/

/-- Data of an observable of Lemma 5.5 for one swap at the entry `e`: its mass `M`, the expanded
terms `Y_k`, and the deterministic and moment bounds used in (6.101)–(6.105). -/
private structure TayObs (N : ℕ) (ε : ℝ) (e : Fin N ⊕ OffDiag N)
    (X : Matrix (Fin N) (Fin N) ℝ → ℝ) : Type where
  M : ℝ
  Y : List ℕ → Entries N → ℂ
  M_nonneg : 0 ≤ M
  M_le : M ≤ 2 * (N : ℝ) ^ (2 * ε)
  cont_X : Continuous fun ω : Entries N => X (symOfEntries ω)
  cont_Y : ∀ k, Continuous (Y k)
  abs_X_le : ∀ ω, |X (symOfEntries ω)| ≤ M * N
  abs_sub_le : ∀ ω, |X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))| ≤ 2 * M
  abs_X_le_of : ∀ ω (A : ℝ), (∀ y, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
      obsPoint N ε y (symOfEntries ω) ≤ A) → |X (symOfEntries ω)| ≤ M * A
  expand : ∀ C0 : ℝ, (∀ y, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
      (⟨y, etaEdge N ε⟩ : ℂ) ∈ specDomain N C0) → ∀ ω ∈ goodEvent N C0,
      16 * |entryVal e ω| ≤ 1 → ∀ ξ : ℕ,
      ‖((X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω)) : ℝ) : ℂ) -
        ∑ c ∈ Finset.Icc 1 ξ, (((-entryVal e ω) ^ c : ℝ) : ℂ) *
          ∑ k ∈ Finset.Nat.antidiagonalTuple 2 c, Y (List.ofFn k) (zeroEntry e ω)‖ ≤
        M * (etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * |entryVal e ω|) ^ (ξ + 1))
  Y_le : ∀ k : List ℕ, k.length = 2 → ∀ ω, ‖Y k ω‖ ≤
      M * (etaEdge N ε ^ 2 * ((N : ℝ) ^ 2 * (2 ^ k.sum * ((etaEdge N ε)⁻¹ + 1) ^ (2 + k.sum))))
  moment : ∀ (μ : Measure (Entries N)), IsProbabilityMeasure μ → ∀ (k : List ℕ),
      k.length = 2 → ∀ (p : ℕ), 1 ≤ p → ∀ B : ℝ, 0 ≤ B →
      (∀ y, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
        ∫ ω, ‖opPPair e k (resR e ⟨y, etaEdge N ε⟩ ω)‖ ^ p ∂μ ≤ B ^ p) →
      ∫ ω, ‖Y k (zeroEntry e ω)‖ ^ p ∂μ ≤ (M * etaEdge N ε ^ 2 * B) ^ p

/-- The observable (5.14) as data. -/
private def taylor_obsPointData {N : ℕ} {ε E : ℝ} (hN : 0 < N) (hε : 0 ≤ ε)
    (hE : |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) (e : Fin N ⊕ OffDiag N) :
    TayObs N ε e (obsPoint N ε E) where
  M := 1
  Y k ω := ((etaEdge N ε ^ 2 : ℝ) : ℂ) * opPPair e k (resolventC (symOfEntries ω) ⟨E, etaEdge N ε⟩)
  M_nonneg := zero_le_one
  M_le := by
    have := taylor_one_le_rpow hN (a := 2 * ε) (by linarith)
    linarith
  cont_X := taylor_continuous_obsPoint hN continuous_id continuous_const
  cont_Y k := continuous_const.mul (taylor_continuous_opPPair_res
    (taylor_eta_pos N ε hN).ne' continuous_id continuous_const e k)
  abs_X_le ω := by
    rw [abs_of_nonneg (taylor_obsPoint_nonneg ε E _), one_mul]
    exact taylor_obsPoint_le hN E _ (symOfEntries_isHermitian ω)
  abs_sub_le ω := by
    have := taylor_abs_obsPoint_sub_le (ε := ε) hN E e ω
    linarith
  abs_X_le_of ω A h := by
    rw [abs_of_nonneg (taylor_obsPoint_nonneg ε E _), one_mul]
    exact h E hE
  expand C0 hspec ω hω hv ξ := by
    have h := norm_sq_sum_sub_expansion_le_of_good hω (hspec E hE) e hv ξ
    rw [one_mul, Complex.ofReal_sub]
    exact h
  Y_le k hk ω := by
    have hη := taylor_eta_pos N ε hN
    rw [one_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left
      (taylor_norm_opPPair_le (taylor_norm_res_le hη ω E) e k hk) (by positivity)
  moment μ _ k _ p _ B _ h := by
    have hη := taylor_eta_pos N ε hN
    have heq : ∀ ω, ‖((etaEdge N ε ^ 2 : ℝ) : ℂ) *
        opPPair e k (resolventC (symOfEntries (zeroEntry e ω)) ⟨E, etaEdge N ε⟩)‖ ^ p =
        (etaEdge N ε ^ 2) ^ p * ‖opPPair e k (resR e ⟨E, etaEdge N ε⟩ ω)‖ ^ p := by
      intro ω
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow]
      rfl
    simp only [heq]
    rw [integral_const_mul, one_mul, mul_pow]
    exact mul_le_mul_of_nonneg_left (h E hE) (by positivity)

/-- (6.87)–(6.88) for the observable (5.15): the expansion of `X_S - X_R`, integrated over
`[E₁, E₂]`, with remainder `η⁻¹ |E₂ - E₁|` times that of (6.88). -/
private lemma taylor_obsInt_expand {N : ℕ} {ε E₁ E₂ : ℝ} (hN : 0 < N)
    (hE₁ : |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) (hE₂ : |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε))
    (e : Fin N ⊕ OffDiag N) {C0 : ℝ} (hspec : ∀ y, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
      (⟨y, etaEdge N ε⟩ : ℂ) ∈ specDomain N C0) {ω : Entries N} (hω : ω ∈ goodEvent N C0)
    (hv : 16 * |entryVal e ω| ≤ 1) (ξ : ℕ) :
    ‖((obsInt N ε E₁ E₂ (symOfEntries ω) - obsInt N ε E₁ E₂ (symOfEntries (zeroEntry e ω)) : ℝ) :
        ℂ) - ∑ c ∈ Finset.Icc 1 ξ, (((-entryVal e ω) ^ c : ℝ) : ℂ) *
          ∑ k ∈ Finset.Nat.antidiagonalTuple 2 c, ((etaEdge N ε : ℝ) : ℂ) *
            ∫ y in E₁..E₂, opPPair e (List.ofFn k)
              (resolventC (symOfEntries (zeroEntry e ω)) ⟨y, etaEdge N ε⟩)‖ ≤
      |E₂ - E₁| / etaEdge N ε *
        (etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * |entryVal e ω|) ^ (ξ + 1)) := by
  have hη := taylor_eta_pos N ε hN
  set η := etaEdge N ε with hηdef
  set v := entryVal e ω with hvdef
  set δ := η ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * |v|) ^ (ξ + 1) with hδ
  have hwin : ∀ y ∈ Set.uIoc E₁ E₂, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) :=
    fun y hy => taylor_mem_window hE₁ hE₂ (Set.uIoc_subset_uIcc hy)
  have hcx : ∀ ω : Entries N, Continuous fun y => obsPoint N ε y (symOfEntries ω) :=
    fun ω => taylor_continuous_obsPoint hN continuous_const continuous_id
  have hcF : ∀ k : List ℕ, Continuous fun y => opPPair e k (resR e ⟨y, η⟩ ω) :=
    fun k => taylor_continuous_opPPair_res hη.ne' continuous_const continuous_id e k
  have hXeq : ∀ ω : Entries N, obsInt N ε E₁ E₂ (symOfEntries ω) =
      ∫ y in E₁..E₂, η⁻¹ * obsPoint N ε y (symOfEntries ω) :=
    fun ω => taylor_obsInt_eq hN E₁ E₂ _ (symOfEntries_isHermitian ω)
  set g : ℝ → ℝ := fun y => obsPoint N ε y (symOfEntries ω) -
    obsPoint N ε y (symOfEntries (zeroEntry e ω)) with hg
  have hgc : Continuous g := (hcx ω).sub (hcx _)
  set T : ℝ → ℂ := fun y => ∑ c ∈ Finset.Icc 1 ξ, (((-v) ^ c : ℝ) : ℂ) *
    ∑ k ∈ Finset.Nat.antidiagonalTuple 2 c,
      ((η : ℝ) : ℂ) * opPPair e (List.ofFn k) (resR e ⟨y, η⟩ ω)
    with hT
  have hTc : Continuous T := continuous_finsetSum _ fun c _ => continuous_const.mul
    (continuous_finsetSum _ fun k _ => continuous_const.mul (hcF _))
  have hi : ∀ ω' : Entries N, IntervalIntegrable
      (fun y => η⁻¹ * obsPoint N ε y (symOfEntries ω')) volume E₁ E₂ :=
    fun ω' => (continuous_const.mul (hcx ω')).intervalIntegrable _ _
  have h1 : ((obsInt N ε E₁ E₂ (symOfEntries ω) - obsInt N ε E₁ E₂
      (symOfEntries (zeroEntry e ω)) : ℝ) : ℂ) = ∫ y in E₁..E₂, (((η⁻¹ * g y) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_ofReal, hXeq, hXeq, ← intervalIntegral.integral_sub (hi ω) (hi _)]
    simp only [hg, mul_sub]
  have h2 : ∑ c ∈ Finset.Icc 1 ξ, (((-v) ^ c : ℝ) : ℂ) *
      ∑ k ∈ Finset.Nat.antidiagonalTuple 2 c, ((η : ℝ) : ℂ) *
        ∫ y in E₁..E₂, opPPair e (List.ofFn k) (resolventC (symOfEntries (zeroEntry e ω)) ⟨y, η⟩) =
      ∫ y in E₁..E₂, T y := by
    have hci1 : ∀ k : List ℕ, IntervalIntegrable
        (fun y => ((η : ℝ) : ℂ) * opPPair e k (resR e ⟨y, η⟩ ω)) volume E₁ E₂ :=
      fun k => (continuous_const.mul (hcF k)).intervalIntegrable _ _
    have hci2 : ∀ c : ℕ, IntervalIntegrable (fun y => (((-v) ^ c : ℝ) : ℂ) *
        ∑ k ∈ Finset.Nat.antidiagonalTuple 2 c, ((η : ℝ) : ℂ) *
          opPPair e (List.ofFn k) (resR e ⟨y, η⟩ ω)) volume E₁ E₂ := by
      intro c
      have : Continuous (fun y => ∑ k ∈ Finset.Nat.antidiagonalTuple 2 c, ((η : ℝ) : ℂ) *
          opPPair e (List.ofFn k) (resR e ⟨y, η⟩ ω)) :=
        continuous_finsetSum _ fun k _ => continuous_const.mul (hcF _)
      exact (continuous_const.mul this).intervalIntegrable _ _
    simp only [hT]
    rw [intervalIntegral.integral_finsetSum fun c _ => hci2 c]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum fun k _ => hci1 _]
    refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
    rw [intervalIntegral.integral_const_mul]
    rfl
  have hgi : IntervalIntegrable (fun y => (((η⁻¹ * g y) : ℝ) : ℂ)) volume E₁ E₂ :=
    (Complex.continuous_ofReal.comp (continuous_const.mul hgc)).intervalIntegrable _ _
  rw [h1, h2, ← intervalIntegral.integral_sub hgi (hTc.intervalIntegrable _ _)]
  have hpt : ∀ y ∈ Set.uIoc E₁ E₂, ‖(((η⁻¹ * g y) : ℝ) : ℂ) - T y‖ ≤ η⁻¹ * δ := by
    intro y hy
    have hb := norm_sq_sum_sub_expansion_le_of_good hω (hspec y (hwin y hy)) e hv ξ
    have hid : (((η⁻¹ * g y) : ℝ) : ℂ) - T y = ((η⁻¹ : ℝ) : ℂ) *
        (((g y : ℝ) : ℂ) - ∑ c ∈ Finset.Icc 1 ξ, (((-v) ^ c : ℝ) : ℂ) *
          ∑ k ∈ Finset.Nat.antidiagonalTuple 2 c,
            ((η ^ 2 : ℝ) : ℂ) * opPPair e (List.ofFn k) (resR e ⟨y, η⟩ ω)) := by
      have hη0 : ((η : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hη.ne'
      have hm : ∀ x : ℂ, ((η : ℝ) : ℂ) * x = ((η⁻¹ : ℝ) : ℂ) * (((η ^ 2 : ℝ) : ℂ) * x) := by
        intro x; push_cast; field_simp
      simp only [hT, hm, ← Finset.mul_sum, mul_left_comm _ ((η⁻¹ : ℝ) : ℂ)]
      push_cast
      ring
    rw [hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hη).le]
    refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hη).le
    have : ((g y : ℝ) : ℂ) = ((obsPoint N ε y (symOfEntries ω) : ℝ) : ℂ) -
        ((obsPoint N ε y (symOfEntries (zeroEntry e ω)) : ℝ) : ℂ) := by
      rw [hg, Complex.ofReal_sub]
    rw [this]
    exact hb
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hpt).trans_eq ?_
  field_simp

/-- The observable (5.15) as data. -/
private def taylor_obsIntData {N : ℕ} {ε E₁ E₂ : ℝ} (hN : 0 < N)
    (hE₁ : |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) (hE₂ : |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε))
    (e : Fin N ⊕ OffDiag N) : TayObs N ε e (obsInt N ε E₁ E₂) := by
  have hη := taylor_eta_pos N ε hN
  set η := etaEdge N ε with hηdef
  have hwin : ∀ y ∈ Set.uIoc E₁ E₂, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) :=
    fun y hy => taylor_mem_window hE₁ hE₂ (Set.uIoc_subset_uIcc hy)
  have hXeq : ∀ ω : Entries N, obsInt N ε E₁ E₂ (symOfEntries ω) =
      ∫ y in E₁..E₂, η⁻¹ * obsPoint N ε y (symOfEntries ω) :=
    fun ω => taylor_obsInt_eq hN E₁ E₂ _ (symOfEntries_isHermitian ω)
  have hcx : ∀ ω : Entries N, Continuous fun y => obsPoint N ε y (symOfEntries ω) :=
    fun ω => taylor_continuous_obsPoint hN continuous_const continuous_id
  have hcF : ∀ (k : List ℕ) (ω : Entries N),
      Continuous fun y => opPPair e k (resolventC (symOfEntries ω) ⟨y, η⟩) :=
    fun k ω => taylor_continuous_opPPair_res hη.ne' continuous_const continuous_id e k
  exact {
  M := |E₂ - E₁| / η
  Y := fun k ω => ((η : ℝ) : ℂ) * ∫ y in E₁..E₂, opPPair e k (resolventC (symOfEntries ω) ⟨y, η⟩)
  M_nonneg := by positivity
  M_le := by
    rw [← taylor_window_div_eta hN ε, mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ hη.le
    have := abs_sub_le E₂ 2 E₁
    rw [abs_sub_comm 2 E₁] at this
    linarith
  cont_X := by
    have hj : Continuous (Function.uncurry fun (ω : Entries N) (y : ℝ) =>
        (stieltjesM (symOfEntries ω) ⟨y, η⟩).im) := by
      unfold stieltjesM Matrix.trace
      exact Complex.continuous_im.comp (continuous_const.mul (continuous_finsetSum _ fun i _ =>
        taylor_continuous_resolvent continuous_fst continuous_snd hη.ne' i i))
    exact continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hj continuous_const)
  cont_Y := fun k => continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (taylor_continuous_opPPair_res hη.ne' continuous_fst continuous_snd e k) continuous_const)
  abs_X_le := fun ω => by
    rw [hXeq, ← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := η⁻¹ * N)
      fun y _ => ?_).trans_eq ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 hη),
        abs_of_nonneg (taylor_obsPoint_nonneg ε y _)]
      exact mul_le_mul_of_nonneg_left (taylor_obsPoint_le hN y _ (symOfEntries_isHermitian ω))
        (inv_pos.2 hη).le
    · field_simp
  abs_sub_le := fun ω => by
    have hi : ∀ ω' : Entries N, IntervalIntegrable
        (fun y => η⁻¹ * obsPoint N ε y (symOfEntries ω')) volume E₁ E₂ :=
      fun ω' => (continuous_const.mul (hcx ω')).intervalIntegrable _ _
    rw [hXeq, hXeq, ← intervalIntegral.integral_sub (hi ω) (hi _), ← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := η⁻¹ * 2)
      fun y _ => ?_).trans_eq ?_
    · rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 hη)]
      exact mul_le_mul_of_nonneg_left (taylor_abs_obsPoint_sub_le hN y e ω) (inv_pos.2 hη).le
    · field_simp
  abs_X_le_of := fun ω A h => by
    rw [hXeq, ← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := η⁻¹ * A)
      fun y hy => ?_).trans_eq ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 hη),
        abs_of_nonneg (taylor_obsPoint_nonneg ε y _)]
      exact mul_le_mul_of_nonneg_left (h y (hwin y hy)) (inv_pos.2 hη).le
    · field_simp
  expand := fun C0 hspec ω hω hv ξ => taylor_obsInt_expand hN hE₁ hE₂ e hspec hω hv ξ
  Y_le := fun k hk ω => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hη.le]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := E₁) (b := E₂)
      (f := fun y => opPPair e k (resolventC (symOfEntries ω) ⟨y, η⟩))
      (C := (N : ℝ) ^ 2 * (2 ^ k.sum * (η⁻¹ + 1) ^ (2 + k.sum)))
      fun y _ => taylor_norm_opPPair_le (taylor_norm_res_le hη ω y) e k hk
    calc η * ‖∫ y in E₁..E₂, opPPair e k (resolventC (symOfEntries ω) ⟨y, η⟩)‖ ≤
        η * ((N : ℝ) ^ 2 * (2 ^ k.sum * (η⁻¹ + 1) ^ (2 + k.sum)) * |E₂ - E₁|) :=
          mul_le_mul_of_nonneg_left this hη.le
      _ = _ := by rw [← hηdef]; field_simp
  moment := fun μ _ k hk _ hp _ _ h => taylor_obsInt_moment hN hE₁ hE₂ e μ k hk hp h }

/-- Every observable of Lemma 5.5 has the data of one swap. -/
private lemma taylor_tayObs {N : ℕ} {ε : ℝ} (hN : 0 < N) (hε : 0 ≤ ε)
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (hX : X ∈ edgeObs N ε) (e : Fin N ⊕ OffDiag N) :
    Nonempty (TayObs N ε e X) := by
  rcases hX with ⟨E, hE, rfl⟩ | ⟨E₁, E₂, h₁, h₂, rfl⟩
  · exact ⟨taylor_obsPointData hN hε hE e⟩
  · exact ⟨taylor_obsIntData hN h₁ h₂ e⟩

/-- `z = y + iη ∈ S(C0)` for every `y ∈ I_ε` once `N` is large (`0 ≤ ε < 1/3`). -/
private lemma taylor_ev_specDomain (C0 : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (hε3 : ε < 1 / 3) :
    ∀ᶠ N : ℕ in atTop, ∀ y : ℝ, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
      (⟨y, etaEdge N ε⟩ : ℂ) ∈ specDomain N C0 := by
  have hc : 0 < (1 / 3 - ε) / 2 := by linarith
  filter_upwards [phi_rpow_le_rpow C0 hc, eventually_ge_atTop 2] with N hφ h2 y hy
  have hN1 : (1 : ℝ) < N := by exact_mod_cast h2
  have hN0 : (0 : ℝ) < N := by linarith
  have hr : (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1.le (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · change |y| ≤ 5
    rw [abs_le] at hy ⊢; constructor <;> linarith [hy.1, hy.2]
  · change phi N ^ C0 / N < etaEdge N ε
    rw [div_lt_iff₀ hN0]
    have h1 : etaEdge N ε * N = (N : ℝ) ^ (1 / 3 - ε) := by
      unfold etaEdge
      rw [← Real.rpow_add_one hN0.ne']
      congr 1; ring
    rw [h1]
    exact hφ.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hN1 (by linarith))
  · change etaEdge N ε ≤ 10
    have : etaEdge N ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1.le (by linarith)
    linarith

/-- The constant of `Im m_sc(z) ≤ C √(κ + η)` (from (2.12)). -/
private lemma taylor_im_msc_le : ∃ Cm ≥ (1 : ℝ), ∀ z : ℂ, |z.re| ≤ 5 → 0 < z.im → z.im ≤ 10 →
    (msc z).im ≤ Cm * Real.sqrt (kappa z.re + z.im) := by
  obtain ⟨C, hC, h⟩ := msc_bounds
  refine ⟨C, hC, fun z h1 h2 h3 => ?_⟩
  obtain ⟨-, -, hedge, hbulk⟩ := h z h1 h2 h3
  have hk : 0 ≤ kappa z.re := abs_nonneg _
  by_cases hc : z.im ≤ kappa z.re ∧ 2 ≤ |z.re|
  · refine (hedge hc.1 hc.2).2.trans ?_
    have ht : 0 < Real.sqrt (kappa z.re + z.im) := Real.sqrt_pos.2 (by linarith)
    have hsq : Real.sqrt (kappa z.re + z.im) ^ 2 = kappa z.re + z.im := Real.sq_sqrt (by linarith)
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    rw [div_le_iff₀ ht]
    nlinarith
  · have : kappa z.re ≤ z.im ∨ |z.re| ≤ 2 := by
      by_contra hn
      rw [not_or, not_le, not_le] at hn
      exact hc ⟨hn.1.le, hn.2.le⟩
    exact (hbulk this).2

/-- (6.82) on the event of (5.24): `x(y) ≤ √2 C_m + φ^{C}` for `y ∈ I_ε`. -/
private lemma taylor_obsPoint_le_of_localLaw {N : ℕ} {ε C Cm : ℝ} (hN : 0 < N) (hε : 0 ≤ ε)
    (hCm : ∀ z : ℂ, |z.re| ≤ 5 → 0 < z.im → z.im ≤ 10 →
      (msc z).im ≤ Cm * Real.sqrt (kappa z.re + z.im)) (hCm0 : 0 ≤ Cm)
    {y : ℝ} (hy : |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε))
    (hz : (⟨y, etaEdge N ε⟩ : ℂ) ∈ specDomain N C)
    {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    (hll : ‖stieltjesM H ⟨y, etaEdge N ε⟩ - msc ⟨y, etaEdge N ε⟩‖ ≤
      phi N ^ C / (N * (⟨y, etaEdge N ε⟩ : ℂ).im)) :
    obsPoint N ε y H ≤ Real.sqrt 2 * Cm + phi N ^ C := by
  have hη := taylor_eta_pos N ε hN
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set η := etaEdge N ε with hηdef
  have hward : obsPoint N ε y H = N * η * (stieltjesM H ⟨y, η⟩).im := by
    unfold obsPoint
    exact sq_sum_norm_resolventC_eq hH (z := ⟨y, η⟩) hη
  have him : (stieltjesM H ⟨y, η⟩).im ≤ (msc ⟨y, η⟩).im + phi N ^ C / (N * η) := by
    have := (Complex.abs_im_le_norm _).trans hll
    rw [Complex.sub_im] at this
    have h2 := le_abs_self ((stieltjesM H ⟨y, η⟩).im - (msc ⟨y, η⟩).im)
    simp only at this
    linarith
  have hk : kappa y ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) := by
    unfold kappa
    rw [abs_le] at hy ⊢
    constructor
    · have := neg_abs_le y; have := le_abs_self y
      rcases le_or_gt 0 y with h0 | h0
      · rw [abs_of_nonneg h0]; linarith
      · rw [abs_of_neg h0]; linarith
    · rcases le_or_gt 0 y with h0 | h0
      · rw [abs_of_nonneg h0]; linarith
      · rw [abs_of_neg h0]; linarith
  have hηr : η ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hmsc : (msc ⟨y, η⟩).im ≤ Cm * Real.sqrt (kappa y + η) :=
    hCm _ hz.1 hη hz.2.2
  have hsq : N * η * Real.sqrt (kappa y + η) ≤ Real.sqrt 2 := by
    have hk0 : 0 ≤ kappa y := abs_nonneg _
    rw [← Real.sqrt_sq (by positivity : 0 ≤ (N : ℝ) * η), ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have h1 : ((N : ℝ) * η) ^ 2 * (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) = (N : ℝ) ^ (-ε) := by
      rw [hηdef]; unfold etaEdge
      rw [mul_pow, ← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_natCast (_ ^ _) 2,
        ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1; push_cast; ring
    have h2 : (N : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    calc ((N : ℝ) * η) ^ 2 * (kappa y + η) ≤
        ((N : ℝ) * η) ^ 2 * (2 * (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) := by gcongr; linarith
      _ = 2 * (((N : ℝ) * η) ^ 2 * (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) := by ring
      _ ≤ 2 := by rw [h1]; linarith
  rw [hward]
  calc (N : ℝ) * η * (stieltjesM H ⟨y, η⟩).im ≤
      N * η * ((msc ⟨y, η⟩).im + phi N ^ C / (N * η)) :=
        mul_le_mul_of_nonneg_left him (by positivity)
    _ = N * η * (msc ⟨y, η⟩).im + phi N ^ C := by field_simp
    _ ≤ N * η * (Cm * Real.sqrt (kappa y + η)) + phi N ^ C := by gcongr
    _ = Cm * (N * η * Real.sqrt (kappa y + η)) + phi N ^ C := by ring
    _ ≤ Cm * Real.sqrt 2 + phi N ^ C := by gcongr
    _ = Real.sqrt 2 * Cm + phi N ^ C := by ring

/-- A law of Theorem 3.6 has support exponent `φs ≤ 1/2`: `N⁻¹ = E h² ≤ N^{-2φs}`. -/
private lemma taylor_phis_le_half {C1 φs : ℝ} {N : ℕ} (hN : 2 ≤ N) {L : EntryLaws N}
    (hL : SmallQClass C1 φs N L) : φs ≤ 1 / 2 := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  let p : OffDiag N := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.lt_def]⟩
  have hprob := hL.1.isProb.off p
  have hae : ∀ᵐ x ∂(L.off p), x ^ 2 ≤ ((N : ℝ) ^ φs)⁻¹ ^ 2 := by
    have h0 := hL.2.2 p
    have h1 : ∀ᵐ x ∂(L.off p), ¬ (((N : ℝ) ^ φs)⁻¹ < |x|) := by
      rw [ae_iff]; simpa using h0
    filter_upwards [h1] with x hx
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg x) (not_lt.1 hx) 2
  have hint := (hL.2.integrable_pow hL.1.isProb 2).2 p
  have hle : ∫ x, x ^ 2 ∂(L.off p) ≤ ((N : ℝ) ^ φs)⁻¹ ^ 2 := by
    have := integral_mono_ae hint (integrable_const _) hae
    simpa using this
  rw [hL.1.var_off p] at hle
  have h2 : ((N : ℝ) ^ φs)⁻¹ ^ 2 = ((N : ℝ) ^ (2 * φs))⁻¹ := by
    rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
  rw [h2, inv_le_inv₀ hN0 (by positivity)] at hle
  have := (Real.rpow_le_rpow_left_iff hN1).1 (hle.trans_eq (Real.rpow_one _).symm)
  linarith

/-! ### Moments of the expanded terms -/

/-- `(a + b + c)³ ≤ 9 (a³ + b³ + c³)` for `a, b, c ≥ 0`. -/
private lemma taylor_cube_add_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a + b + c) ^ 3 ≤ 9 * (a ^ 3 + b ^ 3 + c ^ 3) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), mul_nonneg ha hb,
    mul_nonneg hb hc, mul_nonneg ha hc, mul_nonneg (mul_nonneg ha hb) hc,
    mul_nonneg ha (sq_nonneg (b - c)), mul_nonneg hb (sq_nonneg (a - c)),
    mul_nonneg hc (sq_nonneg (a - b)), mul_nonneg ha (sq_nonneg (a - b)),
    mul_nonneg ha (sq_nonneg (a - c)), mul_nonneg hb (sq_nonneg (b - c)),
    mul_nonneg hb (sq_nonneg (a - b)), mul_nonneg hc (sq_nonneg (a - c)),
    mul_nonneg hc (sq_nonneg (b - c))]

/-- `a³ ≤ (t a² + a⁴/t)/2` for `t > 0`. -/
private lemma taylor_cube_le (a : ℝ) {t : ℝ} (ht : 0 < t) :
    a ^ 3 ≤ (t * a ^ 2 + a ^ 4 / t) / 2 := by
  have : t * a ^ 2 + a ^ 4 / t - 2 * a ^ 3 = (t * a - a ^ 2) ^ 2 / t := by field_simp; ring
  nlinarith [div_nonneg (sq_nonneg (t * a - a ^ 2)) ht.le]

/-- `a ≤ (t + a²/t)/2` for `t > 0`. -/
private lemma taylor_self_le (a : ℝ) {t : ℝ} (ht : 0 < t) : a ≤ (t + a ^ 2 / t) / 2 := by
  have : t + a ^ 2 / t - 2 * a = (t - a) ^ 2 / t := by field_simp; ring
  nlinarith [div_nonneg (sq_nonneg (t - a)) ht.le]

/-- A continuous bounded function is integrable for a finite measure. -/
private lemma taylor_integrable_of_le {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] [NormedAddCommGroup E] [SecondCountableTopology E]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → E} (hf : Continuous f) {K : ℝ}
    (hK : ∀ ω, ‖f ω‖ ≤ K) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable K (Eventually.of_forall hK)

/-- The real form of `integral_mul_zeroEntry`: `E[g(Q) (-v)^k] = E[g(Q)] n_k`. -/
private lemma taylor_integral_mul_zeroEntry_real {N : ℕ} {L : EntryLaws N} (hL : L.IsProb)
    (e : Fin N ⊕ OffDiag N) {g : Entries N → ℝ} (hg : Measurable g) {K : ℝ}
    (hK : ∀ ω, |g ω| ≤ K) (k : ℕ) (hk : Integrable (fun x : ℝ => x ^ k) (L.entry e)) :
    ∫ ω, g (zeroEntry e ω) * (-entryVal e ω) ^ k ∂L.law =
      (∫ ω, g (zeroEntry e ω) ∂L.law) * L.entryMoment e k := by
  have hprob := isProbabilityMeasure_law hL
  have hgc : Measurable fun ω => (g ω : ℂ) := Complex.measurable_ofReal.comp hg
  have hi : Integrable (fun ω => (g (zeroEntry e ω) : ℂ)) L.law :=
    Integrable.of_bound
      (hgc.comp (expansion_continuous_zeroEntry e).measurable).aestronglyMeasurable K
      (Eventually.of_forall fun ω => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hK _)
  have h := integral_mul_zeroEntry hL e (fun ω => (g ω : ℂ)) k hgc hi hk
  have h1 : ∫ ω, (g (zeroEntry e ω) : ℂ) * (((-entryVal e ω) ^ k : ℝ) : ℂ) ∂L.law =
      ((∫ ω, g (zeroEntry e ω) * (-entryVal e ω) ^ k ∂L.law : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1; funext ω; push_cast; ring
  have h2 : ∫ ω, (g (zeroEntry e ω) : ℂ) ∂L.law = ((∫ ω, g (zeroEntry e ω) ∂L.law : ℝ) : ℂ) :=
    integral_complex_ofReal
  apply Complex.ofReal_injective
  rw [← h1, h, h2]
  push_cast
  ring

/-- The index set `{(c, k) : 1 ≤ c ≤ ξ, k ∈ ℕ², |k| = c}` of (6.88). -/
private def taylor_idx (ξ : ℕ) : Finset (Σ _ : ℕ, Fin 2 → ℕ) :=
  (Finset.Icc 1 ξ).sigma fun c => Finset.Nat.antidiagonalTuple 2 c

/-- The index set consists of `k ∈ ℕ²` with `1 ≤ |k| ≤ ξ`. -/
private lemma taylor_mem_idx {ξ : ℕ} {x : Σ _ : ℕ, Fin 2 → ℕ} (hx : x ∈ taylor_idx ξ) :
    (List.ofFn x.2).length = 2 ∧ 1 ≤ (List.ofFn x.2).sum ∧ (List.ofFn x.2).sum ≤ ξ := by
  simp only [taylor_idx, Finset.mem_sigma, Finset.mem_Icc, Finset.Nat.mem_antidiagonalTuple] at hx
  refine ⟨List.length_ofFn, ?_, ?_⟩ <;> rw [List.sum_ofFn, hx.2] <;> omega

/-- `Z = Σ_{(c, k)} ‖Y_k‖`, a function of `Q`. -/
private def taylor_Z {N : ℕ} {ε : ℝ} {e : Fin N ⊕ OffDiag N} {X : Matrix (Fin N) (Fin N) ℝ → ℝ}
    (D : TayObs N ε e X) (ξ : ℕ) (ω : Entries N) : ℝ :=
  ∑ x ∈ taylor_idx ξ, ‖D.Y (List.ofFn x.2) ω‖

/-- `Z ≥ 0`. -/
private lemma taylor_Z_nonneg {N : ℕ} {ε : ℝ} {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) (ξ : ℕ) (ω : Entries N) :
    0 ≤ taylor_Z D ξ ω :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- `Z` is continuous. -/
private lemma taylor_Z_continuous {N : ℕ} {ε : ℝ} {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) (ξ : ℕ) :
    Continuous (taylor_Z D ξ) :=
  continuous_finsetSum _ fun _ _ => (D.cont_Y _).norm

/-- The crude bound `Z ≤ Z_c` from `|G_ij| ≤ η⁻¹`. -/
private def taylor_Zc {N : ℕ} {ε : ℝ} {e : Fin N ⊕ OffDiag N} {X : Matrix (Fin N) (Fin N) ℝ → ℝ}
    (D : TayObs N ε e X) (ξ : ℕ) : ℝ :=
  (taylor_idx ξ).card * (D.M * (etaEdge N ε ^ 2 * ((N : ℝ) ^ 2 *
    (2 ^ ξ * ((etaEdge N ε)⁻¹ + 1) ^ (2 + ξ)))))

/-- `Z ≤ Z_c`. -/
private lemma taylor_Z_le {N : ℕ} {ε : ℝ} (hN : 0 < N) {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) (ξ : ℕ) (ω : Entries N) :
    taylor_Z D ξ ω ≤ taylor_Zc D ξ := by
  have hη := taylor_eta_pos N ε hN
  unfold taylor_Z taylor_Zc
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun x hx => (D.Y_le _ (taylor_mem_idx hx).1 ω).trans ?_
  obtain ⟨-, -, h3⟩ := taylor_mem_idx hx
  have h1 : (1 : ℝ) ≤ (etaEdge N ε)⁻¹ + 1 := by linarith [inv_pos.2 hη]
  gcongr
  · exact D.M_nonneg
  · norm_num

/-- `‖Σ_{1 ≤ c ≤ ξ} (-v)^c Σ_{|k| = c} Y_k‖ ≤ |v| Z` for `|v| ≤ 1`. -/
private lemma taylor_norm_T_le {N : ℕ} {ε : ℝ} {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) (ξ : ℕ) {v : ℝ} (hv : |v| ≤ 1)
    (ω : Entries N) :
    ‖∑ c ∈ Finset.Icc 1 ξ, (((-v) ^ c : ℝ) : ℂ) *
        ∑ k ∈ Finset.Nat.antidiagonalTuple 2 c, D.Y (List.ofFn k) ω‖ ≤ |v| * taylor_Z D ξ ω := by
  unfold taylor_Z taylor_idx
  rw [Finset.sum_sigma, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c hc => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_neg, Finset.mul_sum]
  have hc1 : 1 ≤ c := (Finset.mem_Icc.1 hc).1
  have hvc : |v| ^ c ≤ |v| := by
    calc |v| ^ c = |v| ^ (c - 1) * |v| := by rw [← pow_succ, Nat.sub_add_cancel hc1]
      _ ≤ 1 * |v| := by gcongr; exact pow_le_one₀ (abs_nonneg v) hv
      _ = |v| := one_mul _
  calc |v| ^ c * ‖∑ k ∈ Finset.Nat.antidiagonalTuple 2 c, D.Y (List.ofFn k) ω‖ ≤
      |v| * ∑ k ∈ Finset.Nat.antidiagonalTuple 2 c, ‖D.Y (List.ofFn k) ω‖ :=
        mul_le_mul hvc (norm_sum_le _ _) (norm_nonneg _) (abs_nonneg v)
    _ = _ := by rw [Finset.mul_sum]

/-- From the moments of order `2` and `4`: `E‖Y‖ ≤ B` and `E‖Y‖³ ≤ B³`. -/
private lemma taylor_moment_one_three {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (hf : Measurable f) {K : ℝ}
    (hK : ∀ ω, f ω ≤ K) {B : ℝ} (hB : 0 < B) (h2 : ∫ ω, f ω ^ 2 ∂μ ≤ B ^ 2)
    (h4 : ∫ ω, f ω ^ 4 ∂μ ≤ B ^ 4) :
    ∫ ω, f ω ∂μ ≤ B ∧ ∫ ω, f ω ^ 3 ∂μ ≤ B ^ 3 := by
  have hb : ∀ q : ℕ, Integrable (fun ω => f ω ^ q) μ := fun q =>
    Integrable.of_bound (hf.pow_const q).aestronglyMeasurable (K ^ q)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (pow_nonneg (hf0 ω) q)]
        exact pow_le_pow_left₀ (hf0 ω) (hK ω) q)
  constructor
  · calc ∫ ω, f ω ∂μ ≤ ∫ ω, (B + f ω ^ 2 / B) / 2 ∂μ :=
          integral_mono_of_nonneg (Eventually.of_forall hf0)
            (((integrable_const B).add ((hb 2).div_const B)).div_const 2)
            (Eventually.of_forall fun ω => taylor_self_le (f ω) hB)
      _ = (B + (∫ ω, f ω ^ 2 ∂μ) / B) / 2 := by
          rw [integral_div, integral_add (integrable_const B) ((hb 2).div_const B), integral_div,
            integral_const]
          simp
      _ ≤ (B + B ^ 2 / B) / 2 := by gcongr
      _ = B := by field_simp; ring
  · calc ∫ ω, f ω ^ 3 ∂μ ≤ ∫ ω, (B * f ω ^ 2 + f ω ^ 4 / B) / 2 ∂μ :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω => pow_nonneg (hf0 ω) 3)
            ((((hb 2).const_mul B).add ((hb 4).div_const B)).div_const 2)
            (Eventually.of_forall fun ω => taylor_cube_le (f ω) hB)
      _ = (B * (∫ ω, f ω ^ 2 ∂μ) + (∫ ω, f ω ^ 4 ∂μ) / B) / 2 := by
          rw [integral_div, integral_add ((hb 2).const_mul B) ((hb 4).div_const B), integral_div,
            integral_const_mul]
      _ ≤ (B * B ^ 2 + B ^ 4 / B) / 2 := by gcongr
      _ = B ^ 3 := by field_simp; ring

/-- Moments of `Z`: `E Z^q ≤ (#idx · B)^q` for `q = 1, 2, 3`, from the moments of order `2` and
`4` of every `Y_k`. -/
private lemma taylor_integral_Z_pow_le {N : ℕ} {ε : ℝ} (hN : 0 < N) {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) (ξ : ℕ) {μ : Measure (Entries N)}
    [IsProbabilityMeasure μ] {B : ℝ} (hB : 0 < B)
    (hmom : ∀ x ∈ taylor_idx ξ, ∀ q ∈ ({2, 4} : Finset ℕ),
      ∫ ω, ‖D.Y (List.ofFn x.2) (zeroEntry e ω)‖ ^ q ∂μ ≤ B ^ q) (q : ℕ) (hq : q ∈ Finset.Icc 1 3) :
    ∫ ω, taylor_Z D ξ (zeroEntry e ω) ^ q ∂μ ≤ ((taylor_idx ξ).card * B) ^ q := by
  set I := taylor_idx ξ
  have hη := taylor_eta_pos N ε hN
  have hcY : ∀ x : Σ _ : ℕ, Fin 2 → ℕ, Continuous fun ω => ‖D.Y (List.ofFn x.2) (zeroEntry e ω)‖ :=
    fun x => ((D.cont_Y _).comp (expansion_continuous_zeroEntry e)).norm
  have hKY : ∀ x ∈ I, ∀ ω, ‖D.Y (List.ofFn x.2) (zeroEntry e ω)‖ ≤ taylor_Zc D ξ := by
    intro x hx ω
    refine le_trans ?_ (taylor_Z_le hN D ξ (zeroEntry e ω))
    exact Finset.single_le_sum (f := fun x => ‖D.Y (List.ofFn x.2) (zeroEntry e ω)‖)
      (fun _ _ => norm_nonneg _) hx
  have h13 : ∀ x ∈ I, ∫ ω, ‖D.Y (List.ofFn x.2) (zeroEntry e ω)‖ ∂μ ≤ B ∧
      ∫ ω, ‖D.Y (List.ofFn x.2) (zeroEntry e ω)‖ ^ 3 ∂μ ≤ B ^ 3 := fun x hx =>
    taylor_moment_one_three (fun _ => norm_nonneg _) (hcY x).measurable (hKY x hx) hB
      (hmom x hx 2 (by simp)) (hmom x hx 4 (by simp))
  have hqB : ∀ x ∈ I, ∫ ω, ‖D.Y (List.ofFn x.2) (zeroEntry e ω)‖ ^ q ∂μ ≤ B ^ q := by
    intro x hx
    simp only [Finset.mem_Icc] at hq
    obtain ⟨h1, h3⟩ := hq
    interval_cases q
    · simpa using (h13 x hx).1
    · exact hmom x hx 2 (by simp)
    · exact (h13 x hx).2
  have hint : ∀ x ∈ I, Integrable (fun ω => ‖D.Y (List.ofFn x.2) (zeroEntry e ω)‖ ^ q) μ :=
    fun x hx => taylor_integrable_of_le ((hcY x).pow q) (K := taylor_Zc D ξ ^ q) fun ω => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hKY x hx ω) q
  have hq1 : 1 ≤ q := (Finset.mem_Icc.1 hq).1
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  have hpt : ∀ ω, taylor_Z D ξ (zeroEntry e ω) ^ (n + 1) ≤
      (I.card : ℝ) ^ n * ∑ x ∈ I, ‖D.Y (List.ofFn x.2) (zeroEntry e ω)‖ ^ (n + 1) :=
    fun ω => pow_sum_le_card_mul_sum_pow (fun _ _ => norm_nonneg _) n
  calc ∫ ω, taylor_Z D ξ (zeroEntry e ω) ^ (n + 1) ∂μ ≤
      ∫ ω, (I.card : ℝ) ^ n * ∑ x ∈ I, ‖D.Y (List.ofFn x.2) (zeroEntry e ω)‖ ^ (n + 1) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => by
          have := taylor_Z_nonneg D ξ (zeroEntry e ω); positivity)
          ((integrable_finsetSum _ hint).const_mul _) (Eventually.of_forall hpt)
    _ = (I.card : ℝ) ^ n * ∑ x ∈ I, ∫ ω, ‖D.Y (List.ofFn x.2) (zeroEntry e ω)‖ ^ (n + 1) ∂μ := by
        rw [integral_const_mul, integral_finsetSum _ hint]
    _ ≤ (I.card : ℝ) ^ n * ∑ x ∈ I, B ^ (n + 1) := by gcongr with x hx; exact hqB x hx
    _ = ((I.card : ℝ) * B) ^ (n + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_pow]; ring

/-- Monomials are integrable for the law of an almost surely bounded entry. -/
private lemma taylor_integrable_entry_pow {N : ℕ} {L : EntryLaws N} {q : ℝ}
    (hs : L.BoundedSupportAS q) (hL : L.IsProb) (e : Fin N ⊕ OffDiag N) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (L.entry e) := by
  rcases e with i | p
  · exact (hs.integrable_pow hL k).1 i
  · exact (hs.integrable_pow hL k).2 p

/-- `E[|v|³ g(Q)] ≤ ((t n₂ + n₄/t)/2) E[g(Q)]` for `g ≥ 0`, `t > 0` (the bound
`E|h|³ ≤ (E h² E h⁴)^{1/2}` before (6.101)). -/
private lemma taylor_integral_abs_cube_le_off {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) {q : ℝ}
    (hs : L.BoundedSupportAS q) (e : Fin N ⊕ OffDiag N) {θ : ℝ}
    (hvθ : ∀ᵐ ω ∂L.law, |entryVal e ω| ≤ θ) {t : ℝ} (ht : 0 < t) (g : Entries N → ℝ)
    (hg : Measurable g) (hg0 : ∀ ω, 0 ≤ g ω) (K : ℝ) (hK : ∀ ω, g ω ≤ K) :
    ∫ ω, |entryVal e ω| ^ 3 * g (zeroEntry e ω) ∂L.law ≤
      ((t * L.entryMoment e 2 + L.entryMoment e 4 / t) / 2) * ∫ ω, g (zeroEntry e ω) ∂L.law := by
  have hprob := isProbabilityMeasure_law hL
  have hgK : ∀ ω, |g ω| ≤ K := fun ω => by rw [abs_of_nonneg (hg0 ω)]; exact hK ω
  have h2 := taylor_integral_mul_zeroEntry_real hL e hg hgK 2
    (taylor_integrable_entry_pow hs hL e 2)
  have h4 := taylor_integral_mul_zeroEntry_real hL e hg hgK 4
    (taylor_integrable_entry_pow hs hL e 4)
  have hvc : Continuous fun ω : Entries N => entryVal e ω := by
    rcases e with i | p
    · exact (continuous_apply i).comp continuous_fst
    · exact (continuous_apply p).comp continuous_snd
  have hgq : Measurable fun ω => g (zeroEntry e ω) :=
    hg.comp (expansion_continuous_zeroEntry e).measurable
  have hint : ∀ k : ℕ, Integrable (fun ω => g (zeroEntry e ω) * (-entryVal e ω) ^ k) L.law := by
    intro k
    refine Integrable.of_bound (hgq.mul ((hvc.neg.pow k).measurable)).aestronglyMeasurable
      (K * θ ^ k) ?_
    filter_upwards [hvθ] with ω hω
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_nonneg (hg0 _)]
    exact mul_le_mul (hK _) (pow_le_pow_left₀ (abs_nonneg _) hω k) (by positivity)
      ((hg0 (zeroEntry e ω)).trans (hK _))
  have hpt : ∀ ω, |entryVal e ω| ^ 3 * g (zeroEntry e ω) ≤
      (t * (g (zeroEntry e ω) * (-entryVal e ω) ^ 2) +
        g (zeroEntry e ω) * (-entryVal e ω) ^ 4 / t) / 2 := by
    intro ω
    have h := taylor_cube_le |entryVal e ω| ht
    have hg' := hg0 (zeroEntry e ω)
    rw [neg_pow_two, show (-entryVal e ω) ^ 4 = |entryVal e ω| ^ 4 by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, neg_pow_two, sq_abs]]
    rw [← sq_abs (entryVal e ω)]
    calc |entryVal e ω| ^ 3 * g (zeroEntry e ω) ≤
        ((t * |entryVal e ω| ^ 2 + |entryVal e ω| ^ 4 / t) / 2) * g (zeroEntry e ω) :=
          mul_le_mul_of_nonneg_right h hg'
      _ = _ := by ring
  calc ∫ ω, |entryVal e ω| ^ 3 * g (zeroEntry e ω) ∂L.law ≤
      ∫ ω, (t * (g (zeroEntry e ω) * (-entryVal e ω) ^ 2) +
        g (zeroEntry e ω) * (-entryVal e ω) ^ 4 / t) / 2 ∂L.law :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => by
          have := hg0 (zeroEntry e ω); positivity)
          ((((hint 2).const_mul t).add ((hint 4).div_const t)).div_const 2)
          (Eventually.of_forall hpt)
    _ = ((t * L.entryMoment e 2 + L.entryMoment e 4 / t) / 2) * ∫ ω, g (zeroEntry e ω) ∂L.law := by
        rw [integral_div, integral_add ((hint 2).const_mul t) ((hint 4).div_const t),
          integral_div, integral_const_mul, h2, h4]
        ring

/-- `E[|v|³ g(Q)] ≤ θ n₂ E[g(Q)]` for `g ≥ 0` when `|v| ≤ θ` almost surely. -/
private lemma taylor_integral_abs_cube_le_diag {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) {q : ℝ}
    (hs : L.BoundedSupportAS q) (e : Fin N ⊕ OffDiag N) {θ : ℝ}
    (hvθ : ∀ᵐ ω ∂L.law, |entryVal e ω| ≤ θ) (g : Entries N → ℝ)
    (hg : Measurable g) (hg0 : ∀ ω, 0 ≤ g ω) (K : ℝ) (hK : ∀ ω, g ω ≤ K) :
    ∫ ω, |entryVal e ω| ^ 3 * g (zeroEntry e ω) ∂L.law ≤
      (θ * L.entryMoment e 2) * ∫ ω, g (zeroEntry e ω) ∂L.law := by
  have hprob := isProbabilityMeasure_law hL
  have hgK : ∀ ω, |g ω| ≤ K := fun ω => by rw [abs_of_nonneg (hg0 ω)]; exact hK ω
  have h2 := taylor_integral_mul_zeroEntry_real hL e hg hgK 2
    (taylor_integrable_entry_pow hs hL e 2)
  have hvc : Continuous fun ω : Entries N => entryVal e ω := by
    rcases e with i | p
    · exact (continuous_apply i).comp continuous_fst
    · exact (continuous_apply p).comp continuous_snd
  have hgq : Measurable fun ω => g (zeroEntry e ω) :=
    hg.comp (expansion_continuous_zeroEntry e).measurable
  have hint : Integrable (fun ω => g (zeroEntry e ω) * (-entryVal e ω) ^ 2) L.law := by
    refine Integrable.of_bound (hgq.mul ((hvc.neg.pow 2).measurable)).aestronglyMeasurable
      (K * θ ^ 2) ?_
    filter_upwards [hvθ] with ω hω
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_nonneg (hg0 _)]
    exact mul_le_mul (hK _) (pow_le_pow_left₀ (abs_nonneg _) hω 2) (by positivity)
      ((hg0 (zeroEntry e ω)).trans (hK _))
  calc ∫ ω, |entryVal e ω| ^ 3 * g (zeroEntry e ω) ∂L.law ≤
      ∫ ω, θ * (g (zeroEntry e ω) * (-entryVal e ω) ^ 2) ∂L.law := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ω => by
          have := hg0 (zeroEntry e ω); positivity) (hint.const_mul θ) ?_
        filter_upwards [hvθ] with ω hω
        have hg' := hg0 (zeroEntry e ω)
        rw [neg_pow_two, ← sq_abs]
        calc |entryVal e ω| ^ 3 * g (zeroEntry e ω) = |entryVal e ω| * |entryVal e ω| ^ 2 *
            g (zeroEntry e ω) := by ring
          _ ≤ θ * |entryVal e ω| ^ 2 * g (zeroEntry e ω) := by gcongr
          _ = _ := by ring
    _ = (θ * L.entryMoment e 2) * ∫ ω, g (zeroEntry e ω) ∂L.law := by
        rw [integral_const_mul, h2]; ring

/-- The indicator of the measurable hull of the complement of an event. -/
private lemma taylor_indicator_hull {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (S : Set Ω)
    (ω : Ω) : 0 ≤ (toMeasurable μ Sᶜ).indicator (fun _ => (1 : ℝ)) ω ∧
      (toMeasurable μ Sᶜ).indicator (fun _ => (1 : ℝ)) ω ≤ 1 ∧
      (ω ∉ S → (toMeasurable μ Sᶜ).indicator (fun _ => (1 : ℝ)) ω = 1) := by
  refine ⟨Set.indicator_nonneg (fun _ _ => zero_le_one) ω, ?_, fun h => ?_⟩
  · by_cases h : ω ∈ toMeasurable μ Sᶜ
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h]; exact zero_le_one
  · rw [Set.indicator_of_mem (subset_toMeasurable μ Sᶜ h)]

/-- `E 1_{hull of Sᶜ} = P(Sᶜ)`. -/
private lemma taylor_integral_indicator_hull {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : Set Ω) : ∫ ω, (toMeasurable μ Sᶜ).indicator (fun _ => (1 : ℝ)) ω ∂μ = μ.real Sᶜ := by
  rw [integral_indicator_const _ (measurableSet_toMeasurable μ Sᶜ), smul_eq_mul, mul_one,
    Measure.real, Measure.real, measure_toMeasurable]

/-- (6.101) in abstract form: with `|v| ≤ θ` almost surely, `16 θ ≤ 1`, the good event of the
expansion, the moments `E‖Y_k‖^q ≤ B^q` (`q = 2, 4`) and `E[|v|³ g(Q)] ≤ a₃ E g(Q)`,
`E|X_S - X_R|³ ≤ 9 (a₃ (#idx B)³ + (M δ₀)³ + 8 M³ P(good event fails))`. -/
private lemma taylor_third_moment {N : ℕ} {ε : ℝ} (hN : 0 < N) {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) {μ : Measure (Entries N)}
    [IsProbabilityMeasure μ] {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 16 * θ ≤ 1)
    (hvθ : ∀ᵐ ω ∂μ, |entryVal e ω| ≤ θ) {C0 : ℝ}
    (hspec : ∀ y, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
      (⟨y, etaEdge N ε⟩ : ℂ) ∈ specDomain N C0)
    (ξ : ℕ) {B : ℝ} (hB : 0 < B)
    (hmom : ∀ x ∈ taylor_idx ξ, ∀ q ∈ ({2, 4} : Finset ℕ),
      ∫ ω, ‖D.Y (List.ofFn x.2) (zeroEntry e ω)‖ ^ q ∂μ ≤ B ^ q)
    {a3 : ℝ} (ha3 : 0 ≤ a3)
    (hv3 : ∀ g : Entries N → ℝ, Measurable g → (∀ ω, 0 ≤ g ω) → ∀ K, (∀ ω, g ω ≤ K) →
      ∫ ω, |entryVal e ω| ^ 3 * g (zeroEntry e ω) ∂μ ≤ a3 * ∫ ω, g (zeroEntry e ω) ∂μ) :
    ∫ ω, |X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))| ^ 3 ∂μ ≤
      9 * (a3 * ((taylor_idx ξ).card * B) ^ 3 +
        (D.M * (etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * θ) ^ (ξ + 1))) ^ 3 +
        8 * D.M ^ 3 * μ.real (goodEvent N C0)ᶜ) := by
  set δ₀ := etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * θ) ^ (ξ + 1) with hδ₀
  set T := toMeasurable μ (goodEvent N C0)ᶜ
  set ind : Entries N → ℝ := fun ω => T.indicator (fun _ => (1 : ℝ)) ω with hind
  have hM := D.M_nonneg
  have hη := taylor_eta_pos N ε hN
  have hδ0 : 0 ≤ δ₀ := by positivity
  set Δ : Entries N → ℝ := fun ω => X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω)) with hΔ
  set Zq : Entries N → ℝ := fun ω => taylor_Z D ξ (zeroEntry e ω) with hZq
  have hZ0 : ∀ ω, 0 ≤ Zq ω := fun ω => taylor_Z_nonneg D ξ _
  have hZc : ∀ ω, Zq ω ≤ taylor_Zc D ξ := fun ω => taylor_Z_le hN D ξ _
  -- the pointwise bound
  have hpt : ∀ᵐ ω ∂μ, |Δ ω| ≤ |entryVal e ω| * Zq ω + D.M * δ₀ + 2 * D.M * ind ω := by
    filter_upwards [hvθ] with ω hω
    have hv1 : |entryVal e ω| ≤ 1 := by linarith
    obtain ⟨hi0, -, hi1⟩ := taylor_indicator_hull μ (goodEvent N C0) ω
    by_cases hg : ω ∈ goodEvent N C0
    · have h16 : 16 * |entryVal e ω| ≤ 1 := by linarith
      have hexp := D.expand C0 hspec ω hg h16 ξ
      have hT := taylor_norm_T_le D ξ hv1 (zeroEntry e ω)
      have hδv : etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * |entryVal e ω|) ^ (ξ + 1) ≤ δ₀ := by
        rw [hδ₀]; gcongr
      have h1 : |Δ ω| ≤ D.M * δ₀ + |entryVal e ω| * Zq ω := by
        rw [← Real.norm_eq_abs, ← Complex.norm_real]
        set Tc := ∑ c ∈ Finset.Icc 1 ξ, (((-entryVal e ω) ^ c : ℝ) : ℂ) *
          ∑ k ∈ Finset.Nat.antidiagonalTuple 2 c, D.Y (List.ofFn k) (zeroEntry e ω)
        calc ‖((Δ ω : ℝ) : ℂ)‖ = ‖(((Δ ω : ℝ) : ℂ) - Tc) + Tc‖ := by rw [sub_add_cancel]
          _ ≤ ‖((Δ ω : ℝ) : ℂ) - Tc‖ + ‖Tc‖ := norm_add_le _ _
          _ ≤ D.M * δ₀ + |entryVal e ω| * Zq ω :=
            add_le_add (hexp.trans (mul_le_mul_of_nonneg_left hδv hM)) hT
      have : 0 ≤ 2 * D.M * ind ω := by positivity
      linarith
    · have h2 := D.abs_sub_le ω
      have h3 : ind ω = 1 := hi1 hg
      have : 0 ≤ |entryVal e ω| * Zq ω := mul_nonneg (abs_nonneg _) (hZ0 ω)
      have : 0 ≤ D.M * δ₀ := mul_nonneg hM hδ0
      rw [h3]
      change |X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))| ≤ _
      linarith
  have hcube : ∀ᵐ ω ∂μ, |Δ ω| ^ 3 ≤ 9 * (|entryVal e ω| ^ 3 * Zq ω ^ 3 + (D.M * δ₀) ^ 3 +
      8 * D.M ^ 3 * ind ω) := by
    filter_upwards [hpt] with ω h
    obtain ⟨hi0, hi1, -⟩ := taylor_indicator_hull μ (goodEvent N C0) ω
    have hind3 : (2 * D.M * ind ω) ^ 3 = 8 * D.M ^ 3 * ind ω := by
      have : ind ω = 0 ∨ ind ω = 1 := by
        simp only [hind]
        by_cases hT : ω ∈ T
        · right; exact Set.indicator_of_mem hT _
        · left; exact Set.indicator_of_notMem hT _
      rcases this with h0 | h0 <;> rw [h0] <;> ring
    calc |Δ ω| ^ 3 ≤ (|entryVal e ω| * Zq ω + D.M * δ₀ + 2 * D.M * ind ω) ^ 3 :=
          pow_le_pow_left₀ (abs_nonneg _) h 3
      _ ≤ 9 * ((|entryVal e ω| * Zq ω) ^ 3 + (D.M * δ₀) ^ 3 + (2 * D.M * ind ω) ^ 3) :=
          taylor_cube_add_le (mul_nonneg (abs_nonneg _) (hZ0 ω)) (mul_nonneg hM hδ0)
            (by positivity)
      _ = _ := by rw [hind3, mul_pow]
  -- integrability
  have hZc0 : Continuous Zq := (taylor_Z_continuous D ξ).comp (expansion_continuous_zeroEntry e)
  have hvc : Continuous fun ω : Entries N => entryVal e ω := by
    rcases e with i | p
    · exact (continuous_apply i).comp continuous_fst
    · exact (continuous_apply p).comp continuous_snd
  have hi1 : Integrable (fun ω => |entryVal e ω| ^ 3 * Zq ω ^ 3) μ := by
    refine Integrable.of_bound ((hvc.abs.pow 3).mul (hZc0.pow 3)).aestronglyMeasurable
      (θ ^ 3 * taylor_Zc D ξ ^ 3) ?_
    filter_upwards [hvθ] with ω hω
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (abs_nonneg _) 3) (pow_nonneg (hZ0 ω) 3))]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hω 3) (pow_le_pow_left₀ (hZ0 ω) (hZc ω) 3)
      (pow_nonneg (hZ0 ω) 3) (pow_nonneg hθ0 3)
  have hi3 : Integrable ind μ :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_toMeasurable μ _)
  have hiR : Integrable (fun ω => 9 * (|entryVal e ω| ^ 3 * Zq ω ^ 3 + (D.M * δ₀) ^ 3 +
      8 * D.M ^ 3 * ind ω)) μ :=
    ((hi1.add (integrable_const _)).add (hi3.const_mul _)).const_mul 9
  have hmain := integral_mono_of_nonneg (Eventually.of_forall fun ω => by positivity) hiR hcube
  have hi12 : Integrable (fun ω => |entryVal e ω| ^ 3 * Zq ω ^ 3 + (D.M * δ₀) ^ 3) μ :=
    hi1.add (integrable_const _)
  have hi3' : Integrable (fun ω => 8 * D.M ^ 3 * ind ω) μ := hi3.const_mul _
  have hind_int : ∫ ω, ind ω ∂μ = μ.real (goodEvent N C0)ᶜ :=
    taylor_integral_indicator_hull μ _
  rw [integral_const_mul, integral_add hi12 hi3', integral_add hi1 (integrable_const _),
    integral_const_mul, integral_const, hind_int] at hmain
  simp only [probReal_univ, one_smul] at hmain
  -- the term `E |v|³ Z³`
  have hZ3 : ∫ ω, |entryVal e ω| ^ 3 * Zq ω ^ 3 ∂μ ≤ a3 * ((taylor_idx ξ).card * B) ^ 3 := by
    have h := hv3 (fun ω => taylor_Z D ξ ω ^ 3) ((taylor_Z_continuous D ξ).pow 3).measurable
      (fun ω => pow_nonneg (taylor_Z_nonneg D ξ ω) 3) (taylor_Zc D ξ ^ 3)
      (fun ω => pow_le_pow_left₀ (taylor_Z_nonneg D ξ ω) (taylor_Z_le hN D ξ ω) 3)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ ha3)
    exact taylor_integral_Z_pow_le hN D ξ hB hmom 3 (by simp)
  refine hmain.trans ?_
  gcongr

/-- The support parameter `q₀ = min(N^{φs}, √N/((2C1+4)C1 log N))` of the matched pair is positive
and `q₀⁻¹ ≤ (1 + K₀ log N) N^{-φs}`, `K₀ = |(2C1+4)C1|`. -/
private lemma taylor_theta {C1 φs : ℝ} {N : ℕ} (hN : 3 ≤ N) {Lv Lw : EntryLaws N}
    (hv : SmallQClass C1 φs N Lv) (hw : Lv.IsMomentMatch Lw C1) :
    0 < min ((N : ℝ) ^ φs) (Real.sqrt N / ((2 * C1 + 4) * C1 * Real.log N)) ∧
      (min ((N : ℝ) ^ φs) (Real.sqrt N / ((2 * C1 + 4) * C1 * Real.log N)))⁻¹ ≤
        (1 + |(2 * C1 + 4) * C1| * Real.log N) * (N : ℝ) ^ (-φs) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hφ := taylor_phis_le_half (by omega) hv
  have ht := tilde_pos hN hv.1 hw
  have hpos : 0 < min ((N : ℝ) ^ φs) (Real.sqrt N / ((2 * C1 + 4) * C1 * Real.log N)) :=
    lt_min (Real.rpow_pos_of_pos hN0 _) ht
  refine ⟨hpos, ?_⟩
  rcases min_choice ((N : ℝ) ^ φs) (Real.sqrt N / ((2 * C1 + 4) * C1 * Real.log N)) with h | h <;>
    rw [h]
  · rw [← Real.rpow_neg hN0.le]
    have : 0 ≤ |(2 * C1 + 4) * C1| * Real.log N * (N : ℝ) ^ (-φs) := by positivity
    linarith
  · rw [inv_div]
    have hs : Real.sqrt N = (N : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
    have h1 : (N : ℝ) ^ (-(1 : ℝ) / 2) ≤ (N : ℝ) ^ (-φs) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
    calc (2 * C1 + 4) * C1 * Real.log N / Real.sqrt N ≤
        |(2 * C1 + 4) * C1| * Real.log N / Real.sqrt N := by
          gcongr; exact le_abs_self _
      _ = |(2 * C1 + 4) * C1| * Real.log N * (N : ℝ) ^ (-(1 : ℝ) / 2) := by
          rw [hs, div_eq_mul_inv, ← Real.rpow_neg hN0.le]; congr 2; ring
      _ ≤ |(2 * C1 + 4) * C1| * Real.log N * (N : ℝ) ^ (-φs) := by gcongr
      _ ≤ (1 + |(2 * C1 + 4) * C1| * Real.log N) * (N : ℝ) ^ (-φs) := by
          have : 0 ≤ (N : ℝ) ^ (-φs) := by positivity
          nlinarith

/-- The remainder of (6.88): `η² N² 4⁴ (8θ)^{ξ+1} ≤ 256 (8P)^{ξ+1} N^{-7/3-φs}` for
`θ ≤ P N^{-φs}` and `(ξ + 1) φs ≥ 3 + φs`. -/
private lemma taylor_delta_le {N : ℕ} (hN : 0 < N) {ε φs θ P : ℝ} (hε : 0 ≤ ε) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ P * (N : ℝ) ^ (-φs)) {ξ : ℕ} (hξ : 3 + φs ≤ (ξ + 1) * φs) :
    etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * θ) ^ (ξ + 1) ≤
      256 * (8 * P) ^ (ξ + 1) * (N : ℝ) ^ (-(7 : ℝ) / 3 - φs) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hP : 0 ≤ P * (N : ℝ) ^ (-φs) := hθ0.trans hθ
  have h1 : (8 * θ) ^ (ξ + 1) ≤ (8 * P) ^ (ξ + 1) * (N : ℝ) ^ (-3 - φs) := by
    calc (8 * θ) ^ (ξ + 1) ≤ (8 * (P * (N : ℝ) ^ (-φs))) ^ (ξ + 1) := by gcongr
      _ = (8 * P) ^ (ξ + 1) * (N : ℝ) ^ (-((ξ + 1 : ℕ) * φs)) := by
          rw [← mul_assoc, mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (-φs)), ← Real.rpow_mul hN0.le]
          congr 2; ring
      _ ≤ (8 * P) ^ (ξ + 1) * (N : ℝ) ^ (-3 - φs) := by
          have h8P : 0 ≤ 8 * P := by
            by_contra h
            have : P < 0 := by linarith
            have : P * (N : ℝ) ^ (-φs) < 0 := mul_neg_of_neg_of_pos this (by positivity)
            linarith
          gcongr
          push_cast; linarith
  have h2 : etaEdge N ε ^ 2 * (N : ℝ) ^ 2 ≤ (N : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [taylor_eta_sq, ← Real.rpow_natCast, ← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
  calc etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * θ) ^ (ξ + 1) ≤
      (N : ℝ) ^ ((2 : ℝ) / 3) * 4 ^ 4 * ((8 * P) ^ (ξ + 1) * (N : ℝ) ^ (-3 - φs)) := by
        gcongr
    _ = 256 * (8 * P) ^ (ξ + 1) * ((N : ℝ) ^ ((2 : ℝ) / 3) * (N : ℝ) ^ (-3 - φs)) := by ring
    _ = 256 * (8 * P) ^ (ξ + 1) * (N : ℝ) ^ (-(7 : ℝ) / 3 - φs) := by
        rw [← Real.rpow_add hN0]; congr 2; ring

/-- The probabilistic inputs of one swap, uniformly in the laws, `γ`, `e` and the energies:
the good event (6.1) and the event of (5.24) fail with probability at most `N^{-D}`, `x(y) ≤ N^ε`
on the latter ((6.82)), and the moments (6.89) of order `2` and `4` hold. -/
private lemma taylor_setup {C1 φs : ℝ} (hφs : 0 < φs) :
    ∃ ε₀ > (0 : ℝ), ε₀ ≤ 1 / 12 ∧ ∃ Cp > (0 : ℝ), ∃ C0 : ℝ, ∃ ΩL : ∀ N : ℕ, Set (Entries N),
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ D : ℝ, ∃ N0 : ℕ, ∀ N ≥ N0,
        16 ≤ N ∧
        (∀ y : ℝ, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          (⟨y, etaEdge N ε⟩ : ℂ) ∈ specDomain N C0) ∧
        (∀ ω ∈ ΩL N, ∀ y : ℝ, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          obsPoint N ε y (symOfEntries ω) ≤ (N : ℝ) ^ ε) ∧
        ∀ (Lv Lw : EntryLaws N), SmallQClass C1 φs N Lv → Lv.IsMomentMatch Lw C1 → ∀ γ : ℕ,
          (interp (lexPos N) γ Lv Lw).law.real (goodEvent N C0)ᶜ ≤ (N : ℝ) ^ (-D) ∧
          (interp (lexPos N) γ Lv Lw).law.real (ΩL N)ᶜ ≤ (N : ℝ) ^ (-D) ∧
          ∀ (e : Fin N ⊕ OffDiag N) (k : List ℕ), k.length = 2 → 1 ≤ k.sum →
            k.sum ≤ ⌈3 / φs⌉₊ → ∀ y : ℝ, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
            ∀ q ∈ ({2, 4} : Finset ℕ),
              ∫ ω, ‖opPPair e k (resR e ⟨y, etaEdge N ε⟩ ω)‖ ^ q
                ∂(interp (lexPos N) γ Lv Lw).law ≤ ((N : ℝ) ^ (1 + Cp * ε)) ^ q := by
  obtain ⟨ε₁, hε₁, Cp, hCp, hpm⟩ := moment_opP_pair_le (C1 := C1) hφs
  obtain ⟨C0, -, cg, hcg, Cg, -, Ng, hgood⟩ :=
    highProb_goodEvent (C1 := C1) (φq := min φs (1 / 4)) (lt_min hφs (by norm_num))
  obtain ⟨Ns, hNs⟩ := smallQInterp_pairInterp (C1 := C1) hφs
  obtain ⟨CL, hCL, cL, hcL, CL', -, NL, hLL⟩ := stieltjes_local_smallQInterp (C1 := C1) hφs
  obtain ⟨Cm, hCm1, hCm⟩ := taylor_im_msc_le
  refine ⟨min ε₁ (1 / 12), lt_min hε₁ (by norm_num), min_le_right _ _, Cp, hCp, C0,
    fun N => {ω | ∀ z ∈ specDomain N CL,
      ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ phi N ^ CL / (N * z.im)},
    fun ε hε hεε₀ D => ?_⟩
  have hε₁' : ε < ε₁ := lt_of_lt_of_le hεε₀ (min_le_left _ _)
  have hε12 : ε < 1 / 12 := lt_of_lt_of_le hεε₀ (min_le_right _ _)
  obtain ⟨N2, hN2⟩ := hpm ε hε hε₁' 2 even_two
  obtain ⟨N4, hN4⟩ := hpm ε hε hε₁' 4 (by decide)
  have hev := (eventually_ge_atTop (max (max N2 N4) (max (max Ng Ns) (max NL 16)))).and <|
    (taylor_ev_specDomain C0 hε.le (by linarith)).and <|
    (taylor_ev_specDomain CL hε.le (by linarith)).and <|
    (taylor_ev_highProb Cg cg D 3 hcg (by norm_num)).and <|
    (taylor_ev_highProb CL' cL D 1 hcL le_rfl).and <|
    (phi_rpow_le_rpow CL (half_pos hε)).and
    (taylor_ev_const (2 * (Real.sqrt 2 * Cm) + 2) (half_pos hε))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨hNmax, hspec, hspecL, hPG, hPL, hφ, hcm⟩ := hN0 N hN
  have h16 : 16 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_trans (le_max_right _ _) hNmax)
  have hNpos : 0 < N := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  refine ⟨h16, hspec, fun ω hω y hy => ?_, fun Lv Lw hv hw γ => ?_⟩
  · have h := taylor_obsPoint_le_of_localLaw hNpos hε.le hCm (by linarith) hy (hspecL y hy)
      (symOfEntries_isHermitian ω) (hω _ (hspecL y hy))
    refine h.trans ?_
    have h2 : (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) = (N : ℝ) ^ ε := by
      rw [← Real.rpow_add (by positivity)]; ring_nf
    have h3 : 1 ≤ (N : ℝ) ^ (ε / 2) := Real.one_le_rpow hN1 (by linarith)
    nlinarith
  · have hN3 : 3 ≤ N := by omega
    have hcls : SmallQInterpClass C1 φs N (interp (lexPos N) γ Lv Lw) := ⟨Lv, Lw, γ, hv, hw, rfl⟩
    have hmp := (MatchedPair.of_smallQ hN3 hv hw).interp γ
    have hprob := isProbabilityMeasure_law hmp.isProb_v
    have hreal : ∀ S : Set (Entries N), ∀ x : ℝ, 0 ≤ x →
        (interp (lexPos N) γ Lv Lw).law S ≤ ENNReal.ofReal x →
        (interp (lexPos N) γ Lv Lw).law.real S ≤ x := fun S x hx h => by
      rw [Measure.real]; exact ENNReal.toReal_le_of_le_ofReal hx h
    refine ⟨?_, ?_, fun e k hk hk1 hk2 y hy q hq => ?_⟩
    · have h := hgood N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
        (le_trans (le_max_right _ _) hNmax)) _
        (hNs N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
          (le_trans (le_max_right _ _) hNmax)) _ hcls)
      refine (hreal _ _ (by positivity) h).trans ?_
      rw [← Real.rpow_natCast]; exact hPG
    · have h := hLL N (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
        (le_trans (le_max_right _ _) hNmax)) _ hcls
      refine (hreal _ _ (by positivity) h).trans ?_
      simpa using hPL
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact hN2 N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hNmax) Lv Lw γ hv hw
          e k hk hk1 hk2 y hy
      · exact hN4 N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hNmax) Lv Lw γ hv hw
          e k hk hk1 hk2 y hy

/-- The law `H_γ` of one swap: a matched pair with `|h| ≤ θ` almost surely, where
`θ = q₀⁻¹ ≤ (1 + K₀ log N) N^{-φs}`, and `φs ≤ 1/2`. -/
private lemma taylor_swap_law {C1 φs : ℝ} {N : ℕ} (hN : 3 ≤ N) {Lv Lw : EntryLaws N}
    (hv : SmallQClass C1 φs N Lv) (hw : Lv.IsMomentMatch Lw C1) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ (1 + |(2 * C1 + 4) * C1| * Real.log N) * (N : ℝ) ^ (-φs) ∧
      (∀ γ : ℕ, MatchedPair C1 θ⁻¹ (interp (lexPos N) γ Lv Lw) Lw) ∧
      MatchedPair C1 θ⁻¹ Lv Lw ∧
      (∀ γ : ℕ, ∀ e : Fin N ⊕ OffDiag N, ∀ᵐ ω ∂(interp (lexPos N) γ Lv Lw).law,
        |entryVal e ω| ≤ θ) ∧
      φs ≤ 1 / 2 := by
  obtain ⟨hq, hθ⟩ := taylor_theta hN hv hw
  have hmp := MatchedPair.of_smallQ hN hv hw
  refine ⟨(min ((N : ℝ) ^ φs) (Real.sqrt N / ((2 * C1 + 4) * C1 * Real.log N)))⁻¹,
    inv_pos.2 hq, hθ, fun γ => ?_, ?_, fun γ e => ?_, taylor_phis_le_half (by omega) hv⟩
  · rw [inv_inv]; exact hmp.interp γ
  · rw [inv_inv]; exact hmp
  · exact expansion_ae_entryVal_le (hmp.interp γ).isProb_v (hmp.interp γ).supp_v e

/-- The remainder `(M δ₀)³` and the bad event of (6.101) are at most `N^{-5/2}/3` each. -/
private lemma taylor_num_rem {N : ℕ} (hN : 1728 ≤ N) {ε φs M δ₀ PG P K₀ : ℝ}
    (hε : 0 < ε) (hε12 : ε < 1 / 12) (hφs : 0 < φs) (hM0 : 0 ≤ M) (hM : M ≤ 2 * (N : ℝ) ^ (2 * ε))
    (hδ0 : 0 ≤ δ₀) {ξ : ℕ}
    (hδ : δ₀ ≤ 256 * (8 * P) ^ (ξ + 1) * (N : ℝ) ^ (-(7 : ℝ) / 3 - φs))
    (hP1 : 1 ≤ P) (hPK : P ≤ (1 + K₀) * (1 + Real.log N))
    (hPG0 : 0 ≤ PG) (hPG : PG ≤ (N : ℝ) ^ (-(4 : ℝ)))
    (hE2 : 27 * 512 ^ 3 * (8 * (1 + K₀)) ^ (3 * (ξ + 1)) *
      (1 + Real.log N) ^ (3 * (ξ + 1)) ≤ (N : ℝ) ^ ((7 : ℝ) / 2)) :
    9 * (M * δ₀) ^ 3 ≤ (1 / 3) * (N : ℝ) ^ (-(5 : ℝ) / 2) ∧
      9 * (8 * M ^ 3 * PG) ≤ (1 / 3) * (N : ℝ) ^ (-(5 : ℝ) / 2) := by
  have hN' : (1728 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  constructor
  · have hA : (8 * P) ^ (ξ + 1) ≤ (8 * (1 + K₀)) ^ (ξ + 1) * (1 + Real.log N) ^ (ξ + 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) (by nlinarith) _
    have hMδ : M * δ₀ ≤ 512 * (8 * P) ^ (ξ + 1) * (N : ℝ) ^ (-(2 : ℝ)) := by
      calc M * δ₀ ≤ 2 * (N : ℝ) ^ (2 * ε) * (256 * (8 * P) ^ (ξ + 1) *
            (N : ℝ) ^ (-(7 : ℝ) / 3 - φs)) := mul_le_mul hM hδ hδ0 (by positivity)
        _ = 512 * (8 * P) ^ (ξ + 1) * ((N : ℝ) ^ (2 * ε) * (N : ℝ) ^ (-(7 : ℝ) / 3 - φs)) := by
            ring
        _ ≤ 512 * (8 * P) ^ (ξ + 1) * (N : ℝ) ^ (-(2 : ℝ)) := by
            rw [← Real.rpow_add hN0]
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) (by positivity)
    have hcube : (M * δ₀) ^ 3 ≤ 512 ^ 3 * ((8 * (1 + K₀)) ^ (3 * (ξ + 1)) *
        (1 + Real.log N) ^ (3 * (ξ + 1))) * (N : ℝ) ^ (-(6 : ℝ)) := by
      calc (M * δ₀) ^ 3 ≤ (512 * (8 * P) ^ (ξ + 1) * (N : ℝ) ^ (-(2 : ℝ))) ^ 3 :=
            pow_le_pow_left₀ (mul_nonneg hM0 hδ0) hMδ 3
        _ = 512 ^ 3 * ((8 * P) ^ (ξ + 1)) ^ 3 * ((N : ℝ) ^ (-(2 : ℝ))) ^ 3 := by ring
        _ ≤ 512 ^ 3 * ((8 * (1 + K₀)) ^ (ξ + 1) * (1 + Real.log N) ^ (ξ + 1)) ^ 3 *
            ((N : ℝ) ^ (-(2 : ℝ))) ^ 3 := by gcongr
        _ = _ := by
            have h6 : ((N : ℝ) ^ (-(2 : ℝ))) ^ 3 = (N : ℝ) ^ (-(6 : ℝ)) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
            rw [h6, mul_pow, ← pow_mul, ← pow_mul, mul_comm (ξ + 1) 3]
    calc 9 * (M * δ₀) ^ 3 ≤ 9 * (512 ^ 3 * ((8 * (1 + K₀)) ^ (3 * (ξ + 1)) *
        (1 + Real.log N) ^ (3 * (ξ + 1))) * (N : ℝ) ^ (-(6 : ℝ))) := by gcongr
      _ = (1 / 3) * (27 * 512 ^ 3 * (8 * (1 + K₀)) ^ (3 * (ξ + 1)) *
          (1 + Real.log N) ^ (3 * (ξ + 1))) * (N : ℝ) ^ (-(6 : ℝ)) := by ring
      _ ≤ (1 / 3) * (N : ℝ) ^ ((7 : ℝ) / 2) * (N : ℝ) ^ (-(6 : ℝ)) := by gcongr
      _ = (1 / 3) * (N : ℝ) ^ (-(5 : ℝ) / 2) := by
          rw [mul_assoc, ← Real.rpow_add hN0]; norm_num
  · have hM3 : M ^ 3 ≤ 8 * (N : ℝ) ^ (6 * ε) := by
      calc M ^ 3 ≤ (2 * (N : ℝ) ^ (2 * ε)) ^ 3 := pow_le_pow_left₀ hM0 hM 3
        _ = 8 * ((N : ℝ) ^ (2 * ε)) ^ 3 := by ring
        _ = 8 * (N : ℝ) ^ (6 * ε) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num; ring_nf
    calc 9 * (8 * M ^ 3 * PG) ≤ 9 * (8 * (8 * (N : ℝ) ^ (6 * ε)) * (N : ℝ) ^ (-(4 : ℝ))) := by
          gcongr
      _ = 576 * ((N : ℝ) ^ (6 * ε) * (N : ℝ) ^ (-(4 : ℝ))) := by ring
      _ ≤ 576 * (N : ℝ) ^ (-(7 : ℝ) / 2) := by
          rw [← Real.rpow_add hN0]
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) (by norm_num)
      _ = 576 * ((N : ℝ) ^ (-(1 : ℝ)) * (N : ℝ) ^ (-(5 : ℝ) / 2)) := by
          rw [← Real.rpow_add hN0]; norm_num
      _ ≤ (1 / 3) * (N : ℝ) ^ (-(5 : ℝ) / 2) := by
          rw [Real.rpow_neg_one, ← mul_assoc]
          gcongr
          rw [mul_inv_le_iff₀ hN0]; linarith

/-- (6.101), the main term on the diagonal: `9 θ n₂ (#idx B)³ ≤ N^{-2-φs+(3Cp+2)ε}/3`. -/
private lemma taylor_T1_diag {N : ℕ} (hN : 0 < N) {ε φs Cp θ n2 nK K₀ C1 : ℝ}
    (hθ : θ ≤ (1 + K₀) * (1 + Real.log N) * (N : ℝ) ^ (-φs))
    (hn20 : 0 ≤ n2) (hn2 : n2 ≤ |C1| / N) (hnK : 0 ≤ nK) (hK₀ : 0 ≤ K₀)
    (hE : 216 * nK ^ 3 * (1 + |C1|) * (1 + K₀) * (1 + Real.log N) ≤ (N : ℝ) ^ (2 * ε)) :
    9 * (θ * n2 * (8 * nK ^ 3 * (N : ℝ) ^ (-(1 : ℝ) + 3 * Cp * ε))) ≤
      (1 / 3) * ((N : ℝ) ^ (-2 - φs) * (N : ℝ) ^ ((3 * Cp + 2) * ε)) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hrp : ∀ a b : ℝ, (N : ℝ) ^ a * (N : ℝ) ^ b = (N : ℝ) ^ (a + b) :=
    fun a b => (Real.rpow_add hN0 a b).symm
  have ha : θ * n2 ≤ (1 + K₀) * (1 + Real.log N) * |C1| * (N : ℝ) ^ (-1 - φs) := by
    calc θ * n2 ≤ ((1 + K₀) * (1 + Real.log N) * (N : ℝ) ^ (-φs)) * (|C1| / N) :=
          mul_le_mul hθ hn2 hn20 (by positivity)
      _ = (1 + K₀) * (1 + Real.log N) * |C1| * ((N : ℝ) ^ (-φs) * (N : ℝ) ^ (-(1 : ℝ))) := by
          rw [Real.rpow_neg_one]; ring
      _ = _ := by rw [hrp]; ring_nf
  have hc : 72 * nK ^ 3 * |C1| * (1 + K₀) * (1 + Real.log N) ≤ (1 / 3) * (N : ℝ) ^ (2 * ε) := by
    have h0 : 0 ≤ 216 * nK ^ 3 * (1 + K₀) * (1 + Real.log N) := by positivity
    have := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one : |C1| ≤ 1 + |C1|) h0
    linarith
  calc 9 * (θ * n2 * (8 * nK ^ 3 * (N : ℝ) ^ (-(1 : ℝ) + 3 * Cp * ε))) ≤
      9 * ((1 + K₀) * (1 + Real.log N) * |C1| * (N : ℝ) ^ (-1 - φs) *
        (8 * nK ^ 3 * (N : ℝ) ^ (-(1 : ℝ) + 3 * Cp * ε))) := by gcongr
    _ = (72 * nK ^ 3 * |C1| * (1 + K₀) * (1 + Real.log N)) *
        ((N : ℝ) ^ (-1 - φs) * (N : ℝ) ^ (-(1 : ℝ) + 3 * Cp * ε)) := by ring
    _ ≤ ((1 / 3) * (N : ℝ) ^ (2 * ε)) *
        ((N : ℝ) ^ (-1 - φs) * (N : ℝ) ^ (-(1 : ℝ) + 3 * Cp * ε)) := by gcongr
    _ = (1 / 3) * ((N : ℝ) ^ (-2 - φs) * (N : ℝ) ^ ((3 * Cp + 2) * ε)) := by
        rw [hrp, hrp, mul_assoc, hrp]; congr 2; ring

/-- (6.101), the main term off the diagonal: with `t = N^{-1/2}`, `n₂ = N⁻¹`, `n₄ ≤ |C1| log N/N²`,
`9 ((t n₂ + n₄/t)/2) (#idx B)³ ≤ N^{-5/2+(3Cp+2)ε}/3`. -/
private lemma taylor_T1_off {N : ℕ} (hN : 0 < N) {ε Cp n4 nK K₀ C1 : ℝ}
    (hn40 : 0 ≤ n4) (hn4 : n4 ≤ |C1| * Real.log N / (N : ℝ) ^ 2) (hnK : 0 ≤ nK) (hK₀ : 0 ≤ K₀)
    (hE : 216 * nK ^ 3 * (1 + |C1|) * (1 + K₀) * (1 + Real.log N) ≤ (N : ℝ) ^ (2 * ε)) :
    9 * (((N : ℝ) ^ (-(1 : ℝ) / 2) * (N : ℝ)⁻¹ + n4 / (N : ℝ) ^ (-(1 : ℝ) / 2)) / 2 *
      (8 * nK ^ 3 * (N : ℝ) ^ (-(1 : ℝ) + 3 * Cp * ε))) ≤
      (1 / 3) * ((N : ℝ) ^ (-(5 : ℝ) / 2) * (N : ℝ) ^ ((3 * Cp + 2) * ε)) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hrp : ∀ a b : ℝ, (N : ℝ) ^ a * (N : ℝ) ^ b = (N : ℝ) ^ (a + b) :=
    fun a b => (Real.rpow_add hN0 a b).symm
  set t := (N : ℝ) ^ (-(1 : ℝ) / 2) with htdef
  have ht : 0 < t := by positivity
  have e1 : t * (N : ℝ)⁻¹ = (N : ℝ) ^ (-(3 : ℝ) / 2) := by
    rw [htdef, ← Real.rpow_neg_one, hrp]; norm_num
  have e2 : |C1| * Real.log N / (N : ℝ) ^ 2 / t =
      |C1| * Real.log N * (N : ℝ) ^ (-(3 : ℝ) / 2) := by
    rw [htdef, div_div, ← Real.rpow_natCast, mul_comm ((N : ℝ) ^ ((2 : ℕ) : ℝ)), hrp,
      div_eq_mul_inv, ← Real.rpow_neg hN0.le]
    norm_num
  have h3 : n4 / t ≤ |C1| * Real.log N * (N : ℝ) ^ (-(3 : ℝ) / 2) := by
    rw [← e2]; gcongr
  have ha : (t * (N : ℝ)⁻¹ + n4 / t) / 2 ≤ (1 + |C1| * Real.log N) * (N : ℝ) ^ (-(3 : ℝ) / 2) := by
    rw [e1]
    have h0 : 0 ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) := by positivity
    have h1 : 0 ≤ |C1| * Real.log N * (N : ℝ) ^ (-(3 : ℝ) / 2) := by positivity
    linarith
  have hlogC : 1 + |C1| * Real.log N ≤ (1 + |C1|) * (1 + K₀) * (1 + Real.log N) := by
    have h1 : 1 + |C1| * Real.log N ≤ (1 + |C1|) * (1 + Real.log N) := by
      have := abs_nonneg C1
      nlinarith
    have h2 : (1 + |C1|) * (1 + Real.log N) ≤ (1 + |C1|) * (1 + K₀) * (1 + Real.log N) := by
      have h0 : 0 ≤ (1 + |C1|) * (1 + Real.log N) := by positivity
      have := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hK₀ : (1 : ℝ) ≤ 1 + K₀) h0
      linarith
    linarith
  have hc : 72 * nK ^ 3 * (1 + |C1| * Real.log N) ≤ (1 / 3) * (N : ℝ) ^ (2 * ε) := by
    have h0 : 0 ≤ 72 * nK ^ 3 := by positivity
    have := mul_le_mul_of_nonneg_left hlogC h0
    linarith
  have h0 : 0 ≤ (t * (N : ℝ)⁻¹ + n4 / t) / 2 := by positivity
  calc 9 * ((t * (N : ℝ)⁻¹ + n4 / t) / 2 * (8 * nK ^ 3 * (N : ℝ) ^ (-(1 : ℝ) + 3 * Cp * ε))) ≤
      9 * ((1 + |C1| * Real.log N) * (N : ℝ) ^ (-(3 : ℝ) / 2) *
        (8 * nK ^ 3 * (N : ℝ) ^ (-(1 : ℝ) + 3 * Cp * ε))) := by gcongr
    _ = (72 * nK ^ 3 * (1 + |C1| * Real.log N)) *
        ((N : ℝ) ^ (-(3 : ℝ) / 2) * (N : ℝ) ^ (-(1 : ℝ) + 3 * Cp * ε)) := by ring
    _ ≤ ((1 / 3) * (N : ℝ) ^ (2 * ε)) *
        ((N : ℝ) ^ (-(3 : ℝ) / 2) * (N : ℝ) ^ (-(1 : ℝ) + 3 * Cp * ε)) := by gcongr
    _ = (1 / 3) * ((N : ℝ) ^ (-(5 : ℝ) / 2) * (N : ℝ) ^ ((3 * Cp + 2) * ε)) := by
        rw [hrp, hrp, mul_assoc, hrp]; congr 2; ring

/-- (6.101) for one swap and both laws `H_γ`, `H_{γ-1}`, `γ = lexPos N e`:
`E|X_S - X_R|³ ≤ N^{-5/2+Cε}` off the diagonal and `≤ N^{-2-φs+Cε}` on it, for both observables. -/
theorem integral_abs_obs_sub_pow_three_le {C1 φs : ℝ} (hφs : 0 < φs) :
    ∃ ε₀ > (0 : ℝ), ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ N0 : ℕ, ∀ N ≥ N0,
      ∀ (Lv Lw : EntryLaws N), SmallQClass C1 φs N Lv → Lv.IsMomentMatch Lw C1 →
      ∀ X ∈ edgeObs N ε, ∀ e : Fin N ⊕ OffDiag N,
      ∀ γ ∈ ({lexPos N e, lexPos N e - 1} : Finset ℕ),
        ∫ ω, |X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))| ^ 3
            ∂(interp (lexPos N) γ Lv Lw).law ≤
          Sum.elim (fun _ => (N : ℝ) ^ (-2 - φs)) (fun _ => (N : ℝ) ^ (-(5 : ℝ) / 2)) e *
            (N : ℝ) ^ (C * ε) := by
  obtain ⟨ε₀, hε₀, hε₀12, Cp, hCp, C0, ΩL, hset⟩ := taylor_setup (C1 := C1) hφs
  refine ⟨ε₀, hε₀, 3 * Cp + 2, by positivity, fun ε hε hεε₀ => ?_⟩
  have hε12 : ε < 1 / 12 := lt_of_lt_of_le hεε₀ hε₀12
  set ξ := ⌈3 / φs⌉₊ with hξdef
  set nK : ℝ := ((taylor_idx ξ).card : ℝ) with hnK
  set K₀ := |(2 * C1 + 4) * C1| with hK₀
  obtain ⟨N1, hN1⟩ := hset ε hε hεε₀ 4
  have hev := (eventually_ge_atTop (max N1 1728)).and <|
    (taylor_ev_log (216 * nK ^ 3 * (1 + |C1|) * (1 + K₀)) 1 (by positivity : (0 : ℝ) < 2 * ε)).and
    <| (taylor_ev_log (27 * 512 ^ 3 * (8 * (1 + K₀)) ^ (3 * (ξ + 1))) (3 * (ξ + 1))
      (by norm_num : (0 : ℝ) < 7 / 2)).and (taylor_ev_log (16 * (1 + K₀)) 1 hφs)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨N0, fun N hN Lv Lw hv hw X hX e γ' _ => ?_⟩
  obtain ⟨hNmax, hE1, hE2, hE4⟩ := hN0 N hN
  have hN1' : N1 ≤ N := le_trans (le_max_left _ _) hNmax
  have hN1728 : 1728 ≤ N := le_trans (le_max_right _ _) hNmax
  obtain ⟨-, hspec, -, hlaw⟩ := hN1 N hN1'
  obtain ⟨hPG, -, hmomr⟩ := hlaw Lv Lw hv hw γ'
  have hN3 : 3 ≤ N := by omega
  have hNpos : 0 < N := by omega
  have hN0r : (0 : ℝ) < N := Nat.cast_pos.2 hNpos
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  obtain ⟨θ, hθ0', hθP, hmpγ', -, hvθ', hφ⟩ := taylor_swap_law hN3 hv hw
  have hθ0 := hθ0'.le
  have hmpγ := hmpγ' γ'
  have hvθ := hvθ' γ'
  have hprob := isProbabilityMeasure_law hmpγ.isProb_v
  obtain ⟨D⟩ := taylor_tayObs hNpos hε.le hX e
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1r
  have hK₀0 : 0 ≤ K₀ := abs_nonneg _
  have hP1 : 1 ≤ 1 + K₀ * Real.log N := by nlinarith
  have hPK : 1 + K₀ * Real.log N ≤ (1 + K₀) * (1 + Real.log N) := by nlinarith
  have hθ16 : 16 * θ ≤ 1 := by
    have h1 : 16 * θ ≤ 16 * (1 + K₀) * (1 + Real.log N) ^ 1 * (N : ℝ) ^ (-φs) := by
      rw [pow_one]
      calc 16 * θ ≤ 16 * ((1 + K₀ * Real.log N) * (N : ℝ) ^ (-φs)) := by linarith
        _ ≤ 16 * ((1 + K₀) * (1 + Real.log N) * (N : ℝ) ^ (-φs)) := by gcongr
        _ = _ := by ring
    refine h1.trans ?_
    calc 16 * (1 + K₀) * (1 + Real.log N) ^ 1 * (N : ℝ) ^ (-φs) ≤
        (N : ℝ) ^ φs * (N : ℝ) ^ (-φs) := by gcongr
      _ = 1 := by rw [← Real.rpow_add hN0r]; simp
  have hξ : 3 + φs ≤ (ξ + 1) * φs := by
    have : 3 / φs ≤ ξ := Nat.le_ceil _
    rw [div_le_iff₀ hφs] at this
    nlinarith
  set B := 2 * (N : ℝ) ^ (-(1 : ℝ) / 3 + Cp * ε) with hBdef
  have hB : 0 < B := by positivity
  have hmom : ∀ x ∈ taylor_idx ξ, ∀ q ∈ ({2, 4} : Finset ℕ),
      ∫ ω, ‖D.Y (List.ofFn x.2) (zeroEntry e ω)‖ ^ q ∂(interp (lexPos N) γ' Lv Lw).law ≤ B ^ q := by
    intro x hx q hq
    obtain ⟨hk, hk1, hk2⟩ := taylor_mem_idx hx
    have hq1 : 1 ≤ q := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega
    refine (D.moment _ hprob _ hk q hq1 _ (by positivity)
      fun y hy => hmomr e _ hk hk1 hk2 y hy q hq).trans ?_
    have := D.M_nonneg
    have := taylor_eta_pos N ε hNpos
    exact pow_le_pow_left₀ (by positivity) (taylor_mass_rate hNpos D.M_le) q
  have hδ := taylor_delta_le hNpos hε.le hθ0 hθP hξ
  have hδ0 : 0 ≤ etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * θ) ^ (ξ + 1) := by positivity
  obtain ⟨hR1, hR2⟩ := taylor_num_rem hN1728 hε hε12 hφs D.M_nonneg D.M_le hδ0 hδ hP1 hPK
    measureReal_nonneg hPG hE2
  have hnB : (nK * B) ^ 3 = 8 * nK ^ 3 * (N : ℝ) ^ (-(1 : ℝ) + 3 * Cp * ε) := by
    have h3 : ((N : ℝ) ^ (-(1 : ℝ) / 3 + Cp * ε)) ^ 3 = (N : ℝ) ^ (-(1 : ℝ) + 3 * Cp * ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0r.le]; congr 1; push_cast; ring
    rw [hBdef, mul_pow, mul_pow, h3]; ring
  have hnK0 : 0 ≤ nK := Nat.cast_nonneg _
  have hE1' : 216 * nK ^ 3 * (1 + |C1|) * (1 + K₀) * (1 + Real.log N) ≤ (N : ℝ) ^ (2 * ε) := by
    simpa using hE1
  have hc1 : 1 ≤ (N : ℝ) ^ ((3 * Cp + 2) * ε) := Real.one_le_rpow hN1r (by positivity)
  have hfinal : ∀ W a3 : ℝ, (N : ℝ) ^ (-(5 : ℝ) / 2) ≤ W →
      9 * (a3 * (nK * B) ^ 3) ≤ (1 / 3) * (W * (N : ℝ) ^ ((3 * Cp + 2) * ε)) →
      9 * (a3 * (nK * B) ^ 3 +
        (D.M * (etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * θ) ^ (ξ + 1))) ^ 3 +
        8 * D.M ^ 3 * (interp (lexPos N) γ' Lv Lw).law.real (goodEvent N C0)ᶜ) ≤
      W * (N : ℝ) ^ ((3 * Cp + 2) * ε) := by
    intro W a3 hW h1
    have hW0 : 0 ≤ W := le_trans (by positivity) hW
    have h2 : (1 / 3) * (N : ℝ) ^ (-(5 : ℝ) / 2) ≤ (1 / 3) * (W * (N : ℝ) ^ ((3 * Cp + 2) * ε)) :=
      mul_le_mul_of_nonneg_left (hW.trans (le_mul_of_one_le_right hW0 hc1)) (by norm_num)
    rw [mul_add, mul_add]
    linarith
  have hθ' : θ ≤ (1 + K₀) * (1 + Real.log N) * (N : ℝ) ^ (-φs) :=
    hθP.trans (mul_le_mul_of_nonneg_right hPK (by positivity))
  rcases e with i | p
  · -- the diagonal entry: `E|v|³ ≤ θ n₂`
    have hn2 : (interp (lexPos N) γ' Lv Lw).entryMoment (Sum.inl i) 2 ≤ |C1| / N := by
      have h := hmpγ.var_diag_le i
      simp only [EntryLaws.entryMoment, EntryLaws.entry, Sum.elim_inl, neg_sq]
      exact h.trans (by gcongr; exact le_abs_self _)
    have hn20 : 0 ≤ (interp (lexPos N) γ' Lv Lw).entryMoment (Sum.inl i) 2 := by
      simp only [EntryLaws.entryMoment, EntryLaws.entry, Sum.elim_inl, neg_sq]
      exact integral_nonneg fun x => sq_nonneg x
    have h3 := taylor_third_moment hNpos D hθ0 hθ16 (hvθ _) hspec ξ hB hmom
      (mul_nonneg hθ0 hn20) (fun g hg hg0 K hK => taylor_integral_abs_cube_le_diag hmpγ.isProb_v
        hmpγ.supp_v (Sum.inl i) (hvθ _) g hg hg0 K hK)
    refine h3.trans ?_
    simp only [Sum.elim_inl]
    refine hfinal _ _ (Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)) ?_
    rw [hnB]
    exact taylor_T1_diag hNpos hθ' hn20 hn2 hnK0 hK₀0 hE1'
  · -- an off-diagonal entry: `E|v|³ ≤ (N^{-1/2} n₂ + N^{1/2} n₄)/2`
    have hn2 : (interp (lexPos N) γ' Lv Lw).entryMoment (Sum.inr p) 2 = (N : ℝ)⁻¹ := by
      have h := hmpγ.var_off p
      simp only [EntryLaws.entryMoment, EntryLaws.entry, Sum.elim_inr, neg_sq]
      exact h
    have hn4 : (interp (lexPos N) γ' Lv Lw).entryMoment (Sum.inr p) 4 ≤
        |C1| * Real.log N / (N : ℝ) ^ 2 := by
      have h := hmpγ.fourth_off_le p
      have he : ∀ x : ℝ, (-x) ^ 4 = x ^ 4 := fun x => by ring
      simp only [EntryLaws.entryMoment, EntryLaws.entry, Sum.elim_inr, he]
      exact h.trans (by gcongr; exact le_abs_self _)
    have hn40 : 0 ≤ (interp (lexPos N) γ' Lv Lw).entryMoment (Sum.inr p) 4 := by
      have he : ∀ x : ℝ, (-x) ^ 4 = (x ^ 2) ^ 2 := fun x => by ring
      simp only [EntryLaws.entryMoment, EntryLaws.entry, Sum.elim_inr, he]
      exact integral_nonneg fun x => sq_nonneg _
    have ht : 0 < (N : ℝ) ^ (-(1 : ℝ) / 2) := by positivity
    have ha30 : 0 ≤ ((N : ℝ) ^ (-(1 : ℝ) / 2) *
        (interp (lexPos N) γ' Lv Lw).entryMoment (Sum.inr p) 2 +
        (interp (lexPos N) γ' Lv Lw).entryMoment (Sum.inr p) 4 / (N : ℝ) ^ (-(1 : ℝ) / 2)) / 2 := by
      rw [hn2]; positivity
    have h3 := taylor_third_moment hNpos D hθ0 hθ16 (hvθ _) hspec ξ hB hmom ha30
      (fun g hg hg0 K hK => taylor_integral_abs_cube_le_off hmpγ.isProb_v hmpγ.supp_v
        (Sum.inr p) (hvθ _) ht g hg hg0 K hK)
    refine h3.trans ?_
    simp only [Sum.elim_inr]
    refine hfinal _ _ le_rfl ?_
    rw [hnB, hn2]
    exact taylor_T1_off hNpos hn40 hn4 hnK0 hK₀0 hE1'

/-- `C_F ≥ 0` under (5.12). -/
private lemma taylor_CF_nonneg {CF : ℝ} {F : ℝ → ℝ}
    (hFd : ∀ n ∈ Finset.Icc 1 3, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF) : 0 ≤ CF := by
  have h := hFd 1 (by simp) 0
  simp only [abs_zero, add_zero, Real.one_rpow, mul_one] at h
  exact (abs_nonneg _).trans h

/-- `|F^{(n)}(x)| ≤ C_F (1 + A)^{C_F}` for `|x| ≤ A`, `n = 1, 2, 3`. -/
private lemma taylor_abs_iteratedDeriv_le {CF : ℝ} {F : ℝ → ℝ}
    (hFd : ∀ n ∈ Finset.Icc 1 3, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF) {n : ℕ}
    (hn : n ∈ Finset.Icc 1 3) {x A : ℝ} (hA : |x| ≤ A) :
    |iteratedDeriv n F x| ≤ CF * (1 + A) ^ CF := by
  have hCF := taylor_CF_nonneg hFd
  exact (hFd n hn x).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) (by linarith) hCF) hCF)

/-- (6.86) with `max(|x|, |y|) ≤ A`. -/
private lemma taylor_rem_le {CF : ℝ} {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    (hFd : ∀ n ∈ Finset.Icc 1 3, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF) {x y A : ℝ}
    (hA : max |x| |y| ≤ A) :
    |F y - F x - iteratedDeriv 1 F x * (y - x) - iteratedDeriv 2 F x * (y - x) ^ 2 / 2| ≤
      CF * (1 + A) ^ CF * |y - x| ^ 3 / 6 := by
  have hCF := taylor_CF_nonneg hFd
  refine (abs_taylor_three_le hF hFd x y).trans ?_
  have : (1 + max |x| |y|) ^ CF ≤ (1 + A) ^ CF :=
    Real.rpow_le_rpow (by positivity) (by linarith) hCF
  gcongr

/-- `max(|X_S|, |X_R|) ≤ 2 N^{2ε} N` everywhere, and `max(|X_S|, |X_R|) ≤ 2 N^{2ε} (N^ε + 2)`
when `x(y) ≤ N^ε` on `I_ε` ((6.82)). -/
private lemma taylor_obs_bounds {N : ℕ} {ε : ℝ} (hN : 0 < N) {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) (ω : Entries N) :
    max |X (symOfEntries ω)| |X (symOfEntries (zeroEntry e ω))| ≤ 2 * (N : ℝ) ^ (2 * ε) * N ∧
      ((∀ y : ℝ, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
        obsPoint N ε y (symOfEntries ω) ≤ (N : ℝ) ^ ε) →
        max |X (symOfEntries ω)| |X (symOfEntries (zeroEntry e ω))| ≤
          2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) := by
  have hM := D.M_nonneg
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine ⟨max_le ((D.abs_X_le ω).trans (by gcongr; exact D.M_le))
    ((D.abs_X_le _).trans (by gcongr; exact D.M_le)), fun h => ?_⟩
  have h1 := D.abs_X_le_of ω _ h
  have h2 := D.abs_sub_le ω
  have h3 : |X (symOfEntries (zeroEntry e ω))| ≤ D.M * ((N : ℝ) ^ ε + 2) := by
    have := abs_sub_abs_le_abs_sub (X (symOfEntries (zeroEntry e ω))) (X (symOfEntries ω))
    rw [abs_sub_comm] at this
    nlinarith
  have hNε : 0 ≤ (N : ℝ) ^ ε + 2 := by positivity
  refine max_le (h1.trans ?_) (h3.trans ?_)
  · have : D.M * (N : ℝ) ^ ε ≤ D.M * ((N : ℝ) ^ ε + 2) := by nlinarith
    exact this.trans (mul_le_mul_of_nonneg_right D.M_le hNε)
  · exact mul_le_mul_of_nonneg_right D.M_le hNε

/-- `w'(e) ≤ w(e) N^{-φs}` and `N^{-5/2} ≤ w(e) N^{-φs}` for `φs ≤ 1/2`. -/
private lemma taylor_weight_bounds {N : ℕ} (hN : 0 < N) {φs : ℝ} (hφ : φs ≤ 1 / 2)
    (e : Fin N ⊕ OffDiag N) :
    Sum.elim (fun _ => (N : ℝ) ^ (-2 - φs)) (fun _ => (N : ℝ) ^ (-(5 : ℝ) / 2)) e ≤
        swapWeight N e * (N : ℝ) ^ (-φs) ∧
      (N : ℝ) ^ (-(5 : ℝ) / 2) ≤ swapWeight N e * (N : ℝ) ^ (-φs) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : swapWeight N e * (N : ℝ) ^ (-φs) =
      Sum.elim (fun _ => (N : ℝ) ^ (-1 - φs)) (fun _ => (N : ℝ) ^ (-2 - φs)) e := by
    rcases e with i | p
    · simp only [swapWeight, Sum.elim_inl]
      rw [← Real.rpow_neg_one, ← Real.rpow_add hN0]; ring_nf
    · simp only [swapWeight, Sum.elim_inr]
      rw [← Real.rpow_natCast, ← Real.rpow_neg hN0.le, ← Real.rpow_add hN0]; ring_nf
  rw [h1]
  rcases e with i | p <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
    refine ⟨Real.rpow_le_rpow_of_exponent_le hN1 (by linarith),
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)⟩

/-- `N^{-2} ≤ w(e)`. -/
private lemma taylor_weight_bounds2 {N : ℕ} (hN : 0 < N) (e : Fin N ⊕ OffDiag N) :
    (N : ℝ) ^ (-(2 : ℝ)) ≤ swapWeight N e := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rcases e with i | p
  · simp only [swapWeight]
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  · simp only [swapWeight]
    rw [← Real.rpow_natCast, ← Real.rpow_neg hN0.le]
    norm_num

/-- `w(e) ≤ 1`. -/
private lemma taylor_weight_le_one {N : ℕ} (hN : 0 < N) (e : Fin N ⊕ OffDiag N) :
    swapWeight N e ≤ 1 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rcases e with i | p
  · simp only [swapWeight]; exact inv_le_one_of_one_le₀ hN1
  · simp only [swapWeight]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hN1)

/-- (6.102) in abstract form: with `S` the event of (5.24),
`E|rem| ≤ (C_F/6)(1 + A₁)^{C_F} E|X_S - X_R|³ + (C_F/6)(1 + A₂)^{C_F} (2M)³ P(Sᶜ)`. -/
private lemma taylor_rem_integral_le {N : ℕ} {ε : ℝ} (hN : 0 < N) {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) {μ : Measure (Entries N)}
    [IsProbabilityMeasure μ] {CF : ℝ} {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    (hFd : ∀ n ∈ Finset.Icc 1 3, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF)
    (S : Set (Entries N)) (hS : ∀ ω ∈ S, ∀ y : ℝ, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
      obsPoint N ε y (symOfEntries ω) ≤ (N : ℝ) ^ ε) :
    ∫ ω, |F (X (symOfEntries ω)) - F (X (symOfEntries (zeroEntry e ω))) -
        iteratedDeriv 1 F (X (symOfEntries (zeroEntry e ω))) *
          (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) -
        iteratedDeriv 2 F (X (symOfEntries (zeroEntry e ω))) *
          (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) ^ 2 / 2| ∂μ ≤
      CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF / 6 *
          ∫ ω, |X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))| ^ 3 ∂μ +
        CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF / 6 * (2 * D.M) ^ 3 * μ.real Sᶜ := by
  have hCF := taylor_CF_nonneg hFd
  have hM := D.M_nonneg
  set a := CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF / 6 with ha
  set b := CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF / 6 * (2 * D.M) ^ 3 with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  set ind : Entries N → ℝ := fun ω => (toMeasurable μ Sᶜ).indicator (fun _ => (1 : ℝ)) ω
  have hXc : Continuous fun ω => X (symOfEntries ω) := D.cont_X
  have hRc : Continuous fun ω => X (symOfEntries (zeroEntry e ω)) :=
    hXc.comp (expansion_continuous_zeroEntry e)
  have hΔc : Continuous fun ω => |X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))| ^ 3 :=
    ((hXc.sub hRc).abs).pow 3
  have hpt : ∀ ω, |F (X (symOfEntries ω)) - F (X (symOfEntries (zeroEntry e ω))) -
        iteratedDeriv 1 F (X (symOfEntries (zeroEntry e ω))) *
          (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) -
        iteratedDeriv 2 F (X (symOfEntries (zeroEntry e ω))) *
          (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) ^ 2 / 2| ≤
      a * |X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))| ^ 3 + b * ind ω := by
    intro ω
    obtain ⟨hall, hS'⟩ := taylor_obs_bounds hN D ω
    obtain ⟨hi0, -, hi1⟩ := taylor_indicator_hull μ S ω
    have hΔ0 : 0 ≤ |X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))| ^ 3 := by positivity
    by_cases hω : ω ∈ S
    · have h := taylor_rem_le hF hFd (A := 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2))
        (by rw [max_comm]; exact hS' (hS ω hω))
      have : 0 ≤ b * ind ω := mul_nonneg hb0 hi0
      calc _ ≤ CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF *
            |X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))| ^ 3 / 6 := h
        _ ≤ _ := by rw [ha]; linarith
    · have h := taylor_rem_le hF hFd (A := 2 * (N : ℝ) ^ (2 * ε) * N)
        (by rw [max_comm]; exact hall)
      have hd := D.abs_sub_le ω
      have h3 : |X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))| ^ 3 ≤ (2 * D.M) ^ 3 :=
        pow_le_pow_left₀ (abs_nonneg _) hd 3
      have hi : ind ω = 1 := hi1 hω
      have : 0 ≤ a * |X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))| ^ 3 :=
        mul_nonneg ha0 hΔ0
      calc _ ≤ CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF *
            |X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))| ^ 3 / 6 := h
        _ ≤ CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF * (2 * D.M) ^ 3 / 6 := by gcongr
        _ ≤ _ := by rw [hi, hb]; linarith
  have hi3 : Integrable ind μ :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_toMeasurable μ _)
  have hiΔ : Integrable (fun ω => |X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))| ^ 3) μ :=
    taylor_integrable_of_le hΔc (K := (2 * D.M) ^ 3) fun ω => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (abs_nonneg _) (D.abs_sub_le ω) 3
  have hiR : Integrable (fun ω => a * |X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))| ^ 3 +
      b * ind ω) μ := (hiΔ.const_mul a).add (hi3.const_mul b)
  refine (integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _) hiR
    (Eventually.of_forall hpt)).trans_eq ?_
  rw [integral_add (hiΔ.const_mul a) (hi3.const_mul b), integral_const_mul, integral_const_mul]
  congr 1
  rw [taylor_integral_indicator_hull]

/-- (6.102), numerical part. -/
private lemma taylor_num_102 {N : ℕ} (hN : 0 < N) {ε φs CF C3 W w PL E3 M : ℝ} (hε : 0 < ε)
    (hε12 : ε < 1 / 12) (hCF : 0 ≤ CF) (hC3 : 0 ≤ C3) (hE30 : 0 ≤ E3)
    (hE3 : E3 ≤ W * (N : ℝ) ^ (C3 * ε)) (hW : W ≤ w * (N : ℝ) ^ (-φs))
    (hw5 : (N : ℝ) ^ (-(5 : ℝ) / 2) ≤ w * (N : ℝ) ^ (-φs)) (hM0 : 0 ≤ M)
    (hM : M ≤ 2 * (N : ℝ) ^ (2 * ε)) (hPL0 : 0 ≤ PL) (hPL : PL ≤ (N : ℝ) ^ (-(2 * CF + 4)))
    (hEa : CF * 7 ^ CF / 3 ≤ (N : ℝ) ^ ε) (hEb : 64 / 3 * CF * 3 ^ CF ≤ N) :
    CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF / 6 * E3 +
        CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF / 6 * (2 * M) ^ 3 * PL ≤
      w * (N : ℝ) ^ (-φs + (C3 + 3 * CF + 1) * ε) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hrp : ∀ a b : ℝ, (N : ℝ) ^ a * (N : ℝ) ^ b = (N : ℝ) ^ (a + b) :=
    fun a b => (Real.rpow_add hN0 a b).symm
  have hwφ : 0 ≤ w * (N : ℝ) ^ (-φs) := le_trans (by positivity) hw5
  have hNε : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 hε.le
  have hN2ε : 1 ≤ (N : ℝ) ^ (2 * ε) := Real.one_le_rpow hN1 (by linarith)
  have hN3ε : (N : ℝ) ^ (2 * ε) * (N : ℝ) ^ ε = (N : ℝ) ^ (3 * ε) := by rw [hrp]; ring_nf
  have hN3ε1 : 1 ≤ (N : ℝ) ^ (3 * ε) := Real.one_le_rpow hN1 (by linarith)
  have hN23 : (N : ℝ) ^ (2 * ε) ≤ (N : ℝ) ^ (3 * ε) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  -- the first term
  have hA1 : 1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2) ≤ 7 * (N : ℝ) ^ (3 * ε) := by
    nlinarith
  have hA1' : (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF ≤
      7 ^ CF * (N : ℝ) ^ (3 * CF * ε) := by
    refine (Real.rpow_le_rpow (by positivity) hA1 hCF).trans_eq ?_
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hN0.le]
    ring_nf
  have hT1 : CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF / 6 * E3 ≤
      1 / 2 * (w * (N : ℝ) ^ (-φs + (C3 + 3 * CF + 1) * ε)) := by
    calc CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF / 6 * E3 ≤
        CF * (7 ^ CF * (N : ℝ) ^ (3 * CF * ε)) / 6 *
          (w * (N : ℝ) ^ (-φs) * (N : ℝ) ^ (C3 * ε)) := by
          gcongr
          exact hE3.trans (by gcongr)
      _ = (CF * 7 ^ CF / 3) * (1 / 2 * (w * ((N : ℝ) ^ (-φs) * ((N : ℝ) ^ (3 * CF * ε) *
          (N : ℝ) ^ (C3 * ε))))) := by ring
      _ ≤ (N : ℝ) ^ ε * (1 / 2 * (w * ((N : ℝ) ^ (-φs) * ((N : ℝ) ^ (3 * CF * ε) *
          (N : ℝ) ^ (C3 * ε))))) := by
          gcongr
          have : 0 ≤ w := by
            by_contra h
            have : w * (N : ℝ) ^ (-φs) < 0 := mul_neg_of_neg_of_pos (by linarith) (by positivity)
            linarith
          positivity
      _ = 1 / 2 * (w * (N : ℝ) ^ (-φs + (C3 + 3 * CF + 1) * ε)) := by
          rw [hrp, hrp, show (N : ℝ) ^ (-φs + (C3 + 3 * CF + 1) * ε) =
            (N : ℝ) ^ ε * (N : ℝ) ^ (-φs + (3 * CF * ε + C3 * ε)) by rw [hrp]; congr 1; ring]
          ring
  -- the second term
  have hA2 : 1 + 2 * (N : ℝ) ^ (2 * ε) * N ≤ 3 * (N : ℝ) ^ (2 : ℝ) := by
    have h1 : (N : ℝ) ^ (2 * ε) ≤ (N : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    rw [Real.rpow_one] at h1
    have h2 : (N : ℝ) ^ (2 : ℝ) = N * N := by rw [Real.rpow_two]; ring
    have h3 := mul_le_mul_of_nonneg_right h1 hN0.le
    have h4 : 1 ≤ (N : ℝ) * N := one_le_mul_of_one_le_of_one_le hN1 hN1
    rw [h2]
    calc 1 + 2 * (N : ℝ) ^ (2 * ε) * N = 1 + 2 * ((N : ℝ) ^ (2 * ε) * N) := by ring
      _ ≤ 1 + 2 * ((N : ℝ) * N) := by linarith
      _ ≤ 3 * ((N : ℝ) * N) := by linarith
  have hA2' : (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF ≤ 3 ^ CF * (N : ℝ) ^ (2 * CF) := by
    refine (Real.rpow_le_rpow (by positivity) hA2 hCF).trans_eq ?_
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hN0.le]
  have hM3 : (2 * M) ^ 3 ≤ 64 * (N : ℝ) ^ (6 * ε) := by
    calc (2 * M) ^ 3 ≤ (2 * (2 * (N : ℝ) ^ (2 * ε))) ^ 3 := by gcongr
      _ = 64 * ((N : ℝ) ^ (2 * ε)) ^ 3 := by ring
      _ = 64 * (N : ℝ) ^ (6 * ε) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num; ring_nf
  have hT2 : CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF / 6 * (2 * M) ^ 3 * PL ≤
      1 / 2 * (w * (N : ℝ) ^ (-φs + (C3 + 3 * CF + 1) * ε)) := by
    calc CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF / 6 * (2 * M) ^ 3 * PL ≤
        CF * (3 ^ CF * (N : ℝ) ^ (2 * CF)) / 6 * (64 * (N : ℝ) ^ (6 * ε)) *
          (N : ℝ) ^ (-(2 * CF + 4)) := by gcongr
      _ = (32 / 3 * CF * 3 ^ CF) * ((N : ℝ) ^ (2 * CF) * ((N : ℝ) ^ (6 * ε) *
          (N : ℝ) ^ (-(2 * CF + 4)))) := by ring
      _ = (32 / 3 * CF * 3 ^ CF) * (N : ℝ) ^ (6 * ε - 4) := by
          rw [hrp, hrp]; congr 2; ring
      _ ≤ (32 / 3 * CF * 3 ^ CF) * (N : ℝ) ^ (-(7 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
            (by positivity)
      _ = (32 / 3 * CF * 3 ^ CF) * ((N : ℝ) ^ (-(1 : ℝ)) * (N : ℝ) ^ (-(5 : ℝ) / 2)) := by
          rw [hrp]; norm_num
      _ ≤ 1 / 2 * (N : ℝ) ^ (-(5 : ℝ) / 2) := by
          rw [Real.rpow_neg_one, ← mul_assoc]
          gcongr
          rw [← div_eq_mul_inv, div_le_iff₀ hN0]; linarith
      _ ≤ 1 / 2 * (w * (N : ℝ) ^ (-φs + (C3 + 3 * CF + 1) * ε)) := by
          gcongr
          calc (N : ℝ) ^ (-(5 : ℝ) / 2) ≤ w * (N : ℝ) ^ (-φs) := hw5
            _ ≤ w * (N : ℝ) ^ (-φs) * (N : ℝ) ^ ((C3 + 3 * CF + 1) * ε) :=
                le_mul_of_one_le_right hwφ (Real.one_le_rpow hN1 (by positivity))
            _ = w * (N : ℝ) ^ (-φs + (C3 + 3 * CF + 1) * ε) := by rw [mul_assoc, hrp]
  linarith

/-- (6.102) for one swap: the expected third-order Taylor remainder of
`F(X_S) - F(X_R)` under `H_γ` and under `H_{γ-1}` is at most `w(e) N^{-φs+Cε}`. -/
theorem swap_taylor_rem_le {CF C1 φs : ℝ} (hφs : 0 < φs) :
    ∃ ε₀ > (0 : ℝ), ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ N0 : ℕ, ∀ N ≥ N0,
      ∀ (Lv Lw : EntryLaws N), SmallQClass C1 φs N Lv → Lv.IsMomentMatch Lw C1 →
      ∀ F : ℝ → ℝ, ContDiff ℝ 3 F →
        (∀ n ∈ Finset.Icc 1 3, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF) →
        ∀ X ∈ edgeObs N ε, ∀ e : Fin N ⊕ OffDiag N,
        ∀ γ ∈ ({lexPos N e, lexPos N e - 1} : Finset ℕ),
          ∫ ω, |F (X (symOfEntries ω)) - F (X (symOfEntries (zeroEntry e ω))) -
              iteratedDeriv 1 F (X (symOfEntries (zeroEntry e ω))) *
                (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) -
              iteratedDeriv 2 F (X (symOfEntries (zeroEntry e ω))) *
                (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) ^ 2 / 2|
            ∂(interp (lexPos N) γ Lv Lw).law ≤
            swapWeight N e * (N : ℝ) ^ (-φs + C * ε) := by
  obtain ⟨ε₀, hε₀, hε₀12, Cp, -, C0, ΩL, hset⟩ := taylor_setup (C1 := C1) hφs
  obtain ⟨ε₃, hε₃, C3, hC3, h101⟩ := integral_abs_obs_sub_pow_three_le (C1 := C1) hφs
  refine ⟨min ε₀ ε₃, lt_min hε₀ hε₃, C3 + 3 * |CF| + 1, by positivity, fun ε hε hεε => ?_⟩
  have hε₀' : ε < ε₀ := lt_of_lt_of_le hεε (min_le_left _ _)
  have hε₃' : ε < ε₃ := lt_of_lt_of_le hεε (min_le_right _ _)
  have hε12 : ε < 1 / 12 := lt_of_lt_of_le hε₀' hε₀12
  obtain ⟨N1, hN1⟩ := hset ε hε hε₀' (2 * |CF| + 4)
  obtain ⟨N3, hN3⟩ := h101 ε hε hε₃'
  have hev := (eventually_ge_atTop (max N1 N3)).and <|
    (taylor_ev_const (|CF| * 7 ^ |CF| / 3) hε).and
    (taylor_ev_const (64 / 3 * |CF| * 3 ^ |CF|) one_pos)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨N0, fun N hN Lv Lw hv hw F hF hFd X hX e γ' hγ' => ?_⟩
  obtain ⟨hNm, hEa, hEb⟩ := hN0 N hN
  have hCF := taylor_CF_nonneg hFd
  rw [Real.rpow_one] at hEb
  rw [abs_of_nonneg hCF] at hEa hEb ⊢
  obtain ⟨h16, -, hLLb, hlaw⟩ := hN1 N (le_trans (le_max_left _ _) hNm)
  obtain ⟨-, hPL, -⟩ := hlaw Lv Lw hv hw γ'
  rw [abs_of_nonneg hCF] at hPL
  have hNpos : 0 < N := by omega
  obtain ⟨θ, -, -, hmpγ', -, -, hφ⟩ := taylor_swap_law (by omega) hv hw
  have hprob := isProbabilityMeasure_law (hmpγ' γ').isProb_v
  obtain ⟨D⟩ := taylor_tayObs hNpos hε.le hX e
  have h3 := hN3 N (le_trans (le_max_right _ _) hNm) Lv Lw hv hw X hX e γ' hγ'
  have hrem := taylor_rem_integral_le (μ := (interp (lexPos N) γ' Lv Lw).law) hNpos D hF hFd
    (ΩL N) (fun ω hω y hy => hLLb ω hω y hy)
  obtain ⟨hw1, hw2⟩ := taylor_weight_bounds hNpos hφ e
  exact hrem.trans (taylor_num_102 hNpos hε hε12 hCF hC3.le
    (integral_nonneg fun _ => by positivity) h3 hw1 hw2 D.M_nonneg D.M_le measureReal_nonneg
    hPL hEa hEb)

/-! ### The low-order terms (6.103)–(6.105) -/

/-- `W_c = Σ_{k ∈ ℕ², |k| = c} Y_k`. -/
private def taylor_W {N : ℕ} {ε : ℝ} {e : Fin N ⊕ OffDiag N} {X : Matrix (Fin N) (Fin N) ℝ → ℝ}
    (D : TayObs N ε e X) (c : ℕ) (ω : Entries N) : ℂ :=
  ∑ k ∈ Finset.Nat.antidiagonalTuple 2 c, D.Y (List.ofFn k) ω

/-- `G_τ = F^{(s)}(X) Π_i W_{τ_i}`, a function of `Q`. -/
private def taylor_G {N : ℕ} {ε : ℝ} {e : Fin N ⊕ OffDiag N} {X : Matrix (Fin N) (Fin N) ℝ → ℝ}
    (D : TayObs N ε e X) (F : ℝ → ℝ) (s : ℕ) (τ : Fin s → ℕ) (ω : Entries N) : ℂ :=
  ((iteratedDeriv s F (X (symOfEntries ω)) : ℝ) : ℂ) * ∏ i, taylor_W D (τ i) ω

/-- `W_c` is continuous. -/
private lemma taylor_W_continuous {N : ℕ} {ε : ℝ} {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) (c : ℕ) :
    Continuous (taylor_W D c) :=
  continuous_finsetSum _ fun _ _ => D.cont_Y _

/-- `‖W_c‖ ≤ Z` for `1 ≤ c ≤ ξ`. -/
private lemma taylor_norm_W_le {N : ℕ} {ε : ℝ} {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) {ξ c : ℕ} (hc : c ∈ Finset.Icc 1 ξ)
    (ω : Entries N) : ‖taylor_W D c ω‖ ≤ taylor_Z D ξ ω := by
  calc ‖taylor_W D c ω‖ ≤ ∑ k ∈ Finset.Nat.antidiagonalTuple 2 c, ‖D.Y (List.ofFn k) ω‖ :=
        norm_sum_le _ _
    _ ≤ ∑ c' ∈ Finset.Icc 1 ξ, ∑ k ∈ Finset.Nat.antidiagonalTuple 2 c', ‖D.Y (List.ofFn k) ω‖ :=
        Finset.single_le_sum (f := fun c' => ∑ k ∈ Finset.Nat.antidiagonalTuple 2 c',
          ‖D.Y (List.ofFn k) ω‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hc
    _ = taylor_Z D ξ ω := by unfold taylor_Z taylor_idx; rw [Finset.sum_sigma]

/-- `G_τ` is continuous for `s ≤ 3`. -/
private lemma taylor_G_continuous {N : ℕ} {ε : ℝ} {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    {s : ℕ} (hs : s ≤ 3) (τ : Fin s → ℕ) : Continuous (taylor_G D F s τ) := by
  have hFs : Continuous (iteratedDeriv s F) :=
    hF.continuous_iteratedDeriv s (by exact_mod_cast hs)
  have h1 : Continuous fun ω : Entries N => ((iteratedDeriv s F (X (symOfEntries ω)) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hFs.comp D.cont_X)
  have h2 : Continuous fun ω : Entries N => ∏ i, taylor_W D (τ i) ω :=
    continuous_finsetProd _ fun i _ => taylor_W_continuous D (τ i)
  exact h1.mul h2

/-- `‖G_τ‖ ≤ |F^{(s)}(X)| Z^s` for `τ` with entries in `[1, ξ]`. -/
private lemma taylor_norm_G_le {N : ℕ} {ε : ℝ} {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) (F : ℝ → ℝ) {s ξ : ℕ}
    {τ : Fin s → ℕ} (hτ : τ ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc 1 ξ))
    (ω : Entries N) :
    ‖taylor_G D F s τ ω‖ ≤ |iteratedDeriv s F (X (symOfEntries ω))| * taylor_Z D ξ ω ^ s := by
  unfold taylor_G
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_prod]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc ∏ i, ‖taylor_W D (τ i) ω‖ ≤ ∏ _i : Fin s, taylor_Z D ξ ω :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          fun i _ => taylor_norm_W_le D (Fintype.mem_piFinset.1 hτ i) ω
    _ = taylor_Z D ξ ω ^ s := by simp

/-- `(Σ_c (-v)^c W_c)^s = Σ_τ (-v)^{|τ|} Π_i W_{τ_i}`. -/
private lemma taylor_T_pow {N : ℕ} {ε : ℝ} {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) (ξ s : ℕ) (v : ℝ) (ω : Entries N) :
    (∑ c ∈ Finset.Icc 1 ξ, (((-v) ^ c : ℝ) : ℂ) *
        ∑ k ∈ Finset.Nat.antidiagonalTuple 2 c, D.Y (List.ofFn k) ω) ^ s =
      ∑ τ ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc 1 ξ),
        (((-v) ^ (∑ i, τ i) : ℝ) : ℂ) * ∏ i, taylor_W D (τ i) ω := by
  have h1 : (∑ c ∈ Finset.Icc 1 ξ, (((-v) ^ c : ℝ) : ℂ) *
      ∑ k ∈ Finset.Nat.antidiagonalTuple 2 c, D.Y (List.ofFn k) ω) ^ s =
      ∑ τ ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc 1 ξ),
        ∏ i, ((((-v) ^ (τ i) : ℝ) : ℂ) * taylor_W D (τ i) ω) := by
    rw [← Finset.prod_univ_sum (t := fun _ : Fin s => Finset.Icc 1 ξ)
      (f := fun _ c => (((-v) ^ c : ℝ) : ℂ) * taylor_W D c ω)]
    simp [taylor_W]
  rw [h1]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, Finset.prod_pow_eq_pow_sum]

/-- `‖a^s - b^s‖ ≤ 2 ‖a - b‖ (1 + ‖a‖ + ‖b‖)` for `s = 1, 2`. -/
private lemma taylor_norm_pow_sub_le (a b : ℂ) {s : ℕ} (hs : s ∈ Finset.Icc 1 2) :
    ‖a ^ s - b ^ s‖ ≤ 2 * ‖a - b‖ * (1 + ‖a‖ + ‖b‖) := by
  simp only [Finset.mem_Icc] at hs
  obtain ⟨h1, h2⟩ := hs
  interval_cases s
  · simp only [pow_one]
    have := norm_nonneg (a - b)
    nlinarith [norm_nonneg a, norm_nonneg b]
  · have e : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
    rw [e, norm_mul]
    have h3 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
    have := norm_nonneg (a - b)
    nlinarith [norm_nonneg a, norm_nonneg b]

/-- The case split of the remainder of (6.103) into the good term and the two bad events. -/
private lemma taylor_alg_bound {Fb Fb' a c Z Zc iL iG M : ℝ} (hFb : 0 ≤ Fb) (hFb' : 0 ≤ Fb')
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hZ : 0 ≤ Z) (hZc : Z ≤ Zc) (hiL : 0 ≤ iL) (hiG : 0 ≤ iG)
    (hiG1 : iG ≤ 1) (hM : 0 ≤ M) :
    (Fb + Fb' * iL) * (2 * (a + c * iG) * (1 + 2 * M + Z)) ≤
      2 * Fb * a * (1 + 2 * M + Z) + 2 * Fb' * (a + c) * (1 + 2 * M + Zc) * iL +
        2 * Fb * c * (1 + 2 * M + Zc) * iG := by
  have h1 : 1 + 2 * M + Z ≤ 1 + 2 * M + Zc := by linarith
  have hp : 0 ≤ 1 + 2 * M + Z := by linarith
  have e : (Fb + Fb' * iL) * (2 * (a + c * iG) * (1 + 2 * M + Z)) =
      2 * Fb * a * (1 + 2 * M + Z) + 2 * Fb * c * iG * (1 + 2 * M + Z) +
        2 * Fb' * iL * ((a + c * iG) * (1 + 2 * M + Z)) := by ring
  rw [e]
  have t2 : 2 * Fb * c * iG * (1 + 2 * M + Z) ≤ 2 * Fb * c * (1 + 2 * M + Zc) * iG := by
    have : 0 ≤ 2 * Fb * c * iG := by positivity
    nlinarith
  have t3 : (a + c * iG) * (1 + 2 * M + Z) ≤ (a + c) * (1 + 2 * M + Zc) := by
    have : c * iG ≤ c := by nlinarith
    exact mul_le_mul (by linarith) h1 hp (by linarith)
  have t3' : 2 * Fb' * iL * ((a + c * iG) * (1 + 2 * M + Z)) ≤
      2 * Fb' * (a + c) * (1 + 2 * M + Zc) * iL := by
    have : 0 ≤ 2 * Fb' * iL := by positivity
    nlinarith
  linarith

/-- (6.103)–(6.105) in abstract form, for one law `H`: `E[F^{(s)}(X_R)(X_S - X_R)^s]` equals
`Σ_τ E[G_τ(Q)] n_{|τ|}` up to the remainder of (6.88) and the two bad events. -/
private lemma taylor_low_order_expansion {N : ℕ} {ε : ℝ} (hN : 0 < N) {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) {L : EntryLaws N} (hL : L.IsProb)
    {q : ℝ} (hsupp : L.BoundedSupportAS q) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 16 * θ ≤ 1)
    (hvθ : ∀ᵐ ω ∂L.law, |entryVal e ω| ≤ θ) {C0 : ℝ}
    (hspec : ∀ y, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
      (⟨y, etaEdge N ε⟩ : ℂ) ∈ specDomain N C0)
    (ξ : ℕ) {B : ℝ} (hB : 0 < B)
    (hmom : ∀ x ∈ taylor_idx ξ, ∀ q ∈ ({2, 4} : Finset ℕ),
      ∫ ω, ‖D.Y (List.ofFn x.2) (zeroEntry e ω)‖ ^ q ∂L.law ≤ B ^ q)
    {CF : ℝ} {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    (hFd : ∀ n ∈ Finset.Icc 1 3, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF)
    {s : ℕ} (hs : s ∈ Finset.Icc 1 2) (S : Set (Entries N))
    (hS : ∀ ω ∈ S, ∀ y : ℝ, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
      obsPoint N ε y (symOfEntries ω) ≤ (N : ℝ) ^ ε) :
    ‖((∫ ω, iteratedDeriv s F (X (symOfEntries (zeroEntry e ω))) *
          (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) ^ s ∂L.law : ℝ) : ℂ) -
        ∑ τ ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc 1 ξ),
          (∫ ω, taylor_G D F s τ (zeroEntry e ω) ∂L.law) * (L.entryMoment e (∑ i, τ i) : ℂ)‖ ≤
      2 * (CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF) *
          (D.M * (etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * θ) ^ (ξ + 1))) *
          (1 + 2 * D.M + (taylor_idx ξ).card * B) +
        2 * (CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF) *
          (D.M * (etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * θ) ^ (ξ + 1)) +
            (2 * D.M + taylor_Zc D ξ)) * (1 + 2 * D.M + taylor_Zc D ξ) * L.law.real Sᶜ +
        2 * (CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF) *
          (2 * D.M + taylor_Zc D ξ) * (1 + 2 * D.M + taylor_Zc D ξ) *
          L.law.real (goodEvent N C0)ᶜ := by
  have hprob := isProbabilityMeasure_law hL
  have hCF := taylor_CF_nonneg hFd
  have hM := D.M_nonneg
  have hs3 : s ∈ Finset.Icc 1 3 := by
    simp only [Finset.mem_Icc] at hs ⊢; omega
  set A₁ := 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2) with hA₁
  set A₂ := 2 * (N : ℝ) ^ (2 * ε) * N with hA₂
  set Fb := CF * (1 + A₁) ^ CF with hFb
  set Fb' := CF * (1 + A₂) ^ CF with hFb'
  have hA₁0 : 0 ≤ A₁ := by positivity
  have hA₂0 : 0 ≤ A₂ := by positivity
  have hFb0 : 0 ≤ Fb := by positivity
  have hFb'0 : 0 ≤ Fb' := by positivity
  set δ₀ := etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * θ) ^ (ξ + 1) with hδ₀
  have hδ0 : 0 ≤ δ₀ := by have := taylor_eta_pos N ε hN; positivity
  set Zc := taylor_Zc D ξ with hZcdef
  set Zq : Entries N → ℝ := fun ω => taylor_Z D ξ (zeroEntry e ω) with hZq
  have hZ0 : ∀ ω, 0 ≤ Zq ω := fun ω => taylor_Z_nonneg D ξ _
  have hZc : ∀ ω, Zq ω ≤ Zc := fun ω => taylor_Z_le hN D ξ _
  have hZc0 : 0 ≤ Zc := (hZ0 0).trans (hZc 0)
  set iL : Entries N → ℝ := fun ω => (toMeasurable L.law Sᶜ).indicator (fun _ => (1 : ℝ)) ω
  set iG : Entries N → ℝ := fun ω =>
    (toMeasurable L.law (goodEvent N C0)ᶜ).indicator (fun _ => (1 : ℝ)) ω
  set fQ : Entries N → ℝ := fun ω => iteratedDeriv s F (X (symOfEntries (zeroEntry e ω))) with hfQ
  set Δ : Entries N → ℝ := fun ω => X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω)) with hΔ
  set T : Entries N → ℂ := fun ω => ∑ c ∈ Finset.Icc 1 ξ, (((-entryVal e ω) ^ c : ℝ) : ℂ) *
    ∑ k ∈ Finset.Nat.antidiagonalTuple 2 c, D.Y (List.ofFn k) (zeroEntry e ω) with hT
  -- continuity
  have hvc : Continuous fun ω : Entries N => entryVal e ω := by
    rcases e with i | p
    · exact (continuous_apply i).comp continuous_fst
    · exact (continuous_apply p).comp continuous_snd
  have hFs : Continuous (iteratedDeriv s F) :=
    hF.continuous_iteratedDeriv s (by
      have := (Finset.mem_Icc.1 hs).2; exact_mod_cast (show s ≤ 3 by omega))
  have hXc := D.cont_X
  have hRc : Continuous fun ω => X (symOfEntries (zeroEntry e ω)) :=
    hXc.comp (expansion_continuous_zeroEntry e)
  have hfQc : Continuous fQ := hFs.comp hRc
  have hΔc : Continuous Δ := hXc.sub hRc
  have hTc : Continuous T := continuous_finsetSum _ fun c _ =>
    (Complex.continuous_ofReal.comp (hvc.neg.pow c)).mul
      ((taylor_W_continuous D c).comp (expansion_continuous_zeroEntry e))
  -- the bound on `F^{(s)}(X_R)`
  have hfb : ∀ ω, |fQ ω| ≤ Fb + Fb' * iL ω := by
    intro ω
    obtain ⟨hall, hS'⟩ := taylor_obs_bounds hN D ω
    obtain ⟨hi0, -, hi1⟩ := taylor_indicator_hull L.law S ω
    by_cases hω : ω ∈ S
    · have h := taylor_abs_iteratedDeriv_le hFd hs3 ((le_max_right _ _).trans (hS' (hS ω hω)))
      have : 0 ≤ Fb' * iL ω := mul_nonneg hFb'0 hi0
      linarith
    · have h := taylor_abs_iteratedDeriv_le hFd hs3 ((le_max_right _ _).trans hall)
      rw [show iL ω = 1 from hi1 hω, mul_one]
      linarith
  have hfb' : ∀ ω, |fQ ω| ≤ Fb' := by
    intro ω
    obtain ⟨hall, -⟩ := taylor_obs_bounds hN D ω
    exact taylor_abs_iteratedDeriv_le hFd hs3 ((le_max_right _ _).trans hall)
  -- the pointwise bound
  set h : Entries N → ℝ := fun ω => 2 * Fb * (D.M * δ₀) * (1 + 2 * D.M + Zq ω) +
    2 * Fb' * (D.M * δ₀ + (2 * D.M + Zc)) * (1 + 2 * D.M + Zc) * iL ω +
    2 * Fb * (2 * D.M + Zc) * (1 + 2 * D.M + Zc) * iG ω with hh
  have hpt : ∀ᵐ ω ∂L.law, ‖((fQ ω : ℝ) : ℂ) * ((Δ ω : ℝ) : ℂ) ^ s - ((fQ ω : ℝ) : ℂ) * T ω ^ s‖ ≤
      h ω := by
    filter_upwards [hvθ] with ω hω
    have hv1 : |entryVal e ω| ≤ 1 := by linarith
    have hTZ : ‖T ω‖ ≤ Zq ω :=
      (taylor_norm_T_le D ξ hv1 (zeroEntry e ω)).trans (by
        have := hZ0 ω; nlinarith [abs_nonneg (entryVal e ω)])
    have hΔM : |Δ ω| ≤ 2 * D.M := D.abs_sub_le ω
    obtain ⟨hiG0, hiG1, hiGc⟩ := taylor_indicator_hull L.law (goodEvent N C0) ω
    obtain ⟨hiL0, -, -⟩ := taylor_indicator_hull L.law S ω
    have hdiff : ‖((Δ ω : ℝ) : ℂ) - T ω‖ ≤ D.M * δ₀ + (2 * D.M + Zc) * iG ω := by
      by_cases hg : ω ∈ goodEvent N C0
      · have h16 : 16 * |entryVal e ω| ≤ 1 := by linarith
        have hexp := D.expand C0 hspec ω hg h16 ξ
        have hδv : etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * |entryVal e ω|) ^ (ξ + 1) ≤ δ₀ := by
          rw [hδ₀]; gcongr
        have : 0 ≤ (2 * D.M + Zc) * iG ω := by positivity
        calc ‖((Δ ω : ℝ) : ℂ) - T ω‖ ≤ D.M * δ₀ := hexp.trans (mul_le_mul_of_nonneg_left hδv hM)
          _ ≤ _ := by linarith
      · rw [show iG ω = 1 from hiGc hg, mul_one]
        calc ‖((Δ ω : ℝ) : ℂ) - T ω‖ ≤ ‖((Δ ω : ℝ) : ℂ)‖ + ‖T ω‖ := norm_sub_le _ _
          _ ≤ 2 * D.M + Zc := by
              rw [Complex.norm_real, Real.norm_eq_abs]; linarith [hZc ω]
          _ ≤ _ := by have := mul_nonneg hM hδ0; linarith
    have hpow := taylor_norm_pow_sub_le ((Δ ω : ℝ) : ℂ) (T ω) hs
    rw [Complex.norm_real, Real.norm_eq_abs] at hpow
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |fQ ω| * ‖((Δ ω : ℝ) : ℂ) ^ s - T ω ^ s‖ ≤
        (Fb + Fb' * iL ω) * (2 * (D.M * δ₀ + (2 * D.M + Zc) * iG ω) * (1 + 2 * D.M + Zq ω)) := by
          refine mul_le_mul (hfb ω) (hpow.trans ?_) (norm_nonneg _) (by positivity)
          gcongr
      _ ≤ h ω := taylor_alg_bound hFb0 hFb'0 (mul_nonneg hM hδ0) (by positivity) (hZ0 ω)
          (hZc ω) hiL0 hiG0 hiG1 hM
  -- integrability
  have hfQb : ∀ ω, ‖((fQ ω : ℝ) : ℂ)‖ ≤ Fb' := fun ω => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hfb' ω
  have hg1i : Integrable (fun ω => ((fQ ω : ℝ) : ℂ) * ((Δ ω : ℝ) : ℂ) ^ s) L.law := by
    refine Integrable.of_bound (((Complex.continuous_ofReal.comp hfQc).mul
      ((Complex.continuous_ofReal.comp hΔc).pow s)).aestronglyMeasurable) (Fb' * (2 * D.M) ^ s)
      (Eventually.of_forall fun ω => ?_)
    rw [norm_mul, norm_pow]
    refine mul_le_mul (hfQb ω) ?_ (by positivity) hFb'0
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (D.abs_sub_le ω) s
  have hTb : ∀ᵐ ω ∂L.law, ‖T ω‖ ≤ Zc := by
    filter_upwards [hvθ] with ω hω
    have hv1 : |entryVal e ω| ≤ 1 := by linarith
    exact (taylor_norm_T_le D ξ hv1 (zeroEntry e ω)).trans (by
      have := hZ0 ω; have := hZc ω; nlinarith [abs_nonneg (entryVal e ω)])
  have hg2i : Integrable (fun ω => ((fQ ω : ℝ) : ℂ) * T ω ^ s) L.law := by
    refine Integrable.of_bound (((Complex.continuous_ofReal.comp hfQc).mul
      (hTc.pow s)).aestronglyMeasurable) (Fb' * Zc ^ s) ?_
    filter_upwards [hTb] with ω hω
    rw [norm_mul, norm_pow]
    exact mul_le_mul (hfQb ω) (pow_le_pow_left₀ (norm_nonneg _) hω s) (by positivity) hFb'0
  have hiL : Integrable iL L.law :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_toMeasurable _ _)
  have hiG : Integrable iG L.law :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_toMeasurable _ _)
  have hZqi : Integrable Zq L.law :=
    taylor_integrable_of_le ((taylor_Z_continuous D ξ).comp (expansion_continuous_zeroEntry e))
      (K := Zc) fun ω => by rw [Real.norm_of_nonneg (hZ0 ω)]; exact hZc ω
  have hhi1 : Integrable (fun ω => 2 * Fb * (D.M * δ₀) * (1 + 2 * D.M + Zq ω)) L.law :=
    ((integrable_const _).add hZqi).const_mul _
  have hhi2 : Integrable (fun ω => 2 * Fb' * (D.M * δ₀ + (2 * D.M + Zc)) *
      (1 + 2 * D.M + Zc) * iL ω) L.law := hiL.const_mul _
  have hhi3 : Integrable (fun ω => 2 * Fb * (2 * D.M + Zc) * (1 + 2 * D.M + Zc) * iG ω) L.law :=
    hiG.const_mul _
  have hhi : Integrable h L.law := (hhi1.add hhi2).add hhi3
  -- the expectation of the main term
  have h1 : ((∫ ω, iteratedDeriv s F (X (symOfEntries (zeroEntry e ω))) *
      (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) ^ s ∂L.law : ℝ) : ℂ) =
      ∫ ω, ((fQ ω : ℝ) : ℂ) * ((Δ ω : ℝ) : ℂ) ^ s ∂L.law := by
    rw [← integral_complex_ofReal]
    congr 1; funext ω
    simp only [hfQ, hΔ, Complex.ofReal_mul, Complex.ofReal_pow]
  have hGi : ∀ τ ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc 1 ξ),
      Integrable (fun ω => taylor_G D F s τ (zeroEntry e ω)) L.law := fun τ hτ =>
    taylor_integrable_of_le ((taylor_G_continuous D hF (by
      have := (Finset.mem_Icc.1 hs).2; omega) τ).comp (expansion_continuous_zeroEntry e))
      (K := Fb' * Zc ^ s) fun ω => (taylor_norm_G_le D F hτ _).trans
        (mul_le_mul (hfb' ω) (pow_le_pow_left₀ (hZ0 ω) (hZc ω) s) (pow_nonneg (hZ0 _) s) hFb'0)
  have h2 : ∫ ω, ((fQ ω : ℝ) : ℂ) * T ω ^ s ∂L.law =
      ∑ τ ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc 1 ξ),
        (∫ ω, taylor_G D F s τ (zeroEntry e ω) ∂L.law) * (L.entryMoment e (∑ i, τ i) : ℂ) := by
    have hpt2 : ∀ ω, ((fQ ω : ℝ) : ℂ) * T ω ^ s =
        ∑ τ ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc 1 ξ),
          taylor_G D F s τ (zeroEntry e ω) * (((-entryVal e ω) ^ (∑ i, τ i) : ℝ) : ℂ) := by
      intro ω
      simp only [hT]
      rw [taylor_T_pow, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [taylor_G, hfQ]
      ring
    rw [integral_congr_ae (Eventually.of_forall hpt2)]
    have hint : ∀ τ ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc 1 ξ),
        Integrable (fun ω => taylor_G D F s τ (zeroEntry e ω) *
          (((-entryVal e ω) ^ (∑ i, τ i) : ℝ) : ℂ)) L.law := by
      intro τ hτ
      refine Integrable.of_bound ((((taylor_G_continuous D hF (by
        have := (Finset.mem_Icc.1 hs).2; omega) τ).comp (expansion_continuous_zeroEntry e)).mul
          (Complex.continuous_ofReal.comp (hvc.neg.pow _))).aestronglyMeasurable)
        (Fb' * Zc ^ s) ?_
      filter_upwards [hvθ] with ω hω
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_neg]
      have h1 : |entryVal e ω| ^ (∑ i, τ i) ≤ 1 := pow_le_one₀ (abs_nonneg _) (by linarith)
      have h2 := (taylor_norm_G_le D F hτ (zeroEntry e ω)).trans
        (mul_le_mul (hfb' ω) (pow_le_pow_left₀ (hZ0 ω) (hZc ω) s) (pow_nonneg (hZ0 _) s) hFb'0)
      calc ‖taylor_G D F s τ (zeroEntry e ω)‖ * |entryVal e ω| ^ (∑ i, τ i) ≤
          (Fb' * Zc ^ s) * 1 := mul_le_mul h2 h1 (by positivity)
            (mul_nonneg hFb'0 (pow_nonneg hZc0 s))
        _ = Fb' * Zc ^ s := mul_one _
    rw [integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun τ hτ => ?_
    exact integral_mul_zeroEntry hL e (taylor_G D F s τ) (∑ i, τ i)
      (taylor_G_continuous D hF (by have := (Finset.mem_Icc.1 hs).2; omega) τ).measurable
      (hGi τ hτ) (taylor_integrable_entry_pow hsupp hL e _)
  rw [h1, ← h2, ← integral_sub hg1i hg2i]
  refine (norm_integral_le_of_norm_le hhi hpt).trans ?_
  -- the expectation of the bound
  have hEZ : ∫ ω, Zq ω ∂L.law ≤ (taylor_idx ξ).card * B := by
    have := taylor_integral_Z_pow_le hN D ξ hB hmom 1 (by simp)
    simpa using this
  have hint_h : ∫ ω, h ω ∂L.law = 2 * Fb * (D.M * δ₀) * (1 + 2 * D.M + ∫ ω, Zq ω ∂L.law) +
      2 * Fb' * (D.M * δ₀ + (2 * D.M + Zc)) * (1 + 2 * D.M + Zc) * L.law.real Sᶜ +
      2 * Fb * (2 * D.M + Zc) * (1 + 2 * D.M + Zc) * L.law.real (goodEvent N C0)ᶜ := by
    have h12 : Integrable (fun ω => 2 * Fb * (D.M * δ₀) * (1 + 2 * D.M + Zq ω) +
        2 * Fb' * (D.M * δ₀ + (2 * D.M + Zc)) * (1 + 2 * D.M + Zc) * iL ω) L.law := hhi1.add hhi2
    have hL1 : ∫ ω, iL ω ∂L.law = L.law.real Sᶜ := taylor_integral_indicator_hull _ _
    have hG1 : ∫ ω, iG ω ∂L.law = L.law.real (goodEvent N C0)ᶜ :=
      taylor_integral_indicator_hull _ _
    have hc1 : Integrable (fun ω => 1 + 2 * D.M + Zq ω) L.law := (integrable_const _).add hZqi
    simp only [hh]
    rw [integral_add h12 hhi3, integral_add hhi1 hhi2, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_add (integrable_const _) hZqi,
      integral_const, hL1, hG1]
    simp
  rw [hint_h]
  have : 0 ≤ 2 * Fb * (D.M * δ₀) := by positivity
  gcongr

/-- `‖E G_τ(Q)‖ ≤ F_b (1 + (#idx B)²) + F_b' (1 + Z_c²) P(Sᶜ)`. -/
private lemma taylor_norm_integral_G_le {N : ℕ} {ε : ℝ} (hN : 0 < N) {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) {μ : Measure (Entries N)}
    [IsProbabilityMeasure μ] (ξ : ℕ) {B : ℝ} (hB : 0 < B)
    (hmom : ∀ x ∈ taylor_idx ξ, ∀ q ∈ ({2, 4} : Finset ℕ),
      ∫ ω, ‖D.Y (List.ofFn x.2) (zeroEntry e ω)‖ ^ q ∂μ ≤ B ^ q)
    {CF : ℝ} {F : ℝ → ℝ}
    (hFd : ∀ n ∈ Finset.Icc 1 3, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF)
    {s : ℕ} (hs : s ∈ Finset.Icc 1 2) (S : Set (Entries N))
    (hS : ∀ ω ∈ S, ∀ y : ℝ, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
      obsPoint N ε y (symOfEntries ω) ≤ (N : ℝ) ^ ε)
    {τ : Fin s → ℕ} (hτ : τ ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc 1 ξ)) :
    ‖∫ ω, taylor_G D F s τ (zeroEntry e ω) ∂μ‖ ≤
      CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF *
          (1 + ((taylor_idx ξ).card * B) ^ 2) +
        CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF * (1 + taylor_Zc D ξ ^ 2) * μ.real Sᶜ := by
  have hCF := taylor_CF_nonneg hFd
  have hs3 : s ∈ Finset.Icc 1 3 := by
    simp only [Finset.mem_Icc] at hs ⊢; omega
  set Fb := CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF with hFb
  set Fb' := CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF with hFb'
  have hFb0 : 0 ≤ Fb := by positivity
  have hFb'0 : 0 ≤ Fb' := by positivity
  set Zq : Entries N → ℝ := fun ω => taylor_Z D ξ (zeroEntry e ω) with hZq
  have hZ0 : ∀ ω, 0 ≤ Zq ω := fun ω => taylor_Z_nonneg D ξ _
  have hZc : ∀ ω, Zq ω ≤ taylor_Zc D ξ := fun ω => taylor_Z_le hN D ξ _
  have hZc0 : 0 ≤ taylor_Zc D ξ := (hZ0 0).trans (hZc 0)
  set iL : Entries N → ℝ := fun ω => (toMeasurable μ Sᶜ).indicator (fun _ => (1 : ℝ)) ω
  have hpt : ∀ ω, ‖taylor_G D F s τ (zeroEntry e ω)‖ ≤
      Fb * (1 + Zq ω ^ 2) + Fb' * (1 + taylor_Zc D ξ ^ 2) * iL ω := by
    intro ω
    obtain ⟨hall, hS'⟩ := taylor_obs_bounds hN D ω
    obtain ⟨hi0, -, hi1⟩ := taylor_indicator_hull μ S ω
    have hG := taylor_norm_G_le D F hτ (zeroEntry e ω)
    have hZs : Zq ω ^ s ≤ 1 + Zq ω ^ 2 := by
      simp only [Finset.mem_Icc] at hs
      obtain ⟨h1, h2⟩ := hs
      interval_cases s
      · nlinarith [hZ0 ω]
      · linarith
    have hZs' : Zq ω ^ 2 ≤ taylor_Zc D ξ ^ 2 := pow_le_pow_left₀ (hZ0 ω) (hZc ω) 2
    by_cases hω : ω ∈ S
    · have hf := taylor_abs_iteratedDeriv_le hFd hs3 ((le_max_right _ _).trans (hS' (hS ω hω)))
      have : 0 ≤ Fb' * (1 + taylor_Zc D ξ ^ 2) * iL ω := by positivity
      calc ‖taylor_G D F s τ (zeroEntry e ω)‖ ≤ Fb * Zq ω ^ s :=
            hG.trans (mul_le_mul_of_nonneg_right hf (pow_nonneg (hZ0 ω) s))
        _ ≤ Fb * (1 + Zq ω ^ 2) := mul_le_mul_of_nonneg_left hZs hFb0
        _ ≤ _ := by linarith
    · have hf := taylor_abs_iteratedDeriv_le hFd hs3 ((le_max_right _ _).trans hall)
      rw [show iL ω = 1 from hi1 hω, mul_one]
      have : 0 ≤ Fb * (1 + Zq ω ^ 2) := by positivity
      calc ‖taylor_G D F s τ (zeroEntry e ω)‖ ≤ Fb' * Zq ω ^ s :=
            hG.trans (mul_le_mul_of_nonneg_right hf (pow_nonneg (hZ0 ω) s))
        _ ≤ Fb' * (1 + taylor_Zc D ξ ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hFb'0
        _ ≤ _ := by linarith
  have hZqi : Integrable (fun ω => Zq ω ^ 2) μ :=
    taylor_integrable_of_le (((taylor_Z_continuous D ξ).comp
      (expansion_continuous_zeroEntry e)).pow 2) (K := taylor_Zc D ξ ^ 2) fun ω => by
        rw [Real.norm_of_nonneg (pow_nonneg (hZ0 ω) 2)]
        exact pow_le_pow_left₀ (hZ0 ω) (hZc ω) 2
  have hiL : Integrable iL μ :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_toMeasurable _ _)
  have h1 : Integrable (fun ω => Fb * (1 + Zq ω ^ 2)) μ :=
    ((integrable_const _).add hZqi).const_mul _
  have h2 : Integrable (fun ω => Fb' * (1 + taylor_Zc D ξ ^ 2) * iL ω) μ := hiL.const_mul _
  have h12 : Integrable (fun ω => Fb * (1 + Zq ω ^ 2) + Fb' * (1 + taylor_Zc D ξ ^ 2) * iL ω) μ :=
    h1.add h2
  have hc2 : Integrable (fun ω => 1 + Zq ω ^ 2) μ := (integrable_const _).add hZqi
  refine (norm_integral_le_of_norm_le h12 (Eventually.of_forall hpt)).trans ?_
  have hL1 : ∫ ω, iL ω ∂μ = μ.real Sᶜ := taylor_integral_indicator_hull _ _
  have hEZ : ∫ ω, Zq ω ^ 2 ∂μ ≤ ((taylor_idx ξ).card * B) ^ 2 :=
    taylor_integral_Z_pow_le hN D ξ hB hmom 2 (by simp)
  rw [integral_add h1 h2, integral_const_mul, integral_const_mul, hL1,
    integral_add (integrable_const _) hZqi, integral_const]
  simp only [probReal_univ, one_smul]
  gcongr

/-- The moments of the swapped entry under `H_γ` and `H_{γ-1}` agree up to the order
`matchedOrder e` (Lemma 5.1), and differ by at most `2 |C1| N⁻¹ q⁻¹` (diagonal) or
`2 |C1| log N N⁻² q⁻¹` (off the diagonal) for higher orders, `q⁻¹ ≤ 1`. -/
private lemma taylor_moment_diff {N : ℕ} {C1 q : ℝ} {Lv Lw : EntryLaws N}
    (hmp : MatchedPair C1 q Lv Lw) (hq : 0 < q) (hq1 : q⁻¹ ≤ 1) (e : Fin N ⊕ OffDiag N) (k : ℕ) :
    |(interp (lexPos N) (lexPos N e) Lv Lw).entryMoment e k -
        (interp (lexPos N) (lexPos N e - 1) Lv Lw).entryMoment e k| ≤
      (if k ≤ matchedOrder e then 0 else
        2 * Sum.elim (fun _ => |C1| / N * q⁻¹)
          (fun _ => |C1| * Real.log N / (N : ℝ) ^ 2 * q⁻¹) e) := by
  have hge := (lexPos_mem_Icc N e).1
  have h1 : (interp (lexPos N) (lexPos N e) Lv Lw).entryMoment e k = Lv.entryMoment e k := by
    rcases e with i | p <;>
      simp [EntryLaws.entryMoment, EntryLaws.entry, EntryLaws.interp]
  have h0 : (interp (lexPos N) (lexPos N e - 1) Lv Lw).entryMoment e k = Lw.entryMoment e k := by
    have hn : ¬ lexPos N e ≤ lexPos N e - 1 := by omega
    rcases e with i | p <;>
      simp [EntryLaws.entryMoment, EntryLaws.entry, EntryLaws.interp, hn]
  split_ifs with hk
  · rw [h1, h0, hmp.entryMoment_eq e k hk, sub_self, abs_zero]
  · have hq0 : 0 ≤ q⁻¹ := inv_nonneg.2 hq.le
    have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    refine (abs_sub _ _).trans ?_
    rcases e with i | p
    · simp only [matchedOrder, not_le] at hk
      have hb : ∀ γ : ℕ, |(interp (lexPos N) γ Lv Lw).entryMoment (Sum.inl i) k| ≤
          |C1| / N * q⁻¹ := by
        intro γ
        refine (hmp.abs_entryMoment_diag_le hq γ i k (by omega)).trans ?_
        have : q⁻¹ ^ (k - 2) ≤ q⁻¹ := by
          calc q⁻¹ ^ (k - 2) = q⁻¹ ^ (k - 3) * q⁻¹ := by rw [← pow_succ]; congr 1; omega
            _ ≤ 1 * q⁻¹ := by gcongr; exact pow_le_one₀ hq0 hq1
            _ = q⁻¹ := one_mul _
        calc C1 / N * q⁻¹ ^ (k - 2) ≤ |C1| / N * q⁻¹ ^ (k - 2) := by
              gcongr; exact le_abs_self _
          _ ≤ |C1| / N * q⁻¹ := by gcongr
      simp only [Sum.elim_inl]
      linarith [hb (lexPos N (Sum.inl i)), hb (lexPos N (Sum.inl i) - 1)]
    · simp only [matchedOrder, not_le] at hk
      have hb : ∀ γ : ℕ, |(interp (lexPos N) γ Lv Lw).entryMoment (Sum.inr p) k| ≤
          |C1| * Real.log N / (N : ℝ) ^ 2 * q⁻¹ := by
        intro γ
        refine (hmp.abs_entryMoment_off_le hq γ p k (by omega)).trans ?_
        have : q⁻¹ ^ (k - 4) ≤ q⁻¹ := by
          calc q⁻¹ ^ (k - 4) = q⁻¹ ^ (k - 5) * q⁻¹ := by rw [← pow_succ]; congr 1; omega
            _ ≤ 1 * q⁻¹ := by gcongr; exact pow_le_one₀ hq0 hq1
            _ = q⁻¹ := one_mul _
        calc C1 * Real.log N / (N : ℝ) ^ 2 * q⁻¹ ^ (k - 4) ≤
            |C1| * Real.log N / (N : ℝ) ^ 2 * q⁻¹ ^ (k - 4) := by
              gcongr; exact le_abs_self _
          _ ≤ |C1| * Real.log N / (N : ℝ) ^ 2 * q⁻¹ := by gcongr
      simp only [Sum.elim_inr]
      linarith [hb (lexPos N (Sum.inr p)), hb (lexPos N (Sum.inr p) - 1)]

/-! ### Numerical bounds for (6.103)–(6.105) -/

/-- `F_b = C_F (1 + A₁)^{C_F} ≤ C_F 7^{C_F} N^{3 C_F ε}`. -/
private lemma taylor_Fb_le {N : ℕ} (hN : 0 < N) {ε CF : ℝ} (hε : 0 ≤ ε) (hCF : 0 ≤ CF) :
    CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF ≤
      CF * 7 ^ CF * (N : ℝ) ^ (3 * CF * ε) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNε : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 hε
  have hN2ε : 1 ≤ (N : ℝ) ^ (2 * ε) := Real.one_le_rpow hN1 (by linarith)
  have hN3ε : (N : ℝ) ^ (2 * ε) * (N : ℝ) ^ ε = (N : ℝ) ^ (3 * ε) := by
    rw [← Real.rpow_add hN0]; ring_nf
  have hN23 : (N : ℝ) ^ (2 * ε) ≤ (N : ℝ) ^ (3 * ε) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hA1 : 1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2) ≤ 7 * (N : ℝ) ^ (3 * ε) := by
    nlinarith
  have h : (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF ≤
      7 ^ CF * (N : ℝ) ^ (3 * CF * ε) := by
    refine (Real.rpow_le_rpow (by positivity) hA1 hCF).trans_eq ?_
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hN0.le]
    ring_nf
  calc CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF ≤
      CF * (7 ^ CF * (N : ℝ) ^ (3 * CF * ε)) := mul_le_mul_of_nonneg_left h hCF
    _ = _ := by ring

/-- `F_b' = C_F (1 + A₂)^{C_F} ≤ C_F 3^{C_F} N^{2 C_F}` for `ε ≤ 1/2`. -/
private lemma taylor_Fb'_le {N : ℕ} (hN : 0 < N) {ε CF : ℝ} (hε : ε ≤ 1 / 2) (hCF : 0 ≤ CF) :
    CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF ≤ CF * 3 ^ CF * (N : ℝ) ^ (2 * CF) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hA2 : 1 + 2 * (N : ℝ) ^ (2 * ε) * N ≤ 3 * (N : ℝ) ^ (2 : ℝ) := by
    have h1 : (N : ℝ) ^ (2 * ε) ≤ (N : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    rw [Real.rpow_one] at h1
    have h2 : (N : ℝ) ^ (2 : ℝ) = N * N := by rw [Real.rpow_two]; ring
    have h3 := mul_le_mul_of_nonneg_right h1 hN0.le
    have h4 : 1 ≤ (N : ℝ) * N := one_le_mul_of_one_le_of_one_le hN1 hN1
    rw [h2]
    calc 1 + 2 * (N : ℝ) ^ (2 * ε) * N = 1 + 2 * ((N : ℝ) ^ (2 * ε) * N) := by ring
      _ ≤ 1 + 2 * ((N : ℝ) * N) := by linarith
      _ ≤ 3 * ((N : ℝ) * N) := by linarith
  have hA2pos : 0 ≤ 1 + 2 * (N : ℝ) ^ (2 * ε) * N := by positivity
  have h : (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF ≤ 3 ^ CF * (N : ℝ) ^ (2 * CF) := by
    refine (Real.rpow_le_rpow hA2pos hA2 hCF).trans_eq ?_
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hN0.le, mul_comm (2 : ℝ) CF]
  calc CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF ≤ CF * (3 ^ CF * (N : ℝ) ^ (2 * CF)) :=
      mul_le_mul_of_nonneg_left h hCF
    _ = _ := by ring

/-- `Z_c ≤ #idx 2^{2ξ+3} N^{ξ+5}` for `M ≤ 2 N^{2ε}`, `ε ≤ 1/3`. -/
private lemma taylor_Zc_le {N : ℕ} {ε : ℝ} (hN : 0 < N) (hε : 0 ≤ ε) (hε3 : ε ≤ 1 / 3)
    {e : Fin N ⊕ OffDiag N} {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) (ξ : ℕ) :
    taylor_Zc D ξ ≤ (taylor_idx ξ).card * 2 ^ (2 * ξ + 3) * (N : ℝ) ^ (ξ + 5) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hη := taylor_eta_pos N ε hN
  have hη1 : etaEdge N ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hηinv : (etaEdge N ε)⁻¹ ≤ N := by
    unfold etaEdge
    rw [← Real.rpow_neg hN0.le]
    calc (N : ℝ) ^ (-(-(2 : ℝ) / 3 - ε)) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = N := Real.rpow_one _
  have hM : D.M ≤ 2 * N := by
    have h1 : (N : ℝ) ^ (2 * ε) ≤ (N : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    rw [Real.rpow_one] at h1
    linarith [D.M_le]
  have hM0 := D.M_nonneg
  unfold taylor_Zc
  have h1 : etaEdge N ε ^ 2 ≤ 1 := pow_le_one₀ hη.le hη1
  have h2 : (etaEdge N ε)⁻¹ + 1 ≤ 2 * N := by linarith
  calc ((taylor_idx ξ).card : ℝ) * (D.M * (etaEdge N ε ^ 2 * ((N : ℝ) ^ 2 *
        (2 ^ ξ * ((etaEdge N ε)⁻¹ + 1) ^ (2 + ξ))))) ≤
      (taylor_idx ξ).card * ((2 * N) * (1 * ((N : ℝ) ^ 2 * (2 ^ ξ * (2 * N) ^ (2 + ξ))))) := by
        gcongr
    _ = (taylor_idx ξ).card * 2 ^ (2 * ξ + 3) * (N : ℝ) ^ (ξ + 5) := by
        rw [mul_pow]; ring

/-- (6.103), the main term with the cancelled orders removed:
`#τ · |n¹ - n⁰| · F_b (1 + (#idx B)²) ≤ W/4`. -/
private lemma taylor_num_N1 {N : ℕ} (hN : 0 < N) {ε φs CF Cp C1 K₀ θ w nb Fb nKB cardτ nK : ℝ}
    {ξ : ℕ} (hCF : 0 ≤ CF) (hCp : 0 < Cp) (hε : 0 < ε) (hK₀ : 0 ≤ K₀)
    (hθ : θ ≤ (1 + K₀) * (1 + Real.log N) * (N : ℝ) ^ (-φs)) (hw : 0 ≤ w)
    (hnb0 : 0 ≤ nb) (hnb : nb ≤ 2 * |C1| * (1 + Real.log N) * θ * w)
    (hFb0 : 0 ≤ Fb) (hFb : Fb ≤ CF * 7 ^ CF * (N : ℝ) ^ (3 * CF * ε))
    (hnKB : nKB ^ 2 ≤ 4 * nK ^ 2 * (N : ℝ) ^ (2 * Cp * ε))
    (hc : cardτ ≤ ((ξ : ℝ) + 1) ^ 2)
    (hE : 4 * (2 * ((ξ : ℝ) + 1) ^ 2 * |C1| * (1 + K₀) * (CF * 7 ^ CF) * (1 + 4 * nK ^ 2)) *
      (1 + Real.log N) ^ 2 ≤ (N : ℝ) ^ ε) :
    cardτ * nb * (Fb * (1 + nKB ^ 2)) ≤
      1 / 4 * (w * (N : ℝ) ^ (-φs + (3 * CF + 2 * Cp + 5) * ε)) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hrp : ∀ a b : ℝ, (N : ℝ) ^ a * (N : ℝ) ^ b = (N : ℝ) ^ (a + b) :=
    fun a b => (Real.rpow_add hN0 a b).symm
  have hNp : 1 ≤ (N : ℝ) ^ (2 * Cp * ε) := Real.one_le_rpow hN1 (by positivity)
  have h1 : 1 + nKB ^ 2 ≤ (1 + 4 * nK ^ 2) * (N : ℝ) ^ (2 * Cp * ε) := by nlinarith
  have hnb' : nb ≤ 2 * |C1| * (1 + Real.log N) * ((1 + K₀) * (1 + Real.log N) * (N : ℝ) ^ (-φs)) *
      w := by
    refine hnb.trans ?_
    have : 0 ≤ 2 * |C1| * (1 + Real.log N) := by positivity
    have := mul_le_mul_of_nonneg_left hθ this
    nlinarith
  have hcore : cardτ * nb * (Fb * (1 + nKB ^ 2)) ≤
      (2 * ((ξ : ℝ) + 1) ^ 2 * |C1| * (1 + K₀) * (CF * 7 ^ CF) * (1 + 4 * nK ^ 2) *
        (1 + Real.log N) ^ 2) * (w * ((N : ℝ) ^ (-φs) * ((N : ℝ) ^ (3 * CF * ε) *
          (N : ℝ) ^ (2 * Cp * ε)))) := by
    calc cardτ * nb * (Fb * (1 + nKB ^ 2)) ≤ ((ξ : ℝ) + 1) ^ 2 *
        (2 * |C1| * (1 + Real.log N) * ((1 + K₀) * (1 + Real.log N) * (N : ℝ) ^ (-φs)) * w) *
        (CF * 7 ^ CF * (N : ℝ) ^ (3 * CF * ε) * ((1 + 4 * nK ^ 2) * (N : ℝ) ^ (2 * Cp * ε))) := by
          gcongr
      _ = _ := by ring
  refine hcore.trans ?_
  have hX : 0 ≤ w * ((N : ℝ) ^ (-φs) * ((N : ℝ) ^ (3 * CF * ε) * (N : ℝ) ^ (2 * Cp * ε))) := by
    positivity
  calc (2 * ((ξ : ℝ) + 1) ^ 2 * |C1| * (1 + K₀) * (CF * 7 ^ CF) * (1 + 4 * nK ^ 2) *
        (1 + Real.log N) ^ 2) * (w * ((N : ℝ) ^ (-φs) * ((N : ℝ) ^ (3 * CF * ε) *
          (N : ℝ) ^ (2 * Cp * ε)))) ≤
      (1 / 4 * (N : ℝ) ^ ε) * (w * ((N : ℝ) ^ (-φs) * ((N : ℝ) ^ (3 * CF * ε) *
          (N : ℝ) ^ (2 * Cp * ε)))) := mul_le_mul_of_nonneg_right (by linarith) hX
    _ = 1 / 4 * (w * (N : ℝ) ^ (-φs + (3 * CF + 2 * Cp + 1) * ε)) := by
        rw [hrp, hrp, show (N : ℝ) ^ (-φs + (3 * CF + 2 * Cp + 1) * ε) =
          (N : ℝ) ^ ε * (N : ℝ) ^ (-φs + (3 * CF * ε + 2 * Cp * ε)) by rw [hrp]; congr 1; ring]
        ring
    _ ≤ 1 / 4 * (w * (N : ℝ) ^ (-φs + (3 * CF + 2 * Cp + 5) * ε)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)) hw) (by norm_num)

/-- (6.103), the remainder of (6.88) on the good event: `2 F_b M δ₀ (1 + 2M + #idx B) ≤ W/8`. -/
private lemma taylor_num_N3 {N : ℕ} (hN : 0 < N) {ε φs CF Cp K₀ w Fb M δ₀ nKB nK : ℝ} {ξ : ℕ}
    (hCF : 0 ≤ CF) (hCp : 0 < Cp) (hε : 0 < ε) (hK₀ : 0 ≤ K₀) (hw : (N : ℝ) ^ (-(2 : ℝ)) ≤ w)
    (hFb : Fb ≤ CF * 7 ^ CF * (N : ℝ) ^ (3 * CF * ε))
    (hM0 : 0 ≤ M) (hM : M ≤ 2 * (N : ℝ) ^ (2 * ε)) (hδ0 : 0 ≤ δ₀)
    (hδ : δ₀ ≤ 256 * (8 * ((1 + K₀) * (1 + Real.log N))) ^ (ξ + 1) *
      (N : ℝ) ^ (-(7 : ℝ) / 3 - φs))
    (hnKB0 : 0 ≤ nKB) (hnKB : nKB ≤ 2 * nK * (N : ℝ) ^ (Cp * ε))
    (hE : 8 * (1024 * (CF * 7 ^ CF) * (8 * (1 + K₀)) ^ (ξ + 1) * (5 + 2 * nK)) *
      (1 + Real.log N) ^ (ξ + 1) ≤ (N : ℝ) ^ ((1 : ℝ) / 3)) :
    2 * Fb * (M * δ₀) * (1 + 2 * M + nKB) ≤
      1 / 8 * (w * (N : ℝ) ^ (-φs + (3 * CF + 2 * Cp + 5) * ε)) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hrp : ∀ a b : ℝ, (N : ℝ) ^ a * (N : ℝ) ^ b = (N : ℝ) ^ (a + b) :=
    fun a b => (Real.rpow_add hN0 a b).symm
  have hN2 : 1 ≤ (N : ℝ) ^ (2 * ε) := Real.one_le_rpow hN1 (by positivity)
  have hNC : 1 ≤ (N : ℝ) ^ (Cp * ε) := Real.one_le_rpow hN1 (by positivity)
  have hS : 1 + 2 * M + nKB ≤ (5 + 2 * nK) * ((N : ℝ) ^ (2 * ε) * (N : ℝ) ^ (Cp * ε)) := by
    have h1 : (N : ℝ) ^ (2 * ε) ≤ (N : ℝ) ^ (2 * ε) * (N : ℝ) ^ (Cp * ε) :=
      le_mul_of_one_le_right (by positivity) hNC
    have h2 : (N : ℝ) ^ (Cp * ε) ≤ (N : ℝ) ^ (2 * ε) * (N : ℝ) ^ (Cp * ε) :=
      le_mul_of_one_le_left (by positivity) hN2
    have h3 : 1 ≤ (N : ℝ) ^ (2 * ε) * (N : ℝ) ^ (Cp * ε) := by nlinarith
    nlinarith
  set P := (8 * ((1 + K₀) * (1 + Real.log N))) ^ (ξ + 1) with hP
  have hP' : P = (8 * (1 + K₀)) ^ (ξ + 1) * (1 + Real.log N) ^ (ξ + 1) := by
    rw [hP, ← mul_pow]; ring
  have hcore : 2 * Fb * (M * δ₀) * (1 + 2 * M + nKB) ≤
      (1024 * (CF * 7 ^ CF) * (8 * (1 + K₀)) ^ (ξ + 1) * (5 + 2 * nK) *
        (1 + Real.log N) ^ (ξ + 1)) * ((N : ℝ) ^ (3 * CF * ε) * ((N : ℝ) ^ (2 * ε) *
          ((N : ℝ) ^ (-(7 : ℝ) / 3 - φs) * ((N : ℝ) ^ (2 * ε) * (N : ℝ) ^ (Cp * ε))))) := by
    calc 2 * Fb * (M * δ₀) * (1 + 2 * M + nKB) ≤
        2 * (CF * 7 ^ CF * (N : ℝ) ^ (3 * CF * ε)) *
          ((2 * (N : ℝ) ^ (2 * ε)) * (256 * P * (N : ℝ) ^ (-(7 : ℝ) / 3 - φs))) *
          ((5 + 2 * nK) * ((N : ℝ) ^ (2 * ε) * (N : ℝ) ^ (Cp * ε))) := by
          gcongr
      _ = _ := by rw [hP']; ring
  refine hcore.trans ?_
  have hX : 0 ≤ (N : ℝ) ^ (3 * CF * ε) * ((N : ℝ) ^ (2 * ε) *
      ((N : ℝ) ^ (-(7 : ℝ) / 3 - φs) * ((N : ℝ) ^ (2 * ε) * (N : ℝ) ^ (Cp * ε)))) := by positivity
  have hw0 : 0 ≤ w := le_trans (by positivity) hw
  calc (1024 * (CF * 7 ^ CF) * (8 * (1 + K₀)) ^ (ξ + 1) * (5 + 2 * nK) *
        (1 + Real.log N) ^ (ξ + 1)) * ((N : ℝ) ^ (3 * CF * ε) * ((N : ℝ) ^ (2 * ε) *
          ((N : ℝ) ^ (-(7 : ℝ) / 3 - φs) * ((N : ℝ) ^ (2 * ε) * (N : ℝ) ^ (Cp * ε))))) ≤
      (1 / 8 * (N : ℝ) ^ ((1 : ℝ) / 3)) * ((N : ℝ) ^ (3 * CF * ε) * ((N : ℝ) ^ (2 * ε) *
          ((N : ℝ) ^ (-(7 : ℝ) / 3 - φs) * ((N : ℝ) ^ (2 * ε) * (N : ℝ) ^ (Cp * ε))))) :=
        mul_le_mul_of_nonneg_right (by linarith) hX
    _ = 1 / 8 * ((N : ℝ) ^ (-(2 : ℝ)) * (N : ℝ) ^ (-φs + (3 * CF + Cp + 4) * ε)) := by
        rw [hrp, hrp, hrp, hrp, mul_assoc, hrp, hrp]; congr 2; ring
    _ ≤ 1 / 8 * (w * (N : ℝ) ^ (-φs + (3 * CF + 2 * Cp + 5) * ε)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hw
          (Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)) (by positivity) hw0)
          (by norm_num)

/-- A polynomially bounded quantity times the probability of a bad event:
`X P ≤ N^{-5/2}/16` for `X ≤ K N^a`, `P ≤ N^{-(a+4)}` and `16 K ≤ N`. -/
private lemma taylor_num_bad {N : ℕ} (hN : 0 < N) {X P K a : ℝ} (hX0 : 0 ≤ X) (hP0 : 0 ≤ P)
    (hX : X ≤ K * (N : ℝ) ^ a) (hP : P ≤ (N : ℝ) ^ (-(a + 4))) (hK : 16 * K ≤ N) :
    X * P ≤ 1 / 16 * (N : ℝ) ^ (-(5 : ℝ) / 2) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hK0 : 0 ≤ K := by
    by_contra h
    have : K * (N : ℝ) ^ a < 0 := mul_neg_of_neg_of_pos (by linarith) (by positivity)
    linarith
  calc X * P ≤ (K * (N : ℝ) ^ a) * (N : ℝ) ^ (-(a + 4)) := by gcongr
    _ = K * (N : ℝ) ^ (-(4 : ℝ)) := by rw [mul_assoc, ← Real.rpow_add hN0]; congr 2; ring
    _ ≤ (N / 16) * (N : ℝ) ^ (-(4 : ℝ)) := by gcongr; linarith
    _ = 1 / 16 * ((N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(4 : ℝ))) := by rw [Real.rpow_one]; ring
    _ = 1 / 16 * (N : ℝ) ^ (-(3 : ℝ)) := by rw [← Real.rpow_add hN0]; norm_num
    _ ≤ 1 / 16 * (N : ℝ) ^ (-(5 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num))
          (by norm_num)

/-- Crude polynomial bounds for the bad events of (6.103): with `Z_c ≤ K_Z N^{ξ+5}`,
`M δ₀ + 2M + Z_c ≤ (516 + K_Z) N^{ξ+5}`, `1 + 2M + Z_c ≤ (5 + K_Z) N^{ξ+5}`,
`2M + Z_c ≤ (4 + K_Z) N^{ξ+5}`. -/
private lemma taylor_crude {N : ℕ} {ε : ℝ} (hN : 0 < N) (hε : 0 ≤ ε) (hε3 : ε ≤ 1 / 3)
    {e : Fin N ⊕ OffDiag N} {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) (ξ : ℕ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 16 * θ ≤ 1) :
    D.M * (etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * θ) ^ (ξ + 1)) +
        (2 * D.M + taylor_Zc D ξ) ≤
      (516 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) * (N : ℝ) ^ (ξ + 5) ∧
    1 + 2 * D.M + taylor_Zc D ξ ≤ (5 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) * (N : ℝ) ^ (ξ + 5) ∧
    2 * D.M + taylor_Zc D ξ ≤ (4 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) * (N : ℝ) ^ (ξ + 5) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hη := taylor_eta_pos N ε hN
  have hη1 : etaEdge N ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hM : D.M ≤ 2 * N := by
    have h1 : (N : ℝ) ^ (2 * ε) ≤ (N : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    rw [Real.rpow_one] at h1
    linarith [D.M_le]
  have hM0 := D.M_nonneg
  have hZc := taylor_Zc_le hN hε hε3 D ξ
  have hδ : etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * θ) ^ (ξ + 1) ≤ 256 * (N : ℝ) ^ 2 := by
    have h1 : etaEdge N ε ^ 2 ≤ 1 := pow_le_one₀ hη.le hη1
    have h2 : (8 * θ) ^ (ξ + 1) ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
    calc etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * θ) ^ (ξ + 1) ≤
        1 * (N : ℝ) ^ 2 * 4 ^ 4 * 1 := by gcongr
      _ = 256 * (N : ℝ) ^ 2 := by ring
  have hp : ∀ k : ℕ, k ≤ ξ + 5 → (N : ℝ) ^ k ≤ (N : ℝ) ^ (ξ + 5) := fun k hk =>
    pow_le_pow_right₀ hN1 hk
  have h3 := hp 3 (by omega)
  have h1' := hp 1 (by omega)
  have h0 := hp 0 (by omega)
  rw [pow_one] at h1'
  rw [pow_zero] at h0
  have hδ0 : 0 ≤ etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * θ) ^ (ξ + 1) := by positivity
  have hMδ : D.M * (etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * θ) ^ (ξ + 1)) ≤
      512 * (N : ℝ) ^ 3 := by
    calc D.M * (etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * θ) ^ (ξ + 1)) ≤
        (2 * N) * (256 * (N : ℝ) ^ 2) := mul_le_mul hM hδ hδ0 (by positivity)
      _ = 512 * (N : ℝ) ^ 3 := by ring
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- `c N^{2 C_F} N^{2ξ+10} ≤ c N^{2 C_F + 2ξ + 11}`. -/
private lemma taylor_pow_combine {N : ℕ} (hN : 0 < N) {c CF : ℝ} (ξ : ℕ) (hc : 0 ≤ c) :
    c * (N : ℝ) ^ (2 * CF) * (N : ℝ) ^ (2 * ξ + 10) ≤ c * (N : ℝ) ^ (2 * CF + 2 * ξ + 11) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [mul_assoc, ← Real.rpow_natCast (N : ℝ) (2 * ξ + 10), ← Real.rpow_add hN0]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith))
    hc

/-- (6.103), the event of (5.24) fails: at most `N^{-5/2}/16`. -/
private lemma taylor_num_R2 {N : ℕ} {ε : ℝ} (hN : 0 < N) {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) {CF Kb θ PL : ℝ} {ξ : ℕ}
    (hε : 0 < ε) (hε12 : ε < 1 / 12) (hCF : 0 ≤ CF) (hθ0 : 0 ≤ θ) (hθ16 : 16 * θ ≤ 1)
    (hKb : 2 * (CF * 3 ^ CF) * (516 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) *
        (5 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) ≤ Kb)
    (hPL0 : 0 ≤ PL) (hPL : PL ≤ (N : ℝ) ^ (-(2 * CF + 2 * ξ + 11 + 4))) (hE4 : 16 * Kb ≤ N) :
    2 * (CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF) *
          (D.M * (etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * θ) ^ (ξ + 1)) +
            (2 * D.M + taylor_Zc D ξ)) * (1 + 2 * D.M + taylor_Zc D ξ) * PL ≤
      1 / 16 * (N : ℝ) ^ (-(5 : ℝ) / 2) := by
  have hM0 := D.M_nonneg
  have hη := taylor_eta_pos N ε hN
  have hZc0 : 0 ≤ taylor_Zc D ξ := (taylor_Z_nonneg D ξ 0).trans (taylor_Z_le hN D ξ 0)
  have hFb' := taylor_Fb'_le hN (ε := ε) (by linarith) hCF
  obtain ⟨hc1, hc2, -⟩ := taylor_crude hN hε.le (by linarith) D ξ hθ0 hθ16
  refine taylor_num_bad hN (by positivity) hPL0 ?_ hPL hE4
  calc 2 * (CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF) *
      (D.M * (etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * θ) ^ (ξ + 1)) +
        (2 * D.M + taylor_Zc D ξ)) * (1 + 2 * D.M + taylor_Zc D ξ) ≤
      2 * (CF * 3 ^ CF * (N : ℝ) ^ (2 * CF)) *
        ((516 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) * (N : ℝ) ^ (ξ + 5)) *
        ((5 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) * (N : ℝ) ^ (ξ + 5)) := by gcongr
    _ = (2 * (CF * 3 ^ CF) * (516 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) *
        (5 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3))) * (N : ℝ) ^ (2 * CF) *
        (N : ℝ) ^ (2 * ξ + 10) := by ring
    _ ≤ (2 * (CF * 3 ^ CF) * (516 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) *
        (5 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3))) * (N : ℝ) ^ (2 * CF + 2 * ξ + 11) :=
        taylor_pow_combine hN ξ (by positivity)
    _ ≤ Kb * (N : ℝ) ^ (2 * CF + 2 * ξ + 11) := by gcongr

/-- (6.103), the good event (6.1) fails: at most `N^{-5/2}/16`. -/
private lemma taylor_num_R3 {N : ℕ} {ε : ℝ} (hN : 0 < N) {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) {CF Kb θ PG : ℝ} {ξ : ℕ}
    (hε : 0 < ε) (hε12 : ε < 1 / 12) (hCF : 0 ≤ CF) (hθ0 : 0 ≤ θ) (hθ16 : 16 * θ ≤ 1)
    (hKb : 2 * (CF * 7 ^ CF) * (4 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) *
        (5 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) ≤ Kb)
    (hPG0 : 0 ≤ PG) (hPG : PG ≤ (N : ℝ) ^ (-(2 * CF + 2 * ξ + 11 + 4))) (hE4 : 16 * Kb ≤ N) :
    2 * (CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF) *
          (2 * D.M + taylor_Zc D ξ) * (1 + 2 * D.M + taylor_Zc D ξ) * PG ≤
      1 / 16 * (N : ℝ) ^ (-(5 : ℝ) / 2) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hM0 := D.M_nonneg
  have hZc0 : 0 ≤ taylor_Zc D ξ := (taylor_Z_nonneg D ξ 0).trans (taylor_Z_le hN D ξ 0)
  have hFb := taylor_Fb_le hN hε.le hCF
  obtain ⟨-, hc2, hc3⟩ := taylor_crude hN hε.le (by linarith) D ξ hθ0 hθ16
  have h3 : (N : ℝ) ^ (3 * CF * ε) ≤ (N : ℝ) ^ (2 * CF) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)
  have hFb2 : CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF ≤
      CF * 7 ^ CF * (N : ℝ) ^ (2 * CF) :=
    hFb.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
  refine taylor_num_bad hN (by positivity) hPG0 ?_ hPG hE4
  calc 2 * (CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF) *
      (2 * D.M + taylor_Zc D ξ) * (1 + 2 * D.M + taylor_Zc D ξ) ≤
      2 * (CF * 7 ^ CF * (N : ℝ) ^ (2 * CF)) *
        ((4 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) * (N : ℝ) ^ (ξ + 5)) *
        ((5 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) * (N : ℝ) ^ (ξ + 5)) := by gcongr
    _ = (2 * (CF * 7 ^ CF) * (4 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) *
        (5 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3))) * (N : ℝ) ^ (2 * CF) *
        (N : ℝ) ^ (2 * ξ + 10) := by ring
    _ ≤ (2 * (CF * 7 ^ CF) * (4 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) *
        (5 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3))) * (N : ℝ) ^ (2 * CF + 2 * ξ + 11) :=
        taylor_pow_combine hN ξ (by positivity)
    _ ≤ Kb * (N : ℝ) ^ (2 * CF + 2 * ξ + 11) := by gcongr

/-- (6.103), the remainder of one law: the good term is at most `W/8` and the two bad events
at most `N^{-5/2}/16` each. -/
private lemma taylor_num_R {N : ℕ} {ε : ℝ} (hN : 0 < N) {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) {φs CF Cp K₀ Kb θ B PL PG w : ℝ}
    {ξ : ℕ} (hε : 0 < ε) (hε12 : ε < 1 / 12) (hCF : 0 ≤ CF) (hCp : 0 < Cp) (hK₀ : 0 ≤ K₀)
    (hθ0 : 0 ≤ θ) (hθ16 : 16 * θ ≤ 1) (hθ : θ ≤ (1 + K₀) * (1 + Real.log N) * (N : ℝ) ^ (-φs))
    (hξ : 3 + φs ≤ (ξ + 1) * φs) (hB : B = 2 * (N : ℝ) ^ (-(1 : ℝ) / 3 + Cp * ε))
    (hw : (N : ℝ) ^ (-(2 : ℝ)) ≤ w)
    (hKb : 2 * (CF * 3 ^ CF) * (516 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) *
        (5 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) +
      2 * (CF * 7 ^ CF) * (4 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) *
        (5 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) ≤ Kb)
    (hPL0 : 0 ≤ PL) (hPL : PL ≤ (N : ℝ) ^ (-(2 * CF + 2 * ξ + 11 + 4)))
    (hPG0 : 0 ≤ PG) (hPG : PG ≤ (N : ℝ) ^ (-(2 * CF + 2 * ξ + 11 + 4)))
    (hE2 : 8 * (1024 * (CF * 7 ^ CF) * (8 * (1 + K₀)) ^ (ξ + 1) *
      (5 + 2 * ((taylor_idx ξ).card : ℝ))) * (1 + Real.log N) ^ (ξ + 1) ≤ (N : ℝ) ^ ((1 : ℝ) / 3))
    (hE4 : 16 * Kb ≤ N) :
    2 * (CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF) *
          (D.M * (etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * θ) ^ (ξ + 1))) *
          (1 + 2 * D.M + (taylor_idx ξ).card * B) +
        2 * (CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF) *
          (D.M * (etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * θ) ^ (ξ + 1)) +
            (2 * D.M + taylor_Zc D ξ)) * (1 + 2 * D.M + taylor_Zc D ξ) * PL +
        2 * (CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF) *
          (2 * D.M + taylor_Zc D ξ) * (1 + 2 * D.M + taylor_Zc D ξ) * PG ≤
      1 / 8 * (w * (N : ℝ) ^ (-φs + (3 * CF + 2 * Cp + 5) * ε)) +
        2 * (1 / 16 * (N : ℝ) ^ (-(5 : ℝ) / 2)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hη := taylor_eta_pos N ε hN
  have hnK0 : 0 ≤ ((taylor_idx ξ).card : ℝ) := Nat.cast_nonneg _
  have hδ0 : 0 ≤ etaEdge N ε ^ 2 * (N : ℝ) ^ 2 * 4 ^ 4 * (8 * θ) ^ (ξ + 1) := by positivity
  have hFb := taylor_Fb_le hN hε.le hCF
  have hFb0 : 0 ≤ CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF := by positivity
  have hδ := taylor_delta_le hN hε.le hθ0 hθ hξ
  have hnKB : ((taylor_idx ξ).card : ℝ) * B ≤
      2 * ((taylor_idx ξ).card : ℝ) * (N : ℝ) ^ (Cp * ε) := by
    rw [hB]
    have : (N : ℝ) ^ (-(1 : ℝ) / 3 + Cp * ε) ≤ (N : ℝ) ^ (Cp * ε) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    nlinarith
  have hT1 := taylor_num_N3 hN hCF hCp hε hK₀ hw hFb D.M_nonneg D.M_le hδ0 hδ
    (by rw [hB]; positivity) hnKB hE2
  have h7 : 0 ≤ 2 * (CF * 7 ^ CF) * (4 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) *
      (5 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) := by positivity
  have h3 : 0 ≤ 2 * (CF * 3 ^ CF) * (516 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) *
      (5 + (taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) := by positivity
  have hT2 := taylor_num_R2 hN D hε hε12 hCF hθ0 hθ16
    (le_trans (le_add_of_nonneg_right h7) hKb) hPL0 hPL hE4
  have hT3 := taylor_num_R3 hN D hε hε12 hCF hθ0 hθ16
    (le_trans (le_add_of_nonneg_left h3) hKb) hPG0 hPG hE4
  linarith only [hT1, hT2, hT3]

/-- `#τ = ξ^s ≤ (ξ + 1)²` for `s ≤ 2`. -/
private lemma taylor_card_tau_le (ξ : ℕ) {s : ℕ} (hs : s ∈ Finset.Icc 1 2) :
    ((Fintype.piFinset (fun _ : Fin s => Finset.Icc 1 ξ)).card : ℝ) ≤ ((ξ : ℝ) + 1) ^ 2 := by
  rw [Fintype.card_piFinset_const, Nat.card_Icc, Nat.add_sub_cancel]
  push_cast
  have h1 : (1 : ℝ) ≤ (ξ : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) ξ; linarith
  calc (ξ : ℝ) ^ s ≤ ((ξ : ℝ) + 1) ^ s := by gcongr; linarith
    _ ≤ ((ξ : ℝ) + 1) ^ 2 := pow_le_pow_right₀ h1 (Finset.mem_Icc.1 hs).2

/-- The moment-difference weight of (6.103): `2 |C1| N⁻¹ θ` or `2 |C1| log N N⁻² θ` is at most
`2 |C1| (1 + log N) θ w(e)`. -/
private lemma taylor_nbe_le {N : ℕ} (hN : 0 < N) (C1 θ : ℝ) (hθ : 0 ≤ θ) (e : Fin N ⊕ OffDiag N) :
    2 * Sum.elim (fun _ => |C1| / N * θ) (fun _ => |C1| * Real.log N / (N : ℝ) ^ 2 * θ) e ≤
      2 * |C1| * (1 + Real.log N) * θ * swapWeight N e := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  rcases e with i | p
  · simp only [Sum.elim_inl, swapWeight]
    rw [div_eq_mul_inv]
    have : 0 ≤ |C1| * θ * (N : ℝ)⁻¹ := by positivity
    nlinarith
  · simp only [Sum.elim_inr, swapWeight]
    rw [div_eq_mul_inv]
    have : 0 ≤ |C1| * θ * ((N : ℝ) ^ 2)⁻¹ := by positivity
    nlinarith

/-- (6.103), the main term off the cancelled orders on the event of (5.24) fails:
`#τ · |n¹ - n⁰| · F_b' (1 + Z_c²) P(Sᶜ) ≤ N^{-5/2}/16`. -/
private lemma taylor_num_Nb {N : ℕ} {ε : ℝ} (hN : 0 < N) {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) {CF C1 θ PL Kb cardτ nb : ℝ}
    {ξ : ℕ} (hε : 0 < ε) (hε12 : ε < 1 / 12) (hCF : 0 ≤ CF) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hc0 : 0 ≤ cardτ) (hc : cardτ ≤ ((ξ : ℝ) + 1) ^ 2) (hnb0 : 0 ≤ nb)
    (hnb : nb ≤ 2 * |C1| * (1 + Real.log N) * θ * swapWeight N e)
    (hKb : ((ξ : ℝ) + 1) ^ 2 * (2 * |C1|) * (CF * 3 ^ CF) *
      (1 + ((taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) ^ 2) ≤ Kb)
    (hPL0 : 0 ≤ PL) (hPL : PL ≤ (N : ℝ) ^ (-(2 * CF + 2 * ξ + 11 + 4))) (hE4 : 16 * Kb ≤ N) :
    cardτ * nb * (CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF * (1 + taylor_Zc D ξ ^ 2)) * PL ≤
      1 / 16 * (N : ℝ) ^ (-(5 : ℝ) / 2) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 1 + Real.log N ≤ N := by
    have := Real.log_le_sub_one_of_pos hN0; linarith
  have hFb' := taylor_Fb'_le hN (ε := ε) (by linarith) hCF
  have hZc := taylor_Zc_le hN hε.le (by linarith) D ξ
  have hZc0 : 0 ≤ taylor_Zc D ξ := (taylor_Z_nonneg D ξ 0).trans (taylor_Z_le hN D ξ 0)
  set KZ : ℝ := (taylor_idx ξ).card * 2 ^ (2 * ξ + 3) with hKZ
  have hKZ0 : 0 ≤ KZ := by positivity
  have hw1 := taylor_weight_le_one hN e
  have hw0 : 0 ≤ swapWeight N e := le_trans (by positivity) (taylor_weight_bounds2 hN e)
  have hnb' : nb ≤ 2 * |C1| * N := by
    have h1 : θ * swapWeight N e ≤ 1 := by nlinarith
    have h2 : 0 ≤ 2 * |C1| * (1 + Real.log N) := by
      have := Real.log_nonneg hN1; positivity
    calc nb ≤ 2 * |C1| * (1 + Real.log N) * (θ * swapWeight N e) := by linarith
      _ ≤ 2 * |C1| * (1 + Real.log N) * 1 := mul_le_mul_of_nonneg_left h1 h2
      _ ≤ 2 * |C1| * N := by nlinarith [abs_nonneg C1]
  have hZ2 : 1 + taylor_Zc D ξ ^ 2 ≤ (1 + KZ ^ 2) * (N : ℝ) ^ (2 * ξ + 10) := by
    have h1 : taylor_Zc D ξ ^ 2 ≤ KZ ^ 2 * (N : ℝ) ^ (2 * ξ + 10) := by
      calc taylor_Zc D ξ ^ 2 ≤ (KZ * (N : ℝ) ^ (ξ + 5)) ^ 2 := pow_le_pow_left₀ hZc0 hZc 2
        _ = KZ ^ 2 * (N : ℝ) ^ (2 * ξ + 10) := by ring
    have h2 : (1 : ℝ) ≤ (N : ℝ) ^ (2 * ξ + 10) := one_le_pow₀ hN1
    nlinarith
  refine taylor_num_bad hN (by positivity) hPL0 ?_ hPL hE4
  calc cardτ * nb * (CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF * (1 + taylor_Zc D ξ ^ 2)) ≤
      ((ξ : ℝ) + 1) ^ 2 * (2 * |C1| * N) *
        (CF * 3 ^ CF * (N : ℝ) ^ (2 * CF) * ((1 + KZ ^ 2) * (N : ℝ) ^ (2 * ξ + 10))) := by
        gcongr
    _ = (((ξ : ℝ) + 1) ^ 2 * (2 * |C1|) * (CF * 3 ^ CF) * (1 + KZ ^ 2)) *
        ((N : ℝ) ^ (2 * CF) * (N : ℝ) ^ (2 * ξ + 11)) := by ring
    _ = (((ξ : ℝ) + 1) ^ 2 * (2 * |C1|) * (CF * 3 ^ CF) * (1 + KZ ^ 2)) *
        (N : ℝ) ^ (2 * CF + 2 * ξ + 11) := by
        rw [← Real.rpow_natCast (N : ℝ) (2 * ξ + 11), ← Real.rpow_add hN0]; push_cast; ring_nf
    _ ≤ Kb * (N : ℝ) ^ (2 * CF + 2 * ξ + 11) := by gcongr

/-- Combining the three bounds of (6.103). -/
private lemma taylor_num_low_final {I₁ I₀ : ℝ} {M₁ M₀ : ℂ} {R G1 G2 W N' : ℝ}
    (h1 : ‖(I₁ : ℂ) - M₁‖ ≤ R) (h0 : ‖(I₀ : ℂ) - M₀‖ ≤ R) (hM : ‖M₁ - M₀‖ ≤ G1 + G2)
    (hR : R ≤ 1 / 8 * W + 2 * (1 / 16 * N')) (hG1 : G1 ≤ 1 / 4 * W) (hG2 : G2 ≤ 1 / 16 * N')
    (hN'0 : 0 ≤ N') (hN' : N' ≤ W) : |I₁ - I₀| ≤ W := by
  have : |I₁ - I₀| = ‖((I₁ : ℂ) - M₁) + (M₁ - M₀) - ((I₀ : ℂ) - M₀)‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sub]; congr 1; ring
  rw [this]
  calc ‖((I₁ : ℂ) - M₁) + (M₁ - M₀) - ((I₀ : ℂ) - M₀)‖ ≤
      ‖(I₁ : ℂ) - M₁‖ + ‖M₁ - M₀‖ + ‖(I₀ : ℂ) - M₀‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ W := by linarith

/-- (6.103)–(6.105), the main terms: the two laws give the same `E G_τ(Q)`, and the moments of
the swapped entry differ only beyond `matchedOrder e`. -/
private lemma taylor_main_diff {N : ℕ} (hN : 0 < N) {C1 φs ε : ℝ} {Lv Lw : EntryLaws N}
    (hv : SmallQClass C1 φs N Lv) (hw : Lv.IsMomentMatch Lw C1) {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hmp : MatchedPair C1 θ⁻¹ Lv Lw)
    (hmp1 : MatchedPair C1 θ⁻¹ (interp (lexPos N) (lexPos N e) Lv Lw) Lw) (ξ : ℕ) {B : ℝ}
    (hB : 0 < B)
    (hmom : ∀ x ∈ taylor_idx ξ, ∀ q ∈ ({2, 4} : Finset ℕ),
      ∫ ω, ‖D.Y (List.ofFn x.2) (zeroEntry e ω)‖ ^ q
        ∂(interp (lexPos N) (lexPos N e) Lv Lw).law ≤ B ^ q)
    {CF : ℝ} {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    (hFd : ∀ n ∈ Finset.Icc 1 3, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF)
    {s : ℕ} (hs : s ∈ Finset.Icc 1 2) (S : Set (Entries N))
    (hS : ∀ ω ∈ S, ∀ y : ℝ, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
      obsPoint N ε y (symOfEntries ω) ≤ (N : ℝ) ^ ε) :
    ‖∑ τ ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc 1 ξ),
        (∫ ω, taylor_G D F s τ (zeroEntry e ω) ∂(interp (lexPos N) (lexPos N e) Lv Lw).law) *
          ((interp (lexPos N) (lexPos N e) Lv Lw).entryMoment e (∑ i, τ i) : ℂ) -
      ∑ τ ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc 1 ξ),
        (∫ ω, taylor_G D F s τ (zeroEntry e ω) ∂(interp (lexPos N) (lexPos N e - 1) Lv Lw).law) *
          ((interp (lexPos N) (lexPos N e - 1) Lv Lw).entryMoment e (∑ i, τ i) : ℂ)‖ ≤
      ((Fintype.piFinset (fun _ : Fin s => Finset.Icc 1 ξ)).card : ℝ) *
        ((CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF *
            (1 + ((taylor_idx ξ).card * B) ^ 2) +
          CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF * (1 + taylor_Zc D ξ ^ 2) *
            (interp (lexPos N) (lexPos N e) Lv Lw).law.real Sᶜ) *
        (2 * Sum.elim (fun _ => |C1| / N * θ)
          (fun _ => |C1| * Real.log N / (N : ℝ) ^ 2 * θ) e)) := by
  have hCF := taylor_CF_nonneg hFd
  have hs3 : s ≤ 3 := by have := (Finset.mem_Icc.1 hs).2; omega
  have hprob1 := isProbabilityMeasure_law hmp1.isProb_v
  have hEG : ∀ τ : Fin s → ℕ, ∫ ω, taylor_G D F s τ (zeroEntry e ω)
      ∂(interp (lexPos N) (lexPos N e) Lv Lw).law =
      ∫ ω, taylor_G D F s τ (zeroEntry e ω) ∂(interp (lexPos N) (lexPos N e - 1) Lv Lw).law :=
    fun τ => integral_zeroEntry_interp hv.1.isProb hw.1 e (taylor_G D F s τ)
      (taylor_G_continuous D hF hs3 τ).measurable
  have hnbe0 : 0 ≤ 2 * Sum.elim (fun _ => |C1| / N * θ)
      (fun _ => |C1| * Real.log N / (N : ℝ) ^ 2 * θ) e := by
    have := Real.log_natCast_nonneg N
    rcases e with i | p <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> positivity
  have hmom_diff : ∀ k : ℕ, |(interp (lexPos N) (lexPos N e) Lv Lw).entryMoment e k -
      (interp (lexPos N) (lexPos N e - 1) Lv Lw).entryMoment e k| ≤
      2 * Sum.elim (fun _ => |C1| / N * θ) (fun _ => |C1| * Real.log N / (N : ℝ) ^ 2 * θ) e := by
    intro k
    have h := taylor_moment_diff hmp (inv_pos.2 hθ) (by rw [inv_inv]; exact hθ1) e k
    rw [inv_inv] at h
    refine h.trans ?_
    split_ifs
    · exact hnbe0
    · exact le_rfl
  have hGb0 : 0 ≤ CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF *
      (1 + ((taylor_idx ξ).card * B) ^ 2) + CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF *
      (1 + taylor_Zc D ξ ^ 2) * (interp (lexPos N) (lexPos N e) Lv Lw).law.real Sᶜ := by
    have := measureReal_nonneg (μ := (interp (lexPos N) (lexPos N e) Lv Lw).law) (s := Sᶜ)
    positivity
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum (g := fun _ =>
      (CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF *
      (1 + ((taylor_idx ξ).card * B) ^ 2) + CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF *
      (1 + taylor_Zc D ξ ^ 2) * (interp (lexPos N) (lexPos N e) Lv Lw).law.real Sᶜ) *
      (2 * Sum.elim (fun _ => |C1| / N * θ) (fun _ => |C1| * Real.log N / (N : ℝ) ^ 2 * θ) e))
    fun τ hτ => ?_).trans_eq (by rw [Finset.sum_const, nsmul_eq_mul])
  rw [← hEG τ, ← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul (taylor_norm_integral_G_le hN D ξ hB hmom hFd hs S hS hτ)
    (hmom_diff _) (abs_nonneg _) hGb0

/-- (6.103)–(6.105) at a fixed `N`: the numerical combination of the two expansions and the
main-term difference. -/
private lemma taylor_low_N_final {N : ℕ} {ε : ℝ} (hN : 0 < N) {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) {φs CF Cp C1 θ K₀ nK KZ Kb B PL : ℝ}
    {ξ s : ℕ} (hε : 0 < ε) (hε12 : ε < 1 / 12) (hCF : 0 ≤ CF) (hCp : 0 < Cp) (hφ : φs ≤ 1 / 2)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθ : θ ≤ (1 + K₀) * (1 + Real.log N) * (N : ℝ) ^ (-φs))
    (hK₀ : 0 ≤ K₀) (hnK : nK = ((taylor_idx ξ).card : ℝ)) (hKZ : KZ = nK * 2 ^ (2 * ξ + 3))
    (hKb : Kb = ((ξ : ℝ) + 1) ^ 2 * (2 * |C1|) * (CF * 3 ^ CF) * (1 + KZ ^ 2) +
      2 * (CF * 3 ^ CF) * (516 + KZ) * (5 + KZ) + 2 * (CF * 7 ^ CF) * (4 + KZ) * (5 + KZ))
    (hB : B = 2 * (N : ℝ) ^ (-(1 : ℝ) / 3 + Cp * ε)) (hs : s ∈ Finset.Icc 1 2)
    (hPL0 : 0 ≤ PL) (hPL : PL ≤ (N : ℝ) ^ (-(2 * CF + 2 * ξ + 11 + 4)))
    (hE1 : 4 * (2 * ((ξ : ℝ) + 1) ^ 2 * |C1| * (1 + K₀) * (CF * 7 ^ CF) *
      (1 + 4 * nK ^ 2)) * (1 + Real.log N) ^ 2 ≤ (N : ℝ) ^ ε) (hE4 : 16 * Kb ≤ N)
    {I₁ I₀ : ℝ} {M₁ M₀ : ℂ}
    (h1 : ‖(I₁ : ℂ) - M₁‖ ≤ 1 / 8 * (swapWeight N e * (N : ℝ) ^ (-φs + (3 * CF + 2 * Cp + 5) * ε)) +
      2 * (1 / 16 * (N : ℝ) ^ (-(5 : ℝ) / 2)))
    (h0 : ‖(I₀ : ℂ) - M₀‖ ≤ 1 / 8 * (swapWeight N e * (N : ℝ) ^ (-φs + (3 * CF + 2 * Cp + 5) * ε)) +
      2 * (1 / 16 * (N : ℝ) ^ (-(5 : ℝ) / 2)))
    (hmd : ‖M₁ - M₀‖ ≤ ((Fintype.piFinset (fun _ : Fin s => Finset.Icc 1 ξ)).card : ℝ) *
        ((CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF *
            (1 + ((taylor_idx ξ).card * B) ^ 2) +
          CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * N) ^ CF * (1 + taylor_Zc D ξ ^ 2) * PL) *
        (2 * Sum.elim (fun _ => |C1| / N * θ) (fun _ => |C1| * Real.log N / (N : ℝ) ^ 2 * θ) e))) :
    |I₁ - I₀| ≤ swapWeight N e * (N : ℝ) ^ (-φs + (3 * CF + 2 * Cp + 5) * ε) := by
  have hN0r : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnbe_le := taylor_nbe_le hN C1 θ hθ0 e
  have hnbe0 : 0 ≤ 2 * Sum.elim (fun _ => |C1| / N * θ)
      (fun _ => |C1| * Real.log N / (N : ℝ) ^ 2 * θ) e := by
    have := Real.log_natCast_nonneg N
    rcases e with i | p <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> positivity
  have hc := taylor_card_tau_le ξ hs
  have hFb := taylor_Fb_le hN hε.le hCF
  have hFb0 : 0 ≤ CF * (1 + 2 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ ε + 2)) ^ CF := by positivity
  have hw0 : 0 ≤ swapWeight N e := le_trans (by positivity) (taylor_weight_bounds2 hN e)
  have hnKB : (((taylor_idx ξ).card : ℝ) * B) ^ 2 ≤ 4 * nK ^ 2 * (N : ℝ) ^ (2 * Cp * ε) := by
    rw [← hnK, hB, mul_pow, mul_pow]
    have h2 : ((N : ℝ) ^ (-(1 : ℝ) / 3 + Cp * ε)) ^ 2 ≤ (N : ℝ) ^ (2 * Cp * ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0r.le]
      exact Real.rpow_le_rpow_of_exponent_le hN1r (by push_cast; linarith)
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * nK ^ 2)
    calc nK ^ 2 * (2 ^ 2 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + Cp * ε)) ^ 2) =
        4 * nK ^ 2 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + Cp * ε)) ^ 2 := by ring
      _ ≤ _ := h3
  have hG1 := taylor_num_N1 hN hCF hCp hε hK₀ hθ hw0 hnbe0 hnbe_le hFb0 hFb hnKB hc hE1
  have hKZ0 : 0 ≤ KZ := by rw [hKZ, hnK]; positivity
  have hKb1 : ((ξ : ℝ) + 1) ^ 2 * (2 * |C1|) * (CF * 3 ^ CF) *
      (1 + ((taylor_idx ξ).card * 2 ^ (2 * ξ + 3)) ^ 2) ≤ Kb := by
    rw [hKb, ← hnK, ← hKZ]
    have h1 : 0 ≤ 2 * (CF * 3 ^ CF) * (516 + KZ) * (5 + KZ) := by positivity
    have h2 : 0 ≤ 2 * (CF * 7 ^ CF) * (4 + KZ) * (5 + KZ) := by positivity
    linarith only [h1, h2]
  have hG2 := taylor_num_Nb hN D hε hε12 hCF hθ0 hθ1 (Nat.cast_nonneg _) hc hnbe0 hnbe_le
    hKb1 hPL0 hPL hE4
  have hN' : (N : ℝ) ^ (-(5 : ℝ) / 2) ≤
      swapWeight N e * (N : ℝ) ^ (-φs + (3 * CF + 2 * Cp + 5) * ε) := by
    refine (taylor_weight_bounds hN hφ e).2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN1r ?_) hw0)
    have : 0 ≤ (3 * CF + 2 * Cp + 5) * ε := by positivity
    linarith only [this, hφ]
  exact taylor_num_low_final h1 h0 (hmd.trans_eq (by ring)) le_rfl hG1 hG2 (by positivity) hN'

/-- (6.103)–(6.105) at a fixed `N`, from the inputs of `taylor_setup` and the numerical
conditions on `N`. -/
private lemma taylor_low_order_N {N : ℕ} (hN3 : 3 ≤ N) {C1 φs ε Cp C0 CF : ℝ} (hφs : 0 < φs)
    (hε : 0 < ε) (hε12 : ε < 1 / 12) (hCp : 0 < Cp) {Lv Lw : EntryLaws N}
    (hv : SmallQClass C1 φs N Lv) (hw : Lv.IsMomentMatch Lw C1) {ΩL : Set (Entries N)}
    {ξ : ℕ} (hξdef : ξ = ⌈3 / φs⌉₊) {nK K₀ KZ Kb a : ℝ}
    (hnK : nK = ((taylor_idx ξ).card : ℝ)) (hK₀ : K₀ = |(2 * C1 + 4) * C1|)
    (hKZ : KZ = nK * 2 ^ (2 * ξ + 3)) (ha : a = 2 * |CF| + 2 * ξ + 11)
    (hKb : Kb = ((ξ : ℝ) + 1) ^ 2 * (2 * |C1|) * (|CF| * 3 ^ |CF|) * (1 + KZ ^ 2) +
      2 * (|CF| * 3 ^ |CF|) * (516 + KZ) * (5 + KZ) + 2 * (|CF| * 7 ^ |CF|) * (4 + KZ) * (5 + KZ))
    (hspec : ∀ y : ℝ, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
      (⟨y, etaEdge N ε⟩ : ℂ) ∈ specDomain N C0)
    (hLL : ∀ ω ∈ ΩL, ∀ y : ℝ, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
      obsPoint N ε y (symOfEntries ω) ≤ (N : ℝ) ^ ε)
    (hlaw : ∀ γ : ℕ,
      (interp (lexPos N) γ Lv Lw).law.real (goodEvent N C0)ᶜ ≤ (N : ℝ) ^ (-(a + 4)) ∧
      (interp (lexPos N) γ Lv Lw).law.real ΩLᶜ ≤ (N : ℝ) ^ (-(a + 4)) ∧
      ∀ (e : Fin N ⊕ OffDiag N) (k : List ℕ), k.length = 2 → 1 ≤ k.sum →
        k.sum ≤ ⌈3 / φs⌉₊ → ∀ y : ℝ, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
        ∀ q ∈ ({2, 4} : Finset ℕ),
          ∫ ω, ‖opPPair e k (resR e ⟨y, etaEdge N ε⟩ ω)‖ ^ q
            ∂(interp (lexPos N) γ Lv Lw).law ≤ ((N : ℝ) ^ (1 + Cp * ε)) ^ q)
    (hE1 : 4 * (2 * ((ξ : ℝ) + 1) ^ 2 * |C1| * (1 + K₀) * (|CF| * 7 ^ |CF|) *
      (1 + 4 * nK ^ 2)) * (1 + Real.log N) ^ 2 ≤ (N : ℝ) ^ ε)
    (hE2 : 8 * (1024 * (|CF| * 7 ^ |CF|) * (8 * (1 + K₀)) ^ (ξ + 1) * (5 + 2 * nK)) *
      (1 + Real.log N) ^ (ξ + 1) ≤ (N : ℝ) ^ ((1 : ℝ) / 3))
    (hE3 : 16 * (1 + K₀) * (1 + Real.log N) ^ 1 ≤ (N : ℝ) ^ φs)
    (hE4 : 16 * Kb ≤ N)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    (hFd : ∀ n ∈ Finset.Icc 1 3, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF)
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (hX : X ∈ edgeObs N ε) (e : Fin N ⊕ OffDiag N)
    {s : ℕ} (hs : s ∈ Finset.Icc 1 2) :
    |∫ ω, iteratedDeriv s F (X (symOfEntries (zeroEntry e ω))) *
          (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) ^ s
        ∂(interp (lexPos N) (lexPos N e) Lv Lw).law -
      ∫ ω, iteratedDeriv s F (X (symOfEntries (zeroEntry e ω))) *
          (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) ^ s
        ∂(interp (lexPos N) (lexPos N e - 1) Lv Lw).law| ≤
      swapWeight N e * (N : ℝ) ^ (-φs + (3 * |CF| + 2 * Cp + 5) * ε) := by
  have hCF := taylor_CF_nonneg hFd
  rw [abs_of_nonneg hCF] at hE1 hE2 hKb ha ⊢
  have hNpos : 0 < N := by omega
  have hN0r : (0 : ℝ) < N := Nat.cast_pos.2 hNpos
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1r
  have hlogN : 1 + Real.log N ≤ N := by
    have := Real.log_le_sub_one_of_pos hN0r; linarith
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; exact abs_nonneg _
  have hnK0 : 0 ≤ nK := by rw [hnK]; exact Nat.cast_nonneg _
  have hKZ0 : 0 ≤ KZ := by rw [hKZ]; positivity
  obtain ⟨θ, hθpos, hθP, hmpγ, hmp, hvθ, hφ⟩ := taylor_swap_law hN3 hv hw
  have hθ0 := hθpos.le
  obtain ⟨D⟩ := taylor_tayObs hNpos hε.le hX e
  have hM0 := D.M_nonneg
  -- `16 θ ≤ 1`
  have hθ' : θ ≤ (1 + K₀) * (1 + Real.log N) * (N : ℝ) ^ (-φs) := by
    refine hθP.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [hK₀]; nlinarith [abs_nonneg ((2 * C1 + 4) * C1)]
  have hθ16 : 16 * θ ≤ 1 := by
    calc 16 * θ ≤ 16 * ((1 + K₀) * (1 + Real.log N) * (N : ℝ) ^ (-φs)) := by linarith
      _ = 16 * (1 + K₀) * (1 + Real.log N) ^ 1 * (N : ℝ) ^ (-φs) := by ring
      _ ≤ (N : ℝ) ^ φs * (N : ℝ) ^ (-φs) := by gcongr
      _ = 1 := by rw [← Real.rpow_add hN0r]; simp
  have hθ1 : θ ≤ 1 := by linarith
  have hξ : 3 + φs ≤ (ξ + 1) * φs := by
    have : 3 / φs ≤ ξ := hξdef ▸ Nat.le_ceil _
    rw [div_le_iff₀ hφs] at this
    nlinarith
  -- the moments of `Y_k`
  set B := 2 * (N : ℝ) ^ (-(1 : ℝ) / 3 + Cp * ε) with hBdef
  have hB : 0 < B := by positivity
  have hmom : ∀ γ : ℕ, ∀ x ∈ taylor_idx ξ, ∀ q ∈ ({2, 4} : Finset ℕ),
      ∫ ω, ‖D.Y (List.ofFn x.2) (zeroEntry e ω)‖ ^ q ∂(interp (lexPos N) γ Lv Lw).law ≤
        B ^ q := by
    intro γ x hx q hq
    obtain ⟨hk, hk1, hk2⟩ := taylor_mem_idx hx
    have hq1 : 1 ≤ q := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega
    have hprob := isProbabilityMeasure_law (hmpγ γ).isProb_v
    refine (D.moment _ hprob _ hk q hq1 _ (by positivity)
      fun y hy => (hlaw γ).2.2 e _ hk hk1 (hξdef ▸ hk2) y hy q hq).trans ?_
    have := taylor_eta_pos N ε hNpos
    exact pow_le_pow_left₀ (by positivity) (taylor_mass_rate hNpos D.M_le) q
  -- the expansion for both laws
  have hexp : ∀ γ : ℕ, ‖((∫ ω, iteratedDeriv s F (X (symOfEntries (zeroEntry e ω))) *
        (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) ^ s
          ∂(interp (lexPos N) γ Lv Lw).law : ℝ) : ℂ) -
      ∑ τ ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc 1 ξ),
        (∫ ω, taylor_G D F s τ (zeroEntry e ω) ∂(interp (lexPos N) γ Lv Lw).law) *
          ((interp (lexPos N) γ Lv Lw).entryMoment e (∑ i, τ i) : ℂ)‖ ≤
      1 / 8 * (swapWeight N e * (N : ℝ) ^ (-φs + (3 * CF + 2 * Cp + 5) * ε)) +
        2 * (1 / 16 * (N : ℝ) ^ (-(5 : ℝ) / 2)) := by
    intro γ
    have hprob := isProbabilityMeasure_law (hmpγ γ).isProb_v
    refine (taylor_low_order_expansion hNpos D (hmpγ γ).isProb_v (hmpγ γ).supp_v hθ0 hθ16
      (hvθ γ e) hspec ξ hB (hmom γ) hF hFd hs ΩL hLL).trans ?_
    have hP := hlaw γ
    rw [ha] at hP
    refine taylor_num_R hNpos D hε hε12 hCF hCp hK₀0 hθ0 hθ16 hθ' hξ rfl
      (taylor_weight_bounds2 hNpos e) ?_ measureReal_nonneg hP.2.1 measureReal_nonneg hP.1
      (by rw [← hnK]; exact hE2) hE4
    rw [hKb, ← hnK, ← hKZ]
    have : 0 ≤ ((ξ : ℝ) + 1) ^ 2 * (2 * |C1|) * (CF * 3 ^ CF) * (1 + KZ ^ 2) := by positivity
    linarith
  have hmd := taylor_main_diff hNpos hv hw D hθpos hθ1 hmp (hmpγ (lexPos N e)) ξ hB
    (hmom (lexPos N e)) hF hFd hs ΩL hLL
  have hPL := (hlaw (lexPos N e)).2.1
  rw [ha] at hPL
  exact taylor_low_N_final hNpos D hε hε12 hCF hCp hφ hθ0 hθ1 hθ' hK₀0 hnK hKZ hKb hBdef hs
    measureReal_nonneg hPL hE1 hE4 (hexp (lexPos N e)) (hexp (lexPos N e - 1)) hmd

/-- (6.103)–(6.105) for one swap: for `s = 1, 2`,
`|E_{H_γ} F^{(s)}(X_R)(X_S - X_R)^s - E_{H_{γ-1}} F^{(s)}(X_R)(X_T - X_R)^s| ≤ w(e) N^{-φs+Cε}`. -/
theorem swap_low_order_le {CF C1 φs : ℝ} (hφs : 0 < φs) :
    ∃ ε₀ > (0 : ℝ), ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ N0 : ℕ, ∀ N ≥ N0,
      ∀ (Lv Lw : EntryLaws N), SmallQClass C1 φs N Lv → Lv.IsMomentMatch Lw C1 →
      ∀ F : ℝ → ℝ, ContDiff ℝ 3 F →
        (∀ n ∈ Finset.Icc 1 3, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF) →
        ∀ X ∈ edgeObs N ε, ∀ e : Fin N ⊕ OffDiag N, ∀ s ∈ Finset.Icc 1 2,
          |∫ ω, iteratedDeriv s F (X (symOfEntries (zeroEntry e ω))) *
                (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) ^ s
              ∂(interp (lexPos N) (lexPos N e) Lv Lw).law -
            ∫ ω, iteratedDeriv s F (X (symOfEntries (zeroEntry e ω))) *
                (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) ^ s
              ∂(interp (lexPos N) (lexPos N e - 1) Lv Lw).law| ≤
            swapWeight N e * (N : ℝ) ^ (-φs + C * ε) := by
  obtain ⟨ε₀, hε₀, hε₀12, Cp, hCp, C0, ΩL, hset⟩ := taylor_setup (C1 := C1) hφs
  refine ⟨ε₀, hε₀, 3 * |CF| + 2 * Cp + 5, by positivity, fun ε hε hεε₀ => ?_⟩
  have hε12 : ε < 1 / 12 := lt_of_lt_of_le hεε₀ hε₀12
  set ξ := ⌈3 / φs⌉₊ with hξdef
  set nK : ℝ := ((taylor_idx ξ).card : ℝ) with hnK
  set K₀ := |(2 * C1 + 4) * C1| with hK₀
  set KZ : ℝ := nK * 2 ^ (2 * ξ + 3) with hKZ
  set Kb : ℝ := ((ξ : ℝ) + 1) ^ 2 * (2 * |C1|) * (|CF| * 3 ^ |CF|) * (1 + KZ ^ 2) +
    2 * (|CF| * 3 ^ |CF|) * (516 + KZ) * (5 + KZ) + 2 * (|CF| * 7 ^ |CF|) * (4 + KZ) * (5 + KZ)
    with hKb
  set a : ℝ := 2 * |CF| + 2 * ξ + 11 with ha
  obtain ⟨N1, hN1⟩ := hset ε hε hεε₀ (a + 4)
  have hev := (eventually_ge_atTop (max N1 3)).and <|
    (taylor_ev_log (4 * (2 * ((ξ : ℝ) + 1) ^ 2 * |C1| * (1 + K₀) * (|CF| * 7 ^ |CF|) *
      (1 + 4 * nK ^ 2))) 2 hε).and <|
    (taylor_ev_log (8 * (1024 * (|CF| * 7 ^ |CF|) * (8 * (1 + K₀)) ^ (ξ + 1) * (5 + 2 * nK)))
      (ξ + 1) (by norm_num : (0 : ℝ) < 1 / 3)).and <|
    (taylor_ev_log (16 * (1 + K₀)) 1 hφs).and (taylor_ev_const (16 * Kb) one_pos)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨N0, fun N hN Lv Lw hv hw F hF hFd X hX e s hs => ?_⟩
  obtain ⟨hNm, hE1, hE2, hE3, hE4⟩ := hN0 N hN
  rw [Real.rpow_one] at hE4
  obtain ⟨-, hspec, hLL, hlaw⟩ := hN1 N (le_trans (le_max_left _ _) hNm)
  exact taylor_low_order_N (le_trans (le_max_right _ _) hNm) hφs hε hε12 hCp hv hw hξdef hnK hK₀
    hKZ ha hKb hspec hLL (fun γ => hlaw Lv Lw hv hw γ) hE1 hE2 hE3 hE4 hF hFd hX e hs

/-- A continuous function of a bounded continuous observable is integrable. -/
private lemma taylor_integrable_comp {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {G : ℝ → ℝ}
    (hG : Continuous G) {g : Ω → ℝ} (hg : Continuous g) {A : ℝ} (hA : ∀ ω, |g ω| ≤ A) :
    Integrable (fun ω => G (g ω)) μ := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := -A) (b := A)).exists_bound_of_continuousOn
    hG.continuousOn
  exact taylor_integrable_of_le (hG.comp hg) (K := K) fun ω => hK _ (abs_le.1 (hA ω))

/-- The decomposition (6.85)–(6.86) of `E F(X_S)` for one law. -/
private lemma taylor_green_decomp {N : ℕ} {ε : ℝ} {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) {μ : Measure (Entries N)}
    [IsProbabilityMeasure μ] {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F) :
    ∫ ω, F (X (symOfEntries ω)) ∂μ =
      ∫ ω, F (X (symOfEntries (zeroEntry e ω))) ∂μ +
      ∫ ω, iteratedDeriv 1 F (X (symOfEntries (zeroEntry e ω))) *
        (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) ^ 1 ∂μ +
      (∫ ω, iteratedDeriv 2 F (X (symOfEntries (zeroEntry e ω))) *
        (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) ^ 2 ∂μ) / 2 +
      ∫ ω, (F (X (symOfEntries ω)) - F (X (symOfEntries (zeroEntry e ω))) -
          iteratedDeriv 1 F (X (symOfEntries (zeroEntry e ω))) *
            (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) -
          iteratedDeriv 2 F (X (symOfEntries (zeroEntry e ω))) *
            (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) ^ 2 / 2) ∂μ := by
  have hXc := D.cont_X
  have hRc : Continuous fun ω => X (symOfEntries (zeroEntry e ω)) :=
    hXc.comp (expansion_continuous_zeroEntry e)
  have hS : ∀ ω, |X (symOfEntries ω)| ≤ D.M * N := D.abs_X_le
  have hR : ∀ ω, |X (symOfEntries (zeroEntry e ω))| ≤ D.M * N := fun ω => D.abs_X_le _
  have hΔ : ∀ ω, |X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))| ≤ 2 * D.M :=
    D.abs_sub_le
  have hF0 : Continuous F := hF.continuous
  have hF1 : Continuous (iteratedDeriv 1 F) := hF.continuous_iteratedDeriv 1 (by norm_num)
  have hF2 : Continuous (iteratedDeriv 2 F) := hF.continuous_iteratedDeriv 2 (by norm_num)
  have i0 : Integrable (fun ω => F (X (symOfEntries ω))) μ := taylor_integrable_comp hF0 hXc hS
  have iR : Integrable (fun ω => F (X (symOfEntries (zeroEntry e ω)))) μ :=
    taylor_integrable_comp hF0 hRc hR
  have hprod : ∀ (G : ℝ → ℝ), Continuous G → ∀ k : ℕ,
      Integrable (fun ω => G (X (symOfEntries (zeroEntry e ω))) *
        (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) ^ k) μ := by
    intro G hG k
    obtain ⟨K, hK⟩ := (isCompact_Icc (a := -(D.M * N)) (b := D.M * N)).exists_bound_of_continuousOn
      hG.continuousOn
    refine taylor_integrable_of_le ((hG.comp hRc).mul ((hXc.sub hRc).pow k))
      (K := K * (2 * D.M) ^ k) fun ω => ?_
    rw [norm_mul, norm_pow, Real.norm_eq_abs (_ - _)]
    exact mul_le_mul (hK _ (abs_le.1 (hR ω))) (pow_le_pow_left₀ (abs_nonneg _) (hΔ ω) k)
      (by positivity) ((norm_nonneg _).trans (hK _ (abs_le.1 (hR ω))))
  have i1 := hprod _ hF1 1
  have i2 := hprod _ hF2 2
  have i2' : Integrable (fun ω => iteratedDeriv 2 F (X (symOfEntries (zeroEntry e ω))) *
      (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) ^ 2 / 2) μ := i2.div_const 2
  have i1' : Integrable (fun ω => iteratedDeriv 1 F (X (symOfEntries (zeroEntry e ω))) *
      (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω)))) μ := by
    simpa using i1
  have irem : Integrable (fun ω => F (X (symOfEntries ω)) - F (X (symOfEntries (zeroEntry e ω))) -
      iteratedDeriv 1 F (X (symOfEntries (zeroEntry e ω))) *
        (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) -
      iteratedDeriv 2 F (X (symOfEntries (zeroEntry e ω))) *
        (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) ^ 2 / 2) μ :=
    ((i0.sub iR).sub i1').sub i2'
  have iRi1 : Integrable (fun ω => F (X (symOfEntries (zeroEntry e ω))) +
      iteratedDeriv 1 F (X (symOfEntries (zeroEntry e ω))) *
        (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) ^ 1) μ := iR.add i1
  have iRi12 : Integrable (fun ω => F (X (symOfEntries (zeroEntry e ω))) +
      iteratedDeriv 1 F (X (symOfEntries (zeroEntry e ω))) *
        (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) ^ 1 +
      iteratedDeriv 2 F (X (symOfEntries (zeroEntry e ω))) *
        (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) ^ 2 / 2) μ := iRi1.add i2'
  rw [← integral_div, ← integral_add iR i1, ← integral_add iRi1 i2', ← integral_add iRi12 irem]
  congr 1
  funext ω
  ring

/-- Lemma 5.5 for one swap at a fixed `N`: the decomposition (6.85)–(6.86) and the bounds
(6.102), (6.103). -/
private lemma taylor_green_N {N : ℕ} {ε : ℝ} {Lv Lw : EntryLaws N}
    (hv : Lv.IsProb) (hw : Lw.IsProb) {e : Fin N ⊕ OffDiag N}
    {X : Matrix (Fin N) (Fin N) ℝ → ℝ} (D : TayObs N ε e X) {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    {W₁ W₂ : ℝ}
    (hlow : ∀ s ∈ Finset.Icc 1 2,
      |∫ ω, iteratedDeriv s F (X (symOfEntries (zeroEntry e ω))) *
            (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) ^ s
          ∂(interp (lexPos N) (lexPos N e) Lv Lw).law -
        ∫ ω, iteratedDeriv s F (X (symOfEntries (zeroEntry e ω))) *
            (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) ^ s
          ∂(interp (lexPos N) (lexPos N e - 1) Lv Lw).law| ≤ W₁)
    (hrem : ∀ γ ∈ ({lexPos N e, lexPos N e - 1} : Finset ℕ),
      ∫ ω, |F (X (symOfEntries ω)) - F (X (symOfEntries (zeroEntry e ω))) -
          iteratedDeriv 1 F (X (symOfEntries (zeroEntry e ω))) *
            (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) -
          iteratedDeriv 2 F (X (symOfEntries (zeroEntry e ω))) *
            (X (symOfEntries ω) - X (symOfEntries (zeroEntry e ω))) ^ 2 / 2|
        ∂(interp (lexPos N) γ Lv Lw).law ≤ W₂) :
    |∫ ω, F (X (symOfEntries ω)) ∂(interp (lexPos N) (lexPos N e) Lv Lw).law -
        ∫ ω, F (X (symOfEntries ω)) ∂(interp (lexPos N) (lexPos N e - 1) Lv Lw).law| ≤
      W₁ + W₁ / 2 + 2 * W₂ := by
  have hp1 := isProbabilityMeasure_law (interp_isProb (Φ := lexPos N) (γ := lexPos N e) hv hw)
  have hp0 := isProbabilityMeasure_law (interp_isProb (Φ := lexPos N) (γ := lexPos N e - 1) hv hw)
  rw [taylor_green_decomp D (μ := (interp (lexPos N) (lexPos N e) Lv Lw).law) hF,
    taylor_green_decomp D (μ := (interp (lexPos N) (lexPos N e - 1) Lv Lw).law) hF]
  -- `Q` has the same law under both
  have hQ : ∫ ω, F (X (symOfEntries (zeroEntry e ω))) ∂(interp (lexPos N) (lexPos N e) Lv Lw).law =
      ∫ ω, F (X (symOfEntries (zeroEntry e ω)))
        ∂(interp (lexPos N) (lexPos N e - 1) Lv Lw).law := by
    have h := integral_zeroEntry_interp hv hw e (fun ω => (F (X (symOfEntries ω)) : ℂ))
      (Complex.measurable_ofReal.comp (hF.continuous.comp D.cont_X).measurable)
    rw [integral_complex_ofReal, integral_complex_ofReal] at h
    exact_mod_cast h
  rw [hQ]
  have h1 := hlow 1 (by simp)
  have h2 := hlow 2 (by simp)
  have hr1 := abs_integral_le_integral_abs.trans (hrem (lexPos N e) (by simp))
  have hr0 := abs_integral_le_integral_abs.trans (hrem (lexPos N e - 1) (by simp))
  rw [abs_le] at h1 h2 hr1 hr0 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hr1.1, hr1.2, hr0.1, hr0.2]

/-- Lemma 5.5 for one swap, (6.85)–(6.105): for both observables,
`|E_{H_γ} F(X) - E_{H_{γ-1}} F(X)| ≤ w(e) N^{-φs+Cε}`, `γ = lexPos N e`. -/
theorem swap_green_le {CF C1 φs : ℝ} (hφs : 0 < φs) :
    ∃ ε₀ > (0 : ℝ), ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ N0 : ℕ, ∀ N ≥ N0,
      ∀ (Lv Lw : EntryLaws N), SmallQClass C1 φs N Lv → Lv.IsMomentMatch Lw C1 →
      ∀ F : ℝ → ℝ, ContDiff ℝ 3 F →
        (∀ n ∈ Finset.Icc 1 3, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF) →
        ∀ X ∈ edgeObs N ε, ∀ e : Fin N ⊕ OffDiag N,
          |∫ ω, F (X (symOfEntries ω)) ∂(interp (lexPos N) (lexPos N e) Lv Lw).law -
            ∫ ω, F (X (symOfEntries ω)) ∂(interp (lexPos N) (lexPos N e - 1) Lv Lw).law| ≤
            swapWeight N e * (N : ℝ) ^ (-φs + C * ε) := by
  obtain ⟨ε₁, hε₁, C₁, hC₁, hlow⟩ := swap_low_order_le (CF := CF) (C1 := C1) hφs
  obtain ⟨ε₂, hε₂, C₂, hC₂, hrem⟩ := swap_taylor_rem_le (CF := CF) (C1 := C1) hφs
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, max C₁ C₂ + 1, by positivity, fun ε hε hεε => ?_⟩
  obtain ⟨N1, hN1⟩ := hlow ε hε (lt_of_lt_of_le hεε (min_le_left _ _))
  obtain ⟨N2, hN2⟩ := hrem ε hε (lt_of_lt_of_le hεε (min_le_right _ _))
  obtain ⟨N3, hN3⟩ := eventually_atTop.1 (taylor_ev_const 4 hε)
  refine ⟨max (max N1 N2) (max N3 3), fun N hN Lv Lw hv hw F hF hFd X hX e => ?_⟩
  have hNm1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNm2 : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNm3 : N3 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNpos : 0 < N := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN; omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hN0r : (0 : ℝ) < N := by linarith
  obtain ⟨D⟩ := taylor_tayObs hNpos hε.le hX e
  have hw0 : 0 ≤ swapWeight N e := le_trans (by positivity) (taylor_weight_bounds2 hNpos e)
  have hmono : ∀ C' : ℝ, C' ≤ max C₁ C₂ → swapWeight N e * (N : ℝ) ^ (-φs + C' * ε) ≤
      swapWeight N e * (N : ℝ) ^ (-φs + max C₁ C₂ * ε) := fun C' hC' =>
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1r (by nlinarith)) hw0
  have h := taylor_green_N hv.1.isProb hw.1 D hF
    (W₁ := swapWeight N e * (N : ℝ) ^ (-φs + max C₁ C₂ * ε))
    (W₂ := swapWeight N e * (N : ℝ) ^ (-φs + max C₁ C₂ * ε))
    (fun s hs => (hN1 N hNm1 Lv Lw hv hw F hF hFd X hX e s hs).trans (hmono _ (le_max_left _ _)))
    (fun γ hγ => (hN2 N hNm2 Lv Lw hv hw F hF hFd X hX e γ hγ).trans
      (hmono _ (le_max_right _ _)))
  refine h.trans ?_
  have h4 : (4 : ℝ) ≤ (N : ℝ) ^ ε := hN3 N hNm3
  have hX0 : 0 ≤ swapWeight N e * (N : ℝ) ^ (-φs + max C₁ C₂ * ε) := by positivity
  have he : swapWeight N e * (N : ℝ) ^ (-φs + (max C₁ C₂ + 1) * ε) =
      (swapWeight N e * (N : ℝ) ^ (-φs + max C₁ C₂ * ε)) * (N : ℝ) ^ ε := by
    rw [mul_assoc, ← Real.rpow_add hN0r]; congr 2; ring
  rw [he]
  nlinarith

/-! ### Compiled checks

The hypotheses of the targets hold together at `N = 16`: the laws `lawV ≠ lawW` with `C1 = 2`,
`φs = 1/4`, `ε = 1/10`, `F = sin` with `C_F = 1`, and the good event (6.1) on `S(C0)`. -/

/-- `φ(16)^{C0} = 16` for `C0 = log 16 / log φ(16)`, so `S(C0) = {|E| ≤ 5, 1 < η ≤ 10}` at
`N = 16`. -/
private lemma phi16_rpow : phi 16 ^ (Real.log 16 / Real.log (phi 16)) = 16 := by
  have h16 : (1 : ℝ) < Real.log 16 := by
    have := Real.log_two_gt_d9
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; linarith
  have hphi : 1 < phi 16 := lt_of_lt_of_le h16 (by exact_mod_cast log_le_phi (N := 16) le_rfl)
  rw [Real.rpow_def_of_pos (by linarith), mul_div_cancel₀ _ (Real.log_pos hphi).ne',
    Real.exp_log (by norm_num)]

/-- The good event (6.1) and `z ∈ S(C0)` at `N = 16`: with `C0 = log 16 / log φ(16)`,
`S(C0)` is the nonempty set `{|E| ≤ 5, 1 < η ≤ 10}`, the good event is the whole space, and
`z = 2i ∈ S(C0)`. Together with a sample whose entry `e` is `1/32` (`q = 32`, `8 (s + K) = 24 ≤ q`,
`16 |v| = 1/2 ≤ 1`) this instantiates `norm_evalW_wordP_sub_expansion_le_of_good`,
`norm_evalWord_sub_expansion_le_of_good` and `norm_sq_sum_sub_expansion_le_of_good`. -/
example : ∃ C0 : ℝ, (∀ ω : Entries 16, ω ∈ goodEvent 16 C0) ∧
    (⟨0, 2⟩ : ℂ) ∈ specDomain 16 C0 ∧ (⟨0, 1 / 2⟩ : ℂ) ∉ specDomain 16 C0 ∧
    ∃ ω : Entries 16, ∃ e : Fin 16 ⊕ OffDiag 16, entryVal e ω = 1 / 32 ∧
      |entryVal e ω| ≤ (32 : ℝ)⁻¹ ∧ 8 * ((2 + 1 : ℕ) : ℝ) ≤ 32 ∧ 16 * |entryVal e ω| ≤ 1 := by
  refine ⟨Real.log 16 / Real.log (phi 16), fun ω => ?_, ?_, ?_,
    ⟨(fun _ => 0, fun _ => 1 / 32), Sum.inr ⟨(0, 1), by decide⟩, rfl, ?_, by norm_num, ?_⟩⟩
  · intro z hz i j
    have him : 1 < z.im := by
      have := hz.2.1; rw [phi16_rpow] at this; norm_num at this; exact this
    have hz0 : 0 < z.im := by linarith
    have hb : ∀ (H : Matrix (Fin 16) (Fin 16) ℝ), H.IsHermitian → ∀ i j,
        ‖resolventC H z i j‖ ≤ 2 := fun H hH i j =>
      (norm_resolventC_apply_le hH hz0 i j).trans
        (by rw [div_le_iff₀ hz0]; linarith)
    exact ⟨hb _ (symOfEntries_isHermitian _) i j,
      fun e => hb _ (symOfEntries_isHermitian _) i j⟩
  · refine ⟨by norm_num, ?_, by norm_num⟩
    show phi 16 ^ (Real.log 16 / Real.log (phi 16)) / ((16 : ℕ) : ℝ) < 2
    rw [phi16_rpow]; norm_num
  · intro h
    have := h.2.1
    change phi 16 ^ (Real.log 16 / Real.log (phi 16)) / ((16 : ℕ) : ℝ) < 1 / 2 at this
    rw [phi16_rpow] at this; norm_num at this
  · show |(1 / 32 : ℝ)| ≤ 32⁻¹; norm_num
  · show 16 * |(1 / 32 : ℝ)| ≤ 1; norm_num

/-- `F = sin`, `C_F = 1` satisfies (5.12). -/
lemma sin_regularity_cond : ContDiff ℝ 3 Real.sin ∧
    ∀ n ∈ Finset.Icc 1 3, ∀ x, |iteratedDeriv n Real.sin x| ≤ 1 * (1 + |x|) ^ (1 : ℝ) := by
  refine ⟨Real.contDiff_sin, fun n hn x => ?_⟩
  simp only [Finset.mem_Icc] at hn
  obtain ⟨h1, h3⟩ := hn
  have hx : (1 : ℝ) ≤ 1 * (1 + |x|) ^ (1 : ℝ) := by
    rw [Real.rpow_one, one_mul]; linarith [abs_nonneg x]
  have hd2 : iteratedDeriv 2 Real.sin = fun x => -Real.sin x := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, Real.deriv_sin]; exact Real.deriv_cos'
  have hd3 : iteratedDeriv 3 Real.sin = fun x => -Real.cos x := by
    rw [iteratedDeriv_succ, hd2]; funext y; simp
  interval_cases n
  · simp only [iteratedDeriv_one, Real.deriv_sin]; exact (Real.abs_cos_le_one x).trans hx
  · rw [hd2, abs_neg]; exact (Real.abs_sin_le_one x).trans hx
  · rw [hd3, abs_neg]; exact (Real.abs_cos_le_one x).trans hx

/-- The hypotheses of `abs_taylor_three_le`, `law_opPPair_gt_le`,
`integral_abs_obs_sub_pow_three_le`, `swap_taylor_rem_le`, `swap_low_order_le` and
`swap_green_le` hold together at `N = 16`, `C1 = 2`, `φs = 1/4`, `ε = 1/10`, with the D7 laws
`lawV ≠ lawW`, `F = sin`, `C_F = 1`, `k = (1, 0)`, the observable (5.14) at `E = 2` and the
observable (5.15) on the window `[2 - 16^{-2/3+ε}, 2 + 16^{-2/3+ε}]` of positive length. -/
example : SmallQClass 2 (1 / 4) 16 lawV ∧ lawV.IsMomentMatch lawW 2 ∧
    (ContDiff ℝ 3 Real.sin ∧
      ∀ n ∈ Finset.Icc 1 3, ∀ x, |iteratedDeriv n Real.sin x| ≤ 1 * (1 + |x|) ^ (1 : ℝ)) ∧
    ([1, 0] : List ℕ).length = 2 ∧ 1 ≤ ([1, 0] : List ℕ).sum ∧
    ([1, 0] : List ℕ).sum ≤ ⌈3 / (1 / 4 : ℝ)⌉₊ ∧
    obsPoint 16 (1 / 10) 2 ∈ edgeObs 16 (1 / 10) ∧
    obsInt 16 (1 / 10) (2 - (16 : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 10))
      (2 + (16 : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 10)) ∈ edgeObs 16 (1 / 10) ∧
    2 - (16 : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 10) < 2 + (16 : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 10) := by
  have hp : (0 : ℝ) < (16 : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 10) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨⟨lawV_momentCond, lawV_supp⟩, lawVW_isMomentMatch, sin_regularity_cond, rfl,
    by decide, ?_,
    Or.inl ⟨2, by simp [Real.rpow_nonneg], rfl⟩,
    Or.inr ⟨_, _, by simp; exact (abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)).le,
      by simp; exact (abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)).le, rfl⟩, by linarith⟩
  have : (3 / (1 / 4 : ℝ)) = ((12 : ℕ) : ℝ) := by norm_num
  rw [this, Nat.ceil_natCast]; decide

#print axioms abs_taylor_three_le
#print axioms norm_sq_sum_sub_expansion_le_of_good
#print axioms law_opPPair_gt_le
#print axioms sum_swapWeight_le
#print axioms integral_abs_obs_sub_pow_three_le
#print axioms swap_taylor_rem_le
#print axioms swap_low_order_le
#print axioms swap_green_le

end WEdgeNS
