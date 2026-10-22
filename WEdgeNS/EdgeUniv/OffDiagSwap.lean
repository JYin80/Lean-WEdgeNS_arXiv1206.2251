import WEdgeNS.EdgeUniv.DiagSwap
import WEdgeNS.EdgeUniv.OffDiagPartial
import WEdgeNS.EdgeUniv.ExpectationGain

/-!
# One replacement in the Claim
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

-- `((A I_e) M)_ij = A_ib M_dj + A_id M_bj`, continuity in `y`, the bounds on `Ω` and the window.
open private ode_mul_entryMat_mul_apply ode_continuous_resolventC ode_continuous_swapCoeff
  ode_window ode_weight ode_weight_sq from WEdgeNS.EdgeUniv.OffDiagExpansion
-- Continuity in the entries, `conj Σ c_s conj c_t = Σ c_t conj c_s`, and the deterministic bounds.
open private odp_continuous_swapK odp_continuous_swapKpt odp_inner_conj odp_continuous_zeroEntry
  odp_K_global odp_Kpt_global odp_offWardInt_global odp_offWard_global odp_continuous_offWard
  odp_integral_zeroEntry_interp from WEdgeNS.EdgeUniv.OffDiagPartial
open private ward_continuous_b' ward_rpow_mul_exp_le from WEdgeNS.EdgeUniv.WardReduction
-- `E f ≤ δ + M μ(T)` for `f ≤ δ` off `T` and `f ≤ M` everywhere.
open private eg_integral_le_of_event from WEdgeNS.EdgeUniv.ExpectationGain

/-! ### The split (6.77)–(6.78) of `R^{(3)}` -/

private lemma ods_pow_three_mul {N : ℕ} (A M : Matrix (Fin N) (Fin N) ℂ) :
    A ^ 3 * M = A * (A * (A * M)) := by
  simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_assoc]

/-- `((R I_e)^3 R)_ij` written out over the three intermediate indices in `{b, d}`. -/
private lemma ods_coeff3_apply {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (p : OffDiag N) (z : ℂ)
    (i j : Fin N) :
    swapCoeff H (Sum.inr p) z 3 i j =
      resolventC H z i p.1.1 * (resolventC H z p.1.2 p.1.1 *
          (resolventC H z p.1.2 p.1.1 * resolventC H z p.1.2 j +
            resolventC H z p.1.2 p.1.2 * resolventC H z p.1.1 j) +
        resolventC H z p.1.2 p.1.2 * (resolventC H z p.1.1 p.1.1 * resolventC H z p.1.2 j +
            resolventC H z p.1.1 p.1.2 * resolventC H z p.1.1 j)) +
      resolventC H z i p.1.2 * (resolventC H z p.1.1 p.1.1 *
          (resolventC H z p.1.2 p.1.1 * resolventC H z p.1.2 j +
            resolventC H z p.1.2 p.1.2 * resolventC H z p.1.1 j) +
        resolventC H z p.1.1 p.1.2 * (resolventC H z p.1.1 p.1.1 * resolventC H z p.1.2 j +
            resolventC H z p.1.1 p.1.2 * resolventC H z p.1.1 j)) := by
  unfold swapCoeff
  rw [ods_pow_three_mul]
  simp only [ode_mul_entryMat_mul_apply]

/-- One pair of [16] (6.77)–(6.81): with `R_ib, R_id, R_bj, R_dj, R_bd, R_db, R_ij` at most `P`
and `|R_bb - m|, |R_dd - m| ≤ P`, `|m| ≤ 1`, the term `((R I_e)^3 R)_ij conj R_ij` differs from
`m² (R_ib R_dj + R_id R_bj) conj R_ij` by at most `18 P⁴`. -/
private lemma ods_alg {x1 x2 y1 y2 u v s t r m : ℂ} {P : ℝ} (hP : 0 ≤ P) (hP1 : P ≤ 1)
    (hx1 : ‖x1‖ ≤ P) (hx2 : ‖x2‖ ≤ P) (hy1 : ‖y1‖ ≤ P) (hy2 : ‖y2‖ ≤ P) (hs : ‖s‖ ≤ P)
    (ht : ‖t‖ ≤ P) (hr : ‖r‖ ≤ P) (hu : ‖u - m‖ ≤ P) (hv : ‖v - m‖ ≤ P) (hm : ‖m‖ ≤ 1) :
    ‖(x1 * (t * (t * y2 + v * y1) + v * (u * y2 + s * y1)) +
        x2 * (u * (t * y2 + v * y1) + s * (u * y2 + s * y1))) * (starRingEnd ℂ) r -
      m ^ 2 * (x1 * y2 + x2 * y1) * (starRingEnd ℂ) r‖ ≤ 18 * P ^ 4 := by
  have hu2 : ‖u‖ ≤ 2 := by
    calc ‖u‖ = ‖(u - m) + m‖ := by rw [sub_add_cancel]
      _ ≤ ‖u - m‖ + ‖m‖ := norm_add_le _ _
      _ ≤ 2 := by linarith
  have hv2 : ‖v‖ ≤ 2 := by
    calc ‖v‖ = ‖(v - m) + m‖ := by rw [sub_add_cancel]
      _ ≤ ‖v - m‖ + ‖m‖ := norm_add_le _ _
      _ ≤ 2 := by linarith
  have e : (x1 * (t * (t * y2 + v * y1) + v * (u * y2 + s * y1)) +
        x2 * (u * (t * y2 + v * y1) + s * (u * y2 + s * y1))) * (starRingEnd ℂ) r -
      m ^ 2 * (x1 * y2 + x2 * y1) * (starRingEnd ℂ) r =
      (((u - m) * v + m * (v - m)) * (x1 * y2 + x2 * y1) +
        (x1 * t * t * y2 + x1 * t * v * y1 + x1 * v * s * y1 + x2 * u * t * y2 +
          x2 * s * u * y2 + x2 * s * s * y1)) * (starRingEnd ℂ) r := by ring
  rw [e, norm_mul, Complex.norm_conj]
  have hP3 : 0 ≤ P ^ 3 := pow_nonneg hP 3
  have hPP : P * P * P * P ≤ 2 * P ^ 3 := by
    have : P * P * P * P = P ^ 3 * P := by ring
    rw [this]; nlinarith
  have hP2 : P * P * 2 * P = 2 * P ^ 3 := by ring
  have hP2' : P * 2 * P * P = 2 * P ^ 3 := by ring
  have k1 : ‖x1 * t * t * y2‖ ≤ 2 * P ^ 3 := by
    rw [norm_mul, norm_mul, norm_mul]
    exact le_trans (by gcongr) hPP
  have k2 : ‖x1 * t * v * y1‖ ≤ 2 * P ^ 3 := by
    rw [norm_mul, norm_mul, norm_mul, ← hP2]; gcongr
  have k3 : ‖x1 * v * s * y1‖ ≤ 2 * P ^ 3 := by
    rw [norm_mul, norm_mul, norm_mul, ← hP2']; gcongr
  have k4 : ‖x2 * u * t * y2‖ ≤ 2 * P ^ 3 := by
    rw [norm_mul, norm_mul, norm_mul, ← hP2']; gcongr
  have k5 : ‖x2 * s * u * y2‖ ≤ 2 * P ^ 3 := by
    rw [norm_mul, norm_mul, norm_mul, ← hP2]; gcongr
  have k6 : ‖x2 * s * s * y1‖ ≤ 2 * P ^ 3 := by
    rw [norm_mul, norm_mul, norm_mul]
    exact le_trans (by gcongr) hPP
  have kA : ‖((u - m) * v + m * (v - m)) * (x1 * y2 + x2 * y1)‖ ≤ 6 * P ^ 3 := by
    rw [norm_mul]
    have h1 : ‖(u - m) * v + m * (v - m)‖ ≤ 3 * P := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have a1 : ‖u - m‖ * ‖v‖ ≤ P * 2 := by gcongr
      have a2 : ‖m‖ * ‖v - m‖ ≤ 1 * P := by gcongr
      linarith
    have h2 : ‖x1 * y2 + x2 * y1‖ ≤ 2 * P ^ 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have a1 : ‖x1‖ * ‖y2‖ ≤ P * P := by gcongr
      have a2 : ‖x2‖ * ‖y1‖ ≤ P * P := by gcongr
      nlinarith
    calc _ ≤ (3 * P) * (2 * P ^ 2) := by gcongr
      _ = 6 * P ^ 3 := by ring
  have kB : ‖x1 * t * t * y2 + x1 * t * v * y1 + x1 * v * s * y1 + x2 * u * t * y2 +
      x2 * s * u * y2 + x2 * s * s * y1‖ ≤ 12 * P ^ 3 := by
    have n1 := norm_add_le (x1 * t * t * y2 + x1 * t * v * y1 + x1 * v * s * y1 + x2 * u * t * y2 +
      x2 * s * u * y2) (x2 * s * s * y1)
    have n2 := norm_add_le (x1 * t * t * y2 + x1 * t * v * y1 + x1 * v * s * y1 + x2 * u * t * y2)
      (x2 * s * u * y2)
    have n3 := norm_add_le (x1 * t * t * y2 + x1 * t * v * y1 + x1 * v * s * y1) (x2 * u * t * y2)
    have n4 := norm_add_le (x1 * t * t * y2 + x1 * t * v * y1) (x1 * v * s * y1)
    have n5 := norm_add_le (x1 * t * t * y2) (x1 * t * v * y1)
    linarith
  have hsum := norm_add_le (((u - m) * v + m * (v - m)) * (x1 * y2 + x2 * y1))
    (x1 * t * t * y2 + x1 * t * v * y1 + x1 * v * s * y1 + x2 * u * t * y2 +
      x2 * s * u * y2 + x2 * s * s * y1)
  calc _ ≤ (18 * P ^ 3) * P := by gcongr; linarith
    _ = 18 * P ^ 4 := by ring

/-- The main term of [16] (6.77)–(6.78) for one pair, with `R_bb R_dd` replaced by `m²`:
`m² (R_ib R_dj + R_id R_bj) conj R_ij`. -/
private def odsTerm {N : ℕ} (R : Matrix (Fin N) (Fin N) ℂ) (p : OffDiag N) (m : ℂ) (i j : Fin N) :
    ℂ :=
  m ^ 2 * (R i p.1.1 * R p.1.2 j + R i p.1.2 * R p.1.1 j) * (starRingEnd ℂ) (R i j)

/-- The sum of the main terms over the pairs `i ≠ j` outside `{b, d}`. -/
private def odsSum {N : ℕ} (R : Matrix (Fin N) (Fin N) ℂ) (p : OffDiag N) (m : ℂ) : ℂ :=
  ∑ i, ∑ j, if i ≠ j ∧ swapIdx p i j = 0 then odsTerm R p m i j else 0

/-- `swapIdx p i j = 0` means that neither `i` nor `j` lies in `{b, d}`. -/
private lemma ods_swapIdx_zero {N : ℕ} {p : OffDiag N} {i j : Fin N} (h : swapIdx p i j = 0) :
    i ≠ p.1.1 ∧ i ≠ p.1.2 ∧ j ≠ p.1.1 ∧ j ≠ p.1.2 := by
  unfold swapIdx at h
  by_cases h1 : i = p.1.1 ∨ i = p.1.2
  · simp only [h1, ite_true] at h; omega
  · by_cases h2 : j = p.1.1 ∨ j = p.1.2
    · simp only [h2, ite_true] at h; omega
    · push Not at h1 h2
      exact ⟨h1.1, h1.2, h2.1, h2.2⟩

private lemma ods_swapCoeff_zero {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (e : Fin N ⊕ OffDiag N)
    (z : ℂ) : swapCoeff H e z 0 = resolventC H z := by
  simp [swapCoeff]

/-- [16] (6.77)–(6.81) summed over the pairs: if `|R_kl - δ_kl m| ≤ P ≤ 1` and `|m| ≤ 1`, then
`Σ_{i ≠ j, swapIdx = 0} ((R I_e)^3 R)_ij conj R_ij` differs from the sum of the main terms by at
most `N² · 18 P⁴`. -/
private lemma ods_sum_sub_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {z m : ℂ} {P : ℝ}
    (hP : 0 ≤ P) (hP1 : P ≤ 1) (hm : ‖m‖ ≤ 1)
    (hR : ∀ k l, ‖resolventC H z k l - (if k = l then m else 0)‖ ≤ P) (p : OffDiag N) :
    ‖(∑ i, ∑ j, if i ≠ j ∧ swapIdx p i j = 0 then
        swapCoeff H (Sum.inr p) z 3 i j * (starRingEnd ℂ) (swapCoeff H (Sum.inr p) z 0 i j)
        else 0) - odsSum (resolventC H z) p m‖ ≤ (N : ℝ) ^ 2 * (18 * P ^ 4) := by
  have hoff : ∀ k l, k ≠ l → ‖resolventC H z k l‖ ≤ P := fun k l h => by
    simpa [h] using hR k l
  have hdiag : ∀ k, ‖resolventC H z k k - m‖ ≤ P := fun k => by simpa using hR k k
  have hbd : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  have hterm : ∀ i j : Fin N, ‖(if i ≠ j ∧ swapIdx p i j = 0 then
      swapCoeff H (Sum.inr p) z 3 i j * (starRingEnd ℂ) (swapCoeff H (Sum.inr p) z 0 i j)
      else 0) - (if i ≠ j ∧ swapIdx p i j = 0 then odsTerm (resolventC H z) p m i j else 0)‖ ≤
      18 * P ^ 4 := by
    intro i j
    split_ifs with h
    · obtain ⟨hij, h0⟩ := h
      obtain ⟨hib, hid, hjb, hjd⟩ := ods_swapIdx_zero h0
      rw [ods_coeff3_apply, ods_swapCoeff_zero]
      unfold odsTerm
      exact ods_alg hP hP1 (hoff _ _ hib) (hoff _ _ hid) (hoff _ _ (Ne.symm hjb))
        (hoff _ _ (Ne.symm hjd)) (hoff _ _ hbd) (hoff _ _ (Ne.symm hbd)) (hoff _ _ hij)
        (hdiag _) (hdiag _) hm
    · simp only [sub_self, norm_zero]; positivity
  unfold odsSum
  simp_rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ i : Fin N, ∑ j : Fin N, 18 * P ^ 4 :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm i j))
    _ = (N : ℝ) ^ 2 * (18 * P ^ 4) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- `‖Σ main terms‖ ≤ N² · 2B³` when every entry of `R` is at most `B` and `|m| ≤ 1`. -/
private lemma ods_sum_global {N : ℕ} {R : Matrix (Fin N) (Fin N) ℂ} {m : ℂ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ k l, ‖R k l‖ ≤ B) (hm : ‖m‖ ≤ 1) (p : OffDiag N) :
    ‖odsSum R p m‖ ≤ (N : ℝ) ^ 2 * (2 * B ^ 3) := by
  have hterm : ∀ i j : Fin N, ‖(if i ≠ j ∧ swapIdx p i j = 0 then odsTerm R p m i j else 0)‖ ≤
      2 * B ^ 3 := by
    intro i j
    split_ifs
    · unfold odsTerm
      rw [norm_mul, norm_mul, Complex.norm_conj, norm_pow]
      have h1 : ‖R i p.1.1 * R p.1.2 j + R i p.1.2 * R p.1.1 j‖ ≤ B * B + B * B := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
        gcongr <;> exact hB _ _
      have h2 : ‖m‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hm
      calc _ ≤ 1 * (B * B + B * B) * B := by gcongr; exact hB _ _
        _ = 2 * B ^ 3 := by ring
    · simp only [norm_zero]; positivity
  unfold odsSum
  calc _ ≤ ∑ i : Fin N, ∑ j : Fin N, 2 * B ^ 3 :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm i j))
    _ = (N : ℝ) ^ 2 * (2 * B ^ 3) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The sum of the main terms is continuous in `(R, m)`. -/
private lemma ods_continuous_sum {α : Type*} [TopologicalSpace α] {N : ℕ} (p : OffDiag N)
    {R : α → Matrix (Fin N) (Fin N) ℂ} {m : α → ℂ} (hR : Continuous R) (hm : Continuous m) :
    Continuous fun a => odsSum (R a) p (m a) := by
  unfold odsSum odsTerm
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_if_const _ (fun _ => ((hm.pow 2).mul
      (((hR.matrix_elem _ _).mul (hR.matrix_elem _ _)).add
        ((hR.matrix_elem _ _).mul (hR.matrix_elem _ _)))).mul
      (Complex.continuous_conj.comp (hR.matrix_elem _ _))) fun _ => continuous_const

/-- `y ↦ m_sc(y + iη)` is continuous for `η > 0`. -/
private lemma ods_continuous_msc {η : ℝ} (hη : 0 < η) : Continuous fun y : ℝ => msc ⟨y, η⟩ := by
  have hz : Continuous fun y : ℝ => (⟨y, η⟩ : ℂ) := by
    have : (fun y : ℝ => (⟨y, η⟩ : ℂ)) = fun y : ℝ => (y : ℂ) + (η : ℂ) * Complex.I := by
      funext y; apply Complex.ext <;> simp
    rw [this]; exact Complex.continuous_ofReal.add continuous_const
  have hs : ∀ c : ℂ, c.im = 0 → Continuous fun y : ℝ => ((⟨y, η⟩ : ℂ) + c) ^ (1 / 2 : ℂ) :=
    fun c hc => continuous_iff_continuousAt.2 fun y =>
      (continuousAt_cpow_const (Complex.mem_slitPlane_iff.2 (Or.inr (by simp [hc, hη.ne'])))).comp
        (hz.add continuous_const).continuousAt
  have e : (fun y : ℝ => msc ⟨y, η⟩) = fun y : ℝ =>
      (-(⟨y, η⟩ : ℂ) + ((⟨y, η⟩ : ℂ) + (-2 : ℂ)) ^ (1 / 2 : ℂ) *
        ((⟨y, η⟩ : ℂ) + (2 : ℂ)) ^ (1 / 2 : ℂ)) / 2 := by
    funext y; unfold msc sqrtZ4; rw [sub_eq_add_neg]
  rw [e]
  exact ((hz.neg.add ((hs _ (by simp)).mul (hs _ (by simp)))).div_const 2)

/-! ### The main term in expectation: [16] (6.84)–(6.85) -/

/-- A continuous bounded function is integrable under a probability law. -/
private lemma ods_integrable {N : ℕ} {μ : Measure (Entries N)} [IsProbabilityMeasure μ]
    {f : Entries N → ℂ} (hf : Continuous f) {C : ℝ} (hC : ∀ ω, ‖f ω‖ ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.measurable.aestronglyMeasurable C (Eventually.of_forall hC)

/-- (6.85) at one point: if every `|E φ R_ib R_dj conj R_ij|` with `i, j, b, d` distinct is at most
`G` (both orders of `(b, d)`), then `|E φ Σ main terms| ≤ N² · 2G` for `|m| ≤ 1`. -/
private lemma ods_expect_sum {N : ℕ} {μ : Measure (Entries N)} [IsProbabilityMeasure μ]
    (p : OffDiag N) {φ : Entries N → ℝ} (hφ : Continuous φ) {Kφ : ℝ} (hφb : ∀ ω, |φ ω| ≤ Kφ)
    {R : Entries N → Matrix (Fin N) (Fin N) ℂ} (hR : Continuous R) {B : ℝ} (hB0 : 0 ≤ B)
    (hRb : ∀ ω k l, ‖R ω k l‖ ≤ B) {m : ℂ} (hm : ‖m‖ ≤ 1) {G : ℝ} (hG0 : 0 ≤ G)
    (hG : ∀ b d i j : Fin N, ((b = p.1.1 ∧ d = p.1.2) ∨ (b = p.1.2 ∧ d = p.1.1)) →
      i ≠ j → i ≠ b → i ≠ d → j ≠ b → j ≠ d →
      ‖∫ ω, ((φ ω : ℝ) : ℂ) * R ω i b * R ω d j * (starRingEnd ℂ) (R ω i j) ∂μ‖ ≤ G) :
    ‖∫ ω, ((φ ω : ℝ) : ℂ) * odsSum (R ω) p m ∂μ‖ ≤ (N : ℝ) ^ 2 * (2 * G) := by
  have hK0 : 0 ≤ Kφ := (abs_nonneg _).trans (hφb 0)
  have hφc : Continuous fun ω => ((φ ω : ℝ) : ℂ) := Complex.continuous_ofReal.comp hφ
  have hX : ∀ a b c d i j : Fin N, Integrable (fun ω => ((φ ω : ℝ) : ℂ) * R ω a b * R ω c d *
      (starRingEnd ℂ) (R ω i j)) μ := fun a b c d i j =>
    ods_integrable (((hφc.mul (hR.matrix_elem a b)).mul (hR.matrix_elem c d)).mul
      (Complex.continuous_conj.comp (hR.matrix_elem i j))) (C := Kφ * B * B * B) fun ω => by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
      gcongr
      exacts [hφb ω, hRb ω _ _, hRb ω _ _, hRb ω _ _]
  have hterm : ∀ i j : Fin N, Integrable (fun ω => ((φ ω : ℝ) : ℂ) *
      (if i ≠ j ∧ swapIdx p i j = 0 then odsTerm (R ω) p m i j else 0)) μ ∧
      ‖∫ ω, ((φ ω : ℝ) : ℂ) *
        (if i ≠ j ∧ swapIdx p i j = 0 then odsTerm (R ω) p m i j else 0) ∂μ‖ ≤ 2 * G := by
    intro i j
    by_cases h : i ≠ j ∧ swapIdx p i j = 0
    · simp only [eq_true h, ite_true]
      have e : (fun ω => ((φ ω : ℝ) : ℂ) * odsTerm (R ω) p m i j) = fun ω =>
          m ^ 2 * (((φ ω : ℝ) : ℂ) * R ω i p.1.1 * R ω p.1.2 j * (starRingEnd ℂ) (R ω i j)) +
          m ^ 2 * (((φ ω : ℝ) : ℂ) * R ω i p.1.2 * R ω p.1.1 j * (starRingEnd ℂ) (R ω i j)) := by
        funext ω; unfold odsTerm; ring
      rw [e]
      have i1 := (hX i p.1.1 p.1.2 j i j).const_mul (m ^ 2)
      have i2 := (hX i p.1.2 p.1.1 j i j).const_mul (m ^ 2)
      refine ⟨i1.add i2, ?_⟩
      rw [integral_add i1 i2, integral_const_mul, integral_const_mul]
      obtain ⟨hij, h0⟩ := h
      obtain ⟨hib, hid, hjb, hjd⟩ := ods_swapIdx_zero h0
      have g1 := hG p.1.1 p.1.2 i j (Or.inl ⟨rfl, rfl⟩) hij hib hid hjb hjd
      have g2 := hG p.1.2 p.1.1 i j (Or.inr ⟨rfl, rfl⟩) hij hid hib hjd hjb
      have hm2 : ‖m ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hm
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have a1 : ‖m ^ 2‖ * ‖∫ ω, ((φ ω : ℝ) : ℂ) * R ω i p.1.1 * R ω p.1.2 j *
          (starRingEnd ℂ) (R ω i j) ∂μ‖ ≤ 1 * G := by gcongr
      have a2 : ‖m ^ 2‖ * ‖∫ ω, ((φ ω : ℝ) : ℂ) * R ω i p.1.2 * R ω p.1.1 j *
          (starRingEnd ℂ) (R ω i j) ∂μ‖ ≤ 1 * G := by gcongr
      linarith
    · simp only [eq_false h, ite_false, mul_zero, integral_zero, norm_zero]
      exact ⟨integrable_zero _ _ _, by linarith⟩
  have e : (fun ω => ((φ ω : ℝ) : ℂ) * odsSum (R ω) p m) = fun ω => ∑ i, ∑ j,
      ((φ ω : ℝ) : ℂ) * (if i ≠ j ∧ swapIdx p i j = 0 then odsTerm (R ω) p m i j else 0) := by
    funext ω; unfold odsSum; simp_rw [Finset.mul_sum]
  rw [e, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hterm i j).1]
  simp_rw [integral_finsetSum _ fun j _ => (hterm _ j).1]
  calc _ ≤ ∑ i : Fin N, ∑ j : Fin N, 2 * G :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (hterm i j).2))
    _ = (N : ℝ) ^ 2 * (2 * G) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- (6.84)–(6.85) for the functional (6.56): Fubini for `E` and `∫ dy`, then (6.85) at every
`y` between `E₁` and `E₂`. -/
private lemma ods_expect_int {N : ℕ} {μ : Measure (Entries N)} [IsProbabilityMeasure μ]
    (p : OffDiag N) {φ : Entries N → ℝ} (hφ : Continuous φ) {Kφ : ℝ} (hφb : ∀ ω, |φ ω| ≤ Kφ)
    {η : ℝ} (hη : 0 < η) {R : Entries N → ℝ → Matrix (Fin N) (Fin N) ℂ}
    (hR : Continuous fun q : Entries N × ℝ => R q.1 q.2) {B : ℝ} (hB0 : 0 ≤ B)
    (hRb : ∀ ω y k l, ‖R ω y k l‖ ≤ B) {E₁ E₂ G : ℝ} (hG0 : 0 ≤ G)
    (hG : ∀ y ∈ Set.uIoc E₁ E₂, ∀ b d i j : Fin N,
      ((b = p.1.1 ∧ d = p.1.2) ∨ (b = p.1.2 ∧ d = p.1.1)) →
      i ≠ j → i ≠ b → i ≠ d → j ≠ b → j ≠ d →
      ‖∫ ω, ((φ ω : ℝ) : ℂ) * R ω y i b * R ω y d j * (starRingEnd ℂ) (R ω y i j) ∂μ‖ ≤ G) :
    ‖∫ ω, ((φ ω : ℝ) : ℂ) * ((η : ℂ) * ∫ y in E₁..E₂, odsSum (R ω y) p (msc ⟨y, η⟩)) ∂μ‖ ≤
      η * |E₂ - E₁| * ((N : ℝ) ^ 2 * (2 * G)) := by
  have hK0 : 0 ≤ Kφ := (abs_nonneg _).trans (hφb 0)
  have : IsFiniteMeasure (volume.restrict (Set.uIoc E₁ E₂)) := Real.isFiniteMeasure_restrict_Ioc _ _
  have hm := ods_continuous_msc hη
  have hmb : ∀ y : ℝ, ‖msc ⟨y, η⟩‖ ≤ 1 := fun y =>
    (norm_msc_eq_inv_and_lt_one (z := ⟨y, η⟩) hη).2.le
  set g : ℝ → Entries N → ℂ := fun y ω => ((φ ω : ℝ) : ℂ) * odsSum (R ω y) p (msc ⟨y, η⟩) with hg
  have hgc : Continuous (Function.uncurry g) := by
    have h1 : Continuous fun q : ℝ × Entries N => R q.2 q.1 := hR.comp continuous_swap
    exact (Complex.continuous_ofReal.comp (hφ.comp continuous_snd)).mul
      (ods_continuous_sum p h1 (hm.comp continuous_fst))
  have hgb : ∀ q : ℝ × Entries N, ‖Function.uncurry g q‖ ≤ Kφ * ((N : ℝ) ^ 2 * (2 * B ^ 3)) := by
    intro q
    simp only [Function.uncurry, hg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hφb _) (ods_sum_global hB0 (hRb q.2 q.1) (hmb q.1) p) (norm_nonneg _) hK0
  have hint : Integrable (Function.uncurry g) ((volume.restrict (Set.uIoc E₁ E₂)).prod μ) :=
    Integrable.of_bound hgc.measurable.aestronglyMeasurable _ (Eventually.of_forall hgb)
  have e1 : (fun ω => ((φ ω : ℝ) : ℂ) * ((η : ℂ) * ∫ y in E₁..E₂, odsSum (R ω y) p (msc ⟨y, η⟩))) =
      fun ω => (η : ℂ) * ∫ y in E₁..E₂, g y ω := by
    funext ω
    rw [hg, intervalIntegral.integral_const_mul]
    ring
  rw [e1, integral_const_mul, ← intervalIntegral_integral_swap hint, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hη, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hη.le
  rw [mul_comm]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
  exact ods_expect_sum p hφ hφb (hR.comp (continuous_id.prodMk continuous_const)) hB0
    (fun ω => hRb ω y) (hmb y) hG0 (hG y hy)

/-! ### The main terms of the two functionals -/

/-- The main part of `K^{(3,0)}_0` for the functional (6.56): `η ∫_{E₁}^{E₂} Σ main terms dy` with
`m = m_sc(y + iη)`. -/
private def odsMainInt {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (p : OffDiag N) (η E₁ E₂ : ℝ) : ℂ :=
  (η : ℂ) * ∫ y in E₁..E₂, odsSum (resolventC H ⟨y, η⟩) p (msc ⟨y, η⟩)

/-- The main part of `K^{(3,0)}_0` for the functional `η² Σ_{i ≠ j} |G_ij(z)|²`. -/
private def odsMainPt {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (p : OffDiag N) (z : ℂ) : ℂ :=
  (z.im : ℂ) ^ 2 * odsSum (resolventC H z) p (msc z)

private lemma ods_mainInt_sub_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    (p : OffDiag N) {η : ℝ} (hη : 0 < η) {E₁ E₂ P : ℝ} (hP : 0 ≤ P) (hP1 : P ≤ 1)
    (hR : ∀ y ∈ Set.uIoc E₁ E₂, ∀ k l,
      ‖resolventC H ⟨y, η⟩ k l - (if k = l then msc ⟨y, η⟩ else 0)‖ ≤ P) :
    ‖swapK H p η E₁ E₂ 0 3 0 - odsMainInt H p η E₁ E₂‖ ≤
      η * |E₂ - E₁| * ((N : ℝ) ^ 2 * (18 * P ^ 4)) := by
  have hc1 : Continuous fun y : ℝ => ∑ i, ∑ j, if i ≠ j ∧ swapIdx p i j = 0 then
      swapCoeff H (Sum.inr p) ⟨y, η⟩ 3 i j * (starRingEnd ℂ) (swapCoeff H (Sum.inr p) ⟨y, η⟩ 0 i j)
      else 0 :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_if_const _ (fun _ => (ode_continuous_swapCoeff hH hη _ 3 i j).mul
        (Complex.continuous_conj.comp (ode_continuous_swapCoeff hH hη _ 0 i j)))
        fun _ => continuous_const
  have hc2 : Continuous fun y : ℝ => odsSum (resolventC H ⟨y, η⟩) p (msc ⟨y, η⟩) :=
    ods_continuous_sum p (ode_continuous_resolventC hH hη) (ods_continuous_msc hη)
  unfold swapK odsMainInt
  rw [← mul_sub, ← intervalIntegral.integral_sub (hc1.intervalIntegrable _ _)
    (hc2.intervalIntegrable _ _), norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη,
    mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hη.le
  refine (intervalIntegral.norm_integral_le_of_norm_le_const fun y hy =>
    ods_sum_sub_le hP hP1 (norm_msc_eq_inv_and_lt_one (z := ⟨y, η⟩) hη).2.le (hR y hy) p).trans
    (le_of_eq (by ring))

private lemma ods_mainPt_sub_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (p : OffDiag N) {z : ℂ}
    {P : ℝ} (hP : 0 ≤ P) (hP1 : P ≤ 1) (hm : ‖msc z‖ ≤ 1)
    (hR : ∀ k l, ‖resolventC H z k l - (if k = l then msc z else 0)‖ ≤ P) :
    ‖swapKpt H p z 0 3 0 - odsMainPt H p z‖ ≤ z.im ^ 2 * ((N : ℝ) ^ 2 * (18 * P ^ 4)) := by
  unfold swapKpt odsMainPt
  rw [← mul_sub, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact mul_le_mul_of_nonneg_left (ods_sum_sub_le hP hP1 hm hR p) (sq_nonneg _)

private lemma ods_mainInt_global {N : ℕ} (hN : 1 ≤ N) {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (p : OffDiag N) {η : ℝ} (hη : 0 < η) (hηN : 1 / η ≤ N) {E₁ E₂ : ℝ}
    (hW : η * |E₂ - E₁| ≤ 2) : ‖odsMainInt H p η E₁ E₂‖ ≤ 32 * (N : ℝ) ^ 8 := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hi0 : 0 ≤ 1 / η := by positivity
  unfold odsMainInt
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := E₁) (b := E₂)
    (C := (N : ℝ) ^ 2 * (2 * (1 / η) ^ 3))
    (f := fun y => odsSum (resolventC H ⟨y, η⟩) p (msc ⟨y, η⟩)) fun y _ =>
      ods_sum_global hi0 (norm_resolventC_apply_le hH (z := ⟨y, η⟩) hη)
        (norm_msc_eq_inv_and_lt_one (z := ⟨y, η⟩) hη).2.le p
  have h3 : (1 / η) ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ hi0 hηN 3
  have hW0 : 0 ≤ η * |E₂ - E₁| := by positivity
  calc η * ‖_‖ ≤ η * ((N : ℝ) ^ 2 * (2 * (1 / η) ^ 3) * |E₂ - E₁|) :=
        mul_le_mul_of_nonneg_left hint hη.le
    _ = (η * |E₂ - E₁|) * (2 * (N : ℝ) ^ 2 * (1 / η) ^ 3) := by ring
    _ ≤ 2 * (2 * (N : ℝ) ^ 2 * (N : ℝ) ^ 3) :=
        mul_le_mul hW (by gcongr) (by positivity) (by norm_num)
    _ ≤ 32 * (N : ℝ) ^ 8 := by
        have : (N : ℝ) ^ 5 ≤ (N : ℝ) ^ 8 := pow_le_pow_right₀ hn1 (by norm_num)
        nlinarith

private lemma ods_mainPt_global {N : ℕ} (hN : 1 ≤ N) {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (p : OffDiag N) {z : ℂ} (hz : 0 < z.im) (hηN : 1 / z.im ≤ N) :
    ‖odsMainPt H p z‖ ≤ 32 * (N : ℝ) ^ 8 := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hi0 : 0 ≤ 1 / z.im := by positivity
  unfold odsMainPt
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h := ods_sum_global hi0 (norm_resolventC_apply_le hH hz)
    (norm_msc_eq_inv_and_lt_one hz).2.le p
  have e : z.im ^ 2 * ((N : ℝ) ^ 2 * (2 * (1 / z.im) ^ 3)) = 2 * (N : ℝ) ^ 2 * (1 / z.im) := by
    field_simp
  calc _ ≤ z.im ^ 2 * ((N : ℝ) ^ 2 * (2 * (1 / z.im) ^ 3)) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = 2 * (N : ℝ) ^ 2 * (1 / z.im) := e
    _ ≤ 2 * (N : ℝ) ^ 2 * N := mul_le_mul_of_nonneg_left hηN (by positivity)
    _ ≤ 32 * (N : ℝ) ^ 8 := by
        have : (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 8 := pow_le_pow_right₀ hn1 (by norm_num)
        nlinarith

private lemma ods_continuous_mainInt {N : ℕ} (p : OffDiag N) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) :
    Continuous fun ω : Entries N => odsMainInt (symOfEntries ω) p η E₁ E₂ := by
  have hR : Continuous fun q : Entries N × ℝ => resolventC (symOfEntries q.1) ⟨q.2, η⟩ :=
    continuous_matrix fun i j => continuous_resolventC_symOfEntries_prod hη i j
  have h := ods_continuous_sum p hR ((ods_continuous_msc hη).comp continuous_snd)
  exact continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun ω y => odsSum (resolventC (symOfEntries ω) ⟨y, η⟩) p (msc ⟨y, η⟩)) h E₁ E₂)

private lemma ods_continuous_mainPt {N : ℕ} (p : OffDiag N) {z : ℂ} (hz : 0 < z.im) :
    Continuous fun ω : Entries N => odsMainPt (symOfEntries ω) p z :=
  continuous_const.mul (ods_continuous_sum p
    (continuous_matrix fun i j => continuous_resolventC_symOfEntries hz.ne' i j) continuous_const)

/-- `(ω, y) ↦ G(Q)(y + iη)` is jointly continuous, `Q` the matrix with the entry `e` set to zero. -/
private lemma ods_continuous_resolventC_zeroEntry {N : ℕ} (e : Fin N ⊕ OffDiag N) {η : ℝ}
    (hη : 0 < η) :
    Continuous fun q : Entries N × ℝ => resolventC (symOfEntries (zeroEntry e q.1)) ⟨q.2, η⟩ := by
  have h1 : Continuous fun q : Entries N × ℝ => resolventC (symOfEntries q.1) ⟨q.2, η⟩ :=
    continuous_matrix fun i j => continuous_resolventC_symOfEntries_prod hη i j
  have h2 : Continuous fun q : Entries N × ℝ => (zeroEntry e q.1, q.2) :=
    ((odp_continuous_zeroEntry e).comp continuous_fst).prodMk continuous_snd
  have h3 := h1.comp h2
  exact h3

/-! ### `K^{(0,3)}_0 = conj K^{(3,0)}_0` -/

private lemma ods_intervalIntegral_conj (f : ℝ → ℂ) (a b : ℝ) :
    ∫ y in a..b, (starRingEnd ℂ) (f y) = (starRingEnd ℂ) (∫ y in a..b, f y) := by
  simp only [intervalIntegral, integral_conj, map_sub]

private lemma ods_swapK_conj {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (p : OffDiag N)
    (η E₁ E₂ : ℝ) :
    swapK H p η E₁ E₂ 0 0 3 = (starRingEnd ℂ) (swapK H p η E₁ E₂ 0 3 0) := by
  unfold swapK
  rw [map_mul, Complex.conj_ofReal, ← ods_intervalIntegral_conj]
  congr 1
  exact intervalIntegral.integral_congr fun y _ => (odp_inner_conj H p _ 0 3 0).symm

private lemma ods_swapKpt_conj {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (p : OffDiag N) (z : ℂ) :
    swapKpt H p z 0 0 3 = (starRingEnd ℂ) (swapKpt H p z 0 3 0) := by
  unfold swapKpt
  rw [map_mul, map_pow, Complex.conj_ofReal, odp_inner_conj]

/-! ### `E g₃(Q)` for one law -/

/-- `|E Re φ (K + conj K)| ≤ 2 (A₁ + B A₂ + K_φ 2M P(Ωᶜ))` when `|E φ Mn| ≤ A₁`, and on `Ω`
`|K - Mn| ≤ A₂`, `|φ| ≤ B`, while `|φ| ≤ K_φ` and `|K|, |Mn| ≤ M` everywhere. -/
private lemma ods_perLaw {N : ℕ} {μ : Measure (Entries N)} [IsProbabilityMeasure μ]
    {φ : Entries N → ℝ} (hφ : Continuous φ) {K Mn : Entries N → ℂ} (hK : Continuous K)
    (hMn : Continuous Mn) {Ω : Set (Entries N)} {A₁ A₂ Bx KF Mg : ℝ} (hA₂ : 0 ≤ A₂)
    (hBx : 0 ≤ Bx) (hmain : ‖∫ ω, ((φ ω : ℝ) : ℂ) * Mn ω ∂μ‖ ≤ A₁)
    (hgood : ∀ ω ∈ Ω, ‖K ω - Mn ω‖ ≤ A₂ ∧ |φ ω| ≤ Bx)
    (hφg : ∀ ω, |φ ω| ≤ KF) (hKg : ∀ ω, ‖K ω‖ ≤ Mg) (hMg : ∀ ω, ‖Mn ω‖ ≤ Mg) :
    |∫ ω, (((φ ω : ℝ) : ℂ) * (K ω + (starRingEnd ℂ) (K ω))).re ∂μ| ≤
      2 * (A₁ + Bx * A₂ + KF * (2 * Mg) * (μ Ωᶜ).toReal) := by
  have hKF0 : 0 ≤ KF := (abs_nonneg _).trans (hφg 0)
  have hφc : Continuous fun ω => ((φ ω : ℝ) : ℂ) := Complex.continuous_ofReal.comp hφ
  have hφn : ∀ ω, ‖((φ ω : ℝ) : ℂ)‖ ≤ KF := fun ω => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hφg ω
  have hDg : ∀ ω, ‖K ω - Mn ω‖ ≤ 2 * Mg := fun ω =>
    (norm_sub_le _ _).trans (by linarith [hKg ω, hMg ω])
  have iK : Integrable (fun ω => ((φ ω : ℝ) : ℂ) * K ω) μ :=
    ods_integrable (hφc.mul hK) (C := KF * Mg) fun ω => by
      rw [norm_mul]; exact mul_le_mul (hφn ω) (hKg ω) (norm_nonneg _) hKF0
  have iM : Integrable (fun ω => ((φ ω : ℝ) : ℂ) * Mn ω) μ :=
    ods_integrable (hφc.mul hMn) (C := KF * Mg) fun ω => by
      rw [norm_mul]; exact mul_le_mul (hφn ω) (hMg ω) (norm_nonneg _) hKF0
  have iD : Integrable (fun ω => ((φ ω : ℝ) : ℂ) * (K ω - Mn ω)) μ :=
    ods_integrable (hφc.mul (hK.sub hMn)) (C := KF * (2 * Mg)) fun ω => by
      rw [norm_mul]; exact mul_le_mul (hφn ω) (hDg ω) (norm_nonneg _) hKF0
  have e1 : ∀ ω, (((φ ω : ℝ) : ℂ) * (K ω + (starRingEnd ℂ) (K ω))).re =
      2 * (((φ ω : ℝ) : ℂ) * K ω).re := by
    intro ω; simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  simp_rw [e1]
  have hre := integral_re (𝕜 := ℂ) iK
  simp only [RCLike.re_to_complex] at hre
  rw [integral_const_mul, hre, abs_mul, abs_two]
  refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) (by norm_num)
  have e2 : (fun ω => ((φ ω : ℝ) : ℂ) * K ω) = fun ω =>
      ((φ ω : ℝ) : ℂ) * Mn ω + ((φ ω : ℝ) : ℂ) * (K ω - Mn ω) := by funext ω; ring
  rw [e2, integral_add iM iD]
  refine (norm_add_le _ _).trans ?_
  have hD : ‖∫ ω, ((φ ω : ℝ) : ℂ) * (K ω - Mn ω) ∂μ‖ ≤
      Bx * A₂ + KF * (2 * Mg) * (μ Ωᶜ).toReal := by
    refine (norm_integral_le_integral_norm _).trans ?_
    refine eg_integral_le_of_event iD.norm (T := Ωᶜ) (by positivity) (fun ω hω => ?_)
      (fun ω => ?_)
    · obtain ⟨h1, h2⟩ := hgood ω (not_not.1 hω)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul h2 h1 (norm_nonneg _) hBx
    · rw [norm_mul]; exact mul_le_mul (hφn ω) (hDg ω) (norm_nonneg _) hKF0
  linarith

/-! ### Sizes on `Ω` and the bookkeeping of the powers of `N` -/

private lemma ods_offsum_le {N : ℕ} {R : Matrix (Fin N) (Fin N) ℂ} {P : ℝ}
    (hR : ∀ k l, k ≠ l → ‖R k l‖ ≤ P) :
    |∑ i, ∑ j, if i = j then (0 : ℝ) else ‖R i j‖ ^ 2| ≤ (N : ℝ) ^ 2 * P ^ 2 := by
  rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
    split_ifs <;> positivity)]
  calc _ ≤ ∑ _i : Fin N, ∑ _j : Fin N, P ^ 2 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        split_ifs with h
        · positivity
        · exact pow_le_pow_left₀ (norm_nonneg _) (hR i j h) 2
    _ = (N : ℝ) ^ 2 * P ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- `|x_R| ≤ η |E₂ - E₁| N² P²` for the functional (6.56) when the off-diagonal entries are at
most `P`. -/
private lemma ods_offWardInt_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {η : ℝ} (hη : 0 < η)
    {E₁ E₂ P : ℝ} (hR : ∀ y ∈ Set.uIoc E₁ E₂, ∀ k l, k ≠ l → ‖resolventC H ⟨y, η⟩ k l‖ ≤ P) :
    |offWardInt H η E₁ E₂| ≤ η * |E₂ - E₁| * ((N : ℝ) ^ 2 * P ^ 2) := by
  unfold offWardInt
  rw [abs_mul, abs_of_pos hη, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hη.le
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := E₁) (b := E₂)
    (C := (N : ℝ) ^ 2 * P ^ 2)
    (f := fun y => ∑ i, ∑ j, if i = j then (0 : ℝ) else ‖resolventC H ⟨y, η⟩ i j‖ ^ 2)
    fun y hy => by rw [Real.norm_eq_abs]; exact ods_offsum_le (hR y hy)
  rw [Real.norm_eq_abs] at h
  linarith

/-- `|x_R| ≤ η² N² P²` for the functional `η² Σ_{i ≠ j} |G_ij(z)|²`. -/
private lemma ods_offWard_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ} {P : ℝ}
    (hR : ∀ k l, k ≠ l → ‖resolventC H z k l‖ ≤ P) :
    |offWard H z| ≤ z.im ^ 2 * ((N : ℝ) ^ 2 * P ^ 2) := by
  unfold offWard
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left (ods_offsum_le hR) (sq_nonneg _)

/-- The bad event is beaten by `exp(-c φ)`: `K_F · 64 N⁸ · P(Ωᶜ) ≤ N^{-2/3}` with
`K_F = CF (1 + 32 N⁸)^CF`. -/
private lemma ods_bad {CF c : ℝ} {Cb : ℕ} (hCF : 0 ≤ CF) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ pr : ℝ, 0 ≤ pr → pr ≤ (N : ℝ) ^ Cb * Real.exp (-c * phi N) →
      CF * (1 + 32 * (N : ℝ) ^ 8) ^ CF * (2 * (32 * (N : ℝ) ^ 8)) * pr ≤
        (N : ℝ) ^ (-(2 : ℝ) / 3) := by
  filter_upwards [ward_rpow_mul_exp_le c (9 * CF + 17 + Cb) hc, eventually_ge_atTop 33,
    eventually_ge_atTop ⌈CF⌉₊] with N hexp h33 hCFN pr hpr0 hpr
  have hx : (33 : ℝ) ≤ N := by exact_mod_cast h33
  have hn0 : (0 : ℝ) < N := by linarith
  have hn1 : (1 : ℝ) ≤ N := by linarith
  have hCFle : CF ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hCFN)
  have h8 : (1 : ℝ) ≤ (N : ℝ) ^ 8 := one_le_pow₀ hn1
  have h9 : 1 + 32 * (N : ℝ) ^ 8 ≤ (N : ℝ) ^ 9 := by
    have : (N : ℝ) ^ 9 = N * (N : ℝ) ^ 8 := by ring
    nlinarith
  have hrp : (1 + 32 * (N : ℝ) ^ 8) ^ CF ≤ (N : ℝ) ^ (9 * CF) := by
    calc (1 + 32 * (N : ℝ) ^ 8) ^ CF ≤ ((N : ℝ) ^ 9) ^ CF :=
          Real.rpow_le_rpow (by positivity) h9 hCF
      _ = (N : ℝ) ^ (9 * CF) := by
          rw [← Real.rpow_natCast (N : ℝ) 9, ← Real.rpow_mul hn0.le]; norm_num
  have h64 : 2 * (32 * (N : ℝ) ^ 8) ≤ (N : ℝ) ^ 14 := by
    have : (64 : ℝ) ≤ (N : ℝ) ^ 6 := by
      calc (64 : ℝ) = 2 ^ 6 := by norm_num
        _ ≤ (N : ℝ) ^ 6 := pow_le_pow_left₀ (by norm_num) (by linarith) 6
    have e : (N : ℝ) ^ 14 = (N : ℝ) ^ 6 * (N : ℝ) ^ 8 := by ring
    rw [e]; nlinarith
  set e := Real.exp (-c * phi N) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hKF : CF * (1 + 32 * (N : ℝ) ^ 8) ^ CF * (2 * (32 * (N : ℝ) ^ 8)) ≤
      (N : ℝ) * (N : ℝ) ^ (9 * CF) * (N : ℝ) ^ 14 := by
    gcongr
  have hpow : (N : ℝ) * (N : ℝ) ^ (9 * CF) * (N : ℝ) ^ 14 * ((N : ℝ) ^ Cb * e) =
      (N : ℝ) ^ (-(2 : ℝ)) * ((N : ℝ) ^ (9 * CF + 17 + Cb) * e) := by
    have e1 : (N : ℝ) * (N : ℝ) ^ (9 * CF) * (N : ℝ) ^ 14 * (N : ℝ) ^ Cb =
        (N : ℝ) ^ (-(2 : ℝ)) * (N : ℝ) ^ (9 * CF + 17 + Cb) := by
      have a1 : (N : ℝ) * (N : ℝ) ^ (9 * CF) * (N : ℝ) ^ 14 * (N : ℝ) ^ Cb =
          (N : ℝ) ^ ((1 : ℝ) + 9 * CF + ((14 : ℕ) : ℝ) + (Cb : ℝ)) := by
        rw [Real.rpow_add hn0, Real.rpow_add hn0, Real.rpow_add hn0, Real.rpow_one,
          Real.rpow_natCast, Real.rpow_natCast]
      rw [a1, ← Real.rpow_add hn0]
      congr 1
      push_cast
      ring
    calc _ = (N : ℝ) * (N : ℝ) ^ (9 * CF) * (N : ℝ) ^ 14 * (N : ℝ) ^ Cb * e := by ring
      _ = _ := by rw [e1]; ring
  have hm2 : (N : ℝ) ^ (-(2 : ℝ)) ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hp0 : 0 ≤ (N : ℝ) ^ (-(2 : ℝ)) := (Real.rpow_pos_of_pos hn0 _).le
  calc _ ≤ (N : ℝ) * (N : ℝ) ^ (9 * CF) * (N : ℝ) ^ 14 * pr :=
        mul_le_mul_of_nonneg_right hKF hpr0
    _ ≤ (N : ℝ) * (N : ℝ) ^ (9 * CF) * (N : ℝ) ^ 14 * ((N : ℝ) ^ Cb * e) :=
        mul_le_mul_of_nonneg_left hpr (by positivity)
    _ = _ := hpow
    _ ≤ (N : ℝ) ^ (-(2 : ℝ)) * 1 := mul_le_mul_of_nonneg_left hexp hp0
    _ ≤ _ := by rw [mul_one]; exact hm2

/-- The bookkeeping of [16] (6.84)–(6.85): with `W ≤ 2 N^{-4/3}`, `G = N^{-4/3+C_G ε}`,
`P = N^{-1/3+3ε}`, `|F′| ≤ N^{(7CF+1)ε}` and `N^ε ≥ 2`,
`2 (W N² 2G + N^{(7CF+1)ε} W N² 18 P⁴ + T) ≤ N^{-2/3+(C_G+7CF+20)ε}` once `T ≤ N^{-2/3}`. -/
private lemma ods_arith {N : ℕ} (hN : 1 ≤ N) {ε CG CF W T : ℝ} (hε : 0 < ε) (hCG : 0 ≤ CG)
    (hCF : 0 ≤ CF) (ht : 2 ≤ (N : ℝ) ^ ε) (hW : W ≤ 2 * (N : ℝ) ^ (-(4 : ℝ) / 3))
    (hT : T ≤ (N : ℝ) ^ (-(2 : ℝ) / 3)) :
    2 * (W * ((N : ℝ) ^ 2 * (2 * (N : ℝ) ^ (-(4 : ℝ) / 3 + CG * ε))) +
        (N : ℝ) ^ ((7 * CF + 1) * ε) *
          (W * ((N : ℝ) ^ 2 * (18 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 4))) + T) ≤
      (N : ℝ) ^ (-(2 : ℝ) / 3 + (CG + 7 * CF + 20) * ε) := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hN2 : (N : ℝ) ^ 2 = (N : ℝ) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
  set Y := (N : ℝ) ^ (-(2 : ℝ) / 3 + (CG + 7 * CF + 13) * ε) with hY
  have e1 : (N : ℝ) ^ (-(4 : ℝ) / 3) * (N : ℝ) ^ 2 * (N : ℝ) ^ (-(4 : ℝ) / 3 + CG * ε) =
      (N : ℝ) ^ (-(2 : ℝ) / 3 + CG * ε) := by
    rw [hN2, ← Real.rpow_add hn0, ← Real.rpow_add hn0]; congr 1; ring
  have e2 : (N : ℝ) ^ ((7 * CF + 1) * ε) * (N : ℝ) ^ (-(4 : ℝ) / 3) * (N : ℝ) ^ 2 *
      ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 4 = (N : ℝ) ^ (-(2 : ℝ) / 3 + (7 * CF + 13) * ε) := by
    rw [hN2, ← Real.rpow_natCast ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) 4, ← Real.rpow_mul hn0.le,
      ← Real.rpow_add hn0, ← Real.rpow_add hn0, ← Real.rpow_add hn0]
    congr 1; push_cast; ring
  have m1 : (N : ℝ) ^ (-(2 : ℝ) / 3 + CG * ε) ≤ Y :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith)
  have m2 : (N : ℝ) ^ (-(2 : ℝ) / 3 + (7 * CF + 13) * ε) ≤ Y :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith)
  have m0 : (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ Y :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith)
  have t1 : W * ((N : ℝ) ^ 2 * (2 * (N : ℝ) ^ (-(4 : ℝ) / 3 + CG * ε))) ≤ 4 * Y := by
    calc _ ≤ (2 * (N : ℝ) ^ (-(4 : ℝ) / 3)) *
          ((N : ℝ) ^ 2 * (2 * (N : ℝ) ^ (-(4 : ℝ) / 3 + CG * ε))) :=
          mul_le_mul_of_nonneg_right hW (by positivity)
      _ = 4 * ((N : ℝ) ^ (-(4 : ℝ) / 3) * (N : ℝ) ^ 2 * (N : ℝ) ^ (-(4 : ℝ) / 3 + CG * ε)) := by
          ring
      _ ≤ 4 * Y := by rw [e1]; linarith
  have t2 : (N : ℝ) ^ ((7 * CF + 1) * ε) *
      (W * ((N : ℝ) ^ 2 * (18 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 4))) ≤ 36 * Y := by
    calc _ ≤ (N : ℝ) ^ ((7 * CF + 1) * ε) * ((2 * (N : ℝ) ^ (-(4 : ℝ) / 3)) *
          ((N : ℝ) ^ 2 * (18 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 4))) := by gcongr
      _ = 36 * ((N : ℝ) ^ ((7 * CF + 1) * ε) * (N : ℝ) ^ (-(4 : ℝ) / 3) * (N : ℝ) ^ 2 *
          ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 4) := by ring
      _ ≤ 36 * Y := by rw [e2]; linarith
  have h7 : 128 ≤ (N : ℝ) ^ (7 * ε) := by
    rw [show 7 * ε = ε * ((7 : ℕ) : ℝ) by push_cast; ring, Real.rpow_mul_natCast hn0.le]
    calc (128 : ℝ) = 2 ^ 7 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) ht 7
  have eY : (N : ℝ) ^ (-(2 : ℝ) / 3 + (CG + 7 * CF + 20) * ε) = (N : ℝ) ^ (7 * ε) * Y := by
    rw [hY, ← Real.rpow_add hn0]; congr 1; ring
  have hY0 : 0 ≤ Y := (Real.rpow_pos_of_pos hn0 _).le
  rw [eY]
  nlinarith

/-- On `Ω` the functional of `Q` is at most `N^{7ε}`: `W N² P² ≤ 2 N^{6ε} ≤ N^{7ε}`. -/
private lemma ods_x_le {N : ℕ} (hN : 1 ≤ N) {ε W : ℝ} (ht : 2 ≤ (N : ℝ) ^ ε)
    (hW : W ≤ 2 * (N : ℝ) ^ (-(4 : ℝ) / 3)) :
    W * ((N : ℝ) ^ 2 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 2) ≤ (N : ℝ) ^ (7 * ε) := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have e : (N : ℝ) ^ (-(4 : ℝ) / 3) * ((N : ℝ) ^ 2 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 2) =
      (N : ℝ) ^ (6 * ε) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) 2, ← Real.rpow_mul hn0.le,
      ← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_add hn0, ← Real.rpow_add hn0]
    congr 1; push_cast; ring
  have e7 : (N : ℝ) ^ (7 * ε) = (N : ℝ) ^ ε * (N : ℝ) ^ (6 * ε) := by
    rw [← Real.rpow_add hn0]; congr 1; ring
  have h6 : 0 ≤ (N : ℝ) ^ (6 * ε) := (Real.rpow_pos_of_pos hn0 _).le
  calc _ ≤ 2 * (N : ℝ) ^ (-(4 : ℝ) / 3) *
        ((N : ℝ) ^ 2 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 2) :=
        mul_le_mul_of_nonneg_right hW (by positivity)
    _ = 2 * (N : ℝ) ^ (6 * ε) := by rw [mul_assoc, e]
    _ ≤ _ := by rw [e7]; nlinarith

/-! ### (6.77)–(6.86): the third-order term -/

/-- [16] (6.77)–(6.86) at `f = 0`: `|E g₃(Q)| ≤ N^{-2/3+Cε}` for every `H_γ`, every off-diagonal
entry and both functionals; `C` depends only on `CF`. -/
private lemma ods_g3_le {CF C0 φs : ℝ} (hC0 : 0 ≤ C0) (hφs : 1 / 3 < φs) (hφs' : φs ≤ 1 / 2) :
    ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < 1 / 10 → ∃ N0 : ℕ, ∀ N ≥ N0,
      ∀ L : EntryLaws N, (∃ Lv γ, LargeQClass C0 φs N Lv ∧ L = interp (lexPos N) γ Lv (goeLaws N)) →
      ∀ p : OffDiag N, ∀ F : ℝ → ℝ, ContDiff ℝ 4 F →
        (∀ n ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF) →
        (∀ E₁ E₂ : ℝ, |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |∫ ω, swapB3Int F (symOfEntries (zeroEntry (Sum.inr p) ω)) p
              ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂ ∂L.law| ≤
            (N : ℝ) ^ (-(2 : ℝ) / 3 + C * ε)) ∧
        (∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |∫ ω, swapB3Pt F (symOfEntries (zeroEntry (Sum.inr p) ω)) p
              ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ ∂L.law| ≤
            (N : ℝ) ^ (-(2 : ℝ) / 3 + C * ε)) := by
  obtain ⟨CG, hCG, hEG⟩ := expectation_gain_largeQ (CF := CF) hC0 hφs hφs'
  refine ⟨CG + 7 * |CF| + 20, by positivity, fun ε hε hε' => ?_⟩
  by_cases hCF : 0 ≤ CF
  swap
  · refine ⟨0, fun N _ L _ p F _ hF => ?_⟩
    exfalso
    have h1 := hF 1 (by simp) 0
    exact hCF (by simpa using (abs_nonneg _).trans h1)
  rw [abs_of_nonneg hCF]
  obtain ⟨c, hc, Cb, -, N1, hHP⟩ := (apriori_largeQInterp_event hC0 hφs hφs' ε hε hε').inter
    (entryVal_le_largeQInterp hC0 hφs hφs' ε hε hε')
  obtain ⟨N2, hN2⟩ := norm_resolventC_zeroEntry_sub_le hφs hφs' ε hε hε'
  obtain ⟨N3, hN3⟩ := hEG ε hε hε'
  obtain ⟨N4, hN4⟩ := abs_iteratedDeriv_le_rpow_eps (CF := CF) (a := 7) (by norm_num) hε
  obtain ⟨N5, hN5⟩ := eventually_atTop.1 <|
    (eventually_ge_atTop 1).and <|
    (((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2).and <|
    ods_bad (Cb := Cb) hCF hc
  refine ⟨max (max N1 N2) (max (max N3 N4) N5), fun N hN L hL p F hF4 hF => ?_⟩
  have hNN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNN2 : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNN3 : N3 ≤ N :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hN
  have hNN4 : N4 ≤ N :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hN
  have hNN5 : N5 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨hN1', ht, hbad⟩ := hN5 N hNN5
  replace ht : 2 ≤ (N : ℝ) ^ ε := ht
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1'
  have hn0 : (0 : ℝ) < N := by linarith
  have hη : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) := Real.rpow_pos_of_pos hn0 _
  have hηN : 1 / (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) ≤ N := by
    rw [one_div, ← Real.rpow_neg hn0.le]
    calc (N : ℝ) ^ (-(-(2 : ℝ) / 3 - ε)) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      _ = N := Real.rpow_one _
  have hP0 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) := (Real.rpow_pos_of_pos hn0 _).le
  have hP1 : (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  set Ω : Set (Entries N) := aprioriEvent N ε ∩
    {ω | ∀ e : Fin N ⊕ OffDiag N, |entryVal e ω| ≤ (N : ℝ) ^ (ε - φs)} with hΩdef
  obtain ⟨Lv, γ, hLv, rfl⟩ := hL
  have hgw := interp_isGenWigner (Φ := lexPos N) (γ := γ) hLv.1 (goeLaws_isGenWigner N)
  have hμ := isProbabilityMeasure_law hgw.isProb
  have hpr : ((interp (lexPos N) γ Lv (goeLaws N)).law Ωᶜ).toReal ≤
      (N : ℝ) ^ Cb * Real.exp (-c * phi N) := by
    have h := hHP N hNN1 _ ⟨Lv, γ, hLv, rfl⟩
    have h' := ENNReal.toReal_le_of_le_ofReal (by positivity) h
    simpa only [Real.rpow_one] using h'
  have hT := hbad _ ENNReal.toReal_nonneg hpr
  have hRb : ∀ ω ∈ Ω, ∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) → ∀ k l,
      ‖resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l -
          (if k = l then msc ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ else 0)‖ ≤
        (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) :=
    fun ω hω => hN2 N hNN2 ω (Sum.inr p) hω.1 (hω.2 _)
  have hRoff : ∀ ω ∈ Ω, ∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) → ∀ k l, k ≠ l →
      ‖resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l‖ ≤
        (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) := fun ω hω E hE k l hkl => by
    simpa [hkl] using hRb ω hω E hE k l
  have hF1 : ∀ ζ : ℝ, |ζ| ≤ (N : ℝ) ^ (7 * ε) →
      |iteratedDeriv 1 F ζ| ≤ (N : ℝ) ^ ((7 * CF + 1) * ε) := fun ζ hζ =>
    hN4 N hNN4 F hF ζ hζ 1 (by simp)
  have hFg : ∀ ζ : ℝ, |ζ| ≤ 32 * (N : ℝ) ^ 8 →
      |iteratedDeriv 1 F ζ| ≤ CF * (1 + 32 * (N : ℝ) ^ 8) ^ CF := fun ζ hζ =>
    (hF 1 (by simp) ζ).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by linarith) hCF) hCF)
  have hzc := odp_continuous_zeroEntry (N := N) (Sum.inr p)
  have hF1c := hF4.continuous_iteratedDeriv 1 (by norm_num)
  have hH := fun ω : Entries N => symOfEntries_isHermitian (zeroEntry (Sum.inr p) ω)
  refine ⟨fun E₁ E₂ h1 h2 => ?_, fun E hE => ?_⟩
  · -- the functional (6.56)
    have hW := ode_weight hn1 h1 h2
    have hW2 : (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) * |E₂ - E₁| ≤ 2 := by
      have := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num : (-(4 : ℝ) / 3) ≤ 0)
      linarith
    have e : (fun ω => swapB3Int F (symOfEntries (zeroEntry (Sum.inr p) ω)) p
        ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂) = fun ω =>
        (((iteratedDeriv 1 F (offWardInt (symOfEntries (zeroEntry (Sum.inr p) ω))
          ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂) : ℝ) : ℂ) *
          (swapK (symOfEntries (zeroEntry (Sum.inr p) ω)) p ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂
              0 3 0 +
            (starRingEnd ℂ) (swapK (symOfEntries (zeroEntry (Sum.inr p) ω)) p
              ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂ 0 3 0))).re := by
      funext ω; unfold swapB3Int; rw [ods_swapK_conj]
    rw [e]
    have hRc := ods_continuous_resolventC_zeroEntry (Sum.inr p) hη
    have hφc : Continuous fun ω => iteratedDeriv 1 F (offWardInt
        (symOfEntries (zeroEntry (Sum.inr p) ω)) ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂) := by
      have h := hF1c.comp ((ward_continuous_b' hη E₁ E₂).comp hzc); exact h
    have hKc : Continuous fun ω => swapK (symOfEntries (zeroEntry (Sum.inr p) ω)) p
        ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂ 0 3 0 := by
      have h := (odp_continuous_swapK hη p E₁ E₂ 0 3 0).comp hzc; exact h
    have hMc : Continuous fun ω => odsMainInt (symOfEntries (zeroEntry (Sum.inr p) ω)) p
        ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂ := by
      have h := (ods_continuous_mainInt p hη E₁ E₂).comp hzc; exact h
    have hφg : ∀ ω, |iteratedDeriv 1 F (offWardInt (symOfEntries (zeroEntry (Sum.inr p) ω))
        ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂)| ≤ CF * (1 + 32 * (N : ℝ) ^ 8) ^ CF := fun ω =>
      hFg _ (odp_offWardInt_global hN1' (hH ω) hη hηN hW2)
    have hmain := ods_expect_int (μ := (interp (lexPos N) γ Lv (goeLaws N)).law) p hφc hφg hη hRc
      (B := 1 / (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) (by positivity)
      (fun ω y k l => norm_resolventC_apply_le (hH ω) (z := ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩)
        hη k l) (G := (N : ℝ) ^ (-(4 : ℝ) / 3 + CG * ε)) (Real.rpow_pos_of_pos hn0 _).le
      (fun y hy b d i j hbd hij hib hid hjb hjd =>
        (hN3 N hNN3 _ ⟨Lv, γ, hLv, rfl⟩ p b d i j hbd hij hib hid hjb hjd F hF4 hF y
          (ode_window h1 h2 hy)).1 E₁ E₂ h1 h2)
    refine (ods_perLaw (μ := (interp (lexPos N) γ Lv (goeLaws N)).law) hφc hKc hMc (Ω := Ω)
      (A₂ := (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) * |E₂ - E₁| *
        ((N : ℝ) ^ 2 * (18 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 4)))
      (Bx := (N : ℝ) ^ ((7 * CF + 1) * ε)) (by positivity)
      (Real.rpow_pos_of_pos hn0 _).le hmain (fun ω hω => ⟨?_, ?_⟩) hφg
      (fun ω => odp_K_global hN1' (hH ω) hη hηN hW2 p (k := 0) (s := 3) (t := 0) (by norm_num))
      (fun ω => ods_mainInt_global hN1' (hH ω) p hη hηN hW2)).trans ?_
    · exact ods_mainInt_sub_le (hH ω) p hη hP0 hP1 fun y hy => hRb ω hω y (ode_window h1 h2 hy)
    · exact hF1 _ ((ods_offWardInt_le hη fun y hy => hRoff ω hω y (ode_window h1 h2 hy)).trans
        (ods_x_le hN1' ht hW))
    · exact ods_arith hN1' hε hCG.le hCF ht hW hT
  · -- the functional `η² Σ_{i ≠ j} |G_ij(z)|²`
    have hz : 0 < (⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ : ℂ).im := hη
    have hW := ode_weight_sq hn1 hε (ε := ε)
    have e : (fun ω => swapB3Pt F (symOfEntries (zeroEntry (Sum.inr p) ω)) p
        ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩) = fun ω =>
        (((iteratedDeriv 1 F (offWard (symOfEntries (zeroEntry (Sum.inr p) ω))
          ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩) : ℝ) : ℂ) *
          (swapKpt (symOfEntries (zeroEntry (Sum.inr p) ω)) p ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩
              0 3 0 +
            (starRingEnd ℂ) (swapKpt (symOfEntries (zeroEntry (Sum.inr p) ω)) p
              ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ 0 3 0))).re := by
      funext ω; unfold swapB3Pt; rw [ods_swapKpt_conj]
    rw [e]
    have hRc : Continuous fun ω : Entries N =>
        resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ :=
      (continuous_matrix fun i j => continuous_resolventC_symOfEntries hz.ne' i j).comp hzc
    have hφc : Continuous fun ω => iteratedDeriv 1 F (offWard
        (symOfEntries (zeroEntry (Sum.inr p) ω)) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩) := by
      have h := hF1c.comp ((odp_continuous_offWard hz).comp hzc); exact h
    have hKc : Continuous fun ω => swapKpt (symOfEntries (zeroEntry (Sum.inr p) ω)) p
        ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ 0 3 0 := by
      have h := (odp_continuous_swapKpt hz p 0 3 0).comp hzc; exact h
    have hMc : Continuous fun ω => odsMainPt (symOfEntries (zeroEntry (Sum.inr p) ω)) p
        ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ := by
      have h := (ods_continuous_mainPt p hz).comp hzc; exact h
    have hφg : ∀ ω, |iteratedDeriv 1 F (offWard (symOfEntries (zeroEntry (Sum.inr p) ω))
        ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩)| ≤ CF * (1 + 32 * (N : ℝ) ^ 8) ^ CF := fun ω =>
      hFg _ (odp_offWard_global hN1' (hH ω) hz)
    have hsum := ods_expect_sum (μ := (interp (lexPos N) γ Lv (goeLaws N)).law) p hφc hφg hRc
      (B := 1 / (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) (by positivity)
      (fun ω k l => norm_resolventC_apply_le (hH ω) hz k l)
      (norm_msc_eq_inv_and_lt_one hz).2.le (G := (N : ℝ) ^ (-(4 : ℝ) / 3 + CG * ε))
      (Real.rpow_pos_of_pos hn0 _).le
      (fun b d i j hbd hij hib hid hjb hjd =>
        (hN3 N hNN3 _ ⟨Lv, γ, hLv, rfl⟩ p b d i j hbd hij hib hid hjb hjd F hF4 hF E hE).2 E hE)
    have hmain : ‖∫ ω, ((iteratedDeriv 1 F (offWard (symOfEntries (zeroEntry (Sum.inr p) ω))
          ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩) : ℝ) : ℂ) *
          odsMainPt (symOfEntries (zeroEntry (Sum.inr p) ω)) p ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩
          ∂(interp (lexPos N) γ Lv (goeLaws N)).law‖ ≤
        ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) ^ 2 *
          ((N : ℝ) ^ 2 * (2 * (N : ℝ) ^ (-(4 : ℝ) / 3 + CG * ε))) := by
      have e2 : (fun ω => ((iteratedDeriv 1 F (offWard (symOfEntries (zeroEntry (Sum.inr p) ω))
          ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩) : ℝ) : ℂ) *
          odsMainPt (symOfEntries (zeroEntry (Sum.inr p) ω)) p
            ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩) = fun ω =>
          (((N : ℝ) ^ (-(2 : ℝ) / 3 - ε) : ℝ) : ℂ) ^ 2 *
            (((iteratedDeriv 1 F (offWard (symOfEntries (zeroEntry (Sum.inr p) ω))
              ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩) : ℝ) : ℂ) *
            odsSum (resolventC (symOfEntries (zeroEntry (Sum.inr p) ω))
              ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩) p (msc ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩)) := by
        funext ω; unfold odsMainPt; ring
      rw [e2, integral_const_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hη]
      exact mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    refine (ods_perLaw (μ := (interp (lexPos N) γ Lv (goeLaws N)).law) hφc hKc hMc (Ω := Ω)
      (A₂ := ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) ^ 2 *
        ((N : ℝ) ^ 2 * (18 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 4)))
      (Bx := (N : ℝ) ^ ((7 * CF + 1) * ε)) (by positivity)
      (Real.rpow_pos_of_pos hn0 _).le hmain (fun ω hω => ⟨?_, ?_⟩) hφg
      (fun ω => odp_Kpt_global hN1' (hH ω) hz hηN p (k := 0) (s := 3) (t := 0) (by norm_num))
      (fun ω => ods_mainPt_global hN1' (hH ω) p hz hηN)).trans ?_
    · exact ods_mainPt_sub_le p hP0 hP1 (norm_msc_eq_inv_and_lt_one hz).2.le (hRb ω hω E hE)
    · exact hF1 _ ((ods_offWard_le (hRoff ω hω E hE)).trans (ods_x_le hN1' ht hW))
    · exact ods_arith hN1' hε hCG.le hCF ht hW hT

/-! ### One replacement -/

private lemma ods_continuous_swapB3Int {N : ℕ} {F : ℝ → ℝ} (hF : ContDiff ℝ 4 F) {η : ℝ}
    (hη : 0 < η) (p : OffDiag N) (E₁ E₂ : ℝ) :
    Continuous fun ω : Entries N => swapB3Int F (symOfEntries ω) p η E₁ E₂ := by
  have hx := ward_continuous_b' (N := N) hη E₁ E₂
  have h1 := (hF.continuous_iteratedDeriv 1 (by norm_num)).comp hx
  have hK := odp_continuous_swapK (N := N) hη p E₁ E₂
  unfold swapB3Int
  exact Complex.continuous_re.comp ((Complex.continuous_ofReal.comp h1).mul
    ((hK 0 3 0).add (hK 0 0 3)))

private lemma ods_continuous_swapB3Pt {N : ℕ} {F : ℝ → ℝ} (hF : ContDiff ℝ 4 F) {z : ℂ}
    (hz : 0 < z.im) (p : OffDiag N) :
    Continuous fun ω : Entries N => swapB3Pt F (symOfEntries ω) p z := by
  have hx := odp_continuous_offWard (N := N) hz
  have h1 := (hF.continuous_iteratedDeriv 1 (by norm_num)).comp hx
  have hK := odp_continuous_swapKpt (N := N) hz p
  unfold swapB3Pt
  exact Complex.continuous_re.comp ((Complex.continuous_ofReal.comp h1).mul
    ((hK 0 3 0).add (hK 0 0 3)))

/-- `|n₃| = |E(-h_e)³| ≤ E|h_e|³`. -/
private lemma ods_moment3_le {N : ℕ} (L : EntryLaws N) (e : Fin N ⊕ OffDiag N) :
    |L.entryMoment e 3| ≤ ∫ x, |x| ^ 3 ∂(L.entry e) := by
  unfold EntryLaws.entryMoment
  refine abs_integral_le_integral_abs.trans (le_of_eq ?_)
  congr 1; funext x; rw [abs_pow, abs_neg]

/-- The bookkeeping of one off-diagonal step: `2 N^{-5/3-φs+C_S ε} + N^{-2/3+C_3 ε} 2 C_A N⁻¹ q⁻¹`
is at most `N^{-5/3+Cε-φs}`, `C = C_D + C_S + C_3 + 1`, once `N^ε ≥ 2 + 2 C_A`. -/
private lemma ods_final {N : ℕ} (hN : 1 ≤ N) {ε φs CS C3 CD CA T₁ T₀ g n₁ n₀ : ℝ} (hε : 0 < ε)
    (hCS : 0 ≤ CS) (hC3 : 0 ≤ C3) (hCD : 0 ≤ CD) (hCA : 0 ≤ CA) (ht : 2 + 2 * CA ≤ (N : ℝ) ^ ε)
    (hT₁ : |T₁| ≤ (N : ℝ) ^ (-(5 : ℝ) / 3 - φs + CS * ε))
    (hT₀ : |T₀| ≤ (N : ℝ) ^ (-(5 : ℝ) / 3 - φs + CS * ε))
    (hg : |g| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + C3 * ε))
    (hn₁ : |n₁| ≤ CA * (N : ℝ)⁻¹ * (N : ℝ) ^ (φs * (2 - ((3 : ℕ) : ℝ))))
    (hn₀ : |n₀| ≤ CA * (N : ℝ)⁻¹ * (N : ℝ) ^ (φs * (2 - ((3 : ℕ) : ℝ)))) :
    |T₁ - T₀ + g * (n₁ - n₀)| ≤ (N : ℝ) ^ (-(5 : ℝ) / 3 + (CD + CS + C3 + 1) * ε - φs) := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  set Z := (N : ℝ) ^ (-(5 : ℝ) / 3 - φs + (CS + C3) * ε) with hZ
  have hZ0 : 0 ≤ Z := (Real.rpow_pos_of_pos hn0 _).le
  have m1 : (N : ℝ) ^ (-(5 : ℝ) / 3 - φs + CS * ε) ≤ Z :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith)
  have e3 : (N : ℝ) ^ (-(2 : ℝ) / 3 + C3 * ε) * ((N : ℝ)⁻¹ * (N : ℝ) ^ (φs * (2 - ((3 : ℕ) : ℝ)))) =
      (N : ℝ) ^ (-(5 : ℝ) / 3 - φs + C3 * ε) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hn0, ← Real.rpow_add hn0]
    congr 1; push_cast; ring
  have m3 : (N : ℝ) ^ (-(5 : ℝ) / 3 - φs + C3 * ε) ≤ Z :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith)
  have hgn : |g * (n₁ - n₀)| ≤ 2 * CA * Z := by
    have hn : |n₁ - n₀| ≤ 2 * (CA * ((N : ℝ)⁻¹ * (N : ℝ) ^ (φs * (2 - ((3 : ℕ) : ℝ))))) := by
      have := abs_sub n₁ n₀
      have e : CA * (N : ℝ)⁻¹ * (N : ℝ) ^ (φs * (2 - ((3 : ℕ) : ℝ))) =
          CA * ((N : ℝ)⁻¹ * (N : ℝ) ^ (φs * (2 - ((3 : ℕ) : ℝ)))) := by ring
      linarith
    rw [abs_mul]
    calc |g| * |n₁ - n₀| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + C3 * ε) *
          (2 * (CA * ((N : ℝ)⁻¹ * (N : ℝ) ^ (φs * (2 - ((3 : ℕ) : ℝ)))))) :=
          mul_le_mul hg hn (abs_nonneg _) (Real.rpow_pos_of_pos hn0 _).le
      _ = 2 * CA * ((N : ℝ) ^ (-(2 : ℝ) / 3 + C3 * ε) *
          ((N : ℝ)⁻¹ * (N : ℝ) ^ (φs * (2 - ((3 : ℕ) : ℝ))))) := by ring
      _ ≤ 2 * CA * Z := by rw [e3]; exact mul_le_mul_of_nonneg_left m3 (by positivity)
  have eF : (N : ℝ) ^ (-(5 : ℝ) / 3 + (CD + CS + C3 + 1) * ε - φs) =
      (N : ℝ) ^ (CD * ε) * ((N : ℝ) ^ ε * Z) := by
    rw [hZ, ← Real.rpow_add hn0, ← Real.rpow_add hn0]; congr 1; ring
  have hCDε : 1 ≤ (N : ℝ) ^ (CD * ε) := Real.one_le_rpow hn1 (by positivity)
  have hsum := abs_add_le (T₁ - T₀) (g * (n₁ - n₀))
  have hsub := abs_sub T₁ T₀
  have hεZ : (2 + 2 * CA) * Z ≤ (N : ℝ) ^ ε * Z := mul_le_mul_of_nonneg_right ht hZ0
  have hεZ0 : 0 ≤ (N : ℝ) ^ ε * Z := by positivity
  rw [eF]
  nlinarith

/-- (3.29) and (3.38): one replacement `H_{γ-1} → H_γ`, `γ = lexPos N e`, between a law of Lemma 3.5
and the GOE, for both functionals of the Claim; the error is `N^{-5/3+Cε} q⁻¹` off the diagonal and
`N^{-1/3+Cε} q⁻²` on it, `q = N^{φs}`. -/
theorem swap_comparison_largeQ {CF C0 φs : ℝ} (hC0 : 0 ≤ C0) (hφs : 1 / 3 < φs)
    (hφs' : φs ≤ 1 / 2) :
    ∃ ε₀ > (0 : ℝ), ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ N0 : ℕ, ∀ N ≥ N0,
      ∀ Lv : EntryLaws N, LargeQClass C0 φs N Lv → ∀ e : Fin N ⊕ OffDiag N,
      ∀ F : ℝ → ℝ, ContDiff ℝ 4 F →
        (∀ n ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF) →
        (∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |∫ ω, F (offWard (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩)
              ∂(interp (lexPos N) (lexPos N e) Lv (goeLaws N)).law -
            ∫ ω, F (offWard (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩)
              ∂(interp (lexPos N) (lexPos N e - 1) Lv (goeLaws N)).law| ≤
            Sum.elim (fun _ => (N : ℝ) ^ (-(1 : ℝ) / 3 + C * ε - 2 * φs))
              (fun _ => (N : ℝ) ^ (-(5 : ℝ) / 3 + C * ε - φs)) e) ∧
        (∀ E₁ E₂ : ℝ, |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |∫ ω, F (offWardInt (symOfEntries ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂)
              ∂(interp (lexPos N) (lexPos N e) Lv (goeLaws N)).law -
            ∫ ω, F (offWardInt (symOfEntries ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂)
              ∂(interp (lexPos N) (lexPos N e - 1) Lv (goeLaws N)).law| ≤
            Sum.elim (fun _ => (N : ℝ) ^ (-(1 : ℝ) / 3 + C * ε - 2 * φs))
              (fun _ => (N : ℝ) ^ (-(5 : ℝ) / 3 + C * ε - φs)) e) := by
  obtain ⟨ε₀D, hε₀D, CD, hCD, hD⟩ := swap_comparison_diag_largeQ (CF := CF) hC0 hφs hφs'
  obtain ⟨CS, hCS, hS⟩ := swap_expansion_largeQ (CF := CF) hC0 hφs hφs'
  obtain ⟨C3, hC3, hG3⟩ := ods_g3_le (CF := CF) hC0 hφs hφs'
  obtain ⟨CA, hCA, hA⟩ := entry_abs_pow_le_largeQInterp hC0 hφs hφs'
  refine ⟨min ε₀D (1 / 10), lt_min hε₀D (by norm_num), CD + CS + C3 + 1, by positivity,
    fun ε hε hε' => ?_⟩
  have hεD : ε < ε₀D := lt_of_lt_of_le hε' (min_le_left _ _)
  have hε10 : ε < 1 / 10 := lt_of_lt_of_le hε' (min_le_right _ _)
  obtain ⟨ND, hND⟩ := hD ε hε hεD
  obtain ⟨NS, hNS⟩ := hS ε hε hε10
  obtain ⟨NG, hNG⟩ := hG3 ε hε hε10
  obtain ⟨NA, hNA⟩ := eventually_atTop.1 <| (eventually_ge_atTop 1).and <|
    ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (2 + 2 * CA)
  refine ⟨max (max ND NS) (max NG NA), fun N hN Lv hLv e F hF4 hF => ?_⟩
  have hNND : ND ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNNS : NS ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNNG : NG ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNNA : NA ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨hN1, ht⟩ := hNA N hNNA
  replace ht : 2 + 2 * CA ≤ (N : ℝ) ^ ε := ht
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < N := by linarith
  rcases e with a | p
  · -- a diagonal entry: (3.30)–(3.38)
    obtain ⟨h1, h2⟩ := hND N hNND Lv hLv a F hF4 hF
    have hmono : (N : ℝ) ^ (-(1 : ℝ) / 3 + CD * ε - 2 * φs) ≤
        (N : ℝ) ^ (-(1 : ℝ) / 3 + (CD + CS + C3 + 1) * ε - 2 * φs) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith)
    simp only [Sum.elim_inl]
    exact ⟨fun E hE => (h1 E hE).trans hmono, fun E₁ E₂ hE₁ hE₂ => (h2 E₁ E₂ hE₁ hE₂).trans hmono⟩
  · -- an off-diagonal entry: [16] (6.74)–(6.86)
    simp only [Sum.elim_inr]
    have hη : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) := Real.rpow_pos_of_pos hn0 _
    have hmem : ∀ γ : ℕ, ∃ Lv' γ', LargeQClass C0 φs N Lv' ∧
        interp (lexPos N) γ Lv (goeLaws N) = interp (lexPos N) γ' Lv' (goeLaws N) :=
      fun γ => ⟨Lv, γ, hLv, rfl⟩
    have hn3 : ∀ γ : ℕ, |(interp (lexPos N) γ Lv (goeLaws N)).entryMoment (Sum.inr p) 3| ≤
        CA * (N : ℝ)⁻¹ * (N : ℝ) ^ (φs * (2 - ((3 : ℕ) : ℝ))) := fun γ =>
      (ods_moment3_le _ _).trans (hA N (by omega) _ (hmem γ) (Sum.inr p) 3 (by norm_num)
        (by norm_num)).2
    have hS1 := hNS N hNNS _ (hmem (lexPos N (Sum.inr p))) p F hF4 hF
    have hS0 := hNS N hNNS _ (hmem (lexPos N (Sum.inr p) - 1)) p F hF4 hF
    have hG := hNG N hNNG _ (hmem (lexPos N (Sum.inr p))) p F hF4 hF
    refine ⟨fun E hE => ?_, fun E₁ E₂ hE₁ hE₂ => ?_⟩
    · have hz : 0 < (⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ : ℂ).im := hη
      have hR := odp_integral_zeroEntry_interp hLv.1.isProb (Sum.inr p)
        (f := fun ω => F (offWard (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩))
        (hF4.continuous.comp (odp_continuous_offWard hz))
      have hB := (swapB_interp_eq hLv p F hF4 hη 0 0 _ hz).2
      have hg := odp_integral_zeroEntry_interp hLv.1.isProb (Sum.inr p)
        (f := fun ω => swapB3Pt F (symOfEntries ω) p ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩)
        (ods_continuous_swapB3Pt hF4 hz p)
      have k := ods_final hN1 hε hCS.le hC3.le hCD.le hCA.le ht (hS1.2 E hE) (hS0.2 E hE)
        (hG.2 E hE) (hn3 (lexPos N (Sum.inr p)))
        (hn3 (lexPos N (Sum.inr p) - 1))
      refine le_of_eq_of_le (congrArg abs ?_) (k.trans_eq ?_)
      · rw [hR, hB, hg]; ring
      · congr 1
    · have hR := odp_integral_zeroEntry_interp hLv.1.isProb (Sum.inr p)
        (f := fun ω => F (offWardInt (symOfEntries ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂))
        (hF4.continuous.comp (ward_continuous_b' hη E₁ E₂))
      have hB := (swapB_interp_eq hLv p F hF4 hη E₁ E₂ Complex.I (by simp)).1
      have hg := odp_integral_zeroEntry_interp hLv.1.isProb (Sum.inr p)
        (f := fun ω => swapB3Int F (symOfEntries ω) p ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂)
        (ods_continuous_swapB3Int hF4 hη p E₁ E₂)
      have k := ods_final hN1 hε hCS.le hC3.le hCD.le hCA.le ht (hS1.1 E₁ E₂ hE₁ hE₂)
        (hS0.1 E₁ E₂ hE₁ hE₂) (hG.1 E₁ E₂ hE₁ hE₂) (hn3 (lexPos N (Sum.inr p)))
        (hn3 (lexPos N (Sum.inr p) - 1))
      refine le_of_eq_of_le (congrArg abs ?_) (k.trans_eq ?_)
      · rw [hR, hB, hg]; ring
      · congr 1

/-! ### Checks -/

-- The entry law of Lemma 3.5 at `N = 1024` with diagonal values `±1/16, 0, 0` (variance `2/N`)
-- and off-diagonal values `±1/32` (variance `1/N`), in `LargeQClass 1 (2/5) 1024`.
open private lawA lawA_isGenWigner lawA_supp from WEdgeNS.EdgeUniv.LargeQClass

/-- Every hypothesis of `swap_comparison_largeQ` that is not existential holds at one point:
`N = 1024`, `C0 = 1`, `φs = 2/5`, `ε = 1/15` (the window `I_ε` is `|E - 2| ≤ 1/64`), `Lv` the law
above, the off-diagonal entry `e = (4, 913)` with `γ = lexPos N e = 5000` (under `H_γ` the entry `e`
has the law of `Lv` and under `H_{γ-1}` the Gaussian law; rows `4`–`1023` have both entry types),
`F = K(·/π)` for the edge cutoff `K`, `E = 2` and `E₁ = 2 - 1/100 < E₂ = 2 + 1/100`. -/
example : ∃ CF : ℝ, 0 < CF ∧ (0 : ℝ) ≤ 1 ∧ (1 / 3 : ℝ) < 2 / 5 ∧ (2 / 5 : ℝ) ≤ 1 / 2 ∧
    (0 : ℝ) < 1 / 15 ∧ (1 / 15 : ℝ) < 1 / 10 ∧
    LargeQClass 1 (2 / 5) 1024 lawA ∧
    lexPos 1024 (Sum.inr (⟨(4, 913), by decide⟩ : OffDiag 1024)) = 5000 ∧
    (interp (lexPos 1024) (lexPos 1024 (Sum.inr (⟨(4, 913), by decide⟩ : OffDiag 1024))) lawA
      (goeLaws 1024)).off ⟨(4, 913), by decide⟩ = lawA.off ⟨(4, 913), by decide⟩ ∧
    (interp (lexPos 1024) (lexPos 1024 (Sum.inr (⟨(4, 913), by decide⟩ : OffDiag 1024)) - 1) lawA
      (goeLaws 1024)).off ⟨(4, 913), by decide⟩ = (goeLaws 1024).off ⟨(4, 913), by decide⟩ ∧
    ContDiff ℝ 4 (fun x => edgeCutoff (x / Real.pi)) ∧
    (∀ n ∈ Finset.Icc 1 4, ∀ x : ℝ,
      |iteratedDeriv n (fun x => edgeCutoff (x / Real.pi)) x| ≤ CF * (1 + |x|) ^ CF) ∧
    |(2 - 1 / 100 : ℝ) - 2| ≤ ((1024 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) ∧
    |(2 + 1 / 100 : ℝ) - 2| ≤ ((1024 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) ∧
    (2 - 1 / 100 : ℝ) < 2 + 1 / 100 ∧
    |(2 : ℝ) - 2| ≤ ((1024 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) := by
  obtain ⟨CF, hCF, h⟩ := edgeCutoff_deriv_le
  have hpos : lexPos 1024 (Sum.inr (⟨(4, 913), by decide⟩ : OffDiag 1024)) = 5000 := rfl
  refine ⟨CF, hCF, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    ⟨lawA_isGenWigner, lawA_supp⟩, hpos, ?_, ?_,
    (edgeCutoff_props.1 4).comp (contDiff_id.div_const _), h, ?_, ?_, by norm_num, ?_⟩
  · simp only [interp, le_refl, ite_true]
  · simp only [interp, hpos, show ¬ (5000 ≤ 5000 - 1) by decide, ite_false]
  all_goals
    rw [rpow_1024_window]; norm_num [abs_of_nonneg, abs_of_nonpos]

/-- The conclusion of `swap_comparison_largeQ` at `C0 = 1`, `φs = 2/5`, for every `ε ∈ (0, ε₀)`
and all large `N`: the Rademacher law against the GOE, the off-diagonal entry `e = (0, 1)`,
`F = K(·/π)`, `E = 2` and `[E₁, E₂] = [2 - N^{-2/3+ε}, 2 + N^{-2/3+ε}]`. -/
example : ∃ ε₀ > (0 : ℝ), ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ᶠ N : ℕ in atTop,
    32 ≤ N ∧ ∃ p : OffDiag N,
    (2 : ℝ) - (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) < 2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) ∧
    |∫ ω, edgeCutoff (offWard (symOfEntries ω) ⟨2, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ / Real.pi)
          ∂(interp (lexPos N) (lexPos N (Sum.inr p)) (radLaws N) (goeLaws N)).law -
        ∫ ω, edgeCutoff (offWard (symOfEntries ω) ⟨2, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ / Real.pi)
          ∂(interp (lexPos N) (lexPos N (Sum.inr p) - 1) (radLaws N) (goeLaws N)).law| ≤
      (N : ℝ) ^ (-(5 : ℝ) / 3 + C * ε - 2 / 5) ∧
    |∫ ω, edgeCutoff (offWardInt (symOfEntries ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε))
          (2 - (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) (2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) / Real.pi)
          ∂(interp (lexPos N) (lexPos N (Sum.inr p)) (radLaws N) (goeLaws N)).law -
        ∫ ω, edgeCutoff (offWardInt (symOfEntries ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε))
          (2 - (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) (2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) / Real.pi)
          ∂(interp (lexPos N) (lexPos N (Sum.inr p) - 1) (radLaws N) (goeLaws N)).law| ≤
      (N : ℝ) ^ (-(5 : ℝ) / 3 + C * ε - 2 / 5) := by
  obtain ⟨CF, hCF, hFd⟩ := edgeCutoff_deriv_le
  obtain ⟨ε₀, hε₀, C, hC, h⟩ := swap_comparison_largeQ (CF := CF) (C0 := 1) (φs := 2 / 5)
    zero_le_one (by norm_num) (by norm_num)
  refine ⟨ε₀, hε₀, C, hC, fun ε hε hε' => ?_⟩
  obtain ⟨N0, hN0⟩ := h ε hε hε'
  filter_upwards [eventually_ge_atTop (max N0 32)] with N hN
  have h32 : 32 ≤ N := le_trans (le_max_right _ _) hN
  let p : OffDiag N := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.lt_def]⟩
  have hr : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) := Real.rpow_pos_of_pos (by positivity) _
  have hE₁ : |(2 - (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) := by
    rw [sub_sub_cancel_left, abs_neg, abs_of_pos hr]
  have hE₂ : |(2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) := by
    rw [add_sub_cancel_left, abs_of_pos hr]
  have hE : |(2 : ℝ) - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) := by
    rw [sub_self, abs_zero]; exact hr.le
  have hk := hN0 N (le_trans (le_max_left _ _) hN) (radLaws N)
    ⟨radLaws_isGenWigner (by omega), radLaws_boundedSupportAS h32⟩ (Sum.inr p)
    (fun x => edgeCutoff (x / Real.pi)) ((edgeCutoff_props.1 4).comp (contDiff_id.div_const _))
    hFd
  exact ⟨h32, p, by linarith, hk.1 2 hE, hk.2 _ _ hE₁ hE₂⟩

#print axioms swap_comparison_largeQ

end WEdgeNS
