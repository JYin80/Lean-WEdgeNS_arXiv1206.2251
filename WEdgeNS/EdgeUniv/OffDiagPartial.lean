import WEdgeNS.EdgeUniv.OffDiagExpansion
import WEdgeNS.Comparison.Classes

/-!
# Partial expectations in one off-diagonal entry
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-! ### The moments (6.42) -/

/-- The entry `e` of `H_γ` follows the law of `Lv` or the law of `Lw`. -/
private lemma odp_interp_entry {N : ℕ} (Φ : Fin N ⊕ OffDiag N → ℕ) (γ : ℕ) (Lv Lw : EntryLaws N)
    (e : Fin N ⊕ OffDiag N) :
    (interp Φ γ Lv Lw).entry e = Lv.entry e ∨ (interp Φ γ Lv Lw).entry e = Lw.entry e := by
  rcases e with i | p <;> simp only [EntryLaws.entry, interp, Sum.elim_inl, Sum.elim_inr] <;>
    split_ifs <;> simp

/-- `(√N)⁻¹ ^ k = N^{-k/2}`. -/
private lemma odp_invSqrt_pow {N : ℕ} (hN : 0 < N) (k : ℕ) :
    ((Real.sqrt N)⁻¹) ^ k = (N : ℝ) ^ (-(k : ℝ) / 2) := by
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hn0.le, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
  congr 1
  ring

/-- `N^{-k/2} ≤ N⁻¹ N^{φs(2-k)}` for `k ≥ 2` and `φs ≤ 1/2`. -/
private lemma odp_rpow_half_le {N : ℕ} (hN : 0 < N) {φs : ℝ} (hφs' : φs ≤ 1 / 2) {k : ℕ}
    (hk : 2 ≤ k) :
    (N : ℝ) ^ (-(k : ℝ) / 2) ≤ (N : ℝ)⁻¹ * (N : ℝ) ^ (φs * (2 - (k : ℝ))) := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rw [← Real.rpow_neg_one, ← Real.rpow_add hn0]
  exact Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith)

/-- The absolute moment `E|h|^k` of the entry `(√N)⁻¹ g`, `g ∼ ν`: integrability and the value
`N^{-k/2} E|g|^k`. -/
private lemma odp_gauss_moment {N : ℕ} (hN : 0 < N) (v : NNReal) (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k) ((gaussianReal 0 v).map (fun x => (Real.sqrt N)⁻¹ * x)) ∧
      ∫ x, |x| ^ k ∂((gaussianReal 0 v).map (fun x => (Real.sqrt N)⁻¹ * x)) =
        (N : ℝ) ^ (-(k : ℝ) / 2) * ∫ x, |x| ^ k ∂(gaussianReal 0 v) := by
  have hm : Measurable fun x : ℝ => (Real.sqrt N)⁻¹ * x := measurable_const.mul measurable_id
  have hc0 : 0 ≤ (Real.sqrt N)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hint : Integrable (fun x : ℝ => |x| ^ k) (gaussianReal 0 v) := by
    have h : MemLp id (k : ℕ) (gaussianReal 0 v) := by
      simpa using memLp_id_gaussianReal' (μ := 0) (v := v) (k : ENNReal) (ENNReal.natCast_ne_top k)
    simpa using h.integrable_norm_pow'
  have e : (fun x : ℝ => |x| ^ k) ∘ (fun x => (Real.sqrt N)⁻¹ * x) =
      fun x => ((Real.sqrt N)⁻¹) ^ k * |x| ^ k := by
    funext x; simp only [Function.comp, abs_mul, abs_of_nonneg hc0, mul_pow]
  have hcont : Continuous fun x : ℝ => |x| ^ k := continuous_abs.pow k
  refine ⟨?_, ?_⟩
  · refine (integrable_map_measure hcont.aestronglyMeasurable hm.aemeasurable).2 ?_
    rw [e]; exact hint.const_mul _
  · rw [integral_map hm.aemeasurable hcont.aestronglyMeasurable]
    have e' : ∀ x : ℝ, |(Real.sqrt N)⁻¹ * x| ^ k = ((Real.sqrt N)⁻¹) ^ k * |x| ^ k := fun x => by
      rw [abs_mul, abs_of_nonneg hc0, mul_pow]
    simp_rw [e']
    rw [integral_const_mul, odp_invSqrt_pow hN]

/-- [16] (6.42) for every `H_γ`: `E|h_e|^k ≤ C N⁻¹ q^{2-k}`, `q = N^{φs}`, `2 ≤ k ≤ 6`, with
integrability; from the almost-sure support for the law of Lemma 3.5 and from the Gaussian moments
with `q ≤ N^{1/2}` for the GOE. `C` depends only on `C0`. -/
theorem entry_abs_pow_le_largeQInterp {C0 φs : ℝ} (hC0 : 0 ≤ C0) (hφs : 1 / 3 < φs)
    (hφs' : φs ≤ 1 / 2) :
    ∃ C > (0 : ℝ), ∀ N : ℕ, 0 < N → ∀ L : EntryLaws N,
      (∃ Lv γ, LargeQClass C0 φs N Lv ∧ L = interp (lexPos N) γ Lv (goeLaws N)) →
      ∀ e : Fin N ⊕ OffDiag N, ∀ k : ℕ, 2 ≤ k → k ≤ 6 →
        Integrable (fun x : ℝ => |x| ^ k) (L.entry e) ∧
        ∫ x, |x| ^ k ∂(L.entry e) ≤ C * (N : ℝ)⁻¹ * (N : ℝ) ^ (φs * (2 - (k : ℝ))) := by
  set M : ℕ → ℝ := fun k => ∫ x, |x| ^ k ∂(gaussianReal 0 1) + ∫ x, |x| ^ k ∂(gaussianReal 0 2)
    with hM
  have hM0 : ∀ k, 0 ≤ M k := fun k =>
    add_nonneg (integral_nonneg fun x => by positivity) (integral_nonneg fun x => by positivity)
  refine ⟨1 + C0 + ∑ k ∈ Finset.range 7, M k, by
    have := Finset.sum_nonneg fun k (_ : k ∈ Finset.range 7) => hM0 k
    linarith, fun N hN L hL e k hk2 hk6 => ?_⟩
  have hMk : M k ≤ ∑ k ∈ Finset.range 7, M k :=
    Finset.single_le_sum (fun j _ => hM0 j) (Finset.mem_range.2 (by omega))
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range 7, M k := Finset.sum_nonneg fun j _ => hM0 j
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hNi : 0 < (N : ℝ)⁻¹ := inv_pos.2 hn0
  have hR0 : 0 < (N : ℝ) ^ (φs * (2 - (k : ℝ))) := Real.rpow_pos_of_pos hn0 _
  obtain ⟨Lv, γ, ⟨hgw, hsupp⟩, rfl⟩ := hL
  rcases odp_interp_entry (lexPos N) γ Lv (goeLaws N) e with he | he <;> rw [he]
  · -- the law of Lemma 3.5: `|x| ≤ q⁻¹` almost surely
    have hprob : IsProbabilityMeasure (Lv.entry e) := by
      rcases e with i | p
      · exact hgw.isProb.diag i
      · exact hgw.isProb.off p
    have hpow := hsupp.integrable_pow hgw.isProb k
    have hint_k : Integrable (fun x : ℝ => x ^ k) (Lv.entry e) := by
      rcases e with i | p
      · exact hpow.1 i
      · exact hpow.2 p
    have hint2 : Integrable (fun x : ℝ => x ^ 2) (Lv.entry e) := by
      rcases e with i | p
      · exact hgw.sq_int_diag i
      · exact hgw.sq_int_off p
    have htail : Lv.entry e {x | ((N : ℝ) ^ φs)⁻¹ < |x|} = 0 := by
      rcases e with i | p
      · exact hsupp.1 i
      · exact hsupp.2 p
    have hvar : ∫ x, x ^ 2 ∂(Lv.entry e) ≤ (1 + C0) * (N : ℝ)⁻¹ := by
      rcases e with i | p
      · have h := (abs_le.1 (hgw.var_diag i)).2
        change ∫ x, x ^ 2 ∂(Lv.diag i) ≤ _
        linarith
      · change ∫ x, x ^ 2 ∂(Lv.off p) ≤ _
        rw [hgw.var_off p]
        nlinarith
    have hint_abs : Integrable (fun x : ℝ => |x| ^ k) (Lv.entry e) :=
      hint_k.abs.congr (Eventually.of_forall fun x => by simp [abs_pow])
    refine ⟨hint_abs, ?_⟩
    set qi : ℝ := ((N : ℝ) ^ φs)⁻¹ with hqi
    have hqi0 : 0 ≤ qi := by positivity
    have hae : ∀ᵐ x ∂(Lv.entry e), |x| ^ k ≤ qi ^ (k - 2) * x ^ 2 := by
      have h1 : ∀ᵐ x ∂(Lv.entry e), ¬ (qi < |x|) := by
        rw [ae_iff]; simpa using htail
      filter_upwards [h1] with x hx
      have hx' : |x| ≤ qi := not_lt.1 hx
      have e2 : |x| ^ k = |x| ^ (k - 2) * x ^ 2 := by
        rw [← sq_abs x, ← pow_add]; congr 1; omega
      rw [e2]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg x) hx' _) (sq_nonneg _)
    have hqk : qi ^ (k - 2) = (N : ℝ) ^ (φs * (2 - (k : ℝ))) := by
      rw [hqi, ← Real.rpow_neg hn0.le, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      congr 1
      push_cast [Nat.cast_sub hk2]
      ring
    calc ∫ x, |x| ^ k ∂(Lv.entry e) ≤ ∫ x, qi ^ (k - 2) * x ^ 2 ∂(Lv.entry e) :=
          integral_mono_ae hint_abs (hint2.const_mul _) hae
      _ = qi ^ (k - 2) * ∫ x, x ^ 2 ∂(Lv.entry e) := integral_const_mul _ _
      _ ≤ (N : ℝ) ^ (φs * (2 - (k : ℝ))) * ((1 + C0) * (N : ℝ)⁻¹) := by
          rw [hqk]; exact mul_le_mul_of_nonneg_left hvar hR0.le
      _ ≤ (1 + C0 + ∑ k ∈ Finset.range 7, M k) * (N : ℝ)⁻¹ * (N : ℝ) ^ (φs * (2 - (k : ℝ))) := by
          have : (1 + C0) * (N : ℝ)⁻¹ ≤ (1 + C0 + ∑ k ∈ Finset.range 7, M k) * (N : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right (by linarith) hNi.le
          nlinarith
  · -- the GOE: `(√N)⁻¹ g` with `g ∼ N(0, 1)` off the diagonal and `N(0, 2)` on it
    have hgauss : ∃ v : NNReal, (goeLaws N).entry e =
        (gaussianReal 0 v).map (fun x => (Real.sqrt N)⁻¹ * x) ∧
          ∫ x, |x| ^ k ∂(gaussianReal 0 v) ≤ M k := by
      rcases e with i | p
      · refine ⟨2, rfl, ?_⟩
        have : 0 ≤ ∫ x, |x| ^ k ∂(gaussianReal 0 1) := integral_nonneg fun x => by positivity
        simp only [hM]; linarith
      · refine ⟨1, rfl, ?_⟩
        have : 0 ≤ ∫ x, |x| ^ k ∂(gaussianReal 0 2) := integral_nonneg fun x => by positivity
        simp only [hM]; linarith
    obtain ⟨v, hv, hvM⟩ := hgauss
    obtain ⟨hint, hval⟩ := odp_gauss_moment hN v k
    rw [hv]
    refine ⟨hint, ?_⟩
    rw [hval]
    have hhalf := odp_rpow_half_le hN hφs' hk2
    have hhalf0 : 0 ≤ (N : ℝ) ^ (-(k : ℝ) / 2) := (Real.rpow_pos_of_pos hn0 _).le
    have hg0 : 0 ≤ ∫ x, |x| ^ k ∂(gaussianReal 0 v) := integral_nonneg fun x => by positivity
    calc (N : ℝ) ^ (-(k : ℝ) / 2) * ∫ x, |x| ^ k ∂(gaussianReal 0 v)
        ≤ ((N : ℝ)⁻¹ * (N : ℝ) ^ (φs * (2 - (k : ℝ)))) * (∑ k ∈ Finset.range 7, M k) :=
          mul_le_mul hhalf (hvM.trans hMk) hg0 (by positivity)
      _ ≤ (1 + C0 + ∑ k ∈ Finset.range 7, M k) * (N : ℝ)⁻¹ * (N : ℝ) ^ (φs * (2 - (k : ℝ))) := by
          have h1 : 0 ≤ (N : ℝ)⁻¹ * (N : ℝ) ^ (φs * (2 - (k : ℝ))) := by positivity
          nlinarith

/-! ### The factors `g` and `g₃` of (6.74)–(6.75) -/

/-- The factor `g(Q)` of `B` in [16] (6.75) at `f = 0`, for the functional (6.56):
`g = F′(x_R) Σ_{k=0,1} (K^{(2,0)}_k + K^{(1,1)}_k + K^{(0,2)}_k) + ½ F″(x_R) (K^{(1,0)}_0 + K^{(0,1)}_0)²`,
`R = G(H)`; then `B = E g(Q) · E h_e²`. -/
def swapBInt {N : ℕ} (F : ℝ → ℝ) (H : Matrix (Fin N) (Fin N) ℝ) (p : OffDiag N) (η E₁ E₂ : ℝ) : ℝ :=
  (((iteratedDeriv 1 F (offWardInt H η E₁ E₂) : ℝ) : ℂ) *
      ∑ k ∈ Finset.range 2,
        (swapK H p η E₁ E₂ k 2 0 + swapK H p η E₁ E₂ k 1 1 + swapK H p η E₁ E₂ k 0 2) +
    ((iteratedDeriv 2 F (offWardInt H η E₁ E₂) : ℝ) : ℂ) / 2 *
      (swapK H p η E₁ E₂ 0 1 0 + swapK H p η E₁ E₂ 0 0 1) ^ 2).re

/-- The factor `g₃(Q) = F′(x_R) (K^{(3,0)}_0 + K^{(0,3)}_0)` of the terms
`Q^{(3,0)}_0 + Q^{(0,3)}_0` kept in [16] (6.74), for the functional (6.56); the term is
`E g₃(Q) · E(-h_e)³`. -/
def swapB3Int {N : ℕ} (F : ℝ → ℝ) (H : Matrix (Fin N) (Fin N) ℝ) (p : OffDiag N) (η E₁ E₂ : ℝ) :
    ℝ :=
  (((iteratedDeriv 1 F (offWardInt H η E₁ E₂) : ℝ) : ℂ) *
    (swapK H p η E₁ E₂ 0 3 0 + swapK H p η E₁ E₂ 0 0 3)).re

/-- `g(Q)` of [16] (6.75) for the functional `η² Σ_{i ≠ j} |G_ij(z)|²`. -/
def swapBPt {N : ℕ} (F : ℝ → ℝ) (H : Matrix (Fin N) (Fin N) ℝ) (p : OffDiag N) (z : ℂ) : ℝ :=
  (((iteratedDeriv 1 F (offWard H z) : ℝ) : ℂ) *
      ∑ k ∈ Finset.range 2, (swapKpt H p z k 2 0 + swapKpt H p z k 1 1 + swapKpt H p z k 0 2) +
    ((iteratedDeriv 2 F (offWard H z) : ℝ) : ℂ) / 2 * (swapKpt H p z 0 1 0 + swapKpt H p z 0 0 1) ^ 2).re

/-- `g₃(Q)` of [16] (6.74) for the functional `η² Σ_{i ≠ j} |G_ij(z)|²`. -/
def swapB3Pt {N : ℕ} (F : ℝ → ℝ) (H : Matrix (Fin N) (Fin N) ℝ) (p : OffDiag N) (z : ℂ) : ℝ :=
  (((iteratedDeriv 1 F (offWard H z) : ℝ) : ℂ) * (swapKpt H p z 0 3 0 + swapKpt H p z 0 0 3)).re

/-! ### Continuity in the entries -/

-- Joint continuity of `(ω, y) ↦ G(H)(y + iη)` and continuity of the functionals in `ω`.
open private ward_continuous_b ward_continuous_b' ward_integrable_comp ward_integral_sub_le
  ward_rpow_mul_exp_le ward_abs_sub_le from WEdgeNS.EdgeUniv.WardReduction

/-- `(ω, y) ↦ ((R I_e)^m R)_ij(y + iη)` is jointly continuous, `R = G(H)`. -/
private lemma odp_continuous_coeff {N : ℕ} {η : ℝ} (hη : 0 < η) (p : OffDiag N) (m : ℕ)
    (i j : Fin N) :
    Continuous fun q : Entries N × ℝ =>
      swapCoeff (symOfEntries q.1) (Sum.inr p) ⟨q.2, η⟩ m i j := by
  have hR : Continuous fun q : Entries N × ℝ => resolventC (symOfEntries q.1) ⟨q.2, η⟩ :=
    continuous_matrix fun i j => continuous_resolventC_symOfEntries_prod hη i j
  have : Continuous fun q : Entries N × ℝ => swapCoeff (symOfEntries q.1) (Sum.inr p) ⟨q.2, η⟩ m :=
    ((hR.mul continuous_const).pow m).mul hR
  exact this.matrix_elem i j

/-- `ω ↦ K^{(s,t)}_k(H)` is continuous for the functional (6.56). -/
private lemma odp_continuous_swapK {N : ℕ} {η : ℝ} (hη : 0 < η) (p : OffDiag N) (E₁ E₂ : ℝ)
    (k s t : ℕ) : Continuous fun ω : Entries N => swapK (symOfEntries ω) p η E₁ E₂ k s t := by
  have hj : Continuous fun q : Entries N × ℝ => ∑ i, ∑ j, if i ≠ j ∧ swapIdx p i j = k then
      swapCoeff (symOfEntries q.1) (Sum.inr p) ⟨q.2, η⟩ s i j *
        (starRingEnd ℂ) (swapCoeff (symOfEntries q.1) (Sum.inr p) ⟨q.2, η⟩ t i j) else 0 :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_if_const _ (fun _ => (odp_continuous_coeff hη p s i j).mul
        (Complex.continuous_conj.comp (odp_continuous_coeff hη p t i j))) fun _ => continuous_const
  exact continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (ω : Entries N) (y : ℝ) => ∑ i, ∑ j, if i ≠ j ∧ swapIdx p i j = k then
      swapCoeff (symOfEntries ω) (Sum.inr p) ⟨y, η⟩ s i j *
        (starRingEnd ℂ) (swapCoeff (symOfEntries ω) (Sum.inr p) ⟨y, η⟩ t i j) else 0) hj E₁ E₂)

/-- `ω ↦ G(H)(z)` is continuous for `Im z > 0`. -/
private lemma odp_continuous_resolventC {N : ℕ} {z : ℂ} (hz : 0 < z.im) :
    Continuous fun ω : Entries N => resolventC (symOfEntries ω) z :=
  continuous_matrix fun i j => continuous_resolventC_symOfEntries hz.ne' i j

/-- `ω ↦ K^{(s,t)}_k(H)` is continuous for the functional `η² Σ_{i ≠ j} |G_ij(z)|²`. -/
private lemma odp_continuous_swapKpt {N : ℕ} {z : ℂ} (hz : 0 < z.im) (p : OffDiag N)
    (k s t : ℕ) : Continuous fun ω : Entries N => swapKpt (symOfEntries ω) p z k s t := by
  have hR := odp_continuous_resolventC (N := N) hz
  have hc : ∀ m i j, Continuous fun ω : Entries N =>
      swapCoeff (symOfEntries ω) (Sum.inr p) z m i j :=
    fun m i j => (((hR.mul continuous_const).pow m).mul hR).matrix_elem i j
  exact continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_if_const _ (fun _ => (hc s i j).mul (Complex.continuous_conj.comp (hc t i j)))
      fun _ => continuous_const)

/-- `ω ↦ offWard(H)(z)` is continuous for `Im z > 0`. -/
private lemma odp_continuous_offWard {N : ℕ} {z : ℂ} (hz : 0 < z.im) :
    Continuous fun ω : Entries N => offWard (symOfEntries ω) z := by
  have h := ward_continuous_b (N := N) hz z.re
  simpa only [Complex.eta] using h

private lemma odp_continuous_swapBInt {N : ℕ} {F : ℝ → ℝ} (hF : ContDiff ℝ 4 F) {η : ℝ}
    (hη : 0 < η) (p : OffDiag N) (E₁ E₂ : ℝ) :
    Continuous fun ω : Entries N => swapBInt F (symOfEntries ω) p η E₁ E₂ := by
  have hx := ward_continuous_b' (N := N) hη E₁ E₂
  have h1 := (hF.continuous_iteratedDeriv 1 (by norm_num)).comp hx
  have h2 := (hF.continuous_iteratedDeriv 2 (by norm_num)).comp hx
  have hK := odp_continuous_swapK (N := N) hη p E₁ E₂
  unfold swapBInt
  refine Complex.continuous_re.comp ?_
  exact ((Complex.continuous_ofReal.comp h1).mul (continuous_finsetSum _ fun k _ =>
    ((hK k 2 0).add (hK k 1 1)).add (hK k 0 2))).add
    (((Complex.continuous_ofReal.comp h2).div_const 2).mul (((hK 0 1 0).add (hK 0 0 1)).pow 2))

private lemma odp_continuous_swapBPt {N : ℕ} {F : ℝ → ℝ} (hF : ContDiff ℝ 4 F) {z : ℂ}
    (hz : 0 < z.im) (p : OffDiag N) :
    Continuous fun ω : Entries N => swapBPt F (symOfEntries ω) p z := by
  have hx := odp_continuous_offWard (N := N) hz
  have h1 := (hF.continuous_iteratedDeriv 1 (by norm_num)).comp hx
  have h2 := (hF.continuous_iteratedDeriv 2 (by norm_num)).comp hx
  have hK := odp_continuous_swapKpt (N := N) hz p
  unfold swapBPt
  refine Complex.continuous_re.comp ?_
  exact ((Complex.continuous_ofReal.comp h1).mul (continuous_finsetSum _ fun k _ =>
    ((hK k 2 0).add (hK k 1 1)).add (hK k 0 2))).add
    (((Complex.continuous_ofReal.comp h2).div_const 2).mul (((hK 0 1 0).add (hK 0 0 1)).pow 2))

/-! ### The coefficients of (6.69) grouped by the power of the entry -/

/-- `A_m = Σ_{k=0,1} Σ_{s+t=m} K^{(s,t)}_k`, the coefficient of `(-v)^m` in (6.69). -/
private def odpA (K : ℕ → ℕ → ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ k ∈ Finset.range 2, ∑ s ∈ Finset.range (m + 1), K k s (m - s)

/-- The main term of (6.69) as a polynomial in `w = -v`. -/
private lemma odp_sum_eq (K : ℕ → ℕ → ℕ → ℂ) (w : ℂ) :
    (∑ k ∈ Finset.range 2, ∑ s ∈ Finset.range 5, ∑ t ∈ Finset.range 5,
      if 1 ≤ s + t ∧ s + t ≤ 4 then w ^ (s + t) * K k s t else 0) =
      w * odpA K 1 + w ^ 2 * odpA K 2 + w ^ 3 * odpA K 3 + w ^ 4 * odpA K 4 := by
  simp only [odpA, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

/-- The sum in `g` is `A_2`. -/
private lemma odp_A2_eq (K : ℕ → ℕ → ℕ → ℂ) :
    ∑ k ∈ Finset.range 2, (K k 2 0 + K k 1 1 + K k 0 2) = odpA K 2 := by
  simp only [odpA, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

/-- `A_1` splits into its `k = 0` and `k = 1` parts. -/
private lemma odp_A1_eq (K : ℕ → ℕ → ℕ → ℂ) :
    odpA K 1 = (K 0 1 0 + K 0 0 1) + (K 1 1 0 + K 1 0 1) := by
  simp only [odpA, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

/-- `A_3` without the terms `K^{(3,0)}_0 + K^{(0,3)}_0` kept in `g₃`. -/
private lemma odp_A3_eq (K : ℕ → ℕ → ℕ → ℂ) :
    odpA K 3 = (K 0 3 0 + K 0 0 3) +
      (K 0 2 1 + K 0 1 2 + K 1 3 0 + K 1 2 1 + K 1 1 2 + K 1 0 3) := by
  simp only [odpA, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

/-! ### The Taylor expansion of `F` on `Ω`: deterministic algebra -/

/-- `w⁴ ≤ τ² + w⁶/τ` for `τ > 0`. -/
private lemma odp_pow_four_le {w τ : ℝ} (hτ : 0 < τ) : w ^ 4 ≤ τ ^ 2 + w ^ 6 / τ := by
  have key : w ^ 4 * τ ≤ τ ^ 3 + w ^ 6 := by
    by_cases h : w ^ 2 ≤ τ
    · have h4 : w ^ 4 ≤ τ ^ 2 := by
        have := pow_le_pow_left₀ (sq_nonneg w) h 2
        nlinarith
      nlinarith [pow_pos hτ 3, sq_nonneg w]
    · push Not at h
      have : w ^ 4 * τ ≤ w ^ 4 * w ^ 2 := mul_le_mul_of_nonneg_left h.le (by positivity)
      nlinarith [pow_pos hτ 3]
  rw [← sub_le_iff_le_add', le_div_iff₀ hτ]
  nlinarith

/-- The polynomial in `w` of (6.69), `U = Σ_{m ≤ 4} w^m a_m`, is at most `4 B α`. -/
private lemma odp_U_le {w a1 a2 a3 a4 B α : ℝ} (hw : |w| ≤ B) (hB1 : B ≤ 1)
    (h1 : |a1| ≤ α) (h2 : |a2| ≤ α) (h3 : |a3| ≤ α) (h4 : |a4| ≤ α) :
    |w * a1 + w ^ 2 * a2 + w ^ 3 * a3 + w ^ 4 * a4| ≤ 4 * B * α := by
  have hB : 0 ≤ B := (abs_nonneg w).trans hw
  have hα : 0 ≤ α := (abs_nonneg a1).trans h1
  have hw1 : |w| ≤ 1 := hw.trans hB1
  have hp : ∀ n : ℕ, 1 ≤ n → |w| ^ n ≤ B := fun n hn => by
    calc |w| ^ n ≤ |w| ^ 1 := pow_le_pow_of_le_one (abs_nonneg w) hw1 hn
      _ = |w| := pow_one _
      _ ≤ B := hw
  have t : ∀ (n : ℕ) (a : ℝ), 1 ≤ n → |a| ≤ α → |w ^ n * a| ≤ B * α := fun n a hn ha => by
    rw [abs_mul, abs_pow]
    exact mul_le_mul (hp n hn) ha (abs_nonneg _) hB
  have t1 := t 1 a1 le_rfl h1
  rw [pow_one] at t1
  calc _ ≤ |w * a1| + |w ^ 2 * a2| + |w ^ 3 * a3| + |w ^ 4 * a4| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ B * α + B * α + B * α + B * α := by
        gcongr
        exacts [t 2 a2 (by norm_num) h2, t 3 a3 (by norm_num) h3, t 4 a4 (by norm_num) h4]
    _ = 4 * B * α := by ring

/-- The terms of `U² - w² a₁² - 2 w³ a₁ a₂` are of order `w⁴`: at most `16 B⁴ α²`. -/
private lemma odp_U_sq_le {w a1 a2 a3 a4 B α : ℝ} (hw : |w| ≤ B) (hB1 : B ≤ 1)
    (h1 : |a1| ≤ α) (h2 : |a2| ≤ α) (h3 : |a3| ≤ α) (h4 : |a4| ≤ α) :
    |(w * a1 + w ^ 2 * a2 + w ^ 3 * a3 + w ^ 4 * a4) ^ 2 - w ^ 2 * a1 ^ 2 - 2 * w ^ 3 * a1 * a2| ≤
      16 * B ^ 4 * α ^ 2 := by
  have hB : 0 ≤ B := (abs_nonneg w).trans hw
  have hα : 0 ≤ α := (abs_nonneg a1).trans h1
  have hw1 : |w| ≤ 1 := hw.trans hB1
  have hpp : ∀ i j : ℝ, |i| ≤ α → |j| ≤ α → |i * j| ≤ α ^ 2 := fun i j hi hj => by
    rw [abs_mul, sq]; exact mul_le_mul hi hj (abs_nonneg _) hα
  have hwn : ∀ n : ℕ, |w ^ n| ≤ 1 := fun n => by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg w) hw1
  have hS : |a2 * a2 + 2 * (a1 * a3) + w * (2 * (a1 * a4) + 2 * (a2 * a3)) +
      w ^ 2 * (2 * (a2 * a4) + a3 * a3) + w ^ 3 * (2 * (a3 * a4)) + w ^ 4 * (a4 * a4)| ≤
      13 * α ^ 2 := by
    have e1 := hpp a2 a2 h2 h2
    have e2 := hpp a1 a3 h1 h3
    have e3 := hpp a1 a4 h1 h4
    have e4 := hpp a2 a3 h2 h3
    have e5 := hpp a2 a4 h2 h4
    have e6 := hpp a3 a3 h3 h3
    have e7 := hpp a3 a4 h3 h4
    have e8 := hpp a4 a4 h4 h4
    have m : ∀ (n : ℕ) (c : ℝ), |w ^ n * c| ≤ |c| := fun n c => by
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (hwn n)
    have m1 := m 1 (2 * (a1 * a4) + 2 * (a2 * a3))
    rw [pow_one] at m1
    have m2 := m 2 (2 * (a2 * a4) + a3 * a3)
    have m3 := m 3 (2 * (a3 * a4))
    have m4 := m 4 (a4 * a4)
    have f1 : |2 * (a1 * a4) + 2 * (a2 * a3)| ≤ 4 * α ^ 2 := by
      have := abs_add_le (2 * (a1 * a4)) (2 * (a2 * a3))
      rw [abs_mul 2 (a1 * a4), abs_mul 2 (a2 * a3), abs_two] at this
      linarith
    have f2 : |2 * (a2 * a4) + a3 * a3| ≤ 3 * α ^ 2 := by
      have := abs_add_le (2 * (a2 * a4)) (a3 * a3)
      rw [abs_mul 2 (a2 * a4), abs_two] at this
      linarith
    have f3 : |2 * (a3 * a4)| ≤ 2 * α ^ 2 := by rw [abs_mul 2 (a3 * a4), abs_two]; linarith
    have f0 : |2 * (a1 * a3)| ≤ 2 * α ^ 2 := by rw [abs_mul 2 (a1 * a3), abs_two]; linarith
    calc _ ≤ |a2 * a2| + |2 * (a1 * a3)| + |w * (2 * (a1 * a4) + 2 * (a2 * a3))| +
          |w ^ 2 * (2 * (a2 * a4) + a3 * a3)| + |w ^ 3 * (2 * (a3 * a4))| +
          |w ^ 4 * (a4 * a4)| := by
          refine (abs_add_le _ _).trans ?_; gcongr
          refine (abs_add_le _ _).trans ?_; gcongr
          refine (abs_add_le _ _).trans ?_; gcongr
          refine (abs_add_le _ _).trans ?_; gcongr
          exact abs_add_le _ _
      _ ≤ 13 * α ^ 2 := by linarith
  have e : (w * a1 + w ^ 2 * a2 + w ^ 3 * a3 + w ^ 4 * a4) ^ 2 - w ^ 2 * a1 ^ 2 -
      2 * w ^ 3 * a1 * a2 = w ^ 4 * (a2 * a2 + 2 * (a1 * a3) + w * (2 * (a1 * a4) + 2 * (a2 * a3)) +
      w ^ 2 * (2 * (a2 * a4) + a3 * a3) + w ^ 3 * (2 * (a3 * a4)) + w ^ 4 * (a4 * a4)) := by ring
  rw [e, abs_mul, abs_pow]
  calc |w| ^ 4 * _ ≤ B ^ 4 * (13 * α ^ 2) :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg w) hw 4) hS (abs_nonneg _) (by positivity)
    _ ≤ 16 * B ^ 4 * α ^ 2 := by nlinarith [pow_nonneg hB 4, sq_nonneg α]

/-- [16] (6.63)–(6.74) on `Ω` for one `ω`, as algebra: with `Δ = x_S - x_R`, the third-order Taylor
expansion of `F` around `x_R` (derivatives `f₁, f₂` at `x_R`, `f₃` at an intermediate point) minus
`Σ_{m ≤ 4} w^m c_m` is at most the sum of the remainders of (6.69), of the dropped terms of order
`w⁴` and `w² a₁^{(1)}`, and of the cube `Δ³`. -/
private lemma odp_taylor_alg {Δ w a1 a2 a3 a4 α0 f1 f2 f3 T₀ B α β G : ℝ}
    (hΔ : |Δ - (w * a1 + w ^ 2 * a2 + w ^ 3 * a3 + w ^ 4 * a4)| ≤ T₀) (hw : |w| ≤ B)
    (hB1 : B ≤ 1) (h1 : |a1| ≤ α) (h2 : |a2| ≤ α) (h3 : |a3| ≤ α) (h4 : |a4| ≤ α)
    (hβ : |a1 - α0| ≤ β) (hf1 : |f1| ≤ G) (hf2 : |f2| ≤ G) (hf3 : |f3| ≤ G) :
    |Δ| ≤ 4 * B * α + T₀ ∧
    |f1 * Δ + f2 * Δ ^ 2 / 2 + f3 * Δ ^ 3 / 6 -
        (w * (f1 * a1) + w ^ 2 * (f1 * a2 + f2 / 2 * α0 ^ 2) + w ^ 3 * (f1 * a3 + f2 * a1 * a2) +
          w ^ 4 * (f1 * a4))| ≤
      G * T₀ + G / 2 * (16 * B ^ 4 * α ^ 2 + B ^ 2 * β * (2 * α + β) + T₀ * (8 * B * α + T₀)) +
        G / 6 * (4 * B * α + T₀) ^ 3 := by
  have hB : 0 ≤ B := (abs_nonneg w).trans hw
  have hα : 0 ≤ α := (abs_nonneg a1).trans h1
  have hβ0 : 0 ≤ β := (abs_nonneg _).trans hβ
  have hT₀ : 0 ≤ T₀ := (abs_nonneg _).trans hΔ
  have hG : 0 ≤ G := (abs_nonneg f1).trans hf1
  set U := w * a1 + w ^ 2 * a2 + w ^ 3 * a3 + w ^ 4 * a4 with hU
  have hUb := odp_U_le hw hB1 h1 h2 h3 h4
  have hUsq := odp_U_sq_le hw hB1 h1 h2 h3 h4
  have hD : |Δ| ≤ 4 * B * α + T₀ := by
    have := abs_sub_abs_le_abs_sub Δ U
    linarith
  refine ⟨hD, ?_⟩
  have hsum : |Δ + U| ≤ 8 * B * α + T₀ := by
    have := abs_add_le Δ U
    linarith
  have hsq : |(Δ - U) * (Δ + U)| ≤ T₀ * (8 * B * α + T₀) := by
    rw [abs_mul]; exact mul_le_mul hΔ hsum (abs_nonneg _) hT₀
  have hw2 : |w ^ 2| ≤ B ^ 2 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg w) hw 2
  have ha1 : |a1 + α0| ≤ 2 * α + β := by
    have e : a1 + α0 = 2 * a1 - (a1 - α0) := by ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_two]; linarith
  have hlin : |w ^ 2 * ((a1 - α0) * (a1 + α0))| ≤ B ^ 2 * β * (2 * α + β) := by
    rw [abs_mul, abs_mul, mul_assoc]
    exact mul_le_mul hw2 (mul_le_mul hβ ha1 (abs_nonneg _) hβ0)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)
  have key : f1 * Δ + f2 * Δ ^ 2 / 2 + f3 * Δ ^ 3 / 6 -
      (w * (f1 * a1) + w ^ 2 * (f1 * a2 + f2 / 2 * α0 ^ 2) + w ^ 3 * (f1 * a3 + f2 * a1 * a2) +
        w ^ 4 * (f1 * a4)) =
      f1 * (Δ - U) + f2 / 2 * ((U ^ 2 - w ^ 2 * a1 ^ 2 - 2 * w ^ 3 * a1 * a2) +
        (Δ - U) * (Δ + U) + w ^ 2 * ((a1 - α0) * (a1 + α0))) + f3 * Δ ^ 3 / 6 := by
    rw [hU]; ring
  rw [key]
  have hmid : |(U ^ 2 - w ^ 2 * a1 ^ 2 - 2 * w ^ 3 * a1 * a2) + (Δ - U) * (Δ + U) +
      w ^ 2 * ((a1 - α0) * (a1 + α0))| ≤
      16 * B ^ 4 * α ^ 2 + B ^ 2 * β * (2 * α + β) + T₀ * (8 * B * α + T₀) := by
    refine (abs_add_le _ _).trans ?_
    have := abs_add_le (U ^ 2 - w ^ 2 * a1 ^ 2 - 2 * w ^ 3 * a1 * a2) ((Δ - U) * (Δ + U))
    linarith
  have hcube : |Δ ^ 3| ≤ (4 * B * α + T₀) ^ 3 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hD 3
  have t1 : |f1 * (Δ - U)| ≤ G * T₀ := by
    rw [abs_mul]; exact mul_le_mul hf1 hΔ (abs_nonneg _) hG
  have t2 : |f2 / 2 * ((U ^ 2 - w ^ 2 * a1 ^ 2 - 2 * w ^ 3 * a1 * a2) + (Δ - U) * (Δ + U) +
      w ^ 2 * ((a1 - α0) * (a1 + α0)))| ≤
      G / 2 * (16 * B ^ 4 * α ^ 2 + B ^ 2 * β * (2 * α + β) + T₀ * (8 * B * α + T₀)) := by
    rw [abs_mul, abs_div, abs_two]
    exact mul_le_mul (by linarith) hmid (abs_nonneg _) (by positivity)
  have t3 : |f3 * Δ ^ 3 / 6| ≤ G / 6 * (4 * B * α + T₀) ^ 3 := by
    rw [abs_div, abs_mul, show |(6 : ℝ)| = 6 by norm_num]
    have := mul_le_mul hf3 hcube (abs_nonneg _) hG
    linarith
  calc _ ≤ |f1 * (Δ - U)| + |f2 / 2 * ((U ^ 2 - w ^ 2 * a1 ^ 2 - 2 * w ^ 3 * a1 * a2) +
        (Δ - U) * (Δ + U) + w ^ 2 * ((a1 - α0) * (a1 + α0)))| + |f3 * Δ ^ 3 / 6| := by
        refine (abs_add_le _ _).trans ?_; gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

/-! ### Sizes of the coefficients `K^{(s,t)}_k(Q)` on `Ω`: [16] (6.59)–(6.68) -/

-- The pair count `|{(i, j) : i ≠ j, swapIdx p i j = k}| ≤ 4 N^{2-k}` and the bounds on `Ω`.
open private ode_good ode_count ode_window ode_weight ode_weight_sq from
  WEdgeNS.EdgeUniv.OffDiagExpansion

/-- The bound `X_m` for one entry `((R I_e)^m R)_ij`, `i ≠ j`, `k = swapIdx p i j`: `P` for `m = 0`
and `2^9 P^{2-k}` for `1 ≤ m ≤ 4`. -/
private def odpX (P : ℝ) (k m : ℕ) : ℝ := if m = 0 then P else 2 ^ 9 * P ^ (2 - k)

private lemma odpX_nonneg {P : ℝ} (hP : 0 ≤ P) (k m : ℕ) : 0 ≤ odpX P k m := by
  unfold odpX; split_ifs <;> positivity

/-- [16] (6.59)–(6.60) for `m ≤ 4` and `i ≠ j`, including `m = 0`. -/
private lemma odp_coeff_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ} {P : ℝ} (hP : 0 ≤ P)
    (hP1 : P ≤ 1) (hR : ∀ k l, ‖resolventC H z k l‖ ≤ 2)
    (hR' : ∀ k l, k ≠ l → ‖resolventC H z k l‖ ≤ P) (p : OffDiag N) {m : ℕ} (hm : m ≤ 4)
    {i j : Fin N} (hij : i ≠ j) :
    ‖swapCoeff H (Sum.inr p) z m i j‖ ≤ odpX P (swapIdx p i j) m := by
  unfold odpX
  split_ifs with h0
  · subst h0
    simpa [swapCoeff] using hR' i j hij
  · have h := norm_mul_entryMat_pow_mul_apply_le hP (by linarith) hR hR' hR hR' p
      (Nat.one_le_iff_ne_zero.2 h0) i j
    calc _ ≤ _ := h
      _ ≤ 2 ^ 9 * P ^ (2 - swapIdx p i j) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)

/-- The sum over the pairs of one part `k`: `‖Σ_{i ≠ j, swapIdx = k} c_s conj c_t‖ ≤
4 N^{2-k} X_s X_t`. -/
private lemma odp_inner_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ} {P : ℝ} (hP : 0 ≤ P)
    (hP1 : P ≤ 1) (hR : ∀ k l, ‖resolventC H z k l‖ ≤ 2)
    (hR' : ∀ k l, k ≠ l → ‖resolventC H z k l‖ ≤ P) (p : OffDiag N) {k s t : ℕ} (hk : k ≤ 2)
    (hs : s ≤ 4) (ht : t ≤ 4) :
    ‖∑ i, ∑ j, if i ≠ j ∧ swapIdx p i j = k then
        swapCoeff H (Sum.inr p) z s i j * (starRingEnd ℂ) (swapCoeff H (Sum.inr p) z t i j)
        else 0‖ ≤ 4 * (N : ℝ) ^ (2 - k) * (odpX P k s * odpX P k t) := by
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => norm_sum_le _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_)
    (ode_count p hk (mul_nonneg (odpX_nonneg hP k s) (odpX_nonneg hP k t)))
  split_ifs with h
  · obtain ⟨hij, hk'⟩ := h
    rw [norm_mul, Complex.norm_conj, ← hk']
    exact mul_le_mul (odp_coeff_le hP hP1 hR hR' p hs hij) (odp_coeff_le hP hP1 hR hR' p ht hij)
      (norm_nonneg _) (odpX_nonneg hP _ _)
  · simp

/-- From the bounds `‖K^{(s,t)}_k‖ ≤ W 4 N^{2-k} X_s X_t` with `W ≤ 2N^{-4/3}`,
`P = N^{-1/3+3ε}` (written with `z = N^{-1/3}`, `y = N^ε`): `|A_m| ≤ 2^25 N^{-1/3+9ε}`,
`|A_1^{(1)}| ≤ 2^22 N^{-1+6ε}`, and the part of `A_3` without `K^{(3,0)}_0 + K^{(0,3)}_0` is at
most `2^24 N^{-2/3+12ε}`. -/
private lemma odp_sizes {N : ℕ} {K : ℕ → ℕ → ℕ → ℂ} {z y P W : ℝ} (hN : 1 ≤ N)
    (hxz : (N : ℝ) * z ^ 3 = 1) (hz : 0 ≤ z) (hy : 1 ≤ y) (hP : P = z * y ^ 3) (hP1 : P ≤ 1)
    (hW : W ≤ 2 * z ^ 4)
    (hK : ∀ k ≤ 1, ∀ s ≤ 4, ∀ t ≤ 4,
      ‖K k s t‖ ≤ W * (4 * (N : ℝ) ^ (2 - k) * (odpX P k s * odpX P k t))) :
    (∀ m, 1 ≤ m → m ≤ 4 → |(odpA K m).re| ≤ 2 ^ 25 * z * y ^ 9) ∧
    |(K 1 1 0 + K 1 0 1).re| ≤ 2 ^ 22 * z ^ 3 * y ^ 6 ∧
    |(K 0 2 1 + K 0 1 2 + K 1 3 0 + K 1 2 1 + K 1 1 2 + K 1 0 3).re| ≤ 2 ^ 24 * z ^ 2 * y ^ 12 := by
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hz1 : z ≤ 1 := by
    by_contra h
    push Not at h
    have : 1 < z ^ 3 := one_lt_pow₀ h (by norm_num)
    nlinarith
  have hy0 : 0 ≤ y := by linarith
  -- the three basic bounds
  have hXX : ∀ k s t, 0 ≤ odpX P k s * odpX P k t := fun k s t =>
    mul_nonneg (odpX_nonneg hP0 _ _) (odpX_nonneg hP0 _ _)
  have b0 : ∀ s ≤ 4, ∀ t ≤ 4, 1 ≤ s + t → ‖K 0 s t‖ ≤ 2 ^ 21 * z * y ^ 9 := by
    intro s hs t ht hst
    have hX : odpX P 0 s * odpX P 0 t ≤ 2 ^ 18 * P ^ 3 := by
      unfold odpX
      split_ifs with h1 h2 h2
      · omega
      · simp only [Nat.sub_zero]; nlinarith [pow_nonneg hP0 3]
      · simp only [Nat.sub_zero]; nlinarith [pow_nonneg hP0 3]
      · simp only [Nat.sub_zero]
        have : P ^ 4 ≤ P ^ 3 := pow_le_pow_of_le_one hP0 hP1 (by norm_num)
        nlinarith
    have h := hK 0 (by norm_num) s hs t ht
    simp only [Nat.sub_zero] at h
    calc ‖K 0 s t‖ ≤ W * (4 * (N : ℝ) ^ 2 * (odpX P 0 s * odpX P 0 t)) := h
      _ ≤ (2 * z ^ 4) * (4 * (N : ℝ) ^ 2 * (2 ^ 18 * P ^ 3)) :=
          mul_le_mul hW (mul_le_mul_of_nonneg_left hX (by positivity))
            (mul_nonneg (by positivity) (hXX 0 s t)) (by positivity)
      _ = 2 ^ 21 * ((N : ℝ) * z ^ 3) ^ 2 * z * y ^ 9 := by rw [hP]; ring
      _ = 2 ^ 21 * z * y ^ 9 := by rw [hxz]; ring
  have b0' : ∀ s ≤ 4, ∀ t ≤ 4, 1 ≤ s → 1 ≤ t → ‖K 0 s t‖ ≤ 2 ^ 21 * z ^ 2 * y ^ 12 := by
    intro s hs t ht h1 h2
    have hX : odpX P 0 s * odpX P 0 t = 2 ^ 18 * P ^ 4 := by
      unfold odpX
      split_ifs <;> first | omega | ring
    have h := hK 0 (by norm_num) s hs t ht
    simp only [Nat.sub_zero] at h
    rw [hX] at h
    calc ‖K 0 s t‖ ≤ W * (4 * (N : ℝ) ^ 2 * (2 ^ 18 * P ^ 4)) := h
      _ ≤ (2 * z ^ 4) * (4 * (N : ℝ) ^ 2 * (2 ^ 18 * P ^ 4)) :=
          mul_le_mul_of_nonneg_right hW (by positivity)
      _ = 2 ^ 21 * ((N : ℝ) * z ^ 3) ^ 2 * z ^ 2 * y ^ 12 := by rw [hP]; ring
      _ = 2 ^ 21 * z ^ 2 * y ^ 12 := by rw [hxz]; ring
  have b1 : ∀ s ≤ 4, ∀ t ≤ 4, ‖K 1 s t‖ ≤ 2 ^ 21 * z ^ 3 * y ^ 6 := by
    intro s hs t ht
    have hX1 : ∀ m, odpX P 1 m ≤ 2 ^ 9 * P := fun m => by
      unfold odpX; split_ifs
      · linarith
      · simp
    have hX : odpX P 1 s * odpX P 1 t ≤ 2 ^ 18 * P ^ 2 := by
      have := mul_le_mul (hX1 s) (hX1 t) (odpX_nonneg hP0 _ _) (by positivity)
      nlinarith
    have h := hK 1 le_rfl s hs t ht
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h
    calc ‖K 1 s t‖ ≤ W * (4 * (N : ℝ) * (odpX P 1 s * odpX P 1 t)) := h
      _ ≤ (2 * z ^ 4) * (4 * (N : ℝ) * (2 ^ 18 * P ^ 2)) :=
          mul_le_mul hW (mul_le_mul_of_nonneg_left hX (by positivity))
            (mul_nonneg (by positivity) (hXX 1 s t)) (by positivity)
      _ = 2 ^ 21 * ((N : ℝ) * z ^ 3) * z ^ 3 * y ^ 6 := by rw [hP]; ring
      _ = 2 ^ 21 * z ^ 3 * y ^ 6 := by rw [hxz]; ring
  have c1 : z ^ 3 * y ^ 6 ≤ z ^ 2 * y ^ 12 := by
    have : z ^ 3 ≤ z ^ 2 := pow_le_pow_of_le_one hz hz1 (by norm_num)
    have : y ^ 6 ≤ y ^ 12 := pow_le_pow_right₀ hy (by norm_num)
    gcongr
  have c2 : z ^ 2 * y ^ 12 ≤ z * y ^ 9 := by
    have : z * y ^ 3 ≤ 1 := hP ▸ hP1
    have e : z ^ 2 * y ^ 12 = (z * y ^ 9) * (z * y ^ 3) := by ring
    rw [e]
    exact mul_le_of_le_one_right (by positivity) this
  have bb : ∀ k < 2, ∀ s ≤ 4, ∀ t ≤ 4, 1 ≤ s + t → ‖K k s t‖ ≤ 2 ^ 21 * z * y ^ 9 := by
    intro k hk s hs t ht hst
    interval_cases k
    · exact b0 s hs t ht hst
    · exact (b1 s hs t ht).trans (by nlinarith)
  refine ⟨fun m hm1 hm4 => ?_, ?_, ?_⟩
  · refine (Complex.abs_re_le_norm _).trans ?_
    unfold odpA
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k hk => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun s hs => bb k (Finset.mem_range.1 hk) s
        (by have := Finset.mem_range.1 hs; omega) (m - s) (by omega)
        (by have := Finset.mem_range.1 hs; omega))).trans ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hm : ((m : ℝ) + 1) ≤ 5 := by exact_mod_cast (by omega : m + 1 ≤ 5)
    push_cast
    have : 0 ≤ 2 ^ 21 * z * y ^ 9 := by positivity
    nlinarith
  · refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans ?_)
    have := b1 1 (by norm_num) 0 (by norm_num)
    have := b1 0 (by norm_num) 1 (by norm_num)
    have : 0 ≤ z ^ 3 * y ^ 6 := by positivity
    linarith
  · refine (Complex.abs_re_le_norm _).trans ?_
    have e1 := b0' 2 (by norm_num) 1 (by norm_num) (by norm_num) (by norm_num)
    have e2 := b0' 1 (by norm_num) 2 (by norm_num) (by norm_num) (by norm_num)
    have e3 := b1 3 (by norm_num) 0 (by norm_num)
    have e4 := b1 2 (by norm_num) 1 (by norm_num)
    have e5 := b1 1 (by norm_num) 2 (by norm_num)
    have e6 := b1 0 (by norm_num) 3 (by norm_num)
    have n1 := norm_add_le (K 0 2 1 + K 0 1 2 + K 1 3 0 + K 1 2 1 + K 1 1 2) (K 1 0 3)
    have n2 := norm_add_le (K 0 2 1 + K 0 1 2 + K 1 3 0 + K 1 2 1) (K 1 1 2)
    have n3 := norm_add_le (K 0 2 1 + K 0 1 2 + K 1 3 0) (K 1 2 1)
    have n4 := norm_add_le (K 0 2 1 + K 0 1 2) (K 1 3 0)
    have n5 := norm_add_le (K 0 2 1) (K 0 1 2)
    have : 0 ≤ z ^ 2 * y ^ 12 := by positivity
    linarith

/-- On `Ω`, the coefficients of the functional `η² Σ_{i ≠ j} |G_ij(z)|²` at `z = E + iη`,
`E ∈ I_ε`: `‖K^{(s,t)}_k(Q)‖ ≤ η² 4 N^{2-k} X_s X_t`. -/
private lemma odp_Kpt_le {N : ℕ} (hN : 1 ≤ N) {ε φs : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 10)
    {ω : Entries N} {p : OffDiag N} (hω : ω ∈ swapEvent N ε φs (Sum.inr p))
    (hRb : ∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) → ∀ k l,
      ‖resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l -
          (if k = l then msc ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ else 0)‖ ≤
        (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε))
    {E : ℝ} (hE : |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε))
    (hP1 : (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) ≤ 1) :
    ∀ k ≤ 1, ∀ s ≤ 4, ∀ t ≤ 4,
      ‖swapKpt (symOfEntries (zeroEntry (Sum.inr p) ω)) p ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k s t‖ ≤
        ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) ^ 2 *
          (4 * (N : ℝ) ^ (2 - k) * (odpX ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) k s *
            odpX ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) k t)) := by
  intro k hk s hs t ht
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨-, -, hR, hR'⟩ := ode_good hN hε hε' hω hRb hE
  unfold swapKpt
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
  exact mul_le_mul_of_nonneg_left (odp_inner_le (Real.rpow_pos_of_pos hn0 _).le hP1 hR hR' p
    (by omega) hs ht) (by positivity)

/-- On `Ω`, the coefficients of the functional (6.56) on `[E₁, E₂] ⊂ I_ε`:
`‖K^{(s,t)}_k(Q)‖ ≤ η |E₂ - E₁| 4 N^{2-k} X_s X_t`. -/
private lemma odp_K_le {N : ℕ} (hN : 1 ≤ N) {ε φs : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 10)
    {ω : Entries N} {p : OffDiag N} (hω : ω ∈ swapEvent N ε φs (Sum.inr p))
    (hRb : ∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) → ∀ k l,
      ‖resolventC (symOfEntries (zeroEntry (Sum.inr p) ω)) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l -
          (if k = l then msc ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ else 0)‖ ≤
        (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε))
    {E₁ E₂ : ℝ} (h1 : |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε))
    (h2 : |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε))
    (hP1 : (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) ≤ 1) :
    ∀ k ≤ 1, ∀ s ≤ 4, ∀ t ≤ 4,
      ‖swapK (symOfEntries (zeroEntry (Sum.inr p) ω)) p ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂
          k s t‖ ≤
        ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε) * |E₂ - E₁|) *
          (4 * (N : ℝ) ^ (2 - k) * (odpX ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) k s *
            odpX ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) k t)) := by
  intro k hk s hs t ht
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hη := Real.rpow_pos_of_pos hn0 (-(2 : ℝ) / 3 - ε)
  unfold swapK
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hη.le
  rw [mul_comm]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
  obtain ⟨-, -, hR, hR'⟩ := ode_good hN hε hε' hω hRb (ode_window h1 h2 hy)
  exact odp_inner_le (Real.rpow_pos_of_pos hn0 _).le hP1 hR hR' p (by omega) hs ht

/-! ### Deterministic bounds for every `H` -/

-- `((A I_e) M)_ij = A_ib M_dj + A_id M_bj`.
open private ode_mul_entryMat_mul_apply from WEdgeNS.EdgeUniv.OffDiagExpansion

/-- `|((R I_e)^m R)_ij| ≤ 2^m η^{-(m+1)}` for every symmetric `H`, `R = G(H)(z)`, `η = Im z`. -/
private lemma odp_coeff_global {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (p : OffDiag N) (m : ℕ) (i j : Fin N) :
    ‖swapCoeff H (Sum.inr p) z m i j‖ ≤ 2 ^ m * (1 / z.im) ^ (m + 1) := by
  have hb := norm_resolventC_apply_le hH hz
  have hη : 0 ≤ 1 / z.im := by positivity
  induction m generalizing i j with
  | zero => simpa [swapCoeff] using hb i j
  | succ m ih =>
    have e : swapCoeff H (Sum.inr p) z (m + 1) =
        (resolventC H z * (entryMat (Sum.inr p)).map (fun x : ℝ => (x : ℂ))) *
          swapCoeff H (Sum.inr p) z m := by
      unfold swapCoeff; rw [pow_succ', Matrix.mul_assoc]
    rw [e, ode_mul_entryMat_mul_apply]
    calc _ ≤ ‖resolventC H z i p.1.1‖ * ‖swapCoeff H (Sum.inr p) z m p.1.2 j‖ +
          ‖resolventC H z i p.1.2‖ * ‖swapCoeff H (Sum.inr p) z m p.1.1 j‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ (1 / z.im) * (2 ^ m * (1 / z.im) ^ (m + 1)) +
          (1 / z.im) * (2 ^ m * (1 / z.im) ^ (m + 1)) :=
          add_le_add (mul_le_mul (hb _ _) (ih _ _) (norm_nonneg _) hη)
            (mul_le_mul (hb _ _) (ih _ _) (norm_nonneg _) hη)
      _ = 2 ^ (m + 1) * (1 / z.im) ^ (m + 1 + 1) := by ring

/-- `‖Σ_{i ≠ j, swapIdx = k} c_s conj c_t‖ ≤ N² 2^{s+t} η^{-(s+t+2)}` for every symmetric `H`. -/
private lemma odp_inner_global {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (p : OffDiag N) (k s t : ℕ) :
    ‖∑ i, ∑ j, if i ≠ j ∧ swapIdx p i j = k then
        swapCoeff H (Sum.inr p) z s i j * (starRingEnd ℂ) (swapCoeff H (Sum.inr p) z t i j)
        else 0‖ ≤ (N : ℝ) ^ 2 * (2 ^ (s + t) * (1 / z.im) ^ (s + t + 2)) := by
  have hη : 0 ≤ 1 / z.im := by positivity
  have hterm : ∀ i j : Fin N, ‖(if i ≠ j ∧ swapIdx p i j = k then
      swapCoeff H (Sum.inr p) z s i j * (starRingEnd ℂ) (swapCoeff H (Sum.inr p) z t i j)
      else 0)‖ ≤ 2 ^ (s + t) * (1 / z.im) ^ (s + t + 2) := by
    intro i j
    split_ifs
    · rw [norm_mul, Complex.norm_conj]
      calc _ ≤ (2 ^ s * (1 / z.im) ^ (s + 1)) * (2 ^ t * (1 / z.im) ^ (t + 1)) :=
            mul_le_mul (odp_coeff_global hH hz p s i j) (odp_coeff_global hH hz p t i j)
              (norm_nonneg _) (by positivity)
        _ = 2 ^ (s + t) * (1 / z.im) ^ (s + t + 2) := by ring
    · simp only [norm_zero]; positivity
  calc _ ≤ ∑ i : Fin N, ∑ j : Fin N, (2 ^ (s + t) * (1 / z.im) ^ (s + t + 2)) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm i j))
    _ = (N : ℝ) ^ 2 * (2 ^ (s + t) * (1 / z.im) ^ (s + t + 2)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- `2^{s+t} η^{-(s+t)} ≤ 16 N⁴` for `s + t ≤ 4` and `η⁻¹ ≤ N`. -/
private lemma odp_pow_le {N : ℕ} (hN : 1 ≤ N) {η : ℝ} (hη : 0 < η) (hηN : 1 / η ≤ N) {n : ℕ}
    (hn : n ≤ 4) : 2 ^ n * (1 / η) ^ n ≤ 16 * (N : ℝ) ^ 4 := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h0 : 0 ≤ 1 / η := by positivity
  calc 2 ^ n * (1 / η) ^ n = (2 * (1 / η)) ^ n := by rw [mul_pow]
    _ ≤ (2 * (N : ℝ)) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
    _ ≤ (2 * (N : ℝ)) ^ 4 := pow_le_pow_right₀ (by linarith) hn
    _ = 16 * (N : ℝ) ^ 4 := by ring

/-- Every coefficient of the functional `η² Σ_{i ≠ j} |G_ij(z)|²` with `s + t ≤ 4` is at most
`32 N⁸` once `η⁻¹ ≤ N`. -/
private lemma odp_Kpt_global {N : ℕ} (hN : 1 ≤ N) {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (hηN : 1 / z.im ≤ N) (p : OffDiag N)
    {k s t : ℕ} (hst : s + t ≤ 4) : ‖swapKpt H p z k s t‖ ≤ 32 * (N : ℝ) ^ 8 := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold swapKpt
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz]
  have hi := odp_inner_global hH hz p k s t
  have hp := odp_pow_le hN hz hηN hst
  have e : z.im ^ 2 * ((N : ℝ) ^ 2 * (2 ^ (s + t) * (1 / z.im) ^ (s + t + 2))) =
      (N : ℝ) ^ 2 * (2 ^ (s + t) * (1 / z.im) ^ (s + t)) := by
    have h2 : z.im ^ 2 * (1 / z.im) ^ 2 = 1 := by field_simp
    calc _ = (N : ℝ) ^ 2 * (2 ^ (s + t) * (1 / z.im) ^ (s + t)) * (z.im ^ 2 * (1 / z.im) ^ 2) := by
          ring
      _ = _ := by rw [h2, mul_one]
  calc _ ≤ z.im ^ 2 * ((N : ℝ) ^ 2 * (2 ^ (s + t) * (1 / z.im) ^ (s + t + 2))) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := e
    _ ≤ (N : ℝ) ^ 2 * (16 * (N : ℝ) ^ 4) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ 32 * (N : ℝ) ^ 8 := by
        have : (N : ℝ) ^ 6 ≤ (N : ℝ) ^ 8 := pow_le_pow_right₀ hn1 (by norm_num)
        have e6 : (N : ℝ) ^ 2 * (16 * (N : ℝ) ^ 4) = 16 * (N : ℝ) ^ 6 := by ring
        have : (0 : ℝ) ≤ (N : ℝ) ^ 8 := by positivity
        linarith

/-- Every coefficient of the functional (6.56) with `s + t ≤ 4` is at most `32 N⁸` once
`η⁻¹ ≤ N` and `η |E₂ - E₁| ≤ 2`. -/
private lemma odp_K_global {N : ℕ} (hN : 1 ≤ N) {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {η : ℝ} (hη : 0 < η) (hηN : 1 / η ≤ N) {E₁ E₂ : ℝ}
    (hW : η * |E₂ - E₁| ≤ 2) (p : OffDiag N) {k s t : ℕ} (hst : s + t ≤ 4) :
    ‖swapK H p η E₁ E₂ k s t‖ ≤ 32 * (N : ℝ) ^ 8 := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hi0 : 0 ≤ 1 / η := by positivity
  unfold swapK
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := E₁) (b := E₂)
    (C := (N : ℝ) ^ 2 * (2 ^ (s + t) * (1 / η) ^ (s + t + 2)))
    (f := fun y : ℝ => ∑ i, ∑ j, if i ≠ j ∧ swapIdx p i j = k then
      swapCoeff H (Sum.inr p) ⟨y, η⟩ s i j * (starRingEnd ℂ) (swapCoeff H (Sum.inr p) ⟨y, η⟩ t i j)
      else 0) fun y _ => odp_inner_global hH (z := ⟨y, η⟩) hη p k s t
  have hp := odp_pow_le hN hη hηN hst
  have hη2 : (1 / η) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hi0 hηN 2
  have hW0 : 0 ≤ η * |E₂ - E₁| := by positivity
  calc η * ‖_‖ ≤ η * ((N : ℝ) ^ 2 * (2 ^ (s + t) * (1 / η) ^ (s + t + 2)) * |E₂ - E₁|) :=
        mul_le_mul_of_nonneg_left hint hη.le
    _ = (η * |E₂ - E₁|) * ((N : ℝ) ^ 2 * (2 ^ (s + t) * (1 / η) ^ (s + t)) * (1 / η) ^ 2) := by
        ring
    _ ≤ 2 * ((N : ℝ) ^ 2 * (16 * (N : ℝ) ^ 4) * (N : ℝ) ^ 2) := by
        refine mul_le_mul hW (mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hη2
          (by positivity) (by positivity)) (by positivity) (by norm_num)
    _ = 32 * (N : ℝ) ^ 8 := by ring

/-- `0 ≤ Σ_{i ≠ j} |G_ij|² ≤ N² η⁻²` for every symmetric `H`. -/
private lemma odp_offsum_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) :
    0 ≤ (∑ i, ∑ j, if i = j then (0 : ℝ) else ‖resolventC H z i j‖ ^ 2) ∧
      (∑ i, ∑ j, if i = j then (0 : ℝ) else ‖resolventC H z i j‖ ^ 2) ≤
        (N : ℝ) ^ 2 * (1 / z.im) ^ 2 := by
  have hb := norm_resolventC_apply_le hH hz
  refine ⟨Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> positivity,
    ?_⟩
  calc _ ≤ ∑ _i : Fin N, ∑ _j : Fin N, (1 / z.im) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        split_ifs
        · positivity
        · exact pow_le_pow_left₀ (norm_nonneg _) (hb i j) 2
    _ = (N : ℝ) ^ 2 * (1 / z.im) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- `|offWard| ≤ 32 N⁸` for every symmetric `H`. -/
private lemma odp_offWard_global {N : ℕ} (hN : 1 ≤ N) {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) : |offWard H z| ≤ 32 * (N : ℝ) ^ 8 := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨h0, h1⟩ := odp_offsum_le hH hz
  unfold offWard
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) h0)]
  have e : z.im ^ 2 * ((N : ℝ) ^ 2 * (1 / z.im) ^ 2) = (N : ℝ) ^ 2 := by field_simp
  calc _ ≤ z.im ^ 2 * ((N : ℝ) ^ 2 * (1 / z.im) ^ 2) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = (N : ℝ) ^ 2 := e
    _ ≤ 32 * (N : ℝ) ^ 8 := by
        have : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 8 := pow_le_pow_right₀ hn1 (by norm_num)
        nlinarith

/-- `|offWardInt| ≤ 32 N⁸` for every symmetric `H` once `η⁻¹ ≤ N` and `η |E₂ - E₁| ≤ 2`. -/
private lemma odp_offWardInt_global {N : ℕ} (hN : 1 ≤ N) {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {η : ℝ} (hη : 0 < η) (hηN : 1 / η ≤ N) {E₁ E₂ : ℝ}
    (hW : η * |E₂ - E₁| ≤ 2) : |offWardInt H η E₁ E₂| ≤ 32 * (N : ℝ) ^ 8 := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hi0 : 0 ≤ 1 / η := by positivity
  unfold offWardInt
  rw [abs_mul, abs_of_pos hη]
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := E₁) (b := E₂)
    (C := (N : ℝ) ^ 2 * (1 / η) ^ 2)
    (f := fun y : ℝ => ∑ i, ∑ j, if i = j then (0 : ℝ) else ‖resolventC H ⟨y, η⟩ i j‖ ^ 2)
    fun y _ => by
      obtain ⟨h0, h1⟩ := odp_offsum_le hH (z := ⟨y, η⟩) hη
      rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  rw [Real.norm_eq_abs] at hint
  have hη2 : (1 / η) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hi0 hηN 2
  have hW0 : 0 ≤ η * |E₂ - E₁| := by positivity
  calc η * |_| ≤ η * ((N : ℝ) ^ 2 * (1 / η) ^ 2 * |E₂ - E₁|) := mul_le_mul_of_nonneg_left hint hη.le
    _ = (η * |E₂ - E₁|) * ((N : ℝ) ^ 2 * (1 / η) ^ 2) := by ring
    _ ≤ 2 * ((N : ℝ) ^ 2 * (N : ℝ) ^ 2) :=
        mul_le_mul hW (mul_le_mul_of_nonneg_left hη2 (by positivity)) (by positivity) (by norm_num)
    _ ≤ 32 * (N : ℝ) ^ 8 := by
        have : (N : ℝ) ^ 4 ≤ (N : ℝ) ^ 8 := pow_le_pow_right₀ hn1 (by norm_num)
        nlinarith

/-! ### `K^{(1,0)}_0 + K^{(0,1)}_0` is real -/

/-- `conj Σ c_s conj c_t = Σ c_t conj c_s`. -/
private lemma odp_inner_conj {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (p : OffDiag N) (z : ℂ)
    (k s t : ℕ) :
    (starRingEnd ℂ) (∑ i, ∑ j, if i ≠ j ∧ swapIdx p i j = k then
        swapCoeff H (Sum.inr p) z s i j * (starRingEnd ℂ) (swapCoeff H (Sum.inr p) z t i j)
        else 0) =
      ∑ i, ∑ j, if i ≠ j ∧ swapIdx p i j = k then
        swapCoeff H (Sum.inr p) z t i j * (starRingEnd ℂ) (swapCoeff H (Sum.inr p) z s i j)
        else 0 := by
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp [mul_comm]

private lemma odp_add_conj_im (a : ℂ) : (a + (starRingEnd ℂ) a).im = 0 := by simp

/-- `K^{(1,0)}_0 + K^{(0,1)}_0` is real for the functional `η² Σ_{i ≠ j} |G_ij(z)|²`. -/
private lemma odp_Kpt_im {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (p : OffDiag N) (z : ℂ) :
    (swapKpt H p z 0 1 0 + swapKpt H p z 0 0 1).im = 0 := by
  unfold swapKpt
  rw [← odp_inner_conj H p z 0 1 0, ← mul_add, Complex.mul_im, odp_add_conj_im,
    ← Complex.ofReal_pow, Complex.ofReal_im]
  ring

/-- `K^{(1,0)}_0 + K^{(0,1)}_0` is real for the functional (6.56). -/
private lemma odp_K_im {N : ℕ} {η : ℝ} (hη : 0 < η) (ω : Entries N) (p : OffDiag N)
    (E₁ E₂ : ℝ) :
    (swapK (symOfEntries ω) p η E₁ E₂ 0 1 0 + swapK (symOfEntries ω) p η E₁ E₂ 0 0 1).im = 0 := by
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℂ, f = fun y => ∑ i, ∑ j, if i ≠ j ∧ swapIdx p i j = 0 then
      swapCoeff (symOfEntries ω) (Sum.inr p) ⟨y, η⟩ 1 i j *
        (starRingEnd ℂ) (swapCoeff (symOfEntries ω) (Sum.inr p) ⟨y, η⟩ 0 i j) else 0 := ⟨_, rfl⟩
  have hc : Continuous f := by
    have hy : Continuous (fun y : ℝ => (ω, y)) := continuous_const.prodMk continuous_id
    have hj : ∀ m i j, Continuous fun y : ℝ =>
        swapCoeff (symOfEntries ω) (Sum.inr p) ⟨y, η⟩ m i j := fun m i j => by
      have h := (odp_continuous_coeff hη p m i j).comp hy
      exact h
    rw [hf]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_if_const _ (fun _ => (hj 1 i j).mul (Complex.continuous_conj.comp (hj 0 i j)))
        fun _ => continuous_const
  have h01 : swapK (symOfEntries ω) p η E₁ E₂ 0 0 1 =
      (η : ℂ) * ∫ y in E₁..E₂, (starRingEnd ℂ) (f y) := by
    unfold swapK
    congr 1
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [hf]
    exact (odp_inner_conj _ p _ 0 1 0).symm
  have h10 : swapK (symOfEntries ω) p η E₁ E₂ 0 1 0 = (η : ℂ) * ∫ y in E₁..E₂, f y := by
    rw [hf]; rfl
  have hre : ∀ a : ℂ, a + (starRingEnd ℂ) a = (((2 * a.re : ℝ)) : ℂ) := fun a => by
    apply Complex.ext <;> simp; ring
  have hcc : Continuous fun y => (starRingEnd ℂ) (f y) := Complex.continuous_conj.comp hc
  rw [h10, h01, ← mul_add, ← intervalIntegral.integral_add (hc.intervalIntegrable E₁ E₂)
    (hcc.intervalIntegrable E₁ E₂)]
  simp_rw [hre]
  rw [intervalIntegral.integral_ofReal, ← Complex.ofReal_mul, Complex.ofReal_im]

/-! ### Partial expectations: [16] (6.70)–(6.76) for one law -/

-- The law of `v_e` and the measurability of `ω ↦ v_e`, `ω ↦ Q`.
open private map_entryVal measurable_entryVal measurable_zeroEntry from WEdgeNS.Comparison.Telescope

/-- `c₁ = F′(x_R) A_1` (the coefficient of `w = -v`). -/
private def odpC1 (F : ℝ → ℝ) (x : ℝ) (K : ℕ → ℕ → ℕ → ℂ) : ℝ :=
  iteratedDeriv 1 F x * (odpA K 1).re

/-- `c₂ = g` (the coefficient of `w²`), in the form of `swapBInt` and `swapBPt`. -/
private def odpC2 (F : ℝ → ℝ) (x : ℝ) (K : ℕ → ℕ → ℕ → ℂ) : ℝ :=
  (((iteratedDeriv 1 F x : ℝ) : ℂ) * ∑ k ∈ Finset.range 2, (K k 2 0 + K k 1 1 + K k 0 2) +
    ((iteratedDeriv 2 F x : ℝ) : ℂ) / 2 * (K 0 1 0 + K 0 0 1) ^ 2).re

/-- `c₃ = F′(x_R) A_3 + F″(x_R) A_1 A_2` (the coefficient of `w³`). -/
private def odpC3 (F : ℝ → ℝ) (x : ℝ) (K : ℕ → ℕ → ℕ → ℂ) : ℝ :=
  iteratedDeriv 1 F x * (odpA K 3).re + iteratedDeriv 2 F x * (odpA K 1).re * (odpA K 2).re

/-- `c₄ = F′(x_R) A_4` (the coefficient of `w⁴`). -/
private def odpC4 (F : ℝ → ℝ) (x : ℝ) (K : ℕ → ℕ → ℕ → ℂ) : ℝ :=
  iteratedDeriv 1 F x * (odpA K 4).re

/-- `g₃ = F′(x_R) (K^{(3,0)}_0 + K^{(0,3)}_0)`, in the form of `swapB3Int` and `swapB3Pt`. -/
private def odpG3 (F : ℝ → ℝ) (x : ℝ) (K : ℕ → ℕ → ℕ → ℂ) : ℝ :=
  (((iteratedDeriv 1 F x : ℝ) : ℂ) * (K 0 3 0 + K 0 0 3)).re

/-- `g = F′ A_2 + ½ F″ (K^{(1,0)}_0 + K^{(0,1)}_0)²` when `K^{(1,0)}_0 + K^{(0,1)}_0` is real. -/
private lemma odpC2_eq (F : ℝ → ℝ) (x : ℝ) (K : ℕ → ℕ → ℕ → ℂ)
    (hIm : (K 0 1 0 + K 0 0 1).im = 0) :
    odpC2 F x K = iteratedDeriv 1 F x * (odpA K 2).re +
      iteratedDeriv 2 F x / 2 * ((K 0 1 0 + K 0 0 1).re) ^ 2 := by
  unfold odpC2
  rw [odp_A2_eq]
  have e : K 0 1 0 + K 0 0 1 = (((K 0 1 0 + K 0 0 1).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simpa using hIm)
  rw [e]
  have e2 : ((iteratedDeriv 2 F x : ℝ) : ℂ) / 2 * (((K 0 1 0 + K 0 0 1).re : ℝ) : ℂ) ^ 2 =
      (((iteratedDeriv 2 F x / 2 * ((K 0 1 0 + K 0 0 1).re) ^ 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [e2, Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
  simp only [Complex.ofReal_re]

private lemma odpG3_eq (F : ℝ → ℝ) (x : ℝ) (K : ℕ → ℕ → ℕ → ℂ) :
    odpG3 F x K = iteratedDeriv 1 F x * (K 0 3 0 + K 0 0 3).re := by
  unfold odpG3; rw [Complex.re_ofReal_mul]

/-- `‖A_m‖ ≤ 10 A` for `m ≤ 4` when every coefficient with `s + t ≤ 4` is at most `A`. -/
private lemma odpA_norm_le {K : ℕ → ℕ → ℕ → ℂ} {Ab : ℝ}
    (hK : ∀ k s t, k < 2 → s + t ≤ 4 → ‖K k s t‖ ≤ Ab) {m : ℕ} (hm : m ≤ 4) :
    ‖odpA K m‖ ≤ 10 * Ab := by
  have hA : 0 ≤ Ab := (norm_nonneg _).trans (hK 0 0 0 (by norm_num) (by norm_num))
  unfold odpA
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun k hk => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun s hs => hK k s (m - s) (Finset.mem_range.1 hk)
      (by have := Finset.mem_range.1 hs; omega))).trans ?_
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : ((m : ℝ) + 1) ≤ 5 := by exact_mod_cast (by omega : m + 1 ≤ 5)
  push_cast
  nlinarith

/-- The global bounds of the coefficients `c_m` and `g₃`: at most `Φ_c = 256 K₀ A²` when
`|F′|, |F″| ≤ K₀` at `x` and every coefficient is at most `A ≥ 1`. -/
private lemma odp_c_bounds {F : ℝ → ℝ} {x : ℝ} {K : ℕ → ℕ → ℕ → ℂ} {Ab K₀ : ℝ} (hAb : 1 ≤ Ab)
    (hK : ∀ k s t, k < 2 → s + t ≤ 4 → ‖K k s t‖ ≤ Ab) (h1 : |iteratedDeriv 1 F x| ≤ K₀)
    (h2 : |iteratedDeriv 2 F x| ≤ K₀) :
    |odpC1 F x K| ≤ 256 * K₀ * Ab ^ 2 ∧ |odpC2 F x K| ≤ 256 * K₀ * Ab ^ 2 ∧
    |odpC3 F x K - odpG3 F x K| ≤ 256 * K₀ * Ab ^ 2 ∧ |odpC3 F x K| ≤ 256 * K₀ * Ab ^ 2 ∧
    |odpC4 F x K| ≤ 256 * K₀ * Ab ^ 2 := by
  have hK0 : 0 ≤ K₀ := (abs_nonneg _).trans h1
  have hA0 : 0 ≤ Ab := by linarith
  have hAA : Ab ≤ Ab ^ 2 := by nlinarith
  have hA : ∀ m, m ≤ 4 → |(odpA K m).re| ≤ 10 * Ab := fun m hm =>
    (Complex.abs_re_le_norm _).trans (odpA_norm_le hK hm)
  have t1 : ∀ m, m ≤ 4 → |iteratedDeriv 1 F x * (odpA K m).re| ≤ 10 * K₀ * Ab := fun m hm => by
    rw [abs_mul]
    calc _ ≤ K₀ * (10 * Ab) := mul_le_mul h1 (hA m hm) (abs_nonneg _) hK0
      _ = 10 * K₀ * Ab := by ring
  have hc3 : |odpC3 F x K| ≤ 110 * K₀ * Ab ^ 2 := by
    unfold odpC3
    refine (abs_add_le _ _).trans ?_
    have a := t1 3 (by norm_num)
    have b : |iteratedDeriv 2 F x * (odpA K 1).re * (odpA K 2).re| ≤
        K₀ * (10 * Ab) * (10 * Ab) := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul h2 (hA 1 (by norm_num)) (abs_nonneg _) hK0)
        (hA 2 (by norm_num)) (abs_nonneg _) (by positivity)
    nlinarith
  have hg3 : |odpG3 F x K| ≤ 2 * K₀ * Ab := by
    rw [odpG3_eq, abs_mul]
    have : |(K 0 3 0 + K 0 0 3).re| ≤ 2 * Ab :=
      (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans (by
        have := hK 0 3 0 (by norm_num) (by norm_num)
        have := hK 0 0 3 (by norm_num) (by norm_num)
        linarith))
    calc _ ≤ K₀ * (2 * Ab) := mul_le_mul h1 this (abs_nonneg _) hK0
      _ = 2 * K₀ * Ab := by ring
  refine ⟨?_, ?_, ?_, by nlinarith, ?_⟩
  · unfold odpC1; have := t1 1 (by norm_num); nlinarith
  · unfold odpC2
    rw [odp_A2_eq]
    refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans ?_)
    have hA2 := odpA_norm_le hK (m := 2) (by norm_num)
    have h10 : ‖K 0 1 0 + K 0 0 1‖ ≤ 2 * Ab := (norm_add_le _ _).trans (by
      have := hK 0 1 0 (by norm_num) (by norm_num)
      have := hK 0 0 1 (by norm_num) (by norm_num)
      linarith)
    have n1 : ‖((iteratedDeriv 1 F x : ℝ) : ℂ) * odpA K 2‖ ≤ K₀ * (10 * Ab) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul h1 hA2 (norm_nonneg _) hK0
    have n2 : ‖((iteratedDeriv 2 F x : ℝ) : ℂ) / 2 * (K 0 1 0 + K 0 0 1) ^ 2‖ ≤
        K₀ / 2 * (2 * Ab) ^ 2 := by
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, norm_pow,
        show ‖(2 : ℂ)‖ = 2 by simp]
      exact mul_le_mul (by linarith) (pow_le_pow_left₀ (norm_nonneg _) h10 2) (by positivity)
        (by positivity)
    nlinarith
  · have := abs_sub (odpC3 F x K) (odpG3 F x K)
    nlinarith
  · unfold odpC4; have := t1 4 (by norm_num); nlinarith

/-- `E[c(Q) w^m] = E[c(Q)] n_m`, `w = -v_e` (independence of `Q` and `v_e`). -/
private lemma odp_factor {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) (e : Fin N ⊕ OffDiag N)
    {c : Entries N → ℝ} (hc : Continuous c) {Cc : ℝ} (hcb : ∀ ω, |c ω| ≤ Cc) (m : ℕ)
    (hm : Integrable (fun x : ℝ => x ^ m) (L.entry e)) :
    ∫ ω, c (zeroEntry e ω) * (-entryVal e ω) ^ m ∂L.law =
      (∫ ω, c (zeroEntry e ω) ∂L.law) * L.entryMoment e m := by
  have hP := isProbabilityMeasure_law hL
  have hcm : Measurable fun ω => ((c ω : ℝ) : ℂ) := (Complex.continuous_ofReal.comp hc).measurable
  have hci : Integrable (fun ω => ((c (zeroEntry e ω) : ℝ) : ℂ)) L.law :=
    Integrable.of_bound (hcm.comp (measurable_zeroEntry e)).aestronglyMeasurable Cc
      (Eventually.of_forall fun ω => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hcb _)
  have h := integral_mul_zeroEntry hL e (fun ω => ((c ω : ℝ) : ℂ)) m hcm hci hm
  have e1 : ∫ ω, ((c (zeroEntry e ω) : ℝ) : ℂ) * (((-entryVal e ω) ^ m : ℝ) : ℂ) ∂L.law =
      ((∫ ω, c (zeroEntry e ω) * (-entryVal e ω) ^ m ∂L.law : ℝ) : ℂ) := by
    have := integral_ofReal (𝕜 := ℂ) (μ := L.law)
      (f := fun ω => c (zeroEntry e ω) * (-entryVal e ω) ^ m)
    refine Eq.trans ?_ this
    congr 1
    funext ω
    change _ = ((c (zeroEntry e ω) * (-entryVal e ω) ^ m : ℝ) : ℂ)
    rw [Complex.ofReal_mul]
  have e2 : ∫ ω, ((c (zeroEntry e ω) : ℝ) : ℂ) ∂L.law = ((∫ ω, c (zeroEntry e ω) ∂L.law : ℝ) : ℂ) :=
    integral_ofReal (𝕜 := ℂ)
  rw [e1, e2] at h
  exact_mod_cast h

/-- `∫|Y| ≤ δ + Φ ((1 + τ²) P(Ωᶜ) + E w⁶/τ)` when `|Y| ≤ δ` on `Ω` and `|Y| ≤ Φ (1 + w⁴)`
everywhere. -/
private lemma odp_abs_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {Y w : α → ℝ} (hY : Integrable Y μ)
    (hw6 : Integrable (fun ω => w ω ^ 6) μ) {Ω : Set α} {δ Φ τ : ℝ} (hδ : 0 ≤ δ) (hΦ : 0 ≤ Φ)
    (hτ : 0 < τ) (hgood : ∀ ω ∈ Ω, |Y ω| ≤ δ) (hbad : ∀ ω, |Y ω| ≤ Φ * (1 + w ω ^ 4)) :
    |∫ ω, Y ω ∂μ| ≤ δ + Φ * ((1 + τ ^ 2) * (μ Ωᶜ).toReal + (∫ ω, w ω ^ 6 ∂μ) / τ) := by
  set T' := toMeasurable μ Ωᶜ with hT'
  have hmeas : MeasurableSet T' := measurableSet_toMeasurable μ _
  have hpt : ∀ ω, |Y ω| ≤ δ + Φ * ((1 + τ ^ 2) * T'.indicator 1 ω + w ω ^ 6 / τ) := by
    intro ω
    have h6 : 0 ≤ w ω ^ 6 / τ := div_nonneg (by positivity) hτ.le
    have h4 := odp_pow_four_le (w := w ω) hτ
    by_cases h : ω ∈ T'
    · simp only [Set.indicator_of_mem h, Pi.one_apply, mul_one]
      have := hbad ω
      nlinarith
    · have hω : ω ∈ Ω := by
        by_contra hn
        exact h (subset_toMeasurable μ _ hn)
      simp only [Set.indicator_of_notMem h, mul_zero, zero_add]
      have := hgood ω hω
      nlinarith
  have hind : Integrable (T'.indicator (1 : α → ℝ)) μ := (integrable_const (1 : ℝ)).indicator hmeas
  have i1 : Integrable (fun ω => (1 + τ ^ 2) * T'.indicator (1 : α → ℝ) ω) μ :=
    hind.const_mul (1 + τ ^ 2)
  have i2 : Integrable (fun ω => w ω ^ 6 / τ) μ := hw6.div_const τ
  have i3 : Integrable (fun ω => Φ * ((1 + τ ^ 2) * T'.indicator (1 : α → ℝ) ω + w ω ^ 6 / τ)) μ :=
    (i1.add i2).const_mul Φ
  calc |∫ ω, Y ω ∂μ| = ‖∫ ω, Y ω ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ ω, ‖Y ω‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (δ + Φ * ((1 + τ ^ 2) * T'.indicator 1 ω + w ω ^ 6 / τ)) ∂μ :=
        integral_mono hY.norm ((integrable_const δ).add i3) fun ω => by
          simpa [Real.norm_eq_abs] using hpt ω
    _ = δ + Φ * ((1 + τ ^ 2) * (μ Ωᶜ).toReal + (∫ ω, w ω ^ 6 ∂μ) / τ) := by
        rw [integral_add (integrable_const δ) i3, integral_const_mul, integral_add i1 i2,
          integral_const_mul, integral_div, integral_indicator_one hmeas, integral_const]
        simp [measureReal_def, hT', measure_toMeasurable]

/-- `ω ↦ Q` is continuous. -/
private lemma odp_continuous_zeroEntry {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    Continuous (zeroEntry e : Entries N → Entries N) := by
  rcases e with a | q
  · change Continuous fun ω : Entries N => (Function.update ω.1 a 0, ω.2)
    exact (continuous_fst.update a continuous_const).prodMk continuous_snd
  · change Continuous fun ω : Entries N => (ω.1, Function.update ω.2 q 0)
    exact continuous_fst.prodMk (continuous_snd.update q continuous_const)

set_option maxHeartbeats 1000000 in
-- one proof treats every term of the expansion (6.69) and of the Taylor formula
/-- [16] (6.70)–(6.76) for one law `L` and one functional `x` with coefficients `K^{(s,t)}_k`:
`E F(x_S) - E F(x_R) - E g(Q) n₂ - E g₃(Q) n₃` is at most the bound of `odp_taylor_alg` on `Ω`,
plus `n₃ E(c₃ - g₃)(Q)` and `n₄ E c₄(Q)` (the gain `q²/N` of the moments), plus the
contribution of `Ωᶜ`. -/
private lemma odp_perLaw {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) (e : Fin N ⊕ OffDiag N)
    {F : ℝ → ℝ} {CF : ℝ} (hF4 : ContDiff ℝ 4 F)
    (hF : ∀ n ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF)
    {xf : Entries N → ℝ} {Kf : ℕ → ℕ → ℕ → Entries N → ℂ} (hxc : Continuous xf)
    (hKc : ∀ k s t, Continuous (Kf k s t)) {Ab : ℝ} (hAb : 1 ≤ Ab) (hxA : ∀ ω, |xf ω| ≤ Ab)
    (hKA : ∀ ω k s t, k < 2 → s + t ≤ 4 → ‖Kf k s t ω‖ ≤ Ab)
    (hIm : ∀ ω, (Kf 0 1 0 ω + Kf 0 0 1 ω).im = 0)
    (hmom : ∀ k ≤ 6, Integrable (fun x : ℝ => x ^ k) (L.entry e)) (hn1 : L.entryMoment e 1 = 0)
    {m3 m4 m6 : ℝ} (hm3 : |L.entryMoment e 3| ≤ m3) (hm4 : |L.entryMoment e 4| ≤ m4)
    (hm6 : ∫ x, x ^ 6 ∂(L.entry e) ≤ m6)
    {Ω : Set (Entries N)} {pΩ : ℝ} (hp : (L.law Ωᶜ).toReal ≤ pΩ)
    {B α β γ T₀ R₁ G τ : ℝ} (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hT₀ : 0 ≤ T₀) (hG0 : 0 ≤ G) (hτ : 0 < τ)
    (hG : ∀ ζ, |ζ| ≤ R₁ → |iteratedDeriv 1 F ζ| ≤ G ∧ |iteratedDeriv 2 F ζ| ≤ G ∧
      |iteratedDeriv 3 F ζ| ≤ G)
    (hΩ : ∀ ω ∈ Ω, |entryVal e ω| ≤ B ∧ |xf ω| + (4 * B * α + T₀) ≤ R₁ ∧
      ‖((xf ω - xf (zeroEntry e ω) : ℝ) : ℂ) -
          ∑ k ∈ Finset.range 2, ∑ s ∈ Finset.range 5, ∑ t ∈ Finset.range 5,
            if 1 ≤ s + t ∧ s + t ≤ 4 then
              (-(entryVal e ω : ℂ)) ^ (s + t) * Kf k s t (zeroEntry e ω) else 0‖ ≤ T₀ ∧
      (∀ m, 1 ≤ m → m ≤ 4 → |(odpA (fun k s t => Kf k s t (zeroEntry e ω)) m).re| ≤ α) ∧
      |(Kf 1 1 0 (zeroEntry e ω) + Kf 1 0 1 (zeroEntry e ω)).re| ≤ β ∧
      |(Kf 0 2 1 (zeroEntry e ω) + Kf 0 1 2 (zeroEntry e ω) + Kf 1 3 0 (zeroEntry e ω) +
        Kf 1 2 1 (zeroEntry e ω) + Kf 1 1 2 (zeroEntry e ω) + Kf 1 0 3 (zeroEntry e ω)).re| ≤ γ) :
    |∫ ω, F (xf ω) ∂L.law - ∫ ω, F (xf (zeroEntry e ω)) ∂L.law -
        (∫ ω, odpC2 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) ∂L.law) *
          L.entryMoment e 2 -
        (∫ ω, odpG3 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) ∂L.law) *
          L.entryMoment e 3| ≤
      (G * T₀ + G / 2 * (16 * B ^ 4 * α ^ 2 + B ^ 2 * β * (2 * α + β) + T₀ * (8 * B * α + T₀)) +
        G / 6 * (4 * B * α + T₀) ^ 3) +
      5 * (256 * (CF * (1 + Ab) ^ CF) * Ab ^ 2) * ((1 + τ ^ 2) * pΩ + m6 / τ) +
      m3 * (G * (γ + α ^ 2) + 256 * (CF * (1 + Ab) ^ CF) * Ab ^ 2 * pΩ) +
      m4 * (G * α + 256 * (CF * (1 + Ab) ^ CF) * Ab ^ 2 * pΩ) := by
  have hP := isProbabilityMeasure_law hL
  have hCF : 0 ≤ CF := by
    have := hF 1 (by simp) 0
    simpa using (abs_nonneg _).trans this
  set K₀ := CF * (1 + Ab) ^ CF with hK₀
  have hK₀0 : 0 ≤ K₀ := mul_nonneg hCF (Real.rpow_nonneg (by linarith) _)
  set Φc := 256 * K₀ * Ab ^ 2 with hΦc
  have hΦc0 : 0 ≤ Φc := by positivity
  have hm30 : 0 ≤ m3 := (abs_nonneg _).trans hm3
  have hm40 : 0 ≤ m4 := (abs_nonneg _).trans hm4
  have hpΩ0 : 0 ≤ pΩ := le_trans ENNReal.toReal_nonneg hp
  -- the coefficients as functions of the entries
  have hQc := odp_continuous_zeroEntry e
  have hv := measurable_entryVal e
  have hFd : ∀ ζ, |ζ| ≤ Ab → |iteratedDeriv 1 F ζ| ≤ K₀ ∧ |iteratedDeriv 2 F ζ| ≤ K₀ :=
    fun ζ hζ => ⟨abs_iteratedDeriv_le_of_abs_le hF hζ 1 (by simp),
      abs_iteratedDeriv_le_of_abs_le hF hζ 2 (by simp)⟩
  have hcb : ∀ ω, _ := fun ω => odp_c_bounds (F := F) (x := xf ω) (K := fun k s t => Kf k s t ω) hAb
    (fun k s t hk hst => hKA ω k s t hk hst) (hFd _ (hxA ω)).1 (hFd _ (hxA ω)).2
  have hd1 : Continuous (iteratedDeriv 1 F) := hF4.continuous_iteratedDeriv 1 (by norm_num)
  have hd2 : Continuous (iteratedDeriv 2 F) := hF4.continuous_iteratedDeriv 2 (by norm_num)
  have hAc : ∀ m, Continuous fun ω => odpA (fun k s t => Kf k s t ω) m := fun m =>
    continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun s _ => hKc k s (m - s)
  have hc1 : Continuous fun ω => odpC1 F (xf ω) (fun k s t => Kf k s t ω) :=
    (hd1.comp hxc).mul (Complex.continuous_re.comp (hAc 1))
  have hc2 : Continuous fun ω => odpC2 F (xf ω) (fun k s t => Kf k s t ω) :=
    Complex.continuous_re.comp (((Complex.continuous_ofReal.comp (hd1.comp hxc)).mul
      (continuous_finsetSum _ fun k _ => ((hKc k 2 0).add (hKc k 1 1)).add (hKc k 0 2))).add
      (((Complex.continuous_ofReal.comp (hd2.comp hxc)).div_const 2).mul
        (((hKc 0 1 0).add (hKc 0 0 1)).pow 2)))
  have hc3 : Continuous fun ω => odpC3 F (xf ω) (fun k s t => Kf k s t ω) :=
    ((hd1.comp hxc).mul (Complex.continuous_re.comp (hAc 3))).add
      (((hd2.comp hxc).mul (Complex.continuous_re.comp (hAc 1))).mul
        (Complex.continuous_re.comp (hAc 2)))
  have hc4 : Continuous fun ω => odpC4 F (xf ω) (fun k s t => Kf k s t ω) :=
    (hd1.comp hxc).mul (Complex.continuous_re.comp (hAc 4))
  have hg3 : Continuous fun ω => odpG3 F (xf ω) (fun k s t => Kf k s t ω) :=
    Complex.continuous_re.comp ((Complex.continuous_ofReal.comp (hd1.comp hxc)).mul
      ((hKc 0 3 0).add (hKc 0 0 3)))
  -- the moments of `w = -v`
  have hwi : ∀ m ≤ 6, Integrable (fun ω => (-entryVal e ω) ^ m) L.law := by
    intro m hm
    have h1 : Integrable (fun x : ℝ => (-x) ^ m) (L.entry e) :=
      ((hmom m hm).const_mul ((-1) ^ m)).congr (Eventually.of_forall fun x => (neg_pow x m).symm)
    have h2 := (integrable_map_measure (μ := L.law) (f := entryVal e)
      (g := fun x : ℝ => (-x) ^ m) (continuous_neg.pow m).aestronglyMeasurable
      hv.aemeasurable).1 (by rw [map_entryVal hL e]; exact h1)
    exact h2
  have hw6 : ∫ ω, (-entryVal e ω) ^ 6 ∂L.law ≤ m6 := by
    have h := integral_map (μ := L.law) hv.aemeasurable (f := fun x : ℝ => (-x) ^ 6)
      (continuous_neg.pow 6).aestronglyMeasurable
    rw [map_entryVal hL e] at h
    have e6 : ∀ x : ℝ, (-x) ^ 6 = x ^ 6 := fun x => by ring
    simp only [e6] at h
    have h' : ∫ ω, (-entryVal e ω) ^ 6 ∂L.law = ∫ x, x ^ 6 ∂(L.entry e) := by
      rw [h]; simp only [e6]
    rw [h']; exact hm6
  -- integrability
  have hFa : Integrable (fun ω => F (xf ω)) L.law := ward_integrable_comp hF4.continuous hxc hxA
  have hFb : Integrable (fun ω => F (xf (zeroEntry e ω))) L.law :=
    ward_integrable_comp hF4.continuous (hxc.comp hQc) (fun ω => hxA _)
  have hbd : ∀ {c : Entries N → ℝ}, Continuous c → (∀ ω, |c ω| ≤ Φc) →
      Integrable (fun ω => c (zeroEntry e ω)) L.law := fun {c} hc hcb =>
    Integrable.of_bound (hc.comp hQc).aestronglyMeasurable Φc
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hcb _)
  have hprod : ∀ {c : Entries N → ℝ}, Continuous c → (∀ ω, |c ω| ≤ Φc) → ∀ m ≤ 6,
      Integrable (fun ω => c (zeroEntry e ω) * (-entryVal e ω) ^ m) L.law := fun {c} hc hcb m hm =>
    Integrable.bdd_mul (c := Φc) (hwi m hm) (hc.comp hQc).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hcb _)
  have i1 := hprod hc1 (fun ω => (hcb ω).1) 1 (by norm_num)
  have i2 := hprod hc2 (fun ω => (hcb ω).2.1) 2 (by norm_num)
  have i3 := hprod hc3 (fun ω => (hcb ω).2.2.2.1) 3 (by norm_num)
  have i4 := hprod hc4 (fun ω => (hcb ω).2.2.2.2) 4 (by norm_num)
  -- the factorization `E[c(Q) w^m] = E c(Q) n_m`
  have f1 := odp_factor hL e hc1 (fun ω => (hcb ω).1) 1 (hmom 1 (by norm_num))
  have f2 := odp_factor hL e hc2 (fun ω => (hcb ω).2.1) 2 (hmom 2 (by norm_num))
  have f3 := odp_factor hL e hc3 (fun ω => (hcb ω).2.2.2.1) 3 (hmom 3 (by norm_num))
  have f4 := odp_factor hL e hc4 (fun ω => (hcb ω).2.2.2.2) 4 (hmom 4 (by norm_num))
  set Y : Entries N → ℝ := fun ω => F (xf ω) - F (xf (zeroEntry e ω)) -
    (odpC1 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) * (-entryVal e ω) ^ 1 +
      odpC2 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) * (-entryVal e ω) ^ 2 +
      odpC3 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) * (-entryVal e ω) ^ 3 +
      odpC4 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) * (-entryVal e ω) ^ 4)
    with hYdef
  have hYi : Integrable Y L.law := (hFa.sub hFb).sub (((i1.add i2).add i3).add i4)
  have hYint : ∫ ω, Y ω ∂L.law = ∫ ω, F (xf ω) ∂L.law - ∫ ω, F (xf (zeroEntry e ω)) ∂L.law -
      ((∫ ω, odpC1 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) ∂L.law) *
          L.entryMoment e 1 +
        (∫ ω, odpC2 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) ∂L.law) *
          L.entryMoment e 2 +
        (∫ ω, odpC3 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) ∂L.law) *
          L.entryMoment e 3 +
        (∫ ω, odpC4 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) ∂L.law) *
          L.entryMoment e 4) := by
    have e1 := integral_sub (hFa.sub hFb) (((i1.add i2).add i3).add i4)
    have e2 := integral_sub hFa hFb
    have e3 := integral_add ((i1.add i2).add i3) i4
    have e4 := integral_add (i1.add i2) i3
    have e5 := integral_add i1 i2
    simp only [Pi.add_apply, Pi.sub_apply] at e1 e2 e3 e4 e5
    rw [hYdef]
    beta_reduce
    rw [e1, e2, e3, e4, e5, f1, f2, f3, f4]
  -- on `Ω`: the a priori bounds give `|x_R| ≤ R₁` and the Taylor expansion
  have hgoodR : ∀ ω ∈ Ω, |xf (zeroEntry e ω)| ≤ R₁ ∧ |xf ω| ≤ R₁ ∧
      |xf ω - xf (zeroEntry e ω)| ≤ 4 * B * α + T₀ := by
    intro ω hω
    obtain ⟨hvB, hR1, hexp, hA, -, -⟩ := hΩ ω hω
    have hU := odp_U_le (w := -entryVal e ω) (by rwa [abs_neg]) hB1 (hA 1 le_rfl (by norm_num))
      (hA 2 (by norm_num) (by norm_num)) (hA 3 (by norm_num) (by norm_num))
      (hA 4 (by norm_num) le_rfl)
    have hsum := odp_sum_eq (fun k s t => Kf k s t (zeroEntry e ω)) (-(entryVal e ω : ℂ))
    rw [hsum] at hexp
    have hre := (Complex.abs_re_le_norm _).trans hexp
    have hwc : (-(entryVal e ω : ℂ)) = ((-entryVal e ω : ℝ) : ℂ) := by push_cast; ring
    rw [hwc] at hre
    simp only [← Complex.ofReal_pow, Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul,
      Complex.ofReal_re] at hre
    have hD : |xf ω - xf (zeroEntry e ω)| ≤ 4 * B * α + T₀ := by
      have := abs_sub_abs_le_abs_sub (xf ω - xf (zeroEntry e ω))
        ((-entryVal e ω) * (odpA (fun k s t => Kf k s t (zeroEntry e ω)) 1).re +
          (-entryVal e ω) ^ 2 * (odpA (fun k s t => Kf k s t (zeroEntry e ω)) 2).re +
          (-entryVal e ω) ^ 3 * (odpA (fun k s t => Kf k s t (zeroEntry e ω)) 3).re +
          (-entryVal e ω) ^ 4 * (odpA (fun k s t => Kf k s t (zeroEntry e ω)) 4).re)
      linarith
    have ha := abs_nonneg (xf ω)
    have hBα : 0 ≤ 4 * B * α := by positivity
    refine ⟨?_, by linarith, hD⟩
    have := abs_sub_abs_le_abs_sub (xf ω) (xf (zeroEntry e ω))
    have := abs_sub_comm (xf ω) (xf (zeroEntry e ω))
    have := abs_sub_abs_le_abs_sub (xf (zeroEntry e ω)) (xf ω)
    linarith
  set δ := G * T₀ + G / 2 * (16 * B ^ 4 * α ^ 2 + B ^ 2 * β * (2 * α + β) +
    T₀ * (8 * B * α + T₀)) + G / 6 * (4 * B * α + T₀) ^ 3 with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hYgood : ∀ ω ∈ Ω, |Y ω| ≤ δ := by
    intro ω hω
    obtain ⟨hvB, hR1, hexp, hA, hβω, -⟩ := hΩ ω hω
    obtain ⟨hbR, haR, -⟩ := hgoodR ω hω
    have hsum := odp_sum_eq (fun k s t => Kf k s t (zeroEntry e ω)) (-(entryVal e ω : ℂ))
    rw [hsum] at hexp
    have hre := (Complex.abs_re_le_norm _).trans hexp
    have hwc : (-(entryVal e ω : ℂ)) = ((-entryVal e ω : ℝ) : ℂ) := by push_cast; ring
    rw [hwc] at hre
    simp only [← Complex.ofReal_pow, Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul,
      Complex.ofReal_re] at hre
    obtain ⟨ζ, hζ, hT⟩ := taylor_third hF4 (xf (zeroEntry e ω)) (xf ω)
    have hζR : |ζ| ≤ R₁ := by
      have a1 := abs_le.1 hbR
      have a2 := abs_le.1 haR
      rcases Set.mem_uIcc.1 hζ with ⟨z1, z2⟩ | ⟨z1, z2⟩ <;>
        exact abs_le.2 ⟨by linarith, by linarith⟩
    have hb1 : (odpA (fun k s t => Kf k s t (zeroEntry e ω)) 1).re -
        (Kf 0 1 0 (zeroEntry e ω) + Kf 0 0 1 (zeroEntry e ω)).re =
        (Kf 1 1 0 (zeroEntry e ω) + Kf 1 0 1 (zeroEntry e ω)).re := by
      rw [odp_A1_eq, Complex.add_re]; ring
    have halg := (odp_taylor_alg (Δ := xf ω - xf (zeroEntry e ω)) (w := -entryVal e ω)
      (a1 := (odpA (fun k s t => Kf k s t (zeroEntry e ω)) 1).re)
      (a2 := (odpA (fun k s t => Kf k s t (zeroEntry e ω)) 2).re)
      (a3 := (odpA (fun k s t => Kf k s t (zeroEntry e ω)) 3).re)
      (a4 := (odpA (fun k s t => Kf k s t (zeroEntry e ω)) 4).re)
      (α0 := (Kf 0 1 0 (zeroEntry e ω) + Kf 0 0 1 (zeroEntry e ω)).re)
      (f1 := iteratedDeriv 1 F (xf (zeroEntry e ω))) (f2 := iteratedDeriv 2 F (xf (zeroEntry e ω)))
      (f3 := iteratedDeriv 3 F ζ) (T₀ := T₀) (B := B) (α := α) (β := β) (G := G) hre
      (by rwa [abs_neg]) hB1 (hA 1 le_rfl (by norm_num))
      (hA 2 (by norm_num) (by norm_num)) (hA 3 (by norm_num) (by norm_num))
      (hA 4 (by norm_num) le_rfl) (by rw [hb1]; exact hβω) (hG _ hbR).1 (hG _ hbR).2.1
      (hG _ hζR).2.2).2
    have hY : Y ω = iteratedDeriv 1 F (xf (zeroEntry e ω)) * (xf ω - xf (zeroEntry e ω)) +
        iteratedDeriv 2 F (xf (zeroEntry e ω)) * (xf ω - xf (zeroEntry e ω)) ^ 2 / 2 +
        iteratedDeriv 3 F ζ * (xf ω - xf (zeroEntry e ω)) ^ 3 / 6 -
        ((-entryVal e ω) * (iteratedDeriv 1 F (xf (zeroEntry e ω)) *
            (odpA (fun k s t => Kf k s t (zeroEntry e ω)) 1).re) +
          (-entryVal e ω) ^ 2 * (iteratedDeriv 1 F (xf (zeroEntry e ω)) *
            (odpA (fun k s t => Kf k s t (zeroEntry e ω)) 2).re +
            iteratedDeriv 2 F (xf (zeroEntry e ω)) / 2 *
              (Kf 0 1 0 (zeroEntry e ω) + Kf 0 0 1 (zeroEntry e ω)).re ^ 2) +
          (-entryVal e ω) ^ 3 * (iteratedDeriv 1 F (xf (zeroEntry e ω)) *
            (odpA (fun k s t => Kf k s t (zeroEntry e ω)) 3).re +
            iteratedDeriv 2 F (xf (zeroEntry e ω)) *
              (odpA (fun k s t => Kf k s t (zeroEntry e ω)) 1).re *
              (odpA (fun k s t => Kf k s t (zeroEntry e ω)) 2).re) +
          (-entryVal e ω) ^ 4 * (iteratedDeriv 1 F (xf (zeroEntry e ω)) *
            (odpA (fun k s t => Kf k s t (zeroEntry e ω)) 4).re)) := by
      have h2 := odpC2_eq F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) (hIm _)
      simp only [hYdef] at h2 ⊢
      rw [h2, hT]
      unfold odpC1 odpC3 odpC4
      ring
    rw [hY]
    exact halg
  have hYbad : ∀ ω, |Y ω| ≤ (5 * Φc) * (1 + (-entryVal e ω) ^ 4) := by
    intro ω
    obtain ⟨b1, b2, -, b3, b4⟩ := hcb (zeroEntry e ω)
    have hdiff : |F (xf ω) - F (xf (zeroEntry e ω))| ≤ Φc := by
      have h := ward_abs_sub_le hF4 (R := Ab) (B := K₀) (fun ζ hζ => (hFd ζ hζ).1)
        (hxA (zeroEntry e ω)) (hxA ω)
      have hd : |xf ω - xf (zeroEntry e ω)| ≤ 2 * Ab := by
        have := abs_sub (xf ω) (xf (zeroEntry e ω))
        linarith [hxA ω, hxA (zeroEntry e ω)]
      calc _ ≤ K₀ * |xf ω - xf (zeroEntry e ω)| := h
        _ ≤ K₀ * (2 * Ab) := mul_le_mul_of_nonneg_left hd hK₀0
        _ ≤ Φc := by rw [hΦc]; nlinarith
    obtain ⟨w, hw⟩ : ∃ w, w = -entryVal e ω := ⟨_, rfl⟩
    have hwk : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → |w ^ k| ≤ 1 + w ^ 4 := by
      intro k hk1 hk4
      rw [abs_pow]
      by_cases h : |w| ≤ 1
      · have : |w| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg w) h
        have : 0 ≤ w ^ 4 := by positivity
        linarith
      · push Not at h
        have : |w| ^ k ≤ |w| ^ 4 := pow_le_pow_right₀ h.le hk4
        have e4 : |w| ^ 4 = w ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
        linarith
    have t : ∀ (c : ℝ) (k : ℕ), |c| ≤ Φc → 1 ≤ k → k ≤ 4 → |c * w ^ k| ≤ Φc * (1 + w ^ 4) :=
      fun c k hc hk1 hk4 => by
        rw [abs_mul]; exact mul_le_mul hc (hwk k hk1 hk4) (abs_nonneg _) hΦc0
    have t1 := t _ 1 b1 le_rfl (by norm_num)
    have t2 := t _ 2 b2 (by norm_num) (by norm_num)
    have t3 := t _ 3 b3 (by norm_num) (by norm_num)
    have t4 := t _ 4 b4 (by norm_num) le_rfl
    have hw4 : 0 ≤ w ^ 4 := by positivity
    simp only [hYdef]
    rw [← hw]
    calc _ ≤ |F (xf ω) - F (xf (zeroEntry e ω))| +
          (|odpC1 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) * w ^ 1| +
            |odpC2 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) * w ^ 2| +
            |odpC3 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) * w ^ 3| +
            |odpC4 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) * w ^ 4|) := by
          refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
          refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
          exact abs_add_le _ _
      _ ≤ (5 * Φc) * (1 + w ^ 4) := by
          have := mul_nonneg hΦc0 hw4
          linarith
  -- the three expectations
  have hEY := odp_abs_integral_le hYi (hwi 6 (by norm_num)) hδ0 (by positivity : 0 ≤ 5 * Φc) hτ
    hYgood hYbad
  have hd34 : ∀ {h : Entries N → ℝ} {δ' : ℝ}, Continuous h → (∀ ω, |h ω| ≤ Φc) → 0 ≤ δ' →
      (∀ ω ∈ Ω, |h (zeroEntry e ω)| ≤ δ') → |∫ ω, h (zeroEntry e ω) ∂L.law| ≤ δ' + Φc * pΩ := by
    intro h δ' hc hb hδ' hgood
    have := ward_integral_sub_le (μ := L.law) (f := fun ω => h (zeroEntry e ω)) (g := fun _ => 0)
      (hbd hc hb) (integrable_const 0) (T := Ωᶜ) hδ'
      (fun ω hω => by
        simp only [sub_zero]
        exact hgood ω (by simpa using hω))
      (fun ω => by simp only [sub_zero]; exact hb _)
    simp only [integral_const, smul_zero, sub_zero] at this
    calc _ ≤ δ' + Φc * (L.law Ωᶜ).toReal := this
      _ ≤ δ' + Φc * pΩ := by gcongr
  have hE3 : |∫ ω, (odpC3 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) -
      odpG3 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω))) ∂L.law| ≤
      G * (γ + α ^ 2) + Φc * pΩ := by
    refine hd34 (h := fun ω => odpC3 F (xf ω) (fun k s t => Kf k s t ω) -
      odpG3 F (xf ω) (fun k s t => Kf k s t ω)) (hc3.sub hg3)
      (fun ω => (hcb ω).2.2.1) (by positivity) fun ω hω => ?_
    obtain ⟨-, -, -, hA, -, hγω⟩ := hΩ ω hω
    obtain ⟨hbR, -, -⟩ := hgoodR ω hω
    obtain ⟨g1, g2, -⟩ := hG _ hbR
    have e3 : odpC3 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) -
        odpG3 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) =
        iteratedDeriv 1 F (xf (zeroEntry e ω)) *
          (Kf 0 2 1 (zeroEntry e ω) + Kf 0 1 2 (zeroEntry e ω) + Kf 1 3 0 (zeroEntry e ω) +
            Kf 1 2 1 (zeroEntry e ω) + Kf 1 1 2 (zeroEntry e ω) + Kf 1 0 3 (zeroEntry e ω)).re +
        iteratedDeriv 2 F (xf (zeroEntry e ω)) *
          (odpA (fun k s t => Kf k s t (zeroEntry e ω)) 1).re *
          (odpA (fun k s t => Kf k s t (zeroEntry e ω)) 2).re := by
      rw [odpG3_eq]
      unfold odpC3
      rw [odp_A3_eq, Complex.add_re]
      ring
    rw [e3]
    have hA1 := hA 1 le_rfl (by norm_num)
    have hA2 := hA 2 (by norm_num) (by norm_num)
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul]
    have p1 := mul_le_mul g1 hγω (abs_nonneg _) hG0
    have p2 := mul_le_mul (mul_le_mul g2 hA1 (abs_nonneg _) hG0) hA2 (abs_nonneg _)
      (mul_nonneg hG0 hα)
    have e' : G * (γ + α ^ 2) = G * γ + G * α * α := by ring
    rw [e']
    exact add_le_add p1 p2
  have hE4 : |∫ ω, odpC4 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) ∂L.law| ≤
      G * α + Φc * pΩ := by
    refine hd34 (h := fun ω => odpC4 F (xf ω) (fun k s t => Kf k s t ω)) hc4
      (fun ω => (hcb ω).2.2.2.2)
      (by positivity) fun ω hω => ?_
    obtain ⟨-, -, -, hA, -, -⟩ := hΩ ω hω
    obtain ⟨hbR, -, -⟩ := hgoodR ω hω
    unfold odpC4
    rw [abs_mul]
    exact mul_le_mul (hG _ hbR).1 (hA 4 (by norm_num) le_rfl) (abs_nonneg _) hG0
  -- assembly
  have hbd' : ∀ {c : Entries N → ℝ} {C : ℝ}, Continuous c → (∀ ω, |c ω| ≤ C) →
      Integrable (fun ω => c (zeroEntry e ω)) L.law := fun {c} {C} hc hcb =>
    Integrable.of_bound (hc.comp hQc).aestronglyMeasurable C
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hcb _)
  have i3' := hbd' hc3 (fun ω => (hcb ω).2.2.2.1)
  have ig := hbd' hg3 (C := 2 * Φc) fun ω => by
    have h1 := (hcb ω).2.2.1
    have h2 := (hcb ω).2.2.2.1
    have := abs_sub_abs_le_abs_sub (odpG3 F (xf ω) (fun k s t => Kf k s t ω))
      (odpC3 F (xf ω) (fun k s t => Kf k s t ω))
    rw [abs_sub_comm] at this
    linarith
  have hsplit := integral_sub i3' ig
  have hkey : ∫ ω, F (xf ω) ∂L.law - ∫ ω, F (xf (zeroEntry e ω)) ∂L.law -
      (∫ ω, odpC2 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) ∂L.law) *
        L.entryMoment e 2 -
      (∫ ω, odpG3 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) ∂L.law) *
        L.entryMoment e 3 =
      ∫ ω, Y ω ∂L.law +
        (∫ ω, (odpC3 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) -
          odpG3 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω))) ∂L.law) *
          L.entryMoment e 3 +
        (∫ ω, odpC4 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) ∂L.law) *
          L.entryMoment e 4 := by
    rw [hYint, hn1, hsplit]; ring
  rw [hkey]
  have hEY' : |∫ ω, Y ω ∂L.law| ≤ δ + 5 * Φc * ((1 + τ ^ 2) * pΩ + m6 / τ) := by
    refine hEY.trans ?_
    gcongr
  calc _ ≤ |∫ ω, Y ω ∂L.law| +
        |∫ ω, (odpC3 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) -
          odpG3 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω))) ∂L.law| *
          |L.entryMoment e 3| +
        |∫ ω, odpC4 F (xf (zeroEntry e ω)) (fun k s t => Kf k s t (zeroEntry e ω)) ∂L.law| *
          |L.entryMoment e 4| := by
        rw [← abs_mul, ← abs_mul]
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact abs_add_le _ _
    _ ≤ (δ + 5 * Φc * ((1 + τ ^ 2) * pΩ + m6 / τ)) + (G * (γ + α ^ 2) + Φc * pΩ) * m3 +
        (G * α + Φc * pΩ) * m4 :=
        add_le_add (add_le_add hEY' (mul_le_mul hE3 hm3 (abs_nonneg _)
          (add_nonneg (mul_nonneg hG0 (by positivity)) (mul_nonneg hΦc0 hpΩ0))))
          (mul_le_mul hE4 hm4 (abs_nonneg _)
            (add_nonneg (mul_nonneg hG0 hα) (mul_nonneg hΦc0 hpΩ0)))
    _ = _ := by ring

/-! ### The exponent bookkeeping of [16] (6.70)–(6.76) -/

set_option maxHeartbeats 1000000 in
-- seven polynomial inequalities in five variables are checked in one proof
/-- The parameter rows of the off-diagonal step on `Ω`, in the variables `z = N^{-1/3}`,
`q = N^{-φs}`, `y = N^ε`, `y₀ = N^{C₀ε}`, `g = N^{C₁ε}` (`q ≤ z`): with `B = yq`,
`α = 2^25 z y⁹`, `β = 2^22 z³ y⁶`, `γ = 2^24 z² y^12`, `T₀ = z⁵ q y₀`, `n₃ ≤ C_A z³ q` and
`n₄ ≤ C_A z³ q²`, the bound of `odp_perLaw` on `Ω` is at most `½ z⁵ q g y₀³ y^40`
(`= ½ N^{-5/3-φs+(C₁+3C₀+40)ε}`) once `y^10 ≥ 2^86 (1 + C_A)`. -/
private lemma odp_numeric {z q y y₀ g CA : ℝ} (hq : 0 < q) (hqz : q ≤ z) (hz1 : z ≤ 1)
    (hy : 1 ≤ y) (hy₀ : 1 ≤ y₀) (hg : 0 ≤ g) (hCA : 0 ≤ CA) (hybig : 2 ^ 86 * (1 + CA) ≤ y ^ 10) :
    (g * (z ^ 5 * q * y₀) + g / 2 * (16 * (y * q) ^ 4 * (2 ^ 25 * z * y ^ 9) ^ 2 +
        (y * q) ^ 2 * (2 ^ 22 * z ^ 3 * y ^ 6) *
          (2 * (2 ^ 25 * z * y ^ 9) + 2 ^ 22 * z ^ 3 * y ^ 6) +
        z ^ 5 * q * y₀ * (8 * (y * q) * (2 ^ 25 * z * y ^ 9) + z ^ 5 * q * y₀)) +
      g / 6 * (4 * (y * q) * (2 ^ 25 * z * y ^ 9) + z ^ 5 * q * y₀) ^ 3) +
      CA * z ^ 3 * q * (g * (2 ^ 24 * z ^ 2 * y ^ 12 + (2 ^ 25 * z * y ^ 9) ^ 2)) +
      CA * z ^ 3 * q ^ 2 * (g * (2 ^ 25 * z * y ^ 9)) ≤
      1 / 2 * (z ^ 5 * q * g * y₀ ^ 3 * y ^ 40) := by
  have hz : 0 < z := lt_of_lt_of_le hq hqz
  have hy0 : 0 ≤ y := by linarith
  have hy₀0 : 0 ≤ y₀ := by linarith
  set M := g * z ^ 5 * q * y ^ 30 * y₀ ^ 3 with hM
  have hM0 : 0 ≤ M := by positivity
  have hyp : ∀ a b : ℕ, a ≤ b → y ^ a ≤ y ^ b := fun a b h => pow_le_pow_right₀ hy h
  have hy₀3 : y₀ ≤ y₀ ^ 3 := by
    calc y₀ = y₀ ^ 1 := (pow_one _).symm
      _ ≤ y₀ ^ 3 := pow_le_pow_right₀ hy₀ (by norm_num)
  have hy₀3' : 1 ≤ y₀ ^ 3 := one_le_pow₀ hy₀
  have hy₀2 : y₀ ^ 2 ≤ y₀ ^ 3 := pow_le_pow_right₀ hy₀ (by norm_num)
  have hq2 : q ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ hq.le hqz 2
  have hq3 : q ^ 3 ≤ z ^ 3 := pow_le_pow_left₀ hq.le hqz 3
  have hz4 : z ^ 4 ≤ 1 := pow_le_one₀ hz.le hz1
  have hzq : z * q ≤ 1 := by nlinarith
  have hgzq : 0 ≤ g * z ^ 5 * q := by positivity
  have hMle : ∀ a : ℕ, a ≤ 30 → g * z ^ 5 * q * y ^ a ≤ M := fun a ha => by
    have := mul_le_mul (hyp a 30 ha) hy₀3' zero_le_one (by positivity)
    calc g * z ^ 5 * q * y ^ a = (g * z ^ 5 * q) * (y ^ a * 1) := by ring
      _ ≤ (g * z ^ 5 * q) * (y ^ 30 * y₀ ^ 3) := mul_le_mul_of_nonneg_left this hgzq
      _ = M := by ring
  -- the seven terms
  have a1 : g * (z ^ 5 * q * y₀) ≤ M := by
    have h1 : (1 : ℝ) ≤ y ^ 30 := one_le_pow₀ hy
    calc g * (z ^ 5 * q * y₀) = (g * z ^ 5 * q) * (1 * y₀) := by ring
      _ ≤ (g * z ^ 5 * q) * (y ^ 30 * y₀ ^ 3) := by gcongr
      _ = M := by ring
  have a2 : g / 2 * (16 * (y * q) ^ 4 * (2 ^ 25 * z * y ^ 9) ^ 2) ≤ 2 ^ 53 * M := by
    calc _ = 2 ^ 53 * (g * z ^ 2 * q * y ^ 22) * q ^ 3 := by ring
      _ ≤ 2 ^ 53 * (g * z ^ 2 * q * y ^ 22) * z ^ 3 := by gcongr
      _ = 2 ^ 53 * (g * z ^ 5 * q * y ^ 22) := by ring
      _ ≤ 2 ^ 53 * M := mul_le_mul_of_nonneg_left (hMle 22 (by norm_num)) (by norm_num)
  have a3 : g / 2 * ((y * q) ^ 2 * (2 ^ 22 * z ^ 3 * y ^ 6) *
      (2 * (2 ^ 25 * z * y ^ 9) + 2 ^ 22 * z ^ 3 * y ^ 6)) ≤ 2 ^ 48 * M := by
    have hb : 2 * (2 ^ 25 * z * y ^ 9) + 2 ^ 22 * z ^ 3 * y ^ 6 ≤ 2 ^ 27 * z * y ^ 9 := by
      have : z ^ 3 * y ^ 6 ≤ z * y ^ 9 := by
        have h1 : z ^ 3 ≤ z := by
          calc z ^ 3 ≤ z ^ 1 := pow_le_pow_of_le_one hz.le hz1 (by norm_num)
            _ = z := pow_one z
        have h2 : y ^ 6 ≤ y ^ 9 := hyp 6 9 (by norm_num)
        exact mul_le_mul h1 h2 (by positivity) hz.le
      nlinarith
    calc _ ≤ g / 2 * ((y * q) ^ 2 * (2 ^ 22 * z ^ 3 * y ^ 6) * (2 ^ 27 * z * y ^ 9)) := by
          gcongr
      _ = 2 ^ 48 * (g * z ^ 4 * q * y ^ 17) * q := by ring
      _ ≤ 2 ^ 48 * (g * z ^ 4 * q * y ^ 17) * z := by gcongr
      _ = 2 ^ 48 * (g * z ^ 5 * q * y ^ 17) := by ring
      _ ≤ 2 ^ 48 * M := mul_le_mul_of_nonneg_left (hMle 17 (by norm_num)) (by norm_num)
  have hT : z ^ 5 * q * y₀ ≤ z * q * y ^ 10 * y₀ := by
    have h1 : z ^ 5 ≤ z := by
      calc z ^ 5 ≤ z ^ 1 := pow_le_pow_of_le_one hz.le hz1 (by norm_num)
        _ = z := pow_one z
    have h2 : (1 : ℝ) ≤ y ^ 10 := one_le_pow₀ hy
    calc z ^ 5 * q * y₀ = z ^ 5 * q * 1 * y₀ := by ring
      _ ≤ z * q * y ^ 10 * y₀ := by gcongr
  have hD : 4 * (y * q) * (2 ^ 25 * z * y ^ 9) + z ^ 5 * q * y₀ ≤ 2 ^ 28 * z * q * y ^ 10 * y₀ := by
    have : 2 ^ 27 * z * q * y ^ 10 ≤ 2 ^ 27 * z * q * y ^ 10 * y₀ := by
      have : 0 ≤ 2 ^ 27 * z * q * y ^ 10 := by positivity
      nlinarith
    have e : 4 * (y * q) * (2 ^ 25 * z * y ^ 9) = 2 ^ 27 * z * q * y ^ 10 := by ring
    have hT' : z ^ 5 * q * y₀ ≤ 2 ^ 27 * (z * q * y ^ 10 * y₀) := by
      have : 0 ≤ z * q * y ^ 10 * y₀ := by positivity
      nlinarith
    nlinarith
  have a4 : g / 2 * (z ^ 5 * q * y₀ * (8 * (y * q) * (2 ^ 25 * z * y ^ 9) + z ^ 5 * q * y₀)) ≤
      2 ^ 28 * M := by
    have hb : 8 * (y * q) * (2 ^ 25 * z * y ^ 9) + z ^ 5 * q * y₀ ≤ 2 ^ 29 * y ^ 10 * y₀ := by
      have e : 8 * (y * q) * (2 ^ 25 * z * y ^ 9) = 2 ^ 28 * (z * q) * y ^ 10 := by ring
      have h1 : 2 ^ 28 * (z * q) * y ^ 10 ≤ 2 ^ 28 * y ^ 10 * y₀ := by
        have : 0 ≤ 2 ^ 28 * y ^ 10 := by positivity
        have : 2 ^ 28 * (z * q) * y ^ 10 ≤ 2 ^ 28 * 1 * y ^ 10 := by gcongr
        nlinarith
      have h2 : z ^ 5 * q * y₀ ≤ 2 ^ 28 * y ^ 10 * y₀ := by
        have : z * q * y ^ 10 * y₀ ≤ 1 * y ^ 10 * y₀ := by gcongr
        have : 0 ≤ y ^ 10 * y₀ := by positivity
        nlinarith
      linarith
    calc _ ≤ g / 2 * (z ^ 5 * q * y₀ * (2 ^ 29 * y ^ 10 * y₀)) := by gcongr
      _ = 2 ^ 28 * (g * z ^ 5 * q) * (y ^ 10 * y₀ ^ 2) := by ring
      _ ≤ 2 ^ 28 * (g * z ^ 5 * q) * (y ^ 30 * y₀ ^ 3) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hyp 10 30 (by norm_num)) hy₀2 (by positivity)
            (by positivity)) (by positivity)
      _ = 2 ^ 28 * M := by ring
  have a5 : g / 6 * (4 * (y * q) * (2 ^ 25 * z * y ^ 9) + z ^ 5 * q * y₀) ^ 3 ≤ 2 ^ 84 * M := by
    have h0 : 0 ≤ 4 * (y * q) * (2 ^ 25 * z * y ^ 9) + z ^ 5 * q * y₀ := by positivity
    calc _ ≤ g / 6 * (2 ^ 28 * z * q * y ^ 10 * y₀) ^ 3 := by gcongr
      _ = (2 ^ 84 / 6) * (g * z ^ 3 * q * y ^ 30 * y₀ ^ 3) * q ^ 2 := by ring
      _ ≤ (2 ^ 84 / 6) * (g * z ^ 3 * q * y ^ 30 * y₀ ^ 3) * z ^ 2 := by gcongr
      _ = (2 ^ 84 / 6) * M := by ring
      _ ≤ 2 ^ 84 * M := by nlinarith
  have a6 : CA * z ^ 3 * q * (g * (2 ^ 24 * z ^ 2 * y ^ 12 + (2 ^ 25 * z * y ^ 9) ^ 2)) ≤
      2 ^ 51 * CA * M := by
    have hb : 2 ^ 24 * z ^ 2 * y ^ 12 + (2 ^ 25 * z * y ^ 9) ^ 2 ≤ 2 ^ 51 * z ^ 2 * y ^ 30 := by
      have h1 : y ^ 12 ≤ y ^ 30 := hyp 12 30 (by norm_num)
      have h2 : y ^ 18 ≤ y ^ 30 := hyp 18 30 (by norm_num)
      have e : (2 ^ 25 * z * y ^ 9) ^ 2 = 2 ^ 50 * z ^ 2 * y ^ 18 := by ring
      rw [e]
      have : 0 ≤ z ^ 2 := by positivity
      nlinarith
    calc _ ≤ CA * z ^ 3 * q * (g * (2 ^ 51 * z ^ 2 * y ^ 30)) := by gcongr
      _ = 2 ^ 51 * CA * (g * z ^ 5 * q * y ^ 30) := by ring
      _ ≤ 2 ^ 51 * CA * M := mul_le_mul_of_nonneg_left (hMle 30 le_rfl) (by positivity)
  have a7 : CA * z ^ 3 * q ^ 2 * (g * (2 ^ 25 * z * y ^ 9)) ≤ 2 ^ 25 * CA * M := by
    calc _ = 2 ^ 25 * CA * (g * z ^ 4 * q * y ^ 9) * q := by ring
      _ ≤ 2 ^ 25 * CA * (g * z ^ 4 * q * y ^ 9) * z := by gcongr
      _ = 2 ^ 25 * CA * (g * z ^ 5 * q * y ^ 9) := by ring
      _ ≤ 2 ^ 25 * CA * M := mul_le_mul_of_nonneg_left (hMle 9 (by norm_num)) (by positivity)
  have hsum : (1 + 2 ^ 53 + 2 ^ 48 + 2 ^ 28 + 2 ^ 84 + (2 ^ 51 + 2 ^ 25) * CA) * M ≤
      2 ^ 85 * (1 + CA) * M := by
    have : (1 + 2 ^ 53 + 2 ^ 48 + 2 ^ 28 + 2 ^ 84 + (2 ^ 51 + 2 ^ 25) * CA : ℝ) ≤
        2 ^ 85 * (1 + CA) := by linarith
    exact mul_le_mul_of_nonneg_right this hM0
  have hfin : 2 ^ 85 * (1 + CA) * M ≤ 1 / 2 * (z ^ 5 * q * g * y₀ ^ 3 * y ^ 40) := by
    have e : 1 / 2 * (z ^ 5 * q * g * y₀ ^ 3 * y ^ 40) = 1 / 2 * M * y ^ 10 := by
      rw [hM]; ring
    rw [e]
    have : 2 ^ 85 * (1 + CA) * M = 1 / 2 * M * (2 ^ 86 * (1 + CA)) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hybig (by positivity)
  linarith

/-- The contribution of `Ωᶜ`: with `A = 32 N⁸`, `Φ_c = 256 CF (1 + A)^CF A²`, `τ = N^{D+4}`,
`D = 8 CF + 16`, moments `|n₃|, |n₄|, E h⁶ ≤ C_A` and `P(Ωᶜ) ≤ N^{-(3D+12)}`, it is at most `N⁻³/2`
once `N ≥ 2^19 CF 64^CF (10 + 7 C_A)`. -/
private lemma odp_offpart {x CF CA pΩ m3 m4 : ℝ} (hx : 1 ≤ x) (hCF : 0 ≤ CF) (hCA : 0 ≤ CA)
    (hm3 : m3 ≤ CA) (hm4 : m4 ≤ CA) (hm30 : 0 ≤ m3) (hm40 : 0 ≤ m4)
    (hp0 : 0 ≤ pΩ) (hp : pΩ ≤ x ^ (-(3 * (8 * CF + 16) + 12)))
    (hxbig : 2 * (2 ^ 18 * CF * 64 ^ CF) * (10 + 7 * CA) ≤ x) :
    5 * (256 * (CF * (1 + 32 * x ^ 8) ^ CF) * (32 * x ^ 8) ^ 2) *
        ((1 + (x ^ (8 * CF + 16 + 4)) ^ 2) * pΩ + CA / x ^ (8 * CF + 16 + 4)) +
      m3 * (256 * (CF * (1 + 32 * x ^ 8) ^ CF) * (32 * x ^ 8) ^ 2 * pΩ) +
      m4 * (256 * (CF * (1 + 32 * x ^ 8) ^ CF) * (32 * x ^ 8) ^ 2 * pΩ) ≤ x ^ (-3 : ℝ) / 2 := by
  have hx0 : 0 < x := by linarith
  set D : ℝ := 8 * CF + 16 with hD
  set K₁ : ℝ := 2 ^ 18 * CF * 64 ^ CF with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  set Φ := 256 * (CF * (1 + 32 * x ^ 8) ^ CF) * (32 * x ^ 8) ^ 2 with hΦ
  have hΦ0 : 0 ≤ Φ := by positivity
  have hΦle : Φ ≤ K₁ * x ^ D := by
    have h1 : 1 + 32 * x ^ 8 ≤ 64 * x ^ 8 := by
      have : (1 : ℝ) ≤ x ^ 8 := one_le_pow₀ hx
      linarith
    have h2 : (1 + 32 * x ^ 8) ^ CF ≤ 64 ^ CF * x ^ (8 * CF) := by
      calc (1 + 32 * x ^ 8) ^ CF ≤ (64 * x ^ 8) ^ CF := Real.rpow_le_rpow (by positivity) h1 hCF
        _ = 64 ^ CF * (x ^ 8) ^ CF := Real.mul_rpow (by norm_num) (by positivity)
        _ = 64 ^ CF * x ^ (8 * CF) := by
            rw [← Real.rpow_natCast x 8, ← Real.rpow_mul hx0.le]; norm_num
    have h3 : x ^ D = x ^ (8 * CF) * x ^ 16 := by
      rw [hD, Real.rpow_add hx0, show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hΦ, h3, hK₁]
    calc 256 * (CF * (1 + 32 * x ^ 8) ^ CF) * (32 * x ^ 8) ^ 2 ≤
        256 * (CF * (64 ^ CF * x ^ (8 * CF))) * (32 * x ^ 8) ^ 2 := by gcongr
      _ = 2 ^ 18 * CF * 64 ^ CF * (x ^ (8 * CF) * x ^ 16) := by ring
  have hτ0 : 0 < x ^ (D + 4) := Real.rpow_pos_of_pos hx0 _
  have hτ1 : 1 ≤ x ^ (D + 4) := Real.one_le_rpow hx (by rw [hD]; positivity)
  have hτsq : (x ^ (D + 4)) ^ 2 = x ^ (2 * D + 8) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
  have hxD : x ^ D * x ^ (2 * D + 8) * x ^ (-(3 * D + 12)) = x ^ (-4 : ℝ) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
  have hxD' : x ^ D / x ^ (D + 4) = x ^ (-4 : ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hx0.le, ← Real.rpow_add hx0]; congr 1; ring
  have hx4 : x ^ (-4 : ℝ) = x ^ (-3 : ℝ) * x⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hx0]; norm_num
  have hpD : 0 ≤ x ^ D := by positivity
  have hx3 : 0 ≤ x ^ (-3 : ℝ) := by positivity
  -- the term `E h⁶/τ`
  have t1 : 5 * Φ * (CA / x ^ (D + 4)) ≤ 5 * K₁ * CA * x ^ (-4 : ℝ) := by
    calc 5 * Φ * (CA / x ^ (D + 4)) ≤ 5 * (K₁ * x ^ D) * (CA / x ^ (D + 4)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΦle (by norm_num))
            (div_nonneg hCA hτ0.le)
      _ = 5 * K₁ * CA * (x ^ D / x ^ (D + 4)) := by ring
      _ = 5 * K₁ * CA * x ^ (-4 : ℝ) := by rw [hxD']
  -- the terms with `P(Ωᶜ)`
  have t2 : Φ * pΩ * (5 * (1 + (x ^ (D + 4)) ^ 2) + m3 + m4) ≤
      K₁ * (10 + 2 * CA) * x ^ (-4 : ℝ) := by
    have hsq1 : 1 ≤ (x ^ (D + 4)) ^ 2 := one_le_pow₀ hτ1
    have hb : 5 * (1 + (x ^ (D + 4)) ^ 2) + m3 + m4 ≤ (10 + 2 * CA) * x ^ (2 * D + 8) := by
      rw [← hτsq]; nlinarith
    calc Φ * pΩ * (5 * (1 + (x ^ (D + 4)) ^ 2) + m3 + m4) ≤
        (K₁ * x ^ D) * x ^ (-(3 * D + 12)) * ((10 + 2 * CA) * x ^ (2 * D + 8)) := by
          gcongr
      _ = K₁ * (10 + 2 * CA) * (x ^ D * x ^ (2 * D + 8) * x ^ (-(3 * D + 12))) := by ring
      _ = K₁ * (10 + 2 * CA) * x ^ (-4 : ℝ) := by rw [hxD]
  have hsum : 5 * Φ * ((1 + (x ^ (D + 4)) ^ 2) * pΩ + CA / x ^ (D + 4)) + m3 * (Φ * pΩ) +
      m4 * (Φ * pΩ) = 5 * Φ * (CA / x ^ (D + 4)) +
        Φ * pΩ * (5 * (1 + (x ^ (D + 4)) ^ 2) + m3 + m4) := by ring
  rw [hsum]
  have hfin : (5 * K₁ * CA + K₁ * (10 + 2 * CA)) * x ^ (-4 : ℝ) ≤ x ^ (-3 : ℝ) / 2 := by
    rw [hx4]
    have hxi : x⁻¹ * x = 1 := inv_mul_cancel₀ hx0.ne'
    have : (5 * K₁ * CA + K₁ * (10 + 2 * CA)) * 2 ≤ x := by nlinarith
    have hxi0 : 0 ≤ x⁻¹ := by positivity
    calc (5 * K₁ * CA + K₁ * (10 + 2 * CA)) * (x ^ (-3 : ℝ) * x⁻¹) =
        x ^ (-3 : ℝ) * x⁻¹ * ((5 * K₁ * CA + K₁ * (10 + 2 * CA)) * 2) / 2 := by ring
      _ ≤ x ^ (-3 : ℝ) * x⁻¹ * x / 2 := by gcongr
      _ = x ^ (-3 : ℝ) / 2 := by rw [mul_assoc, hxi, mul_one]
  linarith

set_option maxHeartbeats 1000000 in
-- the identities between the powers of `N` and the bounds on `Ω` are combined in one proof
/-- [16] (6.70)–(6.76) for one functional and one law `H_γ`: the bound
`N^{-5/3-φs+Cε}`, `C = (C₀ + 11) CF + 3 C₀ + 41`, from `odp_perLaw` with the sizes (6.59)–(6.68)
on `Ω` (`odp_sizes`), `odp_numeric` and `odp_offpart`; `C₀` is the constant of (6.69). -/
private lemma odp_assemble {N : ℕ} (hN : 1 ≤ N) {ε φs CF CA C₀ C0 : ℝ} (hε : 0 < ε)
    (hε' : ε < 1 / 10) (hφs : 1 / 3 < φs) (hφs' : φs ≤ 1 / 2) (hCF : 0 ≤ CF) (hCA : 0 < CA)
    (hC₀ : 0 < C₀) {L : EntryLaws N} (hL : L.IsGenWigner C0) (p : OffDiag N)
    (hA : ∀ k : ℕ, 2 ≤ k → k ≤ 6 → Integrable (fun x : ℝ => |x| ^ k) (L.entry (Sum.inr p)) ∧
      ∫ x, |x| ^ k ∂(L.entry (Sum.inr p)) ≤ CA * (N : ℝ)⁻¹ * (N : ℝ) ^ (φs * (2 - (k : ℝ))))
    {F : ℝ → ℝ} (hF4 : ContDiff ℝ 4 F)
    (hF : ∀ n ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF)
    (hG : ∀ ζ : ℝ, |ζ| ≤ (N : ℝ) ^ ((C₀ + 11) * ε) → ∀ n ∈ Finset.Icc 1 4,
      |iteratedDeriv n F ζ| ≤ (N : ℝ) ^ (((C₀ + 11) * CF + 1) * ε))
    (hy29 : 2 ^ 29 ≤ (N : ℝ) ^ ε) (hybig : 2 ^ 86 * (1 + CA) ≤ ((N : ℝ) ^ ε) ^ 10)
    (hxbig : 2 * (2 ^ 18 * CF * 64 ^ CF) * (10 + 7 * CA) ≤ (N : ℝ))
    {Ω : Set (Entries N)} (hp : (L.law Ωᶜ).toReal ≤ (N : ℝ) ^ (-(3 * (8 * CF + 16) + 12)))
    {xf : Entries N → ℝ} {Kf : ℕ → ℕ → ℕ → Entries N → ℂ} (hxc : Continuous xf)
    (hKc : ∀ k s t, Continuous (Kf k s t)) (hxA : ∀ ω, |xf ω| ≤ 32 * (N : ℝ) ^ 8)
    (hKA : ∀ ω k s t, k < 2 → s + t ≤ 4 → ‖Kf k s t ω‖ ≤ 32 * (N : ℝ) ^ 8)
    (hIm : ∀ ω, (Kf 0 1 0 ω + Kf 0 0 1 ω).im = 0)
    (hΩ : ∀ ω ∈ Ω, |entryVal (Sum.inr p) ω| ≤ (N : ℝ) ^ (ε - φs) ∧
      |xf ω| ≤ 2 * (N : ℝ) ^ (4 * ε) ∧
      ‖((xf ω - xf (zeroEntry (Sum.inr p) ω) : ℝ) : ℂ) -
          ∑ k ∈ Finset.range 2, ∑ s ∈ Finset.range 5, ∑ t ∈ Finset.range 5,
            if 1 ≤ s + t ∧ s + t ≤ 4 then
              (-(entryVal (Sum.inr p) ω : ℂ)) ^ (s + t) * Kf k s t (zeroEntry (Sum.inr p) ω)
            else 0‖ ≤ (N : ℝ) ^ (-(5 : ℝ) / 3 - φs + C₀ * ε) ∧
      ∃ W : ℝ, W ≤ 2 * (N : ℝ) ^ (-(4 : ℝ) / 3) ∧ ∀ k ≤ 1, ∀ s ≤ 4, ∀ t ≤ 4,
        ‖Kf k s t (zeroEntry (Sum.inr p) ω)‖ ≤ W * (4 * (N : ℝ) ^ (2 - k) *
          (odpX ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) k s *
            odpX ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) k t))) :
    |∫ ω, F (xf ω) ∂L.law - ∫ ω, F (xf (zeroEntry (Sum.inr p) ω)) ∂L.law -
        (∫ ω, odpC2 F (xf (zeroEntry (Sum.inr p) ω))
          (fun k s t => Kf k s t (zeroEntry (Sum.inr p) ω)) ∂L.law) *
          L.entryMoment (Sum.inr p) 2 -
        (∫ ω, odpG3 F (xf (zeroEntry (Sum.inr p) ω))
          (fun k s t => Kf k s t (zeroEntry (Sum.inr p) ω)) ∂L.law) *
          L.entryMoment (Sum.inr p) 3| ≤
      (N : ℝ) ^ (-(5 : ℝ) / 3 - φs + ((C₀ + 11) * CF + 3 * C₀ + 41) * ε) := by
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < N := by linarith
  -- the variables `z = N^{-1/3}`, `q = N^{-φs}`, `y = N^ε`, `y₀ = N^{C₀ε}`, `g = N^{C₁ε}`
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = (N : ℝ) ^ (-(1 : ℝ) / 3) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (N : ℝ) ^ (-φs) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (N : ℝ) ^ ε := ⟨_, rfl⟩
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ℝ, y₀ = (N : ℝ) ^ (C₀ * ε) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = (N : ℝ) ^ (((C₀ + 11) * CF + 1) * ε) := ⟨_, rfl⟩
  have hpw : ∀ (a : ℝ) (n : ℕ), ((N : ℝ) ^ a) ^ n = (N : ℝ) ^ (a * n) := fun a n =>
    (Real.rpow_mul_natCast hx0.le a n).symm
  have hz0 : 0 < z := hz ▸ Real.rpow_pos_of_pos hx0 _
  have hq0 : 0 < q := hq ▸ Real.rpow_pos_of_pos hx0 _
  have hqz : q ≤ z := by rw [hq, hz]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hz1 : z ≤ 1 := by
    rw [hz]; exact Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have hq1 : q ≤ 1 := hqz.trans hz1
  have hy1 : 1 ≤ y := by rw [hy]; exact Real.one_le_rpow hx1 hε.le
  have hy₀1 : 1 ≤ y₀ := by rw [hy₀]; exact Real.one_le_rpow hx1 (by positivity)
  have hg1 : 1 ≤ g := by rw [hg]; exact Real.one_le_rpow hx1 (by positivity)
  have hy0 : 0 ≤ y := by linarith
  -- the identities between the powers of `N`
  have exz : (N : ℝ) * z ^ 3 = 1 := by
    rw [hz, hpw, show (-(1 : ℝ) / 3 * ((3 : ℕ) : ℝ)) = -1 by norm_num, Real.rpow_neg_one,
      mul_inv_cancel₀ hx0.ne']
  have eP : (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) = z * y ^ 3 := by
    rw [hz, hy, hpw, ← Real.rpow_add hx0]; congr 1; push_cast; ring
  have eB : (N : ℝ) ^ (ε - φs) = y * q := by
    rw [hy, hq, ← Real.rpow_add hx0, sub_eq_add_neg]
  have eT : (N : ℝ) ^ (-(5 : ℝ) / 3 - φs + C₀ * ε) = z ^ 5 * q * y₀ := by
    rw [hz, hq, hy₀, hpw, ← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; push_cast; ring
  have eW : (N : ℝ) ^ (-(4 : ℝ) / 3) = z ^ 4 := by
    rw [hz, hpw]; congr 1; push_cast; ring
  have eR : (N : ℝ) ^ ((C₀ + 11) * ε) = y ^ 11 * y₀ := by
    rw [hy, hy₀, hpw, ← Real.rpow_add hx0]; congr 1; push_cast; ring
  have e4 : (N : ℝ) ^ (4 * ε) = y ^ 4 := by
    rw [hy, hpw]; congr 1; push_cast; ring
  have eFin : (N : ℝ) ^ (-(5 : ℝ) / 3 - φs + ((C₀ + 11) * CF + 3 * C₀ + 41) * ε) =
      z ^ 5 * q * g * y₀ ^ 3 * y ^ 40 := by
    rw [hz, hq, hg, hy₀, hy, hpw, hpw, hpw, ← Real.rpow_add hx0, ← Real.rpow_add hx0,
      ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1; push_cast; ring
  have e3 : (N : ℝ) ^ (-3 : ℝ) = z ^ 9 := by
    rw [hz, hpw]; congr 1; push_cast; ring
  have emk : ∀ k : ℕ, 2 ≤ k → (N : ℝ)⁻¹ * (N : ℝ) ^ (φs * (2 - (k : ℝ))) = z ^ 3 * q ^ (k - 2) := by
    intro k hk
    have h1 : (N : ℝ)⁻¹ = z ^ 3 := (eq_inv_of_mul_eq_one_right exz).symm
    rw [h1, hq, hpw]
    congr 2
    push_cast [Nat.cast_sub hk]
    ring
  -- the moments
  have hprob : IsProbabilityMeasure (L.entry (Sum.inr p)) := hL.isProb.off p
  have hm3 : |L.entryMoment (Sum.inr p) 3| ≤ CA * z ^ 3 * q := by
    have h := (hA 3 (by norm_num) (by norm_num)).2
    rw [mul_assoc, emk 3 (by norm_num)] at h
    calc |L.entryMoment (Sum.inr p) 3| ≤ ∫ x, |(-x) ^ 3| ∂(L.entry (Sum.inr p)) :=
          abs_integral_le_integral_abs
      _ = ∫ x, |x| ^ 3 ∂(L.entry (Sum.inr p)) := by
          congr 1; funext x; rw [abs_pow, abs_neg]
      _ ≤ CA * (z ^ 3 * q ^ (3 - 2)) := h
      _ = CA * z ^ 3 * q := by norm_num; ring
  have hm4 : |L.entryMoment (Sum.inr p) 4| ≤ CA * z ^ 3 * q ^ 2 := by
    have h := (hA 4 (by norm_num) (by norm_num)).2
    rw [mul_assoc, emk 4 (by norm_num)] at h
    calc |L.entryMoment (Sum.inr p) 4| ≤ ∫ x, |(-x) ^ 4| ∂(L.entry (Sum.inr p)) :=
          abs_integral_le_integral_abs
      _ = ∫ x, |x| ^ 4 ∂(L.entry (Sum.inr p)) := by
          congr 1; funext x; rw [abs_pow, abs_neg]
      _ ≤ CA * (z ^ 3 * q ^ (4 - 2)) := h
      _ = CA * z ^ 3 * q ^ 2 := by norm_num; ring
  have hm6 : ∫ x, x ^ 6 ∂(L.entry (Sum.inr p)) ≤ CA := by
    have h := (hA 6 (by norm_num) (by norm_num)).2
    rw [mul_assoc, emk 6 (by norm_num)] at h
    have e6 : ∫ x, x ^ 6 ∂(L.entry (Sum.inr p)) = ∫ x, |x| ^ 6 ∂(L.entry (Sum.inr p)) := by
      congr 1; funext x; rw [← abs_pow, abs_of_nonneg (by positivity)]
    have hzq : z ^ 3 * q ^ (6 - 2) ≤ 1 := by
      have : z ^ 3 ≤ 1 := pow_le_one₀ hz0.le hz1
      have : q ^ (6 - 2) ≤ 1 := pow_le_one₀ hq0.le hq1
      nlinarith [pow_nonneg hq0.le (6 - 2)]
    rw [e6]
    calc _ ≤ CA * (z ^ 3 * q ^ (6 - 2)) := h
      _ ≤ CA * 1 := mul_le_mul_of_nonneg_left hzq hCA.le
      _ = CA := mul_one _
  have hmom : ∀ k ≤ 6, Integrable (fun x : ℝ => x ^ k) (L.entry (Sum.inr p)) := by
    intro k hk
    have h6 := (hA 6 (by norm_num) le_rfl).1
    refine Integrable.mono' (h6.add (integrable_const 1)) (continuous_pow k).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    by_cases h : |x| ≤ 1
    · have : |x| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg x) h
      have : 0 ≤ |x| ^ 6 := by positivity
      simp only [Pi.add_apply]; linarith
    · push Not at h
      have : |x| ^ k ≤ |x| ^ 6 := pow_le_pow_right₀ h.le hk
      simp only [Pi.add_apply]; linarith
  have hn1 : L.entryMoment (Sum.inr p) 1 = 0 := by
    change ∫ x, (-x) ^ 1 ∂(L.off p) = 0
    simp only [pow_one]
    rw [integral_neg, hL.mean_off p, neg_zero]
  -- the bounds on `Ω`
  have hy29' : 2 ^ 29 ≤ y := hy ▸ hy29
  have hB1 : y * q ≤ 1 := by
    rw [← eB]; exact Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  have hP1 : (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  have hΩ' : ∀ ω ∈ Ω, |entryVal (Sum.inr p) ω| ≤ y * q ∧
      |xf ω| + (4 * (y * q) * (2 ^ 25 * z * y ^ 9) + z ^ 5 * q * y₀) ≤ y ^ 11 * y₀ ∧
      ‖((xf ω - xf (zeroEntry (Sum.inr p) ω) : ℝ) : ℂ) -
          ∑ k ∈ Finset.range 2, ∑ s ∈ Finset.range 5, ∑ t ∈ Finset.range 5,
            if 1 ≤ s + t ∧ s + t ≤ 4 then
              (-(entryVal (Sum.inr p) ω : ℂ)) ^ (s + t) * Kf k s t (zeroEntry (Sum.inr p) ω)
            else 0‖ ≤ z ^ 5 * q * y₀ ∧
      (∀ m, 1 ≤ m → m ≤ 4 →
        |(odpA (fun k s t => Kf k s t (zeroEntry (Sum.inr p) ω)) m).re| ≤ 2 ^ 25 * z * y ^ 9) ∧
      |(Kf 1 1 0 (zeroEntry (Sum.inr p) ω) + Kf 1 0 1 (zeroEntry (Sum.inr p) ω)).re| ≤
        2 ^ 22 * z ^ 3 * y ^ 6 ∧
      |(Kf 0 2 1 (zeroEntry (Sum.inr p) ω) + Kf 0 1 2 (zeroEntry (Sum.inr p) ω) +
        Kf 1 3 0 (zeroEntry (Sum.inr p) ω) + Kf 1 2 1 (zeroEntry (Sum.inr p) ω) +
        Kf 1 1 2 (zeroEntry (Sum.inr p) ω) + Kf 1 0 3 (zeroEntry (Sum.inr p) ω)).re| ≤
        2 ^ 24 * z ^ 2 * y ^ 12 := by
    intro ω hω
    obtain ⟨h1, h2, h3, W, hW, hK⟩ := hΩ ω hω
    have hsz := odp_sizes (K := fun k s t => Kf k s t (zeroEntry (Sum.inr p) ω)) hN exz hz0.le hy1
      eP (eP ▸ hP1) (hW.trans (by rw [eW])) hK
    refine ⟨eB ▸ h1, ?_, eT ▸ h3, hsz⟩
    rw [e4] at h2
    set a := y ^ 10 * y₀ with ha
    have ha1 : 1 ≤ a := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hy1) hy₀1
    have t1 : y ^ 4 ≤ a := by
      have : y ^ 4 ≤ y ^ 10 := pow_le_pow_right₀ hy1 (by norm_num)
      calc y ^ 4 ≤ y ^ 10 * 1 := by linarith
        _ ≤ a := mul_le_mul_of_nonneg_left hy₀1 (by positivity)
    have t2 : 4 * (y * q) * (2 ^ 25 * z * y ^ 9) ≤ 2 ^ 27 * a := by
      have hzq : z * q ≤ 1 := by nlinarith
      have hy10 : 0 ≤ y ^ 10 := by positivity
      calc 4 * (y * q) * (2 ^ 25 * z * y ^ 9) = 2 ^ 27 * ((z * q) * y ^ 10) := by ring
        _ ≤ 2 ^ 27 * (1 * (y ^ 10 * y₀)) := by
            gcongr
            nlinarith
        _ = 2 ^ 27 * a := by rw [ha]; ring
    have t3 : z ^ 5 * q * y₀ ≤ a := by
      have : z ^ 5 * q ≤ 1 := by
        have : z ^ 5 ≤ 1 := pow_le_one₀ hz0.le hz1
        nlinarith
      calc z ^ 5 * q * y₀ ≤ 1 * (1 * y₀) := by
            have := mul_le_mul_of_nonneg_right this (by linarith : (0 : ℝ) ≤ y₀)
            linarith
        _ ≤ a := by
            rw [ha]
            have : (1 : ℝ) ≤ y ^ 10 := one_le_pow₀ hy1
            nlinarith
    have t4 : 2 ^ 29 * a ≤ y ^ 11 * y₀ := by
      calc 2 ^ 29 * a ≤ y * a := mul_le_mul_of_nonneg_right hy29' (by positivity)
        _ = y ^ 11 * y₀ := by rw [ha]; ring
    linarith
  have hG' : ∀ ζ, |ζ| ≤ y ^ 11 * y₀ → |iteratedDeriv 1 F ζ| ≤ g ∧ |iteratedDeriv 2 F ζ| ≤ g ∧
      |iteratedDeriv 3 F ζ| ≤ g := fun ζ hζ => by
    rw [← eR] at hζ
    have := hG ζ hζ
    rw [← hg] at this
    exact ⟨this 1 (by simp), this 2 (by simp), this 3 (by simp)⟩
  have hAb : (1 : ℝ) ≤ 32 * (N : ℝ) ^ 8 := by
    have : (1 : ℝ) ≤ (N : ℝ) ^ 8 := one_le_pow₀ hx1
    linarith
  have key := odp_perLaw hL.isProb (Sum.inr p) hF4 hF hxc hKc hAb hxA hKA hIm hmom hn1 hm3 hm4 hm6
    hp (B := y * q) (α := 2 ^ 25 * z * y ^ 9) (β := 2 ^ 22 * z ^ 3 * y ^ 6)
    (γ := 2 ^ 24 * z ^ 2 * y ^ 12) (T₀ := z ^ 5 * q * y₀) (R₁ := y ^ 11 * y₀) (G := g)
    (τ := (N : ℝ) ^ (8 * CF + 16 + 4)) (by positivity) hB1 (by positivity) (by positivity)
    (by positivity) (by positivity) (by linarith) (Real.rpow_pos_of_pos hx0 _) hG' hΩ'
  have hnum := odp_numeric (g := g) hq0 hqz hz1 hy1 hy₀1 (by linarith) hCA.le (hy ▸ hybig)
  have hz3 : z ^ 3 ≤ 1 := pow_le_one₀ hz0.le hz1
  have hq2' : q ^ 2 ≤ 1 := pow_le_one₀ hq0.le hq1
  have hm3' : CA * z ^ 3 * q ≤ CA := by
    have : z ^ 3 * q ≤ 1 := by simpa using mul_le_mul hz3 hq1 hq0.le zero_le_one
    calc CA * z ^ 3 * q = CA * (z ^ 3 * q) := by ring
      _ ≤ CA * 1 := mul_le_mul_of_nonneg_left this hCA.le
      _ = CA := mul_one _
  have hm4' : CA * z ^ 3 * q ^ 2 ≤ CA := by
    have : z ^ 3 * q ^ 2 ≤ 1 := by simpa using mul_le_mul hz3 hq2' (by positivity) zero_le_one
    calc CA * z ^ 3 * q ^ 2 = CA * (z ^ 3 * q ^ 2) := by ring
      _ ≤ CA * 1 := mul_le_mul_of_nonneg_left this hCA.le
      _ = CA := mul_one _
  have hoff := odp_offpart (x := (N : ℝ)) (m3 := CA * z ^ 3 * q) (m4 := CA * z ^ 3 * q ^ 2)
    (pΩ := (N : ℝ) ^ (-(3 * (8 * CF + 16) + 12))) hx1 hCF hCA.le hm3' hm4' (by positivity)
    (by positivity) (Real.rpow_pos_of_pos hx0 _).le le_rfl hxbig
  have hz9 : z ^ 9 ≤ z ^ 5 * q * g * y₀ ^ 3 * y ^ 40 := by
    have hz4q : z ^ 4 ≤ q := by
      rw [hz, hq, hpw]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
    have h1 : (1 : ℝ) ≤ g * y₀ ^ 3 * y ^ 40 :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hg1 (one_le_pow₀ hy₀1))
        (one_le_pow₀ hy1)
    calc z ^ 9 = z ^ 5 * z ^ 4 * 1 := by ring
      _ ≤ z ^ 5 * q * (g * y₀ ^ 3 * y ^ 40) := by gcongr
      _ = _ := by ring
  rw [eFin]
  rw [e3] at hoff
  refine key.trans ((le_of_eq ?_).trans ((add_le_add hnum hoff).trans ?_))
  · ring
  · linarith only [hz9]

/-! ### (6.70)–(6.76) for every `H_γ` -/

/-- [16] (6.70)–(6.76) at `f = 0` for one off-diagonal entry `e = (b, d)` and every `H_γ`, both
functionals: with `Q` the matrix with the entry `e` set to zero and `n_k = E(-h_e)^k`,
`|E F(x_S) - E F(x_R) - E g(Q) n_2 - E g₃(Q) n_3| ≤ N^{-5/3-φs+Cε}` (`= N^{-1/3+Cε} p^{-4} q⁻¹`);
`C` depends only on `CF`. -/
theorem swap_expansion_largeQ {CF C0 φs : ℝ} (hC0 : 0 ≤ C0) (hφs : 1 / 3 < φs)
    (hφs' : φs ≤ 1 / 2) :
    ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < 1 / 10 → ∃ N0 : ℕ, ∀ N ≥ N0,
      ∀ L : EntryLaws N, (∃ Lv γ, LargeQClass C0 φs N Lv ∧ L = interp (lexPos N) γ Lv (goeLaws N)) →
      ∀ p : OffDiag N, ∀ F : ℝ → ℝ, ContDiff ℝ 4 F →
        (∀ n ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF) →
        (∀ E₁ E₂ : ℝ, |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |∫ ω, F (offWardInt (symOfEntries ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂) ∂L.law -
              ∫ ω, F (offWardInt (symOfEntries (zeroEntry (Sum.inr p) ω))
                ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂) ∂L.law -
              (∫ ω, swapBInt F (symOfEntries (zeroEntry (Sum.inr p) ω)) p
                ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂ ∂L.law) * L.entryMoment (Sum.inr p) 2 -
              (∫ ω, swapB3Int F (symOfEntries (zeroEntry (Sum.inr p) ω)) p
                ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂ ∂L.law) * L.entryMoment (Sum.inr p) 3| ≤
            (N : ℝ) ^ (-(5 : ℝ) / 3 - φs + C * ε)) ∧
        (∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |∫ ω, F (offWard (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩) ∂L.law -
              ∫ ω, F (offWard (symOfEntries (zeroEntry (Sum.inr p) ω))
                ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩) ∂L.law -
              (∫ ω, swapBPt F (symOfEntries (zeroEntry (Sum.inr p) ω)) p
                ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ ∂L.law) * L.entryMoment (Sum.inr p) 2 -
              (∫ ω, swapB3Pt F (symOfEntries (zeroEntry (Sum.inr p) ω)) p
                ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ ∂L.law) * L.entryMoment (Sum.inr p) 3| ≤
            (N : ℝ) ^ (-(5 : ℝ) / 3 - φs + C * ε)) := by
  obtain ⟨C₀, hC₀, hexp⟩ := offWard_sub_eq_sum_swapK hφs hφs'
  obtain ⟨CA, hCA, hmomA⟩ := entry_abs_pow_le_largeQInterp hC0 hφs hφs'
  refine ⟨(C₀ + 11) * |CF| + 3 * C₀ + 41, by positivity, fun ε hε hε' => ?_⟩
  by_cases hCF : 0 ≤ CF
  swap
  · refine ⟨0, fun N _ L _ p F _ hF => ?_⟩
    exfalso
    have h1 := hF 1 (by simp) 0
    exact hCF (by simpa using (abs_nonneg _).trans h1)
  rw [abs_of_nonneg hCF]
  obtain ⟨c, hc, Cb, hCb, N1, hHP⟩ := (apriori_largeQInterp_event hC0 hφs hφs' ε hε hε').inter
    (entryVal_le_largeQInterp hC0 hφs hφs' ε hε hε')
  obtain ⟨N2, hN2⟩ := norm_resolventC_zeroEntry_sub_le hφs hφs' ε hε hε'
  obtain ⟨N3, hN3⟩ := hexp ε hε hε'
  obtain ⟨N4, hN4⟩ := abs_iteratedDeriv_le_rpow_eps (CF := CF) (a := C₀ + 11) (by positivity) hε
  obtain ⟨N5, hN5⟩ := eventually_atTop.1 <|
    (eventually_ge_atTop 1).and <|
    (((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (2 ^ 86 * (1 + CA) + 2 ^ 29)).and <|
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop
      (2 * (2 ^ 18 * CF * 64 ^ CF) * (10 + 7 * CA))).and <|
    ward_rpow_mul_exp_le c (3 * (8 * CF + 16) + 12 + Cb) hc
  refine ⟨max (max N1 N2) (max (max N3 N4) N5), fun N hN L hL p F hF4 hF => ?_⟩
  have hNN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNN2 : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNN3 : N3 ≤ N :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hN
  have hNN4 : N4 ≤ N :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hN
  have hNN5 : N5 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨hN1, hyb, hxbig, hexpφ⟩ := hN5 N hNN5
  replace hyb : 2 ^ 86 * (1 + CA) + 2 ^ 29 ≤ (N : ℝ) ^ ε := hyb
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < N := by linarith
  have hy1 : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hn1 hε.le
  have hy29 : 2 ^ 29 ≤ (N : ℝ) ^ ε := by nlinarith
  have hybig : 2 ^ 86 * (1 + CA) ≤ ((N : ℝ) ^ ε) ^ 10 := by
    have : (N : ℝ) ^ ε ≤ ((N : ℝ) ^ ε) ^ 10 := by
      calc (N : ℝ) ^ ε = ((N : ℝ) ^ ε) ^ 1 := (pow_one _).symm
        _ ≤ ((N : ℝ) ^ ε) ^ 10 := pow_le_pow_right₀ hy1 (by norm_num)
    linarith
  -- the event `Ω`: (3.26) and `|v_e| ≤ N^ε q⁻¹` for every entry
  set Ω : Set (Entries N) := aprioriEvent N ε ∩
    {ω | ∀ e : Fin N ⊕ OffDiag N, |entryVal e ω| ≤ (N : ℝ) ^ (ε - φs)} with hΩdef
  have hp : (L.law Ωᶜ).toReal ≤ (N : ℝ) ^ (-(3 * (8 * CF + 16) + 12)) := by
    have h := hHP N hNN1 L hL
    have h' := ENNReal.toReal_le_of_le_ofReal (by positivity) h
    refine h'.trans ?_
    rw [Real.rpow_one]
    have hC : (N : ℝ) ^ Cb = (N : ℝ) ^ (Cb : ℝ) := (Real.rpow_natCast _ _).symm
    have e2 : (N : ℝ) ^ (3 * (8 * CF + 16) + 12 + (Cb : ℝ)) =
        (N : ℝ) ^ (3 * (8 * CF + 16) + 12) * (N : ℝ) ^ (Cb : ℝ) := Real.rpow_add hn0 _ _
    rw [e2] at hexpφ
    have hpos : 0 < (N : ℝ) ^ (3 * (8 * CF + 16) + 12) := Real.rpow_pos_of_pos hn0 _
    rw [Real.rpow_neg hn0.le, hC, ← one_div, le_div_iff₀ hpos]
    calc (N : ℝ) ^ (Cb : ℝ) * Real.exp (-c * phi N) * (N : ℝ) ^ (3 * (8 * CF + 16) + 12) =
        (N : ℝ) ^ (3 * (8 * CF + 16) + 12) * (N : ℝ) ^ (Cb : ℝ) * Real.exp (-c * phi N) := by ring
      _ ≤ 1 := hexpφ
  obtain ⟨Lv, γ, hLv, rfl⟩ := hL
  have hgw := interp_isGenWigner (Φ := lexPos N) (γ := γ) hLv.1 (goeLaws_isGenWigner N)
  have hA := fun k => hmomA N (by omega) _ ⟨Lv, γ, hLv, rfl⟩ (Sum.inr p) k
  have hG := fun ζ hζ => hN4 N hNN4 F hF ζ hζ
  have hη : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) := Real.rpow_pos_of_pos hn0 _
  have hηN : 1 / (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) ≤ N := by
    rw [one_div, ← Real.rpow_neg hn0.le]
    calc (N : ℝ) ^ (-(-(2 : ℝ) / 3 - ε)) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      _ = N := Real.rpow_one _
  have hP1 : (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hsw : ∀ ω ∈ Ω, ω ∈ swapEvent N ε φs (Sum.inr p) := fun ω hω => ⟨hω.1, hω.2 _⟩
  have hRb := fun ω (hω : ω ∈ Ω) => hN2 N hNN2 ω (Sum.inr p) hω.1 (hω.2 _)
  refine ⟨fun E₁ E₂ h1 h2 => ?_, fun E hE => ?_⟩
  · -- the functional (6.56)
    have hW := ode_weight hn1 h1 h2
    have hW2 : (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) * |E₂ - E₁| ≤ 2 := by
      have := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num : (-(4 : ℝ) / 3) ≤ 0)
      linarith
    exact odp_assemble hN1 hε hε' hφs hφs' hCF hCA hC₀ hgw p hA hF4 hF hG hy29 hybig hxbig hp
      (xf := fun ω => offWardInt (symOfEntries ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂)
      (Kf := fun k s t ω => swapK (symOfEntries ω) p ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂ k s t)
      (ward_continuous_b' hη E₁ E₂) (odp_continuous_swapK hη p E₁ E₂)
      (fun ω => odp_offWardInt_global hN1 (symOfEntries_isHermitian ω) hη hηN hW2)
      (fun ω k s t _ hst => odp_K_global hN1 (symOfEntries_isHermitian ω) hη hηN hW2 p hst)
      (fun ω => odp_K_im hη ω p E₁ E₂)
      (fun ω hω => ⟨hω.2 _, (aprioriEvent_bounds hN1 hε hε' hω.1).2.2 E₁ E₂ h1 h2,
        (hN3 N hNN3 ω p (hsw ω hω)).1 E₁ E₂ h1 h2,
        _, hW, odp_K_le hN1 hε hε' (hsw ω hω) (hRb ω hω) h1 h2 hP1⟩)
  · -- the functional `η² Σ_{i ≠ j} |G_ij(z)|²`
    have hz : 0 < (⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ : ℂ).im := hη
    have hx2 : ∀ ω ∈ Ω, |offWard (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩| ≤
        2 * (N : ℝ) ^ (4 * ε) := fun ω hω => by
      obtain ⟨h0, h1⟩ := (aprioriEvent_bounds hN1 hε hε' hω.1).2.1 E hE
      rw [abs_of_nonneg h0]
      have : (N : ℝ) ^ (2 * ε) ≤ (N : ℝ) ^ (4 * ε) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      have : 0 ≤ (N : ℝ) ^ (4 * ε) := by positivity
      linarith
    exact odp_assemble hN1 hε hε' hφs hφs' hCF hCA hC₀ hgw p hA hF4 hF hG hy29 hybig hxbig hp
      (xf := fun ω => offWard (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩)
      (Kf := fun k s t ω => swapKpt (symOfEntries ω) p ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k s t)
      (ward_continuous_b hη E) (odp_continuous_swapKpt hz p)
      (fun ω => odp_offWard_global hN1 (symOfEntries_isHermitian ω) hz)
      (fun ω k s t _ hst => odp_Kpt_global hN1 (symOfEntries_isHermitian ω) hz hηN p hst)
      (fun ω => odp_Kpt_im _ p _)
      (fun ω hω => ⟨hω.2 _, hx2 ω hω, (hN3 N hNN3 ω p (hsw ω hω)).2 E hE,
        _, ode_weight_sq hn1 hε, odp_Kpt_le hN1 hε hε' (hsw ω hω) (hRb ω hω) hE hP1⟩)

/-! ### `B` under `H_γ` and `H_{γ-1}` -/

/-- A real function of `Q` has the same expectation under `H_γ` and `H_{γ-1}`, `γ = lexPos N e`. -/
private lemma odp_integral_zeroEntry_interp {N : ℕ} {Lv : EntryLaws N} (hv : Lv.IsProb)
    (e : Fin N ⊕ OffDiag N) {f : Entries N → ℝ} (hf : Continuous f) :
    ∫ ω, f (zeroEntry e ω) ∂(interp (lexPos N) (lexPos N e) Lv (goeLaws N)).law =
      ∫ ω, f (zeroEntry e ω) ∂(interp (lexPos N) (lexPos N e - 1) Lv (goeLaws N)).law := by
  have hm : Measurable fun ω : Entries N => ((f ω : ℝ) : ℂ) :=
    (Complex.continuous_ofReal.comp hf).measurable
  have h := integral_zeroEntry_interp hv (goeLaws_isGenWigner N).isProb e _ hm
  have e1 := integral_ofReal (𝕜 := ℂ)
    (μ := (interp (lexPos N) (lexPos N e) Lv (goeLaws N)).law) (f := fun ω => f (zeroEntry e ω))
  have e2 := integral_ofReal (𝕜 := ℂ)
    (μ := (interp (lexPos N) (lexPos N e - 1) Lv (goeLaws N)).law)
    (f := fun ω => f (zeroEntry e ω))
  exact Complex.ofReal_injective (e1.symm.trans (h.trans e2))

/-- The second moment of an off-diagonal entry is `N⁻¹` for every generalized Wigner law. -/
private lemma odp_entryMoment_two {N : ℕ} {L : EntryLaws N} {C0 : ℝ} (hL : L.IsGenWigner C0)
    (p : OffDiag N) : L.entryMoment (Sum.inr p) 2 = (N : ℝ)⁻¹ := by
  change ∫ x, (-x) ^ 2 ∂(L.off p) = _
  simp only [neg_sq]
  exact hL.var_off p

/-- `B` of [16] (6.75) depends on the replaced entry only through its second moment: for
`γ = lexPos N e`, `E g(Q) · E h_e²` is the same under `H_γ` (entry from the law of Lemma 3.5) and
`H_{γ-1}` (Gaussian entry), for both functionals. -/
theorem swapB_interp_eq {C0 φs : ℝ} {N : ℕ} {Lv : EntryLaws N} (hv : LargeQClass C0 φs N Lv)
    (p : OffDiag N) (F : ℝ → ℝ) (hF : ContDiff ℝ 4 F) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (z : ℂ)
    (hz : 0 < z.im) :
    (∫ ω, swapBInt F (symOfEntries (zeroEntry (Sum.inr p) ω)) p η E₁ E₂
        ∂(interp (lexPos N) (lexPos N (Sum.inr p)) Lv (goeLaws N)).law) *
        (interp (lexPos N) (lexPos N (Sum.inr p)) Lv (goeLaws N)).entryMoment (Sum.inr p) 2 =
      (∫ ω, swapBInt F (symOfEntries (zeroEntry (Sum.inr p) ω)) p η E₁ E₂
        ∂(interp (lexPos N) (lexPos N (Sum.inr p) - 1) Lv (goeLaws N)).law) *
        (interp (lexPos N) (lexPos N (Sum.inr p) - 1) Lv (goeLaws N)).entryMoment (Sum.inr p) 2 ∧
    (∫ ω, swapBPt F (symOfEntries (zeroEntry (Sum.inr p) ω)) p z
        ∂(interp (lexPos N) (lexPos N (Sum.inr p)) Lv (goeLaws N)).law) *
        (interp (lexPos N) (lexPos N (Sum.inr p)) Lv (goeLaws N)).entryMoment (Sum.inr p) 2 =
      (∫ ω, swapBPt F (symOfEntries (zeroEntry (Sum.inr p) ω)) p z
        ∂(interp (lexPos N) (lexPos N (Sum.inr p) - 1) Lv (goeLaws N)).law) *
        (interp (lexPos N) (lexPos N (Sum.inr p) - 1) Lv (goeLaws N)).entryMoment (Sum.inr p) 2 := by
  have hw := fun γ : ℕ => interp_isGenWigner (Φ := lexPos N) (γ := γ) hv.1 (goeLaws_isGenWigner N)
  rw [odp_entryMoment_two (hw _) p, odp_entryMoment_two (hw _) p]
  refine ⟨?_, ?_⟩
  · rw [odp_integral_zeroEntry_interp hv.1.isProb (Sum.inr p)
      (f := fun ω => swapBInt F (symOfEntries ω) p η E₁ E₂) (odp_continuous_swapBInt hF hη p E₁ E₂)]
  · rw [odp_integral_zeroEntry_interp hv.1.isProb (Sum.inr p)
      (f := fun ω => swapBPt F (symOfEntries ω) p z) (odp_continuous_swapBPt hF hz p)]

/-! ### Checks -/

-- The entry law of Lemma 3.5 at `N = 1024` with diagonal values `±1/16, 0, 0` (variance `2/N`)
-- and off-diagonal values `±1/32` (variance `1/N`), in `LargeQClass 1 (2/5) 1024`.
open private lawA lawA_isGenWigner lawA_supp from WEdgeNS.EdgeUniv.LargeQClass

/-- Every hypothesis of `swap_expansion_largeQ` and of `swapB_interp_eq` at one point:
`N = 1024`, `C0 = 1`, `φs = 2/5`, `ε = 1/15` (the window `I_ε` is `|E - 2| ≤ 1/64`), `L = H_γ` with
`γ = 5000` between law A and the GOE (both entry types occur), `F = K(·/π)`,
`E₁ = 2 - 1/100 < E₂ = 2 + 1/100`, `E = 2`, `p = (0, 1)`; for `swapB_interp_eq` also `η = 1` and
`z = i`. -/
example : ∃ CF : ℝ, 0 < CF ∧ (0 : ℝ) ≤ 1 ∧ (1 / 3 : ℝ) < 2 / 5 ∧ (2 / 5 : ℝ) ≤ 1 / 2 ∧
    (0 : ℝ) < 1 / 15 ∧ (1 / 15 : ℝ) < 1 / 10 ∧ 0 ≤ 1024 ∧
    (∃ Lv γ, LargeQClass 1 (2 / 5) 1024 Lv ∧
      interp (lexPos 1024) 5000 lawA (goeLaws 1024) = interp (lexPos 1024) γ Lv (goeLaws 1024)) ∧
    LargeQClass 1 (2 / 5) 1024 lawA ∧
    ContDiff ℝ 4 (fun x => edgeCutoff (x / Real.pi)) ∧
    (∀ n ∈ Finset.Icc 1 4, ∀ x : ℝ,
      |iteratedDeriv n (fun x => edgeCutoff (x / Real.pi)) x| ≤ CF * (1 + |x|) ^ CF) ∧
    |(2 - 1 / 100 : ℝ) - 2| ≤ ((1024 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) ∧
    |(2 + 1 / 100 : ℝ) - 2| ≤ ((1024 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) ∧
    (2 - 1 / 100 : ℝ) < 2 + 1 / 100 ∧
    |(2 : ℝ) - 2| ≤ ((1024 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) ∧
    (0 : ℝ) < 1 ∧ 0 < Complex.I.im := by
  obtain ⟨CF, hCF, h⟩ := edgeCutoff_deriv_le
  refine ⟨CF, hCF, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    ⟨lawA, 5000, ⟨lawA_isGenWigner, lawA_supp⟩, rfl⟩, ⟨lawA_isGenWigner, lawA_supp⟩,
    (edgeCutoff_props.1 4).comp (contDiff_id.div_const _), h, ?_, ?_, by norm_num, ?_,
    one_pos, by simp⟩ <;>
  · rw [rpow_1024_window]; norm_num [abs_of_nonneg, abs_of_nonpos]

/-- `swapB_interp_eq` at `N = 1024`, `Lv = ` law A, `p = (0, 1)` (the laws `H_γ` and `H_{γ-1}`,
`γ = lexPos 1024 (0, 1)`), `F = K(·/π)`, `η = 1`, `[E₁, E₂] = [2 - 1/100, 2 + 1/100]`, `z = i`. -/
example := swapB_interp_eq (C0 := 1) (φs := 2 / 5) ⟨lawA_isGenWigner, lawA_supp⟩
  (⟨(0, 1), by decide⟩ : OffDiag 1024) (fun x => edgeCutoff (x / Real.pi))
  ((edgeCutoff_props.1 4).comp (contDiff_id.div_const _)) one_pos (2 - 1 / 100) (2 + 1 / 100)
  Complex.I (by simp)

/-- `entry_abs_pow_le_largeQInterp` at `C0 = 1`, `φs = 2/5`, `N = 1024`, `L = H_5000` between law
A and the GOE, `e = (0, 1)`, `k = 3`. -/
example : ∃ C > (0 : ℝ),
    Integrable (fun x : ℝ => |x| ^ 3)
      ((interp (lexPos 1024) 5000 lawA (goeLaws 1024)).entry (Sum.inr ⟨(0, 1), by decide⟩)) ∧
    ∫ x, |x| ^ 3 ∂((interp (lexPos 1024) 5000 lawA (goeLaws 1024)).entry
        (Sum.inr ⟨(0, 1), by decide⟩)) ≤
      C * ((1024 : ℕ) : ℝ)⁻¹ * ((1024 : ℕ) : ℝ) ^ ((2 / 5 : ℝ) * (2 - ((3 : ℕ) : ℝ))) := by
  obtain ⟨C, hC, h⟩ := entry_abs_pow_le_largeQInterp (C0 := 1) (φs := 2 / 5) zero_le_one
    (by norm_num) (by norm_num)
  exact ⟨C, hC, h 1024 (by norm_num) _ ⟨lawA, 5000, ⟨lawA_isGenWigner, lawA_supp⟩, rfl⟩
    (Sum.inr ⟨(0, 1), by decide⟩) 3 (by norm_num) (by norm_num)⟩

/-- The hypotheses of `swap_expansion_largeQ` hold together at `C0 = 1`, `φs = 2/5`, `ε = 1/15`
for all large `N ≥ 32`: `L = H_γ`, `γ = lexPos N (0, 1)`, between the Rademacher law and the GOE,
`p = (0, 1)`, `F = K(·/π)`, the window `[E₁, E₂] = [2 - N^{-2/3+ε}, 2 + N^{-2/3+ε}]` and `E = 2`;
both conclusions hold there. -/
example : ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, 32 ≤ N ∧ ∃ p : OffDiag N,
    (2 : ℝ) - (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) < 2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) ∧
    |∫ ω, edgeCutoff (offWardInt (symOfEntries ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 15))
          (2 - (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15)) (2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15)) /
          Real.pi) ∂(interp (lexPos N) (lexPos N (Sum.inr p)) (radLaws N) (goeLaws N)).law -
        ∫ ω, edgeCutoff (offWardInt (symOfEntries (zeroEntry (Sum.inr p) ω))
          ((N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 15))
          (2 - (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15)) (2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15)) /
          Real.pi) ∂(interp (lexPos N) (lexPos N (Sum.inr p)) (radLaws N) (goeLaws N)).law -
        (∫ ω, swapBInt (fun x => edgeCutoff (x / Real.pi))
          (symOfEntries (zeroEntry (Sum.inr p) ω)) p ((N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 15))
          (2 - (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15)) (2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15))
          ∂(interp (lexPos N) (lexPos N (Sum.inr p)) (radLaws N) (goeLaws N)).law) *
          (interp (lexPos N) (lexPos N (Sum.inr p)) (radLaws N) (goeLaws N)).entryMoment
            (Sum.inr p) 2 -
        (∫ ω, swapB3Int (fun x => edgeCutoff (x / Real.pi))
          (symOfEntries (zeroEntry (Sum.inr p) ω)) p ((N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 15))
          (2 - (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15)) (2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15))
          ∂(interp (lexPos N) (lexPos N (Sum.inr p)) (radLaws N) (goeLaws N)).law) *
          (interp (lexPos N) (lexPos N (Sum.inr p)) (radLaws N) (goeLaws N)).entryMoment
            (Sum.inr p) 3| ≤
      (N : ℝ) ^ (-(5 : ℝ) / 3 - 2 / 5 + C * (1 / 15)) ∧
    |∫ ω, edgeCutoff (offWard (symOfEntries ω) ⟨2, (N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 15)⟩ / Real.pi)
          ∂(interp (lexPos N) (lexPos N (Sum.inr p)) (radLaws N) (goeLaws N)).law -
        ∫ ω, edgeCutoff (offWard (symOfEntries (zeroEntry (Sum.inr p) ω))
          ⟨2, (N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 15)⟩ / Real.pi)
          ∂(interp (lexPos N) (lexPos N (Sum.inr p)) (radLaws N) (goeLaws N)).law -
        (∫ ω, swapBPt (fun x => edgeCutoff (x / Real.pi))
          (symOfEntries (zeroEntry (Sum.inr p) ω)) p ⟨2, (N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 15)⟩
          ∂(interp (lexPos N) (lexPos N (Sum.inr p)) (radLaws N) (goeLaws N)).law) *
          (interp (lexPos N) (lexPos N (Sum.inr p)) (radLaws N) (goeLaws N)).entryMoment
            (Sum.inr p) 2 -
        (∫ ω, swapB3Pt (fun x => edgeCutoff (x / Real.pi))
          (symOfEntries (zeroEntry (Sum.inr p) ω)) p ⟨2, (N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 15)⟩
          ∂(interp (lexPos N) (lexPos N (Sum.inr p)) (radLaws N) (goeLaws N)).law) *
          (interp (lexPos N) (lexPos N (Sum.inr p)) (radLaws N) (goeLaws N)).entryMoment
            (Sum.inr p) 3| ≤
      (N : ℝ) ^ (-(5 : ℝ) / 3 - 2 / 5 + C * (1 / 15)) := by
  obtain ⟨CF, hCF, hFd⟩ := edgeCutoff_deriv_le
  obtain ⟨C, hC, h⟩ := swap_expansion_largeQ (CF := CF) (C0 := 1) (φs := 2 / 5) zero_le_one
    (by norm_num) (by norm_num)
  obtain ⟨N0, hN0⟩ := h (1 / 15) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (max N0 32)] with N hN
  have h32 : 32 ≤ N := le_trans (le_max_right _ _) hN
  let p : OffDiag N := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.lt_def]⟩
  have hr : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) := Real.rpow_pos_of_pos (by positivity) _
  have hE₁ : |(2 - (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15)) - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) := by
    rw [sub_sub_cancel_left, abs_neg, abs_of_pos hr]
  have hE₂ : |(2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15)) - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) := by
    rw [add_sub_cancel_left, abs_of_pos hr]
  have hE : |(2 : ℝ) - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) := by
    rw [sub_self, abs_zero]; exact hr.le
  have hk := hN0 N (le_trans (le_max_left _ _) hN)
    (interp (lexPos N) (lexPos N (Sum.inr p)) (radLaws N) (goeLaws N))
    ⟨radLaws N, _, ⟨radLaws_isGenWigner (by omega), radLaws_boundedSupportAS h32⟩, rfl⟩ p
    (fun x => edgeCutoff (x / Real.pi)) ((edgeCutoff_props.1 4).comp (contDiff_id.div_const _))
    hFd
  exact ⟨h32, p, by linarith, hk.1 _ _ hE₁ hE₂, hk.2 2 hE⟩

#print axioms entry_abs_pow_le_largeQInterp
#print axioms swap_expansion_largeQ
#print axioms swapB_interp_eq

end WEdgeNS
