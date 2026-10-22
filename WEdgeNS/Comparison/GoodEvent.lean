import WEdgeNS.Comparison.Classes
import WEdgeNS.Comparison.Monomial
import WEdgeNS.LocalLaw.Interface
import WEdgeNS.Resolvent.Expansion

/-!
# The good event of the comparison and resolvent bounds on it
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- A matched pair satisfies the support parameter condition of Lemma 3.1. -/
theorem MatchedPair.supportParam {N : ℕ} {C1 q : ℝ} {Lv Lw : EntryLaws N}
    (h : MatchedPair C1 q Lv Lw) (Q c : ℝ) (hQ : Q ≤ q) :
    Lv.SupportParam Q c q ∧ Lw.SupportParam Q c q :=
  ⟨⟨hQ, h.supp_v.boundedSupport c, h.supp_v.tailVarOff c⟩,
    ⟨hQ, h.supp_w.boundedSupport c, h.supp_w.tailVarOff c⟩⟩

/-- `S = (H - z)⁻¹` at the sample `ω`. -/
def resS {N : ℕ} (z : ℂ) (ω : Entries N) : Matrix (Fin N) (Fin N) ℂ :=
  resolventC (symOfEntries ω) z

/-- `R = (Q - z)⁻¹` with the entry `e` set to `0`. -/
def resR {N : ℕ} (e : Fin N ⊕ OffDiag N) (z : ℂ) (ω : Entries N) : Matrix (Fin N) (Fin N) ℂ :=
  resolventC (symOfEntries (zeroEntry e ω)) z

/-- The good event (6.1) on `S(C0)`: `|G_ij| ≤ 2` and `|R^{(e)}_ij| ≤ 2` for every entry `e`. -/
def goodEvent (N : ℕ) (C0 : ℝ) : Set (Entries N) :=
  {ω | ∀ z ∈ specDomain N C0, ∀ i j, ‖resS z ω i j‖ ≤ 2 ∧ ∀ e, ‖resR e z ω i j‖ ≤ 2}

/-- On `S(2C+2)` the right side of (3.3) is at most `1/4` once `φ ≥ 10` and `φ^C/q ≤ 1/10`. -/
private lemma entryErr_le_quarter {N : ℕ} {C q : ℝ} {z : ℂ} (hC : 0 ≤ C) (hN : 0 < N)
    (hp : 10 ≤ phi N) (haq : phi N ^ C / q ≤ 1 / 10)
    (hz : z ∈ specDomain N (2 * C + 2)) : entryErr N C q z ≤ 1 / 4 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hp0 : 0 < phi N := by linarith
  have ha1 : 1 ≤ phi N ^ C := Real.one_le_rpow (by linarith) hC
  set a := phi N ^ C with ha
  have ha0 : 0 < a := by linarith
  have hzim : 0 < z.im := lt_of_le_of_lt (div_nonneg (Real.rpow_nonneg hp0.le _) hNr.le) hz.2.1
  have hpow : phi N ^ (2 * C + 2) = a ^ 2 * phi N ^ 2 := by
    rw [Real.rpow_add hp0, show (2 : ℝ) * C = C * 2 by ring, Real.rpow_mul hp0.le, Real.rpow_two,
      Real.rpow_two]
  have ht : a ^ 2 * phi N ^ 2 < N * z.im := by
    have := hz.2.1
    rw [div_lt_iff₀ hNr, hpow] at this
    linarith
  set t : ℝ := N * z.im with htdef
  have ht0 : 0 < t := by positivity
  have hap : 0 < a * phi N := by positivity
  have hap2 : (a * phi N) ^ 2 ≤ t := by nlinarith
  have hmsc : (msc z).im ≤ 1 :=
    (Complex.im_le_norm _).trans (norm_msc_eq_inv_and_lt_one hzim).2.le
  have h1 : a * (1 / q) ≤ 1 / 10 := by rw [← div_eq_mul_one_div]; exact haq
  have h2 : a * Real.sqrt ((msc z).im / t) ≤ 1 / 10 := by
    have hs : Real.sqrt ((msc z).im / t) ≤ 1 / (a * phi N) := by
      rw [Real.sqrt_le_left (by positivity)]
      calc (msc z).im / t ≤ 1 / t := div_le_div_of_nonneg_right hmsc ht0.le
        _ ≤ 1 / (a * phi N) ^ 2 := one_div_le_one_div_of_le (by positivity) hap2
        _ = (1 / (a * phi N)) ^ 2 := by rw [_root_.one_div_pow]
    calc a * Real.sqrt ((msc z).im / t) ≤ a * (1 / (a * phi N)) := by gcongr
      _ = 1 / phi N := by field_simp
      _ ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) hp
  have h3 : a * (1 / t) ≤ 1 / 100 := by
    have : 1 / t ≤ 1 / (a ^ 2 * phi N ^ 2) :=
      one_div_le_one_div_of_le (by positivity) ht.le
    calc a * (1 / t) ≤ a * (1 / (a ^ 2 * phi N ^ 2)) := by gcongr
      _ = 1 / (a * phi N ^ 2) := by field_simp
      _ ≤ 1 / 100 := by
          apply one_div_le_one_div_of_le (by norm_num)
          nlinarith
  unfold entryErr
  rw [← ha]
  nlinarith

/-- The entries of `entryMat e` have total absolute value at most `2`. -/
private lemma sum_abs_entryMat_le {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    ∑ l : Fin N, ∑ k : Fin N, |entryMat e k l| ≤ 2 := by
  have h : ∀ k l, |entryMat e k l| = if (k, l) ∈ entryPairs e then 1 else 0 := by
    intro k l
    unfold entryMat
    split_ifs <;> simp
  simp only [h]
  rw [Finset.sum_comm,
    ← Fintype.sum_prod_type' (fun k l => if (k, l) ∈ entryPairs e then (1 : ℝ) else 0),
    Finset.sum_boole]
  have hf : (Finset.univ.filter fun x : Fin N × Fin N => x ∈ entryPairs e) =
      (entryPairs e).toFinset := by
    ext x; simp
  rw [hf]
  have h1 := List.toFinset_card_le (entryPairs e)
  have h2 : (entryPairs e).length ≤ 2 := by rcases e <;> simp [entryPairs]
  exact_mod_cast h1.trans h2

/-- The entries of `R^{(e)}` are at most `2` when those of `S` are at most `5/4` and the entry
`h_e` of `ω` satisfies `|h_e| ≤ 1/10` ((3.28) at order `1`). -/
private lemma norm_resR_le {N : ℕ} {e : Fin N ⊕ OffDiag N} {ω : Entries N} {z : ℂ}
    (hz : 0 < z.im) (hS : ∀ i j, ‖resS z ω i j‖ ≤ 5 / 4) (hv : |entryVal e ω| ≤ 1 / 10)
    (i j : Fin N) : ‖resR e z ω i j‖ ≤ 2 := by
  set v := entryVal e ω with hvdef
  have hH := symOfEntries_eq_zeroEntry_add e ω
  have hQh := symOfEntries_isHermitian (zeroEntry e ω)
  have hVh : (v • entryMat e).IsHermitian := by
    have : v • entryMat e = symOfEntries ω - symOfEntries (zeroEntry e ω) := by
      rw [hH]; abel
    rw [this]
    exact (symOfEntries_isHermitian ω).sub hQh
  have hexp := resolventC_expansion_left hQh hVh hz 1
  rw [← hH] at hexp
  simp only [Finset.sum_range_one, pow_zero, one_mul, pow_one] at hexp
  have hent : ∀ a b, resR e z ω a b = resS z ω a b +
      ∑ l, ∑ k, resS z ω a k * (((v • entryMat e) k l : ℝ) : ℂ) * resR e z ω l b := by
    intro a b
    have := congrFun (congrFun hexp a) b
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.map_apply] at this
    change resR e z ω a b = resS z ω a b + _ at this
    rw [this]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul]
    rfl
  have hbound : ∀ (M : ℝ) (a b : Fin N), 0 ≤ M → (∀ l, ‖resR e z ω l b‖ ≤ M) →
      ‖∑ l, ∑ k, resS z ω a k * (((v • entryMat e) k l : ℝ) : ℂ) * resR e z ω l b‖ ≤
        5 / 4 * |v| * M * 2 := by
    intro M a b hM0 hM
    have hterm : ∀ l k, ‖resS z ω a k * (((v • entryMat e) k l : ℝ) : ℂ) * resR e z ω l b‖ ≤
        5 / 4 * |v| * M * |entryMat e k l| := by
      intro l k
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Matrix.smul_apply, smul_eq_mul,
        abs_mul]
      have h1 := hS a k
      have h2 := hM l
      have h3 : 0 ≤ |v| * |entryMat e k l| := by positivity
      calc _ ≤ 5 / 4 * (|v| * |entryMat e k l|) * M :=
            mul_le_mul (mul_le_mul h1 le_rfl h3 (by norm_num)) h2 (norm_nonneg _) (by positivity)
        _ = _ := by ring
    calc _ ≤ ∑ l, ‖∑ k, resS z ω a k * (((v • entryMat e) k l : ℝ) : ℂ) * resR e z ω l b‖ :=
          norm_sum_le _ _
      _ ≤ ∑ l, ∑ k, ‖resS z ω a k * (((v • entryMat e) k l : ℝ) : ℂ) * resR e z ω l b‖ :=
          Finset.sum_le_sum fun l _ => norm_sum_le _ _
      _ ≤ ∑ l, ∑ k, 5 / 4 * |v| * M * |entryMat e k l| :=
          Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun k _ => hterm l k
      _ = 5 / 4 * |v| * M * ∑ l, ∑ k, |entryMat e k l| := by
          simp only [← Finset.mul_sum]
      _ ≤ 5 / 4 * |v| * M * 2 :=
          mul_le_mul_of_nonneg_left (sum_abs_entryMat_le e) (by positivity)
  obtain ⟨x0, -, hx0⟩ := Finset.exists_max_image Finset.univ
    (fun x : Fin N × Fin N => ‖resR e z ω x.1 x.2‖) ⟨(i, j), Finset.mem_univ _⟩
  set M := ‖resR e z ω x0.1 x0.2‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  have hMall : ∀ l b, ‖resR e z ω l b‖ ≤ M := fun l b => hx0 (l, b) (Finset.mem_univ _)
  have hk := hbound M x0.1 x0.2 hM0 (fun l => hMall l x0.2)
  have hE : M ≤ 5 / 4 + 5 / 4 * |v| * M * 2 :=
    calc M = ‖resR e z ω x0.1 x0.2‖ := rfl
      _ = ‖resS z ω x0.1 x0.2 +
          ∑ l, ∑ k, resS z ω x0.1 k * (((v • entryMat e) k l : ℝ) : ℂ) * resR e z ω l x0.2‖ :=
          congrArg norm (hent x0.1 x0.2)
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (hS _ _) hk)
  have hvM : |v| * M ≤ 1 / 10 * M := mul_le_mul_of_nonneg_right hv hM0
  have : M ≤ 5 / 3 := by nlinarith
  exact (hMall i j).trans (by linarith)

/-- Deterministic part of (6.1): the events (3.2), (3.3) at level `C` and the bound
`|h_e| ≤ q⁻¹` on every entry give `|S_ij| ≤ 2` and `|R^{(e)}_ij| ≤ 2` on `S(2C+2)`. -/
private lemma mem_goodEvent_of_localLaw {N : ℕ} {C q t : ℝ} {ω : Entries N} (hC : 0 ≤ C)
    (hN : 0 < N) (hp : 10 ≤ phi N) (hat : phi N ^ C ≤ t) (ht : 10 ≤ t) (hq : t * t ≤ q)
    (hev : ω ∈ localLawEvent N C q) (hv : ∀ e, |entryVal e ω| ≤ q⁻¹) :
    ω ∈ goodEvent N (2 * C + 2) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hq0 : 0 < q := by nlinarith
  have haq : phi N ^ C / q ≤ 1 / 10 := by
    rw [div_le_iff₀ hq0]
    nlinarith
  have hqinv : q⁻¹ ≤ 1 / 10 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  intro z hz
  have hp1 : (1 : ℝ) ≤ phi N := by linarith
  have hzC : z ∈ specDomain N C :=
    ⟨hz.1, lt_of_le_of_lt (div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)) hNr.le) hz.2.1, hz.2.2⟩
  have hzim : 0 < z.im :=
    lt_of_le_of_lt (div_nonneg (Real.rpow_nonneg (by linarith) _) hNr.le) hz.2.1
  have hmsc : ‖msc z‖ ≤ 1 := (norm_msc_eq_inv_and_lt_one hzim).2.le
  have hS : ∀ i j, ‖resS z ω i j‖ ≤ 5 / 4 := by
    intro i j
    have h := (hev z hzC).2 i j
    have herr := entryErr_le_quarter hC hN hp haq hz
    have hdelta : ‖(if i = j then msc z else 0)‖ ≤ 1 := by
      split_ifs
      · exact hmsc
      · simp
    calc ‖resS z ω i j‖
        = ‖(resolventC (symOfEntries ω) z i j - (if i = j then msc z else 0)) +
            (if i = j then msc z else 0)‖ := by rw [sub_add_cancel]; rfl
      _ ≤ ‖resolventC (symOfEntries ω) z i j - (if i = j then msc z else 0)‖ +
            ‖(if i = j then msc z else 0)‖ := norm_add_le _ _
      _ ≤ 5 / 4 := by linarith
  exact fun i j => ⟨(hS i j).trans (by norm_num),
    fun e => norm_resR_le hzim hS ((hv e).trans hqinv) i j⟩

/-- Entries that are almost surely bounded by `q⁻¹` are all bounded by `q⁻¹` almost surely. -/
private lemma law_not_bounded_null {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) {q : ℝ}
    (hs : L.BoundedSupportAS q) : L.law {ω | ¬ ∀ e, |entryVal e ω| ≤ q⁻¹} = 0 := by
  have hset : {ω : Entries N | ¬ ∀ e, |entryVal e ω| ≤ q⁻¹} =
      ⋃ e, {ω | q⁻¹ < |entryVal e ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, not_forall, not_le]
  rw [hset]
  refine measure_iUnion_null fun e => ?_
  have := hL.diag
  have := hL.off
  have hT : MeasurableSet {x : ℝ | q⁻¹ < |x|} := measurableSet_lt measurable_const measurable_abs
  rcases e with i | p
  · have hmp : MeasurePreserving (fun ω : Entries N => ω.1 i) L.law (L.diag i) :=
      (measurePreserving_eval (fun i => L.diag i) i).comp
        (measurePreserving_fst (μ := Measure.pi L.diag) (ν := Measure.pi L.off))
    have h := hmp.measure_preimage hT.nullMeasurableSet
    exact h.trans (hs.1 i)
  · have hmp : MeasurePreserving (fun ω : Entries N => ω.2 p) L.law (L.off p) :=
      (measurePreserving_eval (fun p => L.off p) p).comp
        (measurePreserving_snd (μ := Measure.pi L.diag) (ν := Measure.pi L.off))
    have h := hmp.measure_preimage hT.nullMeasurableSet
    exact h.trans (hs.2 p)

/-- (6.1): the good event holds with 3-high probability, uniformly over all `H_γ`. -/
theorem highProb_goodEvent {C1 φq : ℝ} (hφq : 0 < φq) :
    ∃ C0 > (0 : ℝ), HighProbOn 3 (PairInterpClass C1 φq) (fun N _ => goodEvent N C0) := by
  obtain ⟨C, hC, hHP⟩ := localLaw (ζ := 3) (C0 := max C1 1) (c := 1) (by norm_num)
    (le_trans zero_le_one (le_max_right _ _)) one_pos
  obtain ⟨c, hc, C', hC', N1, hN1⟩ := hHP
  refine ⟨2 * C + 2, by positivity, c, hc, C', hC', ?_⟩
  have hφ2 : 0 < φq / 2 := half_pos hφq
  have hev := (eventually_ge_atTop N1).and <|
    (eventually_ge_atTop 16).and <|
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 10).and <|
    (phi_rpow_le_rpow C hφ2).and <|
    (((tendsto_rpow_atTop hφ2).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 10)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨N0, fun N hN L hL => ?_⟩
  obtain ⟨hN1', h16, hlog, hat, ht⟩ := hN0 N hN
  obtain ⟨Lv, Lw, q, γ, hmp, hq, rfl⟩ := hL
  have hp : 10 ≤ phi N := hlog.trans (log_le_phi h16)
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  set t : ℝ := (N : ℝ) ^ (φq / 2) with htdef
  have ht' : 10 ≤ t := ht
  have htt : t * t = (N : ℝ) ^ φq := by
    rw [htdef, ← Real.rpow_add hNr]
    congr 1
    ring
  have hQ : phi N ^ C ≤ q :=
    calc phi N ^ C ≤ t := hat
      _ ≤ t * t := by nlinarith [ht']
      _ = (N : ℝ) ^ φq := htt
      _ ≤ q := hq
  obtain ⟨hsv, hsw⟩ := hmp.supportParam (phi N ^ C) 1 hQ
  have hgw : (interp (lexPos N) γ Lv Lw).IsGenWigner (max C1 1) := by
    have := interp_isGenWigner (Φ := lexPos N) (γ := γ) hmp.isGenWigner.1 hmp.isGenWigner.2
    rwa [max_self] at this
  have hsp := interp_supportParam (Φ := lexPos N) (γ := γ) hsv hsw
  have hb := hN1 N hN1' _ hgw
  have hmp' := hmp.interp γ
  have hnull := law_not_bounded_null hmp'.isProb_v hmp'.supp_v
  have hsub : (goodEvent N (2 * C + 2))ᶜ ⊆
      {ω : Entries N | ∀ q', (interp (lexPos N) γ Lv Lw).SupportParam (phi N ^ C) 1 q' →
          ω ∈ localLawEvent N C q'}ᶜ ∪ {ω | ¬ ∀ e, |entryVal e ω| ≤ q⁻¹} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not, Set.mem_ofPred_eq] at hcon
    exact hω (mem_goodEvent_of_localLaw hC.le hNpos hp hat ht' (htt.le.trans hq) (hcon.1 q hsp)
      hcon.2)
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (by rw [hnull, add_zero]; exact hb))

/-- Lemma 6.4 (6.20) on the good event, for `S` and every `R^{(e')}`. -/
theorem norm_evalW_wordP_le_of_good {N : ℕ} {C0 : ℝ} {ω : Entries N} (hω : ω ∈ goodEvent N C0)
    {z : ℂ} (hz : z ∈ specDomain N C0) (e e' : Fin N ⊕ OffDiag N) (k : List ℕ) (w : Word N)
    (hk : k.length = w.length) :
    ‖evalW (resS z ω) (msc z) (wordP e k w)‖ ≤ 4 ^ (w.length + k.sum + 1) ∧
      ‖evalW (resR e' z ω) (msc z) (wordP e k w)‖ ≤ 4 ^ (w.length + k.sum + 1) := by
  have hzim : 0 < z.im :=
    lt_of_le_of_lt (div_nonneg (Real.rpow_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg N) _) _)
      (Nat.cast_nonneg N)) hz.2.1
  have hm : ‖msc z‖ ≤ 1 := (norm_msc_eq_inv_and_lt_one hzim).2.le
  exact ⟨norm_evalW_wordP_le (fun i j => (hω z hz i j).1) hm e k w hk,
    norm_evalW_wordP_le (fun i j => (hω z hz i j).2 e') hm e k w hk⟩

/-- `η = N^{-2/3-ε}` of (5.13). -/
def etaEdge (N : ℕ) (ε : ℝ) : ℝ := (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)

/-- Ward form of `x_S` (6.80): `η² Σ_{ij} |G_ij|² = N η Im m`. -/
theorem sq_sum_norm_resolventC_eq {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) :
    z.im ^ 2 * ∑ i, ∑ j, ‖resolventC H z i j‖ ^ 2 = N * z.im * (stieltjesM H z).im := by
  have hw : ∀ i, ∑ j, ‖resolventC H z i j‖ ^ 2 = (resolventC H z i i).im / z.im :=
    fun i => sum_norm_sq_resolventC hH hz i
  have htr : ((resolventC H z).trace).im = ∑ i, (resolventC H z i i).im := by
    simp [Matrix.trace, Complex.im_sum]
  have hz0 : z.im ≠ 0 := hz.ne'
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp
  · have hN : (N : ℂ)⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    have hNne : (N : ℝ) ≠ 0 := by positivity
    have him : (stieltjesM H z).im = (N : ℝ)⁻¹ * ((resolventC H z).trace).im := by
      unfold stieltjesM
      rw [hN, Complex.im_ofReal_mul]
    rw [him, htr]
    simp only [hw]
    rw [← Finset.sum_div, mul_div_assoc']
    field_simp

/-! ### Compiled checks -/

open private sc_rad_instance from WEdgeNS.LocalLaw.SelfConsistent

/-- Every sample lies in the good event when `φ^{C0}/N ≥ 1/2`, because then `Im z > 1/2` on
`S(C0)` and every entry of a resolvent is at most `1/Im z < 2`. -/
private lemma mem_goodEvent_of_large_eta {N : ℕ} {C0 : ℝ} (h : 1 / 2 ≤ phi N ^ C0 / N)
    (ω : Entries N) : ω ∈ goodEvent N C0 := by
  intro z hz i j
  have hz' : 1 / 2 < z.im := lt_of_le_of_lt h hz.2.1
  have hb : ∀ H : Matrix (Fin N) (Fin N) ℝ, H.IsHermitian → ‖resolventC H z i j‖ ≤ 2 :=
    fun H hH => (norm_resolventC_apply_le hH (by linarith) i j).trans
      ((div_le_iff₀ (by linarith)).2 (by linarith))
  exact ⟨hb _ (symOfEntries_isHermitian ω), fun e => hb _ (symOfEntries_isHermitian _)⟩

private lemma log_sixteen_ge : (11 : ℝ) / 4 ≤ Real.log 16 := by
  have := Real.log_two_gt_d9
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  push_cast
  linarith

private lemma log_sixteen_le : Real.log 16 ≤ 2.78 := by
  have := Real.log_two_lt_d9
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  push_cast
  linarith

/-- `2 ≤ φ(16) ≤ 7/2`. -/
private lemma phi_sixteen_bounds : 2 ≤ phi 16 ∧ phi 16 ≤ 7 / 2 := by
  constructor
  · have h := log_le_phi (N := 16) le_rfl
    have h2 := log_sixteen_ge
    simp only [Nat.cast_ofNat] at h
    linarith
  · rw [phi_eq_exp (by norm_num : 3 ≤ 16)]
    simp only [Nat.cast_ofNat]
    have hl := log_sixteen_le
    have hl1 : (1 : ℝ) ≤ Real.log 16 := by linarith [log_sixteen_ge]
    have hu : Real.log (Real.log 16) ≤ 1.1 := by
      rw [Real.log_le_iff_le_exp (by linarith)]
      have h1 := Real.exp_one_gt_d9
      have h2 := Real.add_one_le_exp (0.1 : ℝ)
      have h3 : Real.exp 1.1 = Real.exp 1 * Real.exp 0.1 := by
        rw [← Real.exp_add]; norm_num
      rw [h3]
      nlinarith [Real.exp_pos (0.1 : ℝ)]
    have hu0 : 0 ≤ Real.log (Real.log 16) := Real.log_nonneg hl1
    have hsq : Real.log (Real.log 16) ^ 2 ≤ 1.21 := by nlinarith
    calc Real.exp (Real.log (Real.log 16) ^ 2) ≤ Real.exp 1.21 := Real.exp_le_exp.mpr hsq
      _ = Real.exp 1 * Real.exp 0.21 := by rw [← Real.exp_add]; norm_num
      _ ≤ 2.7182818286 * (1 / (1 - 0.21)) := by
          have h1 := Real.exp_one_lt_d9
          have h2 := Real.exp_bound_div_one_sub_of_interval' (x := 0.21) (by norm_num)
            (by norm_num)
          exact mul_le_mul h1.le h2.le (Real.exp_pos _).le (by norm_num)
      _ ≤ 7 / 2 := by norm_num

/-- `φ(16)^3 / 16 ≥ 1/2` and `φ(16)^3 / 16 < 10`. -/
private lemma phi_sixteen_cube : 1 / 2 ≤ phi 16 ^ (3 : ℝ) / ((16 : ℕ) : ℝ) ∧
    phi 16 ^ (3 : ℝ) / ((16 : ℕ) : ℝ) < 10 := by
  obtain ⟨h1, h2⟩ := phi_sixteen_bounds
  have hp0 : 0 ≤ phi 16 := by linarith
  have e3 : phi 16 ^ (3 : ℝ) = phi 16 ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e3]
  simp only [Nat.cast_ofNat]
  constructor
  · rw [le_div_iff₀ (by norm_num)]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h1 3]
  · rw [div_lt_iff₀ (by norm_num)]
    nlinarith [pow_le_pow_left₀ hp0 h2 3]

/-- A concrete sample in the good event: `N = 16`, `C0 = 3`, `ω = 0`. -/
example : (0 : Entries 16) ∈ goodEvent 16 3 :=
  mem_goodEvent_of_large_eta (by simpa using phi_sixteen_cube.1) 0

/-- Lemma 6.4 at that sample: `z = 10 i`, the entry `(1, 2)`, `k = (1, 0)` and the word
`G_12 G_21` give the bound `4^{2+1+1} = 256` for both `S` and `R^{(e')}`. -/
example :
    ‖evalW (resS (⟨0, 10⟩ : ℂ) (0 : Entries 16)) (msc ⟨0, 10⟩)
        (wordP (Sum.inr ⟨(0, 1), by decide⟩) [1, 0] [⟨.g, 0, 1⟩, ⟨.g, 1, 0⟩])‖ ≤ 256 ∧
    ‖evalW (resR (Sum.inl 3) (⟨0, 10⟩ : ℂ) (0 : Entries 16)) (msc ⟨0, 10⟩)
        (wordP (Sum.inr ⟨(0, 1), by decide⟩) [1, 0] [⟨.g, 0, 1⟩, ⟨.g, 1, 0⟩])‖ ≤ 256 := by
  have hω : (0 : Entries 16) ∈ goodEvent 16 3 :=
    mem_goodEvent_of_large_eta (by simpa using phi_sixteen_cube.1) 0
  have hz : (⟨0, 10⟩ : ℂ) ∈ specDomain 16 3 :=
    ⟨by simp, by simpa using phi_sixteen_cube.2, le_rfl⟩
  have h := norm_evalW_wordP_le_of_good hω hz (Sum.inr ⟨(0, 1), by decide⟩) (Sum.inl 3) [1, 0]
    [⟨.g, 0, 1⟩, ⟨.g, 1, 0⟩] rfl
  norm_num at h
  exact h

/-- For large `N` the Rademacher laws against themselves form a matched pair with `C1 = 2` and
`q = N^{2/5}`. -/
private lemma matchedPair_radLaws :
    ∀ᶠ N : ℕ in atTop, MatchedPair 2 ((N : ℝ) ^ (2 / 5 : ℝ)) (radLaws N) (radLaws N) := by
  filter_upwards [sc_rad_instance 0 0, eventually_ge_atTop 32] with N hi h32
  have hgw := hi.1
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hlog : (1 : ℝ) / 2 ≤ Real.log N := by
    have h2 : Real.log 2 ≤ Real.log N :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ N))
    linarith [Real.log_two_gt_d9]
  refine ⟨hgw.isProb, hgw.isProb, hi.2.1, hi.2.1, hgw.mean_diag, hgw.mean_off, fun i => ?_,
    hgw.var_off, fun p => ?_, fun p k _ => rfl, fun i k _ => rfl⟩
  · have h := (abs_le.1 (hgw.var_diag i)).2
    rw [div_eq_mul_inv]
    linarith
  · rw [integral_pow_four_radLaws_off hNpos, div_eq_mul_inv]
    have hinv : 0 < ((N : ℝ) ^ 2)⁻¹ := by positivity
    nlinarith

/-- The class `PairInterpClass 2 (2/5)` contains `H_0 = radLaws N` for all large `N`. -/
example : ∀ᶠ N : ℕ in atTop,
    PairInterpClass 2 (2 / 5) N (interp (lexPos N) 0 (radLaws N) (radLaws N)) := by
  filter_upwards [matchedPair_radLaws] with N h
  exact ⟨radLaws N, radLaws N, _, 0, h, le_rfl, rfl⟩

/-- `MatchedPair.supportParam` for that matched pair, with `Q = 1`, `c = 1/2`. -/
example : ∀ᶠ N : ℕ in atTop, (radLaws N).SupportParam 1 (1 / 2) ((N : ℝ) ^ (2 / 5 : ℝ)) ∧
    (radLaws N).SupportParam 1 (1 / 2) ((N : ℝ) ^ (2 / 5 : ℝ)) := by
  filter_upwards [matchedPair_radLaws, eventually_ge_atTop 32] with N h h32
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (2 / 5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ N)) (by norm_num)
  exact h.supportParam 1 (1 / 2) h1

/-- `η = N^{-2/3-ε}` at `N = 8`, `ε = 1/3`. -/
example : etaEdge 8 (1 / 3) = 1 / 8 := by
  unfold etaEdge
  rw [show -(2 : ℝ) / 3 - 1 / 3 = -1 by norm_num, Real.rpow_neg_one]
  norm_num

/-- `η = N^{-2/3-ε}` at `N = 27`, `ε = 0`. -/
example : etaEdge 27 0 = 1 / 9 := by
  unfold etaEdge
  have h : (27 : ℝ) = 3 ^ (3 : ℝ) := by norm_num
  rw [show ((27 : ℕ) : ℝ) = 3 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num),
    show (3 : ℝ) * (-(2 : ℝ) / 3 - 0) = -2 by norm_num, Real.rpow_neg (by norm_num)]
  norm_num

/-- The Ward form for the matrix `[[0, 1], [1, 0]]` at `z = i`. -/
example : (Complex.I.im) ^ 2 * ∑ i, ∑ j, ‖resolventC (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)
      Complex.I i j‖ ^ 2 = (2 : ℕ) * Complex.I.im *
      (stieltjesM (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) Complex.I).im :=
  sq_sum_norm_resolventC_eq (by ext i j; fin_cases i <;> fin_cases j <;> simp) (by simp)

#print axioms MatchedPair.supportParam
#print axioms highProb_goodEvent
#print axioms norm_evalW_wordP_le_of_good
#print axioms sq_sum_norm_resolventC_eq

end WEdgeNS
