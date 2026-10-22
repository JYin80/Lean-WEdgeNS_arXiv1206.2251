import WEdgeNS.Comparison.StarExpansion
import WEdgeNS.Comparison.GoodEvent
import WEdgeNS.Comparison.MomentBounds

/-!
# The expectation expansion of one entry (Lemma 6.5)
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- (6.52), (6.56), (6.63)–(6.65) on the good event (6.1): at `z ∈ S(C0)`, for
`S = resS z ω` and `R = resR e z ω`, with `|v_e| ≤ q⁻¹` and `8 (s + K) ≤ q`, the remainder is at
most `2^K 4^{s+K+2} (4 (s + K) / q)^{n+1}`. -/
theorem norm_evalW_wordP_sub_expansion_le_of_good {N : ℕ} {C0 : ℝ} {ω : Entries N}
    (hω : ω ∈ goodEvent N C0) {z : ℂ} (hz : z ∈ specDomain N C0) (e : Fin N ⊕ OffDiag N)
    {m : ℂ} (hm : ‖m‖ ≤ 1) {q : ℝ} (hq : 0 < q) (hv : |entryVal e ω| ≤ q⁻¹) {s : ℕ}
    (w : Word N) (hw : w.length = s) (κ : Fin s → ℕ)
    (hsq : 8 * ((s + ∑ t, κ t : ℕ) : ℝ) ≤ q) (n : ℕ) :
    ‖evalW (resS z ω) m (wordP e (List.ofFn κ) w) -
        ∑ c ∈ Finset.range (n + 1), (((-entryVal e ω) ^ c : ℝ) : ℂ) *
          ∑ l ∈ Finset.Nat.antidiagonalTuple s c,
            ((∏ t, Nat.choose (κ t + l t) (l t) : ℕ) : ℂ) *
              evalW (resR e z ω) m (wordP e (List.ofFn (κ + l)) w)‖ ≤
      2 ^ (∑ t, κ t) * 4 ^ (s + ∑ t, κ t + 2) *
        (4 * ((s + ∑ t, κ t : ℕ) : ℝ) / q) ^ (n + 1) := by
  have hzim : 0 < z.im :=
    lt_of_le_of_lt (div_nonneg (Real.rpow_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg N) _) _)
      (Nat.cast_nonneg N)) hz.2.1
  have hS : ∀ i j, ‖resolventC (symOfEntries (zeroEntry e ω) + entryVal e ω • entryMat e) z i j‖
      ≤ 2 := by
    rw [← symOfEntries_eq_zeroEntry_add]
    exact fun i j => (hω z hz i j).1
  have hR : ∀ i j, ‖resolventC (symOfEntries (zeroEntry e ω)) z i j‖ ≤ 2 :=
    fun i j => (hω z hz i j).2 e
  have hK : (0 : ℝ) ≤ ((s + ∑ t, κ t : ℕ) : ℝ) := Nat.cast_nonneg _
  have hvq : 8 * ((s + ∑ t, κ t : ℕ) : ℝ) * |entryVal e ω| ≤ 1 := by
    calc 8 * ((s + ∑ t, κ t : ℕ) : ℝ) * |entryVal e ω| ≤ 8 * ((s + ∑ t, κ t : ℕ) : ℝ) * q⁻¹ :=
          mul_le_mul_of_nonneg_left hv (by positivity)
      _ ≤ q * q⁻¹ := mul_le_mul_of_nonneg_right hsq (inv_nonneg.2 hq.le)
      _ = 1 := mul_inv_cancel₀ hq.ne'
  have h := norm_evalW_wordP_sub_expansion_le (symOfEntries_isHermitian (zeroEntry e ω)) e
    (entryVal e ω) hzim hm hS hR w hw κ hvq n
  rw [← symOfEntries_eq_zeroEntry_add] at h
  refine h.trans ?_
  gcongr
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hv (by positivity)

private lemma expansion_wordP_replicate_zero {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    ∀ w : Word N, wordP e (List.replicate w.length 0) w = [w]
  | [] => by simp [wordP]
  | ℓ :: w => by
    rw [List.length_cons, List.replicate_succ, wordP, expansion_wordP_replicate_zero e w]
    simp [letterP]

private lemma expansion_evalW_wordP_zero {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ)
    (e : Fin N ⊕ OffDiag N) {s : ℕ} (w : Word N) (hw : w.length = s) :
    evalW G m (wordP e (List.ofFn (0 : Fin s → ℕ)) w) = evalWord G m w := by
  subst hw
  have : List.ofFn (0 : Fin w.length → ℕ) = List.replicate w.length 0 :=
    List.ofFn_const w.length 0
  rw [this, expansion_wordP_replicate_zero]
  simp [evalW]

/-- (6.56), the input of (6.60)–(6.62) and (6.79): on the good event a word of
length `s` in `S` equals `Σ_{c ≤ n} (-v)^c Σ_{κ ∈ ℕ^s, |κ| = c} P_{γ,κ}(word)(R)` up to
`4^{s+2} (4s/q)^{n+1}`, for `|v_e| ≤ q⁻¹` and `8s ≤ q`. -/
theorem norm_evalWord_sub_expansion_le_of_good {N : ℕ} {C0 : ℝ} {ω : Entries N}
    (hω : ω ∈ goodEvent N C0) {z : ℂ} (hz : z ∈ specDomain N C0) (e : Fin N ⊕ OffDiag N)
    {m : ℂ} (hm : ‖m‖ ≤ 1) {q : ℝ} (hq : 0 < q) (hv : |entryVal e ω| ≤ q⁻¹) {s : ℕ}
    (w : Word N) (hw : w.length = s) (hsq : 8 * (s : ℝ) ≤ q) (n : ℕ) :
    ‖evalWord (resS z ω) m w -
        ∑ c ∈ Finset.range (n + 1), (((-entryVal e ω) ^ c : ℝ) : ℂ) *
          ∑ κ ∈ Finset.Nat.antidiagonalTuple s c,
            evalW (resR e z ω) m (wordP e (List.ofFn κ) w)‖ ≤
      4 ^ (s + 2) * (4 * (s : ℝ) / q) ^ (n + 1) := by
  have h := norm_evalW_wordP_sub_expansion_le_of_good hω hz e hm hq hv w hw 0 (by simpa using hsq) n
  simpa [expansion_evalW_wordP_zero _ m e w hw] using h

/-- The operator `U` of the expansion: `(U y)(κ) = Σ_{1 ≤ c ≤ ξ - |κ|} n_c Σ_{|l| = c}
∏_t C(κ_t + l_t, l_t) y(κ + l)`. -/
private def expU (V : Type*) [AddCommGroup V] [Module ℝ V] (s ξ : ℕ) (n : ℕ → ℝ) :
    Module.End ℝ ((Fin s → ℕ) → V) where
  toFun y κ := ∑ c ∈ Finset.range (ξ - ∑ t, κ t), ∑ l ∈ Finset.Nat.antidiagonalTuple s (c + 1),
      (n (c + 1) * ((∏ t, Nat.choose (κ t + l t) (l t) : ℕ) : ℝ)) • y (κ + l)
  map_add' y y' := by
    funext κ
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' r y := by
    funext κ
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun l _ => ?_
    rw [smul_comm]

private lemma expU_apply {V : Type*} [AddCommGroup V] [Module ℝ V] (s ξ : ℕ) (n : ℕ → ℝ)
    (y : (Fin s → ℕ) → V) (κ : Fin s → ℕ) :
    expU V s ξ n y κ = ∑ c ∈ Finset.range (ξ - ∑ t, κ t),
      ∑ l ∈ Finset.Nat.antidiagonalTuple s (c + 1),
        (n (c + 1) * ((∏ t, Nat.choose (κ t + l t) (l t) : ℕ) : ℝ)) • y (κ + l) := rfl

/-- The inverse `Σ_{j ≤ ξ} (-U)^j` of `1 + U`. -/
private def expS (V : Type*) [AddCommGroup V] [Module ℝ V] (s ξ : ℕ) (n : ℕ → ℝ) :
    Module.End ℝ ((Fin s → ℕ) → V) :=
  ∑ j ∈ Finset.range (ξ + 1), (-expU V s ξ n) ^ j

private lemma expansion_sum_add {s : ℕ} (κ l : Fin s → ℕ) :
    ∑ t, (κ + l) t = ∑ t, κ t + ∑ t, l t := by
  simp [Finset.sum_add_distrib]

/-- `U` vanishes at levels `|κ| ≥ ξ`, and `U^{j+1}` at levels `|κ| + j ≥ ξ`. -/
private lemma expU_pow_apply_eq_zero {V : Type*} [AddCommGroup V] [Module ℝ V] (s ξ : ℕ)
    (n : ℕ → ℝ) : ∀ (j : ℕ) (y : (Fin s → ℕ) → V) (κ : Fin s → ℕ), ξ < ∑ t, κ t + j + 1 →
      ((-expU V s ξ n) ^ (j + 1)) y κ = 0 := by
  intro j
  induction j with
  | zero =>
    intro y κ h
    rw [zero_add, pow_one, LinearMap.neg_apply, Pi.neg_apply, expU_apply,
      show ξ - ∑ t, κ t = 0 by omega]
    simp
  | succ j ih =>
    intro y κ h
    rw [pow_succ', Module.End.mul_apply, LinearMap.neg_apply, Pi.neg_apply, expU_apply, neg_eq_zero]
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun l hl => ?_
    rw [Finset.Nat.mem_antidiagonalTuple] at hl
    rw [ih y (κ + l) (by rw [expansion_sum_add, hl]; omega), smul_zero]

/-- `Σ_{j ≤ ξ} (-U)^j` inverts `1 + U`. -/
private lemma expS_apply_add_expU {V : Type*} [AddCommGroup V] [Module ℝ V] (s ξ : ℕ)
    (n : ℕ → ℝ) (y : (Fin s → ℕ) → V) : expS V s ξ n (y + expU V s ξ n y) = y := by
  have h := geom_sum_mul_neg (-expU V s ξ n) (ξ + 1)
  have h2 : ((∑ j ∈ Finset.range (ξ + 1), (-expU V s ξ n) ^ j) * (1 - -expU V s ξ n)) y =
      (1 - (-expU V s ξ n) ^ (ξ + 1)) y := by rw [h]
  rw [Module.End.mul_apply, sub_neg_eq_add, LinearMap.add_apply, Module.End.one_apply,
    LinearMap.sub_apply, Module.End.one_apply] at h2
  rw [expS, h2]
  funext κ
  rw [Pi.sub_apply, expU_pow_apply_eq_zero s ξ n ξ y κ (by omega), sub_zero]

private lemma expU_smul_const {V : Type*} [AddCommGroup V] [Module ℝ V] (s ξ : ℕ) (n : ℕ → ℝ)
    (f : (Fin s → ℕ) → ℝ) (v : V) :
    expU V s ξ n (fun β => f β • v) = fun κ => expU ℝ s ξ n f κ • v := by
  funext κ
  simp only [expU_apply, Finset.sum_smul, smul_smul, smul_eq_mul]

private lemma expU_neg_pow_smul_const {V : Type*} [AddCommGroup V] [Module ℝ V] (s ξ : ℕ)
    (n : ℕ → ℝ) (f : (Fin s → ℕ) → ℝ) (v : V) (j : ℕ) :
    ((-expU V s ξ n) ^ j) (fun β => f β • v) = fun κ => ((-expU ℝ s ξ n) ^ j) f κ • v := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih, LinearMap.neg_apply, expU_smul_const, pow_succ',
      Module.End.mul_apply, LinearMap.neg_apply]
    funext κ
    simp [neg_smul]

private lemma expS_smul_const {V : Type*} [AddCommGroup V] [Module ℝ V] (s ξ : ℕ) (n : ℕ → ℝ)
    (f : (Fin s → ℕ) → ℝ) (v : V) :
    expS V s ξ n (fun β => f β • v) = fun κ => expS ℝ s ξ n f κ • v := by
  funext κ
  simp only [expS, LinearMap.sum_apply, Finset.sum_apply, expU_neg_pow_smul_const,
    Finset.sum_smul]

private lemma expansion_mem_highIdx {s m0 ξ : ℕ} (β : Fin s → ℕ) :
    β ∈ highIdx s m0 ξ ↔ m0 < ∑ t, β t ∧ ∑ t, β t ≤ ξ := by
  simp only [highIdx, Finset.mem_biUnion, Finset.mem_Icc, Finset.Nat.mem_antidiagonalTuple]
  constructor
  · rintro ⟨c, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨_, ⟨h1, h2⟩, rfl⟩

/-- Values of `U y` at levels `m0 < |κ| ≤ ξ` use only values of `y` at these levels. -/
private lemma expU_eq_zero_of_window {V : Type*} [AddCommGroup V] [Module ℝ V] (s ξ m0 : ℕ)
    (n : ℕ → ℝ) (y : (Fin s → ℕ) → V) (hy : ∀ β ∈ highIdx s m0 ξ, y β = 0) :
    ∀ κ ∈ highIdx s m0 ξ, expU V s ξ n y κ = 0 := by
  intro κ hκ
  rw [expansion_mem_highIdx] at hκ
  rw [expU_apply]
  refine Finset.sum_eq_zero fun c hc => Finset.sum_eq_zero fun l hl => ?_
  rw [Finset.mem_range] at hc
  rw [Finset.Nat.mem_antidiagonalTuple] at hl
  rw [hy _ ((expansion_mem_highIdx _).2 (by rw [expansion_sum_add, hl]; omega)), smul_zero]

private lemma expS_eq_zero_of_window {V : Type*} [AddCommGroup V] [Module ℝ V] (s ξ m0 : ℕ)
    (n : ℕ → ℝ) (y : (Fin s → ℕ) → V) (hy : ∀ β ∈ highIdx s m0 ξ, y β = 0) :
    ∀ κ ∈ highIdx s m0 ξ, expS V s ξ n y κ = 0 := by
  have hp : ∀ j, ∀ κ ∈ highIdx s m0 ξ, ((-expU V s ξ n) ^ j) y κ = 0 := by
    intro j
    induction j with
    | zero => exact hy
    | succ j ih =>
      intro κ hκ
      rw [pow_succ', Module.End.mul_apply, LinearMap.neg_apply, Pi.neg_apply,
        expU_eq_zero_of_window s ξ m0 n _ ih κ hκ, neg_zero]
  intro κ hκ
  simp only [expS, LinearMap.sum_apply, Finset.sum_apply]
  exact Finset.sum_eq_zero fun j _ => hp j κ hκ

/-- On the window `m0 < |κ| ≤ ξ`, `S y` is a combination of the values of `y` on the window, with
real coefficients `(S δ_α)(κ)`. -/
private lemma expS_apply_eq_sum {V : Type*} [AddCommGroup V] [Module ℝ V] (s ξ m0 : ℕ)
    (n : ℕ → ℝ) (y : (Fin s → ℕ) → V) (κ : Fin s → ℕ) (hκ : κ ∈ highIdx s m0 ξ) :
    expS V s ξ n y κ = ∑ α ∈ highIdx s m0 ξ,
      expS ℝ s ξ n (fun β => if β = α then 1 else 0) κ • y α := by
  set yW : (Fin s → ℕ) → V := ∑ α ∈ highIdx s m0 ξ,
    (fun β => (if β = α then (1 : ℝ) else 0) • y α) with hyW
  have hW : ∀ β ∈ highIdx s m0 ξ, (y - yW) β = 0 := by
    intro β hβ
    simp [hyW, Finset.sum_apply, ite_smul, hβ]
  have h1 := expS_eq_zero_of_window s ξ m0 n _ hW κ hκ
  rw [map_sub, Pi.sub_apply, sub_eq_zero] at h1
  rw [h1, hyW, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [expS_smul_const]

private lemma expansion_sum_highIdx {M : Type*} [AddCommMonoid M] (s m0 ξ : ℕ)
    (g : (Fin s → ℕ) → M) :
    ∑ κ ∈ highIdx s m0 ξ, g κ =
      ∑ k ∈ Finset.Icc (m0 + 1) ξ, ∑ κ ∈ Finset.Nat.antidiagonalTuple s k, g κ := by
  rw [highIdx, Finset.sum_biUnion]
  intro a _ b _ hab
  refine Finset.disjoint_left.2 fun κ ha hb => hab ?_
  rw [Finset.Nat.mem_antidiagonalTuple] at ha hb
  exact ha.symm.trans hb

/-- The coefficients `A_α` of (6.21): `Σ_{m0 < |κ| ≤ ξ} n_{|κ|} (S δ_α)(κ)` on the window,
`0` off it. -/
private def expA (s ξ m0 : ℕ) (n : ℕ → ℝ) (α : Fin s → ℕ) : ℝ :=
  if α ∈ highIdx s m0 ξ then
    ∑ κ ∈ highIdx s m0 ξ, n (∑ t, κ t) * expS ℝ s ξ n (fun β => if β = α then 1 else 0) κ
  else 0

/-- The algebraic identity behind (6.21): with `err = X - (1 + U) Y`, the expansion of `X 0`
leaves `err 0 - Σ_α A_α err α`. -/
private lemma expansion_identity (s ξ m0 : ℕ) (n : ℕ → ℝ) (hm0 : m0 ≤ ξ) (hn0 : n 0 = 1)
    (X Y : (Fin s → ℕ) → ℂ) :
    X 0 - (∑ k ∈ Finset.range (m0 + 1), (n k : ℂ) *
        ∑ κ ∈ Finset.Nat.antidiagonalTuple s k, Y κ)
      - ∑ α ∈ highIdx s m0 ξ, (expA s ξ m0 n α : ℂ) * X α =
    (X - (Y + expU ℂ s ξ n Y)) 0 -
      ∑ α ∈ highIdx s m0 ξ, (expA s ξ m0 n α : ℂ) * (X - (Y + expU ℂ s ξ n Y)) α := by
  set err := X - (Y + expU ℂ s ξ n Y) with herr
  -- the value of `(1 + U) Y` at `0`
  have h0 : (Y + expU ℂ s ξ n Y) 0 = Y 0 + ∑ c ∈ Finset.range ξ, (n (c + 1) : ℂ) *
      ∑ l ∈ Finset.Nat.antidiagonalTuple s (c + 1), Y l := by
    rw [Pi.add_apply, expU_apply]
    simp only [Pi.zero_apply, Finset.sum_const_zero, Nat.sub_zero, zero_add, Nat.choose_self,
      Finset.prod_const_one, Nat.cast_one, mul_one, Complex.real_smul, Finset.mul_sum]
  have hlow : ∑ k ∈ Finset.range (m0 + 1), (n k : ℂ) *
      ∑ κ ∈ Finset.Nat.antidiagonalTuple s k, Y κ = Y 0 + ∑ c ∈ Finset.range m0,
        (n (c + 1) : ℂ) * ∑ l ∈ Finset.Nat.antidiagonalTuple s (c + 1), Y l := by
    rw [Finset.sum_range_succ', add_comm]
    simp [hn0, Finset.Nat.antidiagonalTuple_zero_right]
  have hhigh : ∑ c ∈ Finset.range ξ, (n (c + 1) : ℂ) *
      ∑ l ∈ Finset.Nat.antidiagonalTuple s (c + 1), Y l =
      (∑ c ∈ Finset.range m0, (n (c + 1) : ℂ) *
        ∑ l ∈ Finset.Nat.antidiagonalTuple s (c + 1), Y l) +
      ∑ κ ∈ highIdx s m0 ξ, (n (∑ t, κ t) : ℂ) * Y κ := by
    rw [← Finset.sum_range_add_sum_Ico _ hm0, expansion_sum_highIdx]
    congr 1
    rw [Finset.sum_Ico_add' (fun k => (n k : ℂ) * ∑ l ∈ Finset.Nat.antidiagonalTuple s k, Y l),
      show Finset.Ico (m0 + 1) (ξ + 1) = Finset.Icc (m0 + 1) ξ by
        ext; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun κ hκ => ?_
    rw [(Finset.Nat.mem_antidiagonalTuple.1 hκ)]
  -- the window values of `Y`
  have hY : ∀ κ ∈ highIdx s m0 ξ, Y κ = ∑ α ∈ highIdx s m0 ξ,
      (expS ℝ s ξ n (fun β => if β = α then 1 else 0) κ : ℂ) * (X α - err α) := by
    intro κ hκ
    have h1 : Y = expS ℂ s ξ n (X - err) := by
      rw [herr, sub_sub_cancel, expS_apply_add_expU]
    rw [h1, expS_apply_eq_sum s ξ m0 n _ κ hκ]
    simp only [Complex.real_smul, Pi.sub_apply]
  have hsum : ∑ κ ∈ highIdx s m0 ξ, (n (∑ t, κ t) : ℂ) * Y κ =
      ∑ α ∈ highIdx s m0 ξ, (expA s ξ m0 n α : ℂ) * (X α - err α) := by
    rw [Finset.sum_congr rfl fun κ hκ => by rw [hY κ hκ], ]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α hα => ?_
    simp only [expA, hα, ↓reduceIte, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun κ _ => ?_
    ring
  have hX0 : X 0 = (Y + expU ℂ s ξ n Y) 0 + err 0 := by
    rw [herr, Pi.sub_apply]; ring
  rw [hX0, h0, hlow, hhigh, hsum]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- `∏_t C(κ_t + l_t, l_t) ≤ ξ^{|l|}` when `|κ + l| ≤ ξ`. -/
private lemma expansion_binom_le {s ξ : ℕ} (κ l : Fin s → ℕ) (h : ∑ t, (κ + l) t ≤ ξ) :
    ((∏ t, Nat.choose (κ t + l t) (l t) : ℕ) : ℝ) ≤ (ξ : ℝ) ^ (∑ t, l t) := by
  have h1 : (∏ t, Nat.choose (κ t + l t) (l t)) ≤ ∏ t, ξ ^ (l t) := by
    refine Finset.prod_le_prod fun t _ => ?_
    refine (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left ?_ _)
    have := Finset.single_le_sum (f := fun t => (κ + l) t) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ t)
    simp only [Pi.add_apply] at this h
    omega
  rw [Finset.prod_pow_eq_pow_sum] at h1
  exact_mod_cast h1

private lemma expansion_geom_le (m : ℕ) : ∑ c ∈ Finset.range m, (1 / 2 : ℝ) ^ (c + 1) ≤ 1 := by
  have : ∀ m, ∑ c ∈ Finset.range m, (1 / 2 : ℝ) ^ (c + 1) = 1 - (1 / 2) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [this]
  have : (0 : ℝ) ≤ (1 / 2) ^ m := by positivity
  linarith

/-- The bound `|y β| ≤ θ^{D - |β|}` for `|β| ≤ D`, `y β = 0` for `|β| > D`, is kept by `U` when
`|n_c| (s ξ)^c ≤ (θ/2)^c` for `c ≥ 1`. -/
private lemma expU_bound (s ξ : ℕ) (n : ℕ → ℝ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hn : ∀ c : ℕ, |n (c + 1)| * ((s : ℝ) * ξ) ^ (c + 1) ≤ (θ / 2) ^ (c + 1)) (D : ℕ)
    (y : (Fin s → ℕ) → ℝ)
    (hy : ∀ β, (D < ∑ t, β t → y β = 0) ∧ (∑ t, β t ≤ D → |y β| ≤ θ ^ (D - ∑ t, β t))) :
    ∀ κ, (D < ∑ t, κ t → expU ℝ s ξ n y κ = 0) ∧
      (∑ t, κ t ≤ D → |expU ℝ s ξ n y κ| ≤ θ ^ (D - ∑ t, κ t)) := by
  intro κ
  refine ⟨fun hκ => ?_, fun hκ => ?_⟩
  · rw [expU_apply]
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun l hl => ?_
    rw [Finset.Nat.mem_antidiagonalTuple] at hl
    rw [(hy (κ + l)).1 (by rw [expansion_sum_add, hl]; omega), smul_zero]
  · rw [expU_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ c ∈ Finset.range (ξ - ∑ t, κ t),
        |∑ l ∈ Finset.Nat.antidiagonalTuple s (c + 1),
          (n (c + 1) * ((∏ t, Nat.choose (κ t + l t) (l t) : ℕ) : ℝ)) • y (κ + l)| ≤
        θ ^ (D - ∑ t, κ t) * (1 / 2) ^ (c + 1) := by
      intro c hc
      rw [Finset.mem_range] at hc
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      by_cases hD : ∑ t, κ t + (c + 1) ≤ D
      · have hl1 : ∀ l ∈ Finset.Nat.antidiagonalTuple s (c + 1),
            |(n (c + 1) * ((∏ t, Nat.choose (κ t + l t) (l t) : ℕ) : ℝ)) • y (κ + l)| ≤
              |n (c + 1)| * (ξ : ℝ) ^ (c + 1) * θ ^ (D - ∑ t, κ t - (c + 1)) := by
          intro l hl
          rw [Finset.Nat.mem_antidiagonalTuple] at hl
          have hsum : ∑ t, (κ + l) t = ∑ t, κ t + (c + 1) := by rw [expansion_sum_add, hl]
          rw [smul_eq_mul, abs_mul, abs_mul, Nat.abs_cast]
          have hb := expansion_binom_le (ξ := ξ) κ l (by omega)
          rw [hl] at hb
          have hyb := (hy (κ + l)).2 (by omega)
          rw [hsum, show D - (∑ t, κ t + (c + 1)) = D - ∑ t, κ t - (c + 1) by omega] at hyb
          exact mul_le_mul (mul_le_mul_of_nonneg_left hb (abs_nonneg _)) hyb (abs_nonneg _)
            (by positivity)
        refine (Finset.sum_le_sum hl1).trans ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : ((Finset.Nat.antidiagonalTuple s (c + 1)).card : ℝ) ≤ (s : ℝ) ^ (c + 1) := by
          exact_mod_cast card_antidiagonalTuple_le s (c + 1)
        have hsplit : θ ^ (D - ∑ t, κ t) = θ ^ (c + 1) * θ ^ (D - ∑ t, κ t - (c + 1)) := by
          rw [← pow_add]; congr 1; omega
        have hn' := hn c
        rw [mul_pow, div_pow] at hn'
        calc _ ≤ (s : ℝ) ^ (c + 1) *
              (|n (c + 1)| * (ξ : ℝ) ^ (c + 1) * θ ^ (D - ∑ t, κ t - (c + 1))) := by
              gcongr
          _ = (|n (c + 1)| * ((s : ℝ) ^ (c + 1) * (ξ : ℝ) ^ (c + 1))) *
              θ ^ (D - ∑ t, κ t - (c + 1)) := by ring
          _ ≤ (θ ^ (c + 1) / 2 ^ (c + 1)) * θ ^ (D - ∑ t, κ t - (c + 1)) := by gcongr
          _ = _ := by
            rw [hsplit, one_div, inv_pow]
            field_simp
      · have h0 : ∀ l ∈ Finset.Nat.antidiagonalTuple s (c + 1),
            |(n (c + 1) * ((∏ t, Nat.choose (κ t + l t) (l t) : ℕ) : ℝ)) • y (κ + l)| = 0 := by
          intro l hl
          rw [Finset.Nat.mem_antidiagonalTuple] at hl
          rw [(hy (κ + l)).1 (by rw [expansion_sum_add, hl]; omega), smul_zero, abs_zero]
        rw [Finset.sum_congr rfl h0, Finset.sum_const_zero]
        positivity
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    calc _ ≤ θ ^ (D - ∑ t, κ t) * 1 := by gcongr; exact expansion_geom_le _
      _ = _ := mul_one _

/-- `|(S δ_α)(κ)| ≤ (ξ + 1) θ^{|α| - |κ|}`, and `(S δ_α)(κ) = 0` for `|κ| > |α|`. -/
private lemma expS_delta_bound (s ξ : ℕ) (n : ℕ → ℝ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hn : ∀ c : ℕ, |n (c + 1)| * ((s : ℝ) * ξ) ^ (c + 1) ≤ (θ / 2) ^ (c + 1))
    (α κ : Fin s → ℕ) :
    (∑ t, α t < ∑ t, κ t → expS ℝ s ξ n (fun β => if β = α then 1 else 0) κ = 0) ∧
      (∑ t, κ t ≤ ∑ t, α t → |expS ℝ s ξ n (fun β => if β = α then 1 else 0) κ| ≤
        (ξ + 1) * θ ^ (∑ t, α t - ∑ t, κ t)) := by
  set D := ∑ t, α t
  have hj : ∀ j : ℕ, ∀ β, (D < ∑ t, β t →
      ((-expU ℝ s ξ n) ^ j) (fun β => if β = α then 1 else 0) β = 0) ∧
      (∑ t, β t ≤ D → |((-expU ℝ s ξ n) ^ j) (fun β => if β = α then 1 else 0) β| ≤
        θ ^ (D - ∑ t, β t)) := by
    intro j
    induction j with
    | zero =>
      intro β
      simp only [pow_zero, Module.End.one_apply]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have : β ≠ α := fun e => by rw [e] at h; exact lt_irrefl _ h
        simp [this]
      · by_cases e : β = α
        · subst e; simp [D]
        · simp only [e, ↓reduceIte, abs_zero]; positivity
    | succ j ih =>
      intro β
      have h := expU_bound s ξ n hθ hn D _ ih β
      rw [pow_succ', Module.End.mul_apply, LinearMap.neg_apply, Pi.neg_apply, abs_neg, neg_eq_zero]
      exact h
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [expS, LinearMap.sum_apply, Finset.sum_apply]
    exact Finset.sum_eq_zero fun j _ => (hj j κ).1 h
  · simp only [expS, LinearMap.sum_apply, Finset.sum_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ => (hj j κ).2 h).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    exact le_rfl

/-- (6.22) before the choice of parameters: if `|n_k| ≤ β ρ^k` for `k > m0` and `s ρ ≤ θ`, then
`|A_α| ≤ (ξ + 1)² β θ^{|α|}`. -/
private lemma expA_bound (s ξ m0 : ℕ) (n : ℕ → ℝ) {θ β ρ : ℝ} (hθ : 0 ≤ θ) (hβ : 0 ≤ β)
    (hρ : 0 ≤ ρ) (hsρ : (s : ℝ) * ρ ≤ θ)
    (hn : ∀ c : ℕ, |n (c + 1)| * ((s : ℝ) * ξ) ^ (c + 1) ≤ (θ / 2) ^ (c + 1))
    (hlead : ∀ k, m0 < k → |n k| ≤ β * ρ ^ k) (α : Fin s → ℕ) :
    |expA s ξ m0 n α| ≤ ((ξ : ℝ) + 1) ^ 2 * β * θ ^ (∑ t, α t) := by
  unfold expA
  split_ifs with hα
  swap
  · rw [abs_zero]; positivity
  set D := ∑ t, α t
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [expansion_sum_highIdx]
  have hlev : ∀ k ∈ Finset.Icc (m0 + 1) ξ, ∑ κ ∈ Finset.Nat.antidiagonalTuple s k,
      |n (∑ t, κ t) * expS ℝ s ξ n (fun β => if β = α then 1 else 0) κ| ≤
        ((ξ : ℝ) + 1) * β * θ ^ D := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    by_cases hkD : k ≤ D
    · have h1 : ∀ κ ∈ Finset.Nat.antidiagonalTuple s k,
          |n (∑ t, κ t) * expS ℝ s ξ n (fun β => if β = α then 1 else 0) κ| ≤
            β * ρ ^ k * (((ξ : ℝ) + 1) * θ ^ (D - k)) := by
        intro κ hκ
        rw [Finset.Nat.mem_antidiagonalTuple] at hκ
        rw [abs_mul, hκ]
        have h2 := (expS_delta_bound s ξ n hθ hn α κ).2 (by rw [hκ]; exact hkD)
        rw [hκ] at h2
        exact mul_le_mul (hlead k (by omega)) h2 (abs_nonneg _) (by positivity)
      refine (Finset.sum_le_sum h1).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((Finset.Nat.antidiagonalTuple s k).card : ℝ) ≤ (s : ℝ) ^ k := by
        exact_mod_cast card_antidiagonalTuple_le s k
      have hsplit : θ ^ D = θ ^ k * θ ^ (D - k) := by rw [← pow_add]; congr 1; omega
      have hθk : (s : ℝ) ^ k * ρ ^ k ≤ θ ^ k := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hsρ k
      calc _ ≤ (s : ℝ) ^ k * (β * ρ ^ k * (((ξ : ℝ) + 1) * θ ^ (D - k))) := by gcongr
        _ = ((ξ : ℝ) + 1) * β * ((s : ℝ) ^ k * ρ ^ k) * θ ^ (D - k) := by ring
        _ ≤ ((ξ : ℝ) + 1) * β * θ ^ k * θ ^ (D - k) := by gcongr
        _ = _ := by rw [hsplit]; ring
    · have h0 : ∀ κ ∈ Finset.Nat.antidiagonalTuple s k,
          |n (∑ t, κ t) * expS ℝ s ξ n (fun β => if β = α then 1 else 0) κ| = 0 := by
        intro κ hκ
        rw [Finset.Nat.mem_antidiagonalTuple] at hκ
        rw [(expS_delta_bound s ξ n hθ hn α κ).1 (by rw [hκ]; omega), mul_zero, abs_zero]
      rw [Finset.sum_congr rfl h0, Finset.sum_const_zero]
      positivity
  refine (Finset.sum_le_sum hlev).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
  have : ((ξ + 1 - (m0 + 1) : ℕ) : ℝ) ≤ (ξ : ℝ) + 1 := by
    have : ξ + 1 - (m0 + 1) ≤ ξ + 1 := Nat.sub_le _ _
    exact_mod_cast this
  calc _ ≤ ((ξ : ℝ) + 1) * (((ξ : ℝ) + 1) * β * θ ^ D) := by gcongr
    _ = _ := by ring


private lemma expansion_continuous_evalW {N : ℕ} {X : Type*} [TopologicalSpace X]
    (G : X → Matrix (Fin N) (Fin N) ℂ) (hG : ∀ i j, Continuous fun x => G x i j) (m : ℂ)
    (ws : List (Word N)) : Continuous fun x => evalW (G x) m ws := by
  have hl : ∀ ℓ : Letter N, Continuous fun x => evalLetter (G x) m ℓ := by
    rintro ⟨k, i, j⟩
    cases k <;> simp only [evalLetter]
    · exact hG i j
    · exact (hG i j).star
    · exact (hG i j).sub continuous_const
    · exact ((hG i j).sub continuous_const).star
  have hw : ∀ w : Word N, Continuous fun x => evalWord (G x) m w := by
    intro w
    induction w with
    | nil => simp only [evalWord, List.map_nil, List.prod_nil]; exact continuous_const
    | cons ℓ w ih =>
      simp only [evalWord, List.map_cons, List.prod_cons] at ih ⊢
      exact (hl ℓ).mul ih
  induction ws with
  | nil => simp only [evalW, List.map_nil, List.sum_nil]; exact continuous_const
  | cons w ws ih =>
    simp only [evalW, List.map_cons, List.sum_cons] at ih ⊢
    exact (hw w).add ih

private lemma expansion_continuous_zeroEntry {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    Continuous (zeroEntry e) := by
  rcases e with i | p
  · exact (continuous_fst.update i continuous_const).prodMk continuous_snd
  · exact continuous_fst.prodMk (continuous_snd.update p continuous_const)

private lemma expansion_continuous_entryVal {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    Continuous (entryVal e) := by
  rcases e with i | p
  · exact (continuous_apply i).comp continuous_fst
  · exact (continuous_apply p).comp continuous_snd

private lemma expansion_continuous_resS {N : ℕ} {z : ℂ} (hz : z.im ≠ 0) (m : ℂ)
    (ws : List (Word N)) : Continuous fun ω : Entries N => evalW (resS z ω) m ws :=
  expansion_continuous_evalW _ (fun i j => continuous_resolventC_symOfEntries hz i j) m ws

private lemma expansion_continuous_resR {N : ℕ} {z : ℂ} (hz : z.im ≠ 0)
    (e : Fin N ⊕ OffDiag N) (m : ℂ) (ws : List (Word N)) :
    Continuous fun ω : Entries N => evalW (resR e z ω) m ws :=
  (expansion_continuous_resS hz m ws).comp (expansion_continuous_zeroEntry e)

/-- Almost surely `|v_e| ≤ q⁻¹`. -/
private lemma expansion_ae_entryVal_le {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) {q : ℝ}
    (hs : L.BoundedSupportAS q) (e : Fin N ⊕ OffDiag N) :
    ∀ᵐ ω ∂L.law, |entryVal e ω| ≤ q⁻¹ := by
  rw [ae_iff]
  have := hL.diag
  have := hL.off
  have hT : MeasurableSet {x : ℝ | q⁻¹ < |x|} := measurableSet_lt measurable_const measurable_abs
  simp only [not_le]
  rcases e with i | p
  · have hmp : MeasurePreserving (fun ω : Entries N => ω.1 i) L.law (L.diag i) :=
      (measurePreserving_eval (fun i => L.diag i) i).comp
        (measurePreserving_fst (μ := Measure.pi L.diag) (ν := Measure.pi L.off))
    exact (hmp.measure_preimage hT.nullMeasurableSet).trans (hs.1 i)
  · have hmp : MeasurePreserving (fun ω : Entries N => ω.2 p) L.law (L.off p) :=
      (measurePreserving_eval (fun p => L.off p) p).comp
        (measurePreserving_snd (μ := Measure.pi L.diag) (ν := Measure.pi L.off))
    exact (hmp.measure_preimage hT.nullMeasurableSet).trans (hs.2 p)

/-- Split of an expectation over the good event and its complement. -/
private lemma expansion_norm_integral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℂ} {G : Set Ω} {a b : ℝ} (ha : 0 ≤ a)
    (hgood : ∀ᵐ ω ∂μ, ω ∈ G → ‖f ω‖ ≤ a) (hbad : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ b) :
    ‖∫ ω, f ω ∂μ‖ ≤ a + b * (μ Gᶜ).toReal := by
  set T := toMeasurable μ Gᶜ
  have hT : MeasurableSet T := measurableSet_toMeasurable _ _
  have hi : Integrable (fun ω => b * T.indicator (fun _ => (1 : ℝ)) ω) μ :=
    ((integrable_const (1 : ℝ)).indicator hT).const_mul b
  have hg : Integrable (fun ω => a + b * T.indicator (fun _ => (1 : ℝ)) ω) μ :=
    (integrable_const a).add hi
  refine (norm_integral_le_of_norm_le hg ?_).trans_eq ?_
  · filter_upwards [hgood, hbad] with ω h1 h2
    by_cases hω : ω ∈ T
    · rw [Set.indicator_of_mem hω, mul_one]; linarith
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      exact h1 (by_contra fun h => hω (subset_toMeasurable μ Gᶜ h))
  · rw [integral_add (integrable_const a) hi, integral_const, integral_const_mul,
      integral_indicator_const _ hT]
    simp [Measure.real, T, measure_toMeasurable]

/-- `(1 + U) Y` at `κ` as one sum over `0 ≤ c ≤ ξ - |κ|`, when `n_0 = 1`. -/
private lemma expU_add_apply_eq (s ξ : ℕ) (n : ℕ → ℝ) (hn0 : n 0 = 1)
    (Y : (Fin s → ℕ) → ℂ) (κ : Fin s → ℕ) :
    (Y + expU ℂ s ξ n Y) κ = ∑ c ∈ Finset.range (ξ - ∑ t, κ t + 1),
      ∑ l ∈ Finset.Nat.antidiagonalTuple s c,
        ((∏ t, Nat.choose (κ t + l t) (l t) : ℕ) : ℂ) * (Y (κ + l) * (n c : ℂ)) := by
  rw [Finset.sum_range_succ', Pi.add_apply, expU_apply, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.real_smul]
    push_cast
    ring
  · simp [Finset.Nat.antidiagonalTuple_zero_right, hn0]

/-- Entries of the resolvents are at most `1 / η`, so every word image is bounded. -/
private lemma expansion_norm_evalW_le {N : ℕ} {z : ℂ} (hz : 0 < z.im) {B : ℝ}
    (hB : 1 / z.im ≤ B) (H : Matrix (Fin N) (Fin N) ℝ) (hH : H.IsHermitian)
    (e : Fin N ⊕ OffDiag N) (k : List ℕ) (w : Word N) (hk : k.length = w.length) :
    ‖evalW (resolventC H z) (msc z) (wordP e k w)‖ ≤ 2 ^ k.sum * (B + 1) ^ (w.length + k.sum) :=
  norm_evalW_wordP_le_of_le (fun i j => (norm_resolventC_apply_le hH hz i j).trans hB)
    (norm_msc_eq_inv_and_lt_one hz).2.le e k w hk

/-- The remainder of one step of (6.62)–(6.76): with `X κ = E P_κ(word)(S)` and
`Y κ = E P_κ(word)(R)`, the defect `X κ - ((1 + U) Y) κ` is bounded by the good-event remainder of
`norm_evalW_wordP_sub_expansion_le_of_good` plus a crude bound times the probability of the
complement of the good event. -/
private lemma expansion_err_le {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) {q : ℝ} (hq : 0 < q)
    (hq1 : 1 ≤ q) (hs : L.BoundedSupportAS q) {C0 : ℝ} {z : ℂ} (hz : z ∈ specDomain N C0)
    {B : ℝ} (hB : 1 / z.im ≤ B) (e : Fin N ⊕ OffDiag N) {s : ℕ} (w : Word N)
    (hw : w.length = s) (ξ : ℕ) (hsq : 8 * ((s + ξ : ℕ) : ℝ) ≤ q) (κ : Fin s → ℕ)
    (hκ : ∑ t, κ t ≤ ξ) :
    ‖((fun κ : Fin s → ℕ => ∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn κ) w) ∂L.law) -
        ((fun κ : Fin s → ℕ => ∫ ω, evalW (resR e z ω) (msc z) (wordP e (List.ofFn κ) w) ∂L.law) +
          expU ℂ s ξ (L.entryMoment e)
            (fun κ : Fin s → ℕ => ∫ ω, evalW (resR e z ω) (msc z) (wordP e (List.ofFn κ) w)
              ∂L.law))) κ‖ ≤
      2 ^ (∑ t, κ t) * 4 ^ (s + ∑ t, κ t + 2) *
          (4 * ((s + ∑ t, κ t : ℕ) : ℝ) / q) ^ (ξ - ∑ t, κ t + 1) +
        (1 + ((ξ : ℝ) + 1) * ((s : ℝ) * ξ + 1) ^ ξ) * 2 ^ ξ * (B + 1) ^ (s + ξ) *
          (L.law (goodEvent N C0)ᶜ).toReal := by
  have := isProbabilityMeasure_law hL
  set K := ∑ t, κ t with hK
  set v : Entries N → ℝ := entryVal e
  have hzim : 0 < z.im :=
    lt_of_le_of_lt (div_nonneg (Real.rpow_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg N) _) _)
      (Nat.cast_nonneg N)) hz.2.1
  have hB0 : 0 ≤ B := le_trans (by positivity) hB
  set fS : (Fin s → ℕ) → Entries N → ℂ :=
    fun κ ω => evalW (resS z ω) (msc z) (wordP e (List.ofFn κ) w)
  set F : (Fin s → ℕ) → Entries N → ℂ :=
    fun κ ω => evalW (resolventC (symOfEntries ω) z) (msc z) (wordP e (List.ofFn κ) w)
  have hlen : ∀ κ' : Fin s → ℕ, (List.ofFn κ').length = w.length := by simp [hw]
  have hFb : ∀ κ' ω, ‖F κ' ω‖ ≤ 2 ^ (∑ t, κ' t) * (B + 1) ^ (s + ∑ t, κ' t) := by
    intro κ' ω
    have := expansion_norm_evalW_le hzim hB _ (symOfEntries_isHermitian ω) e _ w (hlen κ')
    rwa [List.sum_ofFn, hw] at this
  have hFc : ∀ κ', Continuous (F κ') := fun κ' => expansion_continuous_evalW _
    (fun i j => continuous_resolventC_symOfEntries hzim.ne' i j) _ _
  have hRc : ∀ κ', Continuous fun ω => F κ' (zeroEntry e ω) :=
    fun κ' => (hFc κ').comp (expansion_continuous_zeroEntry e)
  have hvc : Continuous v := expansion_continuous_entryVal e
  have hvae := expansion_ae_entryVal_le hL hs e
  have hFint : ∀ κ', Integrable (F κ') L.law := fun κ' =>
    Integrable.of_bound (hFc κ').aestronglyMeasurable _ (Eventually.of_forall (hFb κ'))
  have hRint : ∀ κ', Integrable (fun ω => F κ' (zeroEntry e ω)) L.law := fun κ' =>
    Integrable.of_bound (hRc κ').aestronglyMeasurable _ (Eventually.of_forall fun ω => hFb κ' _)
  have hRvint : ∀ κ' (c : ℕ), Integrable (fun ω => F κ' (zeroEntry e ω) *
      (((-v ω) ^ c : ℝ) : ℂ)) L.law := by
    intro κ' c
    refine Integrable.of_bound (((hRc κ').mul (Complex.continuous_ofReal.comp
      (hvc.neg.pow c))).aestronglyMeasurable) (2 ^ (∑ t, κ' t) * (B + 1) ^ (s + ∑ t, κ' t) *
        q⁻¹ ^ c) ?_
    filter_upwards [hvae] with ω hω
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_neg]
    exact mul_le_mul (hFb κ' _) (pow_le_pow_left₀ (abs_nonneg _) hω c) (by positivity)
      (by positivity)
  have hmom : ∀ c : ℕ, Integrable (fun x : ℝ => x ^ c) (L.entry e) := by
    intro c
    have h := BoundedSupportAS.integrable_pow hs hL c
    rcases e with i | p
    · exact h.1 i
    · exact h.2 p
  have hn0 : L.entryMoment e 0 = 1 := by
    have h1 := hL.diag
    have h2 := hL.off
    rcases e with i | p <;> simp [EntryLaws.entryMoment, EntryLaws.entry]
  set D : Entries N → ℂ := fun ω => fS κ ω -
    ∑ c ∈ Finset.range (ξ - K + 1), (((-v ω) ^ c : ℝ) : ℂ) *
      ∑ l ∈ Finset.Nat.antidiagonalTuple s c,
        ((∏ t, Nat.choose (κ t + l t) (l t) : ℕ) : ℂ) * F (κ + l) (zeroEntry e ω) with hD
  have hint : ((fun κ : Fin s → ℕ => ∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn κ) w)
        ∂L.law) -
      ((fun κ : Fin s → ℕ => ∫ ω, evalW (resR e z ω) (msc z) (wordP e (List.ofFn κ) w) ∂L.law) +
        expU ℂ s ξ (L.entryMoment e)
          (fun κ : Fin s → ℕ => ∫ ω, evalW (resR e z ω) (msc z) (wordP e (List.ofFn κ) w)
            ∂L.law))) κ = ∫ ω, D ω ∂L.law := by
    rw [Pi.sub_apply, expU_add_apply_eq _ _ _ hn0, ← hK]
    have hcl : ∀ (c : ℕ) (l : Fin s → ℕ), ((∏ t, Nat.choose (κ t + l t) (l t) : ℕ) : ℂ) *
        ((∫ ω, evalW (resR e z ω) (msc z) (wordP e (List.ofFn (κ + l)) w) ∂L.law) *
          (L.entryMoment e c : ℂ)) =
        ∫ ω, ((∏ t, Nat.choose (κ t + l t) (l t) : ℕ) : ℂ) *
          (F (κ + l) (zeroEntry e ω) * (((-v ω) ^ c : ℝ) : ℂ)) ∂L.law := by
      intro c l
      rw [integral_const_mul, integral_mul_zeroEntry hL e (F (κ + l)) c (hFc _).measurable
        (hRint _) (hmom c)]
      rfl
    simp_rw [hcl]
    rw [← Finset.sum_congr rfl fun c _ => integral_finsetSum _ fun l _ =>
      (hRvint (κ + l) c).const_mul _, ← integral_finsetSum _ fun c _ =>
        integrable_finsetSum _ fun l _ => (hRvint (κ + l) c).const_mul _]
    rw [← integral_sub (f := fun ω => evalW (resS z ω) (msc z) (wordP e (List.ofFn κ) w))
      (hFint κ) (integrable_finsetSum _ fun c _ =>
        integrable_finsetSum _ fun l _ => (hRvint (κ + l) c).const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [hD, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hint]
  have hq1' : q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq1
  have hW0 : ∀ κ' : Fin s → ℕ, ∑ t, κ' t ≤ ξ → ∀ ω,
      ‖F κ' ω‖ ≤ 2 ^ ξ * (B + 1) ^ (s + ξ) := by
    intro κ' hκ' ω
    refine (hFb κ' ω).trans ?_
    gcongr
    · norm_num
    · linarith
  refine expansion_norm_integral_le (by positivity) ?_ ?_
  · filter_upwards [hvae] with ω hv hω
    have hsq' : 8 * ((s + ∑ t, κ t : ℕ) : ℝ) ≤ q := by
      refine le_trans ?_ hsq
      gcongr
    exact norm_evalW_wordP_sub_expansion_le_of_good hω hz e
      (norm_msc_eq_inv_and_lt_one hzim).2.le hq hv w hw κ hsq' (ξ - K)
  · filter_upwards [hvae] with ω hv
    have hvq : |v ω| ≤ 1 := hv.trans hq1'
    have hc : ∀ c ∈ Finset.range (ξ - K + 1),
        ‖(((-v ω) ^ c : ℝ) : ℂ) * ∑ l ∈ Finset.Nat.antidiagonalTuple s c,
          ((∏ t, Nat.choose (κ t + l t) (l t) : ℕ) : ℂ) * F (κ + l) (zeroEntry e ω)‖ ≤
        ((s : ℝ) * ξ + 1) ^ ξ * (2 ^ ξ * (B + 1) ^ (s + ξ)) := by
      intro c hc
      rw [Finset.mem_range] at hc
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_neg]
      have h1 : |v ω| ^ c ≤ 1 := pow_le_one₀ (abs_nonneg _) hvq
      have h2 : ∀ l ∈ Finset.Nat.antidiagonalTuple s c,
          ‖((∏ t, Nat.choose (κ t + l t) (l t) : ℕ) : ℂ) * F (κ + l) (zeroEntry e ω)‖ ≤
            (ξ : ℝ) ^ c * (2 ^ ξ * (B + 1) ^ (s + ξ)) := by
        intro l hl
        rw [Finset.Nat.mem_antidiagonalTuple] at hl
        have hsum : ∑ t, (κ + l) t = K + c := by rw [expansion_sum_add, hl]
        rw [norm_mul, Complex.norm_natCast]
        have hb := expansion_binom_le (ξ := ξ) κ l (by omega)
        rw [hl] at hb
        exact mul_le_mul hb (hW0 _ (by omega) _) (norm_nonneg _) (by positivity)
      have h3 := norm_sum_le_of_le _ h2
      rw [Finset.sum_const, nsmul_eq_mul] at h3
      have hcard : ((Finset.Nat.antidiagonalTuple s c).card : ℝ) ≤ (s : ℝ) ^ c := by
        exact_mod_cast card_antidiagonalTuple_le s c
      have h4 : (s : ℝ) ^ c * (ξ : ℝ) ^ c ≤ ((s : ℝ) * ξ + 1) ^ ξ := by
        rw [← mul_pow]
        have h0 : (0 : ℝ) ≤ (s : ℝ) * ξ := by positivity
        have h1' : (1 : ℝ) ≤ (s : ℝ) * ξ + 1 := by linarith
        calc ((s : ℝ) * ξ) ^ c ≤ ((s : ℝ) * ξ + 1) ^ c := by gcongr; linarith
          _ ≤ ((s : ℝ) * ξ + 1) ^ ξ := pow_le_pow_right₀ h1' (by omega)
      calc |v ω| ^ c * ‖∑ l ∈ Finset.Nat.antidiagonalTuple s c,
            ((∏ t, Nat.choose (κ t + l t) (l t) : ℕ) : ℂ) * F (κ + l) (zeroEntry e ω)‖ ≤
            1 * ((s : ℝ) ^ c * ((ξ : ℝ) ^ c * (2 ^ ξ * (B + 1) ^ (s + ξ)))) := by
            refine mul_le_mul h1 (h3.trans ?_) (norm_nonneg _) zero_le_one
            gcongr
        _ = ((s : ℝ) ^ c * (ξ : ℝ) ^ c) * (2 ^ ξ * (B + 1) ^ (s + ξ)) := by ring
        _ ≤ _ := by gcongr
    have hsum := norm_sum_le_of_le _ hc
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range] at hsum
    have hcnt : ((ξ - K + 1 : ℕ) : ℝ) ≤ (ξ : ℝ) + 1 := by
      have : ξ - K + 1 ≤ ξ + 1 := by omega
      exact_mod_cast this
    calc ‖D ω‖ ≤ ‖fS κ ω‖ + ‖∑ c ∈ Finset.range (ξ - K + 1), (((-v ω) ^ c : ℝ) : ℂ) *
          ∑ l ∈ Finset.Nat.antidiagonalTuple s c,
            ((∏ t, Nat.choose (κ t + l t) (l t) : ℕ) : ℂ) * F (κ + l) (zeroEntry e ω)‖ :=
          norm_sub_le _ _
      _ ≤ 2 ^ ξ * (B + 1) ^ (s + ξ) +
          ((ξ : ℝ) + 1) * (((s : ℝ) * ξ + 1) ^ ξ * (2 ^ ξ * (B + 1) ^ (s + ξ))) := by
          gcongr
          · exact hW0 κ hκ ω
          · exact hsum.trans (by gcongr)
      _ = _ := by ring

/-- The good-event part of the remainder of (6.21): the first-step remainder and the remainders of
the conversions, weighted by `|A_α| ≤ (ξ + 1)² β (Λ/q)^{|α|}`, sum to at most
`16 · 4^s (1 + (ξ + 1)³ β) (Γ/q)^{ξ + 1}` with `Γ = 8 (s + 1) Λ + 4 (s + ξ)`. -/
private lemma expansion_good_sum_le (s m0 ξ : ℕ) {q Λ β : ℝ} (hq : 0 < q) (hΛ : 0 ≤ Λ)
    (hβ : 0 ≤ β) (A : (Fin s → ℕ) → ℝ)
    (hA : ∀ α, |A α| ≤ ((ξ : ℝ) + 1) ^ 2 * β * (Λ * q⁻¹) ^ (∑ t, α t)) :
    4 ^ (s + 2) * (4 * (s : ℝ) / q) ^ (ξ + 1) +
      ∑ α ∈ highIdx s m0 ξ, |A α| * (2 ^ (∑ t, α t) * 4 ^ (s + ∑ t, α t + 2) *
        (4 * ((s + ∑ t, α t : ℕ) : ℝ) / q) ^ (ξ - ∑ t, α t + 1)) ≤
    16 * 4 ^ s * (1 + ((ξ : ℝ) + 1) ^ 3 * β) *
      ((8 * ((s : ℝ) + 1) * Λ + 4 * ((s : ℝ) + ξ)) * q⁻¹) ^ (ξ + 1) := by
  set Γ := 8 * ((s : ℝ) + 1) * Λ + 4 * ((s : ℝ) + ξ)
  have hqi : 0 ≤ q⁻¹ := inv_nonneg.2 hq.le
  have hΓ1 : 8 * (s : ℝ) * Λ ≤ Γ := by
    have : 0 ≤ 4 * ((s : ℝ) + ξ) := by positivity
    nlinarith
  have hΓ2 : ∀ K ≤ ξ, 4 * ((s + K : ℕ) : ℝ) ≤ Γ := by
    intro K hK
    have : ((s + K : ℕ) : ℝ) ≤ (s : ℝ) + ξ := by push_cast; exact_mod_cast Nat.add_le_add_left hK s
    have : 0 ≤ 8 * ((s : ℝ) + 1) * Λ := by positivity
    linarith
  have h0 : 4 ^ (s + 2) * (4 * (s : ℝ) / q) ^ (ξ + 1) ≤ 16 * 4 ^ s * (Γ * q⁻¹) ^ (ξ + 1) := by
    rw [pow_add, div_eq_mul_inv]
    have := hΓ2 0 (Nat.zero_le _)
    simp only [add_zero] at this
    have : 4 * (s : ℝ) * q⁻¹ ≤ Γ * q⁻¹ := mul_le_mul_of_nonneg_right this hqi
    calc _ ≤ 4 ^ s * 4 ^ 2 * (Γ * q⁻¹) ^ (ξ + 1) := by gcongr
      _ = _ := by ring
  have hlev : ∀ K ∈ Finset.Icc (m0 + 1) ξ, ∑ α ∈ Finset.Nat.antidiagonalTuple s K,
      |A α| * (2 ^ (∑ t, α t) * 4 ^ (s + ∑ t, α t + 2) *
        (4 * ((s + ∑ t, α t : ℕ) : ℝ) / q) ^ (ξ - ∑ t, α t + 1)) ≤
      16 * 4 ^ s * (((ξ : ℝ) + 1) ^ 2 * β) * (Γ * q⁻¹) ^ (ξ + 1) := by
    intro K hK
    rw [Finset.mem_Icc] at hK
    have h1 : ∀ α ∈ Finset.Nat.antidiagonalTuple s K,
        |A α| * (2 ^ (∑ t, α t) * 4 ^ (s + ∑ t, α t + 2) *
          (4 * ((s + ∑ t, α t : ℕ) : ℝ) / q) ^ (ξ - ∑ t, α t + 1)) ≤
        ((ξ : ℝ) + 1) ^ 2 * β * (Λ * q⁻¹) ^ K * (2 ^ K * 4 ^ (s + K + 2) *
          (Γ * q⁻¹) ^ (ξ - K + 1)) := by
      intro α hα
      rw [Finset.Nat.mem_antidiagonalTuple] at hα
      have h2 := hA α
      rw [hα] at h2 ⊢
      refine mul_le_mul h2 ?_ (by positivity) (by positivity)
      gcongr
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hΓ2 K hK.2) hqi
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.Nat.antidiagonalTuple s K).card : ℝ) ≤ (s : ℝ) ^ K := by
      exact_mod_cast card_antidiagonalTuple_le s K
    have hsplit : (Γ * q⁻¹) ^ (ξ + 1) = (Γ * q⁻¹) ^ K * (Γ * q⁻¹) ^ (ξ - K + 1) := by
      rw [← pow_add]; congr 1; omega
    have h8 : (s : ℝ) ^ K * (Λ * q⁻¹) ^ K * 2 ^ K * 4 ^ K ≤ (Γ * q⁻¹) ^ K := by
      rw [← mul_pow, ← mul_pow, ← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ K
      have := mul_le_mul_of_nonneg_right hΓ1 hqi
      nlinarith
    calc _ ≤ (s : ℝ) ^ K * (((ξ : ℝ) + 1) ^ 2 * β * (Λ * q⁻¹) ^ K * (2 ^ K * 4 ^ (s + K + 2) *
          (Γ * q⁻¹) ^ (ξ - K + 1))) := by gcongr
      _ = 16 * 4 ^ s * (((ξ : ℝ) + 1) ^ 2 * β) *
          ((s : ℝ) ^ K * (Λ * q⁻¹) ^ K * 2 ^ K * 4 ^ K) * (Γ * q⁻¹) ^ (ξ - K + 1) := by
          rw [pow_add, pow_add]; ring
      _ ≤ 16 * 4 ^ s * (((ξ : ℝ) + 1) ^ 2 * β) * (Γ * q⁻¹) ^ K * (Γ * q⁻¹) ^ (ξ - K + 1) := by
          gcongr
      _ = _ := by rw [hsplit]; ring
  rw [expansion_sum_highIdx]
  have hs2 := Finset.sum_le_sum hlev
  rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc] at hs2
  have hcnt : ((ξ + 1 - (m0 + 1) : ℕ) : ℝ) ≤ (ξ : ℝ) + 1 := by
    have : ξ + 1 - (m0 + 1) ≤ ξ + 1 := Nat.sub_le _ _
    exact_mod_cast this
  have hX : 0 ≤ 16 * 4 ^ s * (((ξ : ℝ) + 1) ^ 2 * β) * (Γ * q⁻¹) ^ (ξ + 1) := by positivity
  calc _ ≤ 16 * 4 ^ s * (Γ * q⁻¹) ^ (ξ + 1) +
        ((ξ : ℝ) + 1) * (16 * 4 ^ s * (((ξ : ℝ) + 1) ^ 2 * β) * (Γ * q⁻¹) ^ (ξ + 1)) := by
        gcongr
        exact hs2.trans (mul_le_mul_of_nonneg_right hcnt hX)
    _ = _ := by ring

private lemma expansion_rpow_pow {x : ℝ} (hx : 0 ≤ x) (a : ℝ) (K : ℕ) :
    (x ^ a) ^ K = x ^ (a * K) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

/-- The good-event part is at most `4^s N^{-ζ} / 2`. -/
private lemma expansion_good_le {N : ℕ} {s ξ : ℕ} {q Γ Y ζ φq : ℝ} (hN : 1 ≤ (N : ℝ))
    (hq : 0 < q) (hqN : (N : ℝ) ^ φq ≤ q) (hΓ0 : 0 ≤ Γ)
    (hΓ : Γ ≤ (N : ℝ) ^ (φq / 2)) (hY0 : 0 ≤ Y) (hY : 32 * (1 + Y) ≤ (N : ℝ) ^ (φq / 2))
    (hξ : 2 * ζ ≤ φq * ξ) :
    16 * 4 ^ s * (1 + Y) * (Γ * q⁻¹) ^ (ξ + 1) ≤ 1 / 2 * (4 ^ s * (N : ℝ) ^ (-ζ)) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hqi : q⁻¹ ≤ (N : ℝ) ^ (-φq) := by
    rw [Real.rpow_neg hN0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hN0 _) hqN
  have h1 : Γ * q⁻¹ ≤ (N : ℝ) ^ (-(φq / 2)) := by
    calc Γ * q⁻¹ ≤ (N : ℝ) ^ (φq / 2) * (N : ℝ) ^ (-φq) :=
          mul_le_mul hΓ hqi (inv_nonneg.2 hq.le) (by positivity)
      _ = _ := by rw [← Real.rpow_add hN0]; congr 1; ring
  have h2 : (Γ * q⁻¹) ^ (ξ + 1) ≤ (N : ℝ) ^ (-ζ) * (N : ℝ) ^ (-(φq / 2)) := by
    calc (Γ * q⁻¹) ^ (ξ + 1) ≤ ((N : ℝ) ^ (-(φq / 2))) ^ (ξ + 1) :=
          pow_le_pow_left₀ (mul_nonneg hΓ0 (inv_nonneg.2 hq.le)) h1 _
      _ = (N : ℝ) ^ (-(φq / 2) * ((ξ + 1 : ℕ) : ℝ)) := expansion_rpow_pow hN0.le _ _
      _ ≤ (N : ℝ) ^ (-ζ + -(φq / 2)) := by
          refine Real.rpow_le_rpow_of_exponent_le hN ?_
          push_cast
          nlinarith
      _ = _ := Real.rpow_add hN0 _ _
  have h3 : (1 + Y) * (N : ℝ) ^ (-(φq / 2)) ≤ 1 / 32 := by
    rw [Real.rpow_neg hN0.le, ← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos hN0 _)]
    linarith
  have h4 : 0 ≤ (N : ℝ) ^ (-ζ) := by positivity
  calc 16 * 4 ^ s * (1 + Y) * (Γ * q⁻¹) ^ (ξ + 1) ≤
        16 * 4 ^ s * (1 + Y) * ((N : ℝ) ^ (-ζ) * (N : ℝ) ^ (-(φq / 2))) := by gcongr
    _ = 16 * 4 ^ s * (N : ℝ) ^ (-ζ) * ((1 + Y) * (N : ℝ) ^ (-(φq / 2))) := by ring
    _ ≤ 16 * 4 ^ s * (N : ℝ) ^ (-ζ) * (1 / 32) := by gcongr
    _ = _ := by ring

/-- The bad-event part is at most `N^{-ζ} / 2` once `(6a + 4 + C') log N ≤ c φ`. -/
private lemma expansion_bad_le {N : ℕ} {s ξ : ℕ} {ζ a C' c P : ℝ} (hN : 16 ≤ N)
    (hZ : ((s + ξ + 1 : ℕ) : ℝ) ≤ N) (hZa : ((s + ξ + 1 : ℕ) : ℝ) ≤ a * phi N ^ 2)
    (hζ : ζ ≤ phi N ^ 2) (hφ1 : 1 ≤ phi N) (hlog1 : 1 ≤ Real.log N) (hC' : 0 ≤ C')
    (hD : (6 * a + 4 + C') * Real.log N ≤ c * phi N)
    (hP : P ≤ (N : ℝ) ^ C' * Real.exp (-c * phi N ^ 3)) (hP0 : 0 ≤ P) :
    (1 + ((ξ : ℝ) + 1) * ((s : ℝ) + 1) ^ ξ) *
        ((1 + ((ξ : ℝ) + 1) * ((s : ℝ) * ξ + 1) ^ ξ) * 2 ^ ξ * ((N : ℝ) + 1) ^ (s + ξ) * P) ≤
      1 / 2 * (N : ℝ) ^ (-ζ) := by
  have hN1 : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hξ0 : (0 : ℝ) ≤ ξ := Nat.cast_nonneg _
  have hZr : (s : ℝ) + ξ + 1 ≤ N := by have := hZ; push_cast at this; linarith
  have hs : (s : ℝ) + 1 ≤ N := by linarith
  have hξN : (ξ : ℝ) + 1 ≤ N := by linarith
  set Z := s + ξ + 1 with hZdef
  -- the polynomial factors are at most `4 N^{6Z}`
  have f1 : 1 + ((ξ : ℝ) + 1) * ((s : ℝ) + 1) ^ ξ ≤ 2 * (N : ℝ) ^ Z := by
    have : ((ξ : ℝ) + 1) * ((s : ℝ) + 1) ^ ξ ≤ (N : ℝ) * (N : ℝ) ^ ξ :=
      mul_le_mul hξN (pow_le_pow_left₀ (by positivity) hs _) (by positivity) (by positivity)
    have h2 : (N : ℝ) * (N : ℝ) ^ ξ ≤ (N : ℝ) ^ Z := by
      rw [← pow_succ']; exact pow_le_pow_right₀ (by linarith) (by omega)
    have h3 : (1 : ℝ) ≤ (N : ℝ) ^ Z := one_le_pow₀ (by linarith)
    linarith
  have f2 : 1 + ((ξ : ℝ) + 1) * ((s : ℝ) * ξ + 1) ^ ξ ≤ 2 * (N : ℝ) ^ (2 * Z) := by
    have hsξ : (s : ℝ) * ξ + 1 ≤ (N : ℝ) ^ 2 := by nlinarith
    have : ((ξ : ℝ) + 1) * ((s : ℝ) * ξ + 1) ^ ξ ≤ (N : ℝ) * ((N : ℝ) ^ 2) ^ ξ :=
      mul_le_mul hξN (pow_le_pow_left₀ (by positivity) hsξ _) (by positivity) (by positivity)
    have h2 : (N : ℝ) * ((N : ℝ) ^ 2) ^ ξ ≤ (N : ℝ) ^ (2 * Z) := by
      rw [← pow_mul, ← pow_succ']; exact pow_le_pow_right₀ (by linarith) (by omega)
    have h3 : (1 : ℝ) ≤ (N : ℝ) ^ (2 * Z) := one_le_pow₀ (by linarith)
    linarith
  have f3 : (2 : ℝ) ^ ξ * ((N : ℝ) + 1) ^ (s + ξ) ≤ (N : ℝ) ^ (3 * Z) := by
    have h2 : (2 : ℝ) ^ ξ ≤ (N : ℝ) ^ Z :=
      (pow_le_pow_left₀ (by norm_num) (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith) (by omega))
    have h3 : ((N : ℝ) + 1) ^ (s + ξ) ≤ (N : ℝ) ^ (2 * Z) := by
      calc ((N : ℝ) + 1) ^ (s + ξ) ≤ ((N : ℝ) ^ 2) ^ (s + ξ) :=
            pow_le_pow_left₀ (by positivity) (by nlinarith) _
        _ = (N : ℝ) ^ (2 * (s + ξ)) := by rw [← pow_mul]
        _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
    calc _ ≤ (N : ℝ) ^ Z * (N : ℝ) ^ (2 * Z) := mul_le_mul h2 h3 (by positivity) (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; ring
  have hpoly : (1 + ((ξ : ℝ) + 1) * ((s : ℝ) + 1) ^ ξ) *
        ((1 + ((ξ : ℝ) + 1) * ((s : ℝ) * ξ + 1) ^ ξ) * 2 ^ ξ * ((N : ℝ) + 1) ^ (s + ξ)) ≤
      4 * (N : ℝ) ^ (6 * Z) := by
    calc _ ≤ (2 * (N : ℝ) ^ Z) * (2 * (N : ℝ) ^ (2 * Z) * (N : ℝ) ^ (3 * Z)) := by
          rw [mul_assoc (1 + _ * _ ^ ξ)]
          gcongr
      _ = 4 * ((N : ℝ) ^ Z * (N : ℝ) ^ (2 * Z) * (N : ℝ) ^ (3 * Z)) := by ring
      _ = _ := by rw [← pow_add, ← pow_add]; congr 2; ring
  -- the exponential beats `8 N^{6Z + C' + ζ}`
  have hexp : 8 * (N : ℝ) ^ (6 * Z) * (N : ℝ) ^ C' * (N : ℝ) ^ ζ ≤ Real.exp (c * phi N ^ 3) := by
    have hlogN : Real.log 8 ≤ 3 * Real.log N := by
      have : Real.log 8 < 3 := by
        have := Real.log_two_lt_d9
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; linarith
      linarith
    have hZ' : (Z : ℝ) ≤ a * phi N ^ 2 := hZa
    have hexpo : Real.log 8 + ((6 * Z : ℕ) + C' + ζ) * Real.log N ≤ c * phi N ^ 3 := by
      have hφ2 : 1 ≤ phi N ^ 2 := one_le_pow₀ hφ1
      have hlog0 : 0 ≤ Real.log N := by linarith
      have h1 : (3 + (6 * Z : ℕ) + C' + ζ) ≤ (6 * a + 4 + C') * phi N ^ 2 := by
        push_cast; nlinarith
      calc Real.log 8 + ((6 * Z : ℕ) + C' + ζ) * Real.log N ≤
            (3 + (6 * Z : ℕ) + C' + ζ) * Real.log N := by nlinarith
        _ ≤ (6 * a + 4 + C') * phi N ^ 2 * Real.log N := by gcongr
        _ = phi N ^ 2 * ((6 * a + 4 + C') * Real.log N) := by ring
        _ ≤ phi N ^ 2 * (c * phi N) := by gcongr
        _ = c * phi N ^ 3 := by ring
    have key : ∀ x : ℝ, (N : ℝ) ^ x = Real.exp (x * Real.log N) := fun x => by
      rw [Real.rpow_def_of_pos hN0, mul_comm]
    calc 8 * (N : ℝ) ^ (6 * Z) * (N : ℝ) ^ C' * (N : ℝ) ^ ζ =
          Real.exp (Real.log 8 + ((6 * Z : ℕ) + C' + ζ) * Real.log N) := by
          rw [← Real.rpow_natCast, key, key, key, Real.exp_add, add_mul, add_mul, Real.exp_add,
            Real.exp_add, Real.exp_log (by norm_num)]
          ring
      _ ≤ _ := Real.exp_le_exp.2 hexpo
  have hNζ : 0 < (N : ℝ) ^ ζ := Real.rpow_pos_of_pos hN0 _
  have hE : 0 < Real.exp (c * phi N ^ 3) := Real.exp_pos _
  calc _ = (1 + ((ξ : ℝ) + 1) * ((s : ℝ) + 1) ^ ξ) *
        ((1 + ((ξ : ℝ) + 1) * ((s : ℝ) * ξ + 1) ^ ξ) * 2 ^ ξ * ((N : ℝ) + 1) ^ (s + ξ)) * P := by
        ring
    _ ≤ 4 * (N : ℝ) ^ (6 * Z) * ((N : ℝ) ^ C' * Real.exp (-c * phi N ^ 3)) :=
        mul_le_mul hpoly hP hP0 (by positivity)
    _ = 8 * (N : ℝ) ^ (6 * Z) * (N : ℝ) ^ C' * (N : ℝ) ^ ζ *
        (1 / 2 * (N : ℝ) ^ (-ζ) * (Real.exp (c * phi N ^ 3))⁻¹) := by
        rw [Real.rpow_neg hN0.le, neg_mul, Real.exp_neg]
        field_simp
        norm_num
    _ ≤ Real.exp (c * phi N ^ 3) * (1 / 2 * (N : ℝ) ^ (-ζ) * (Real.exp (c * phi N ^ 3))⁻¹) := by
        gcongr
    _ = _ := by field_simp

/-- The exponent bookkeeping of (6.22): if `β ≤ x N^{-r}`, `(ξ + 1)² x Λ ≤ N^{φq/12}`,
`q ≥ N^{φq}` and `K/12 - (K - m) ≤ -K/d`, then `(ξ + 1)² β q^m (Λ/q)^K ≤ N^{-r - K φq/d}`. -/
private lemma expansion_coeff_le {N ξ K m : ℕ} {β x Λ q φq r d : ℝ} (hN : 1 ≤ (N : ℝ))
    (hmK : m ≤ K) (hK1 : 1 ≤ K) (hβ : β ≤ x * (N : ℝ) ^ (-r))
    (hx : 1 ≤ ((ξ : ℝ) + 1) ^ 2 * x) (hΛ : 1 ≤ Λ)
    (hP : ((ξ : ℝ) + 1) ^ 2 * x * Λ ≤ (N : ℝ) ^ (φq / 12)) (hq : 0 < q)
    (hqN : (N : ℝ) ^ φq ≤ q) (hφq : 0 < φq) (hexp : (K : ℝ) / 12 - ((K : ℝ) - m) ≤ -(K : ℝ) / d) :
    ((ξ : ℝ) + 1) ^ 2 * (β * q ^ m) * (Λ * q⁻¹) ^ K ≤ (N : ℝ) ^ (-r - (K : ℝ) * φq / d) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hqi0 : 0 ≤ q⁻¹ := inv_nonneg.2 hq.le
  have hqi : q⁻¹ ≤ (N : ℝ) ^ (-φq) := by
    rw [Real.rpow_neg hN0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hN0 _) hqN
  have hsplit : q ^ m * (q⁻¹) ^ K = (q⁻¹) ^ (K - m) := by
    rw [show K = m + (K - m) by omega, pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hq.ne',
      one_pow, one_mul, Nat.add_sub_cancel_left]
  have h1 : ((ξ : ℝ) + 1) ^ 2 * x * Λ ^ K ≤ (N : ℝ) ^ (φq / 12 * K) := by
    have hx0 : 0 ≤ ((ξ : ℝ) + 1) ^ 2 * x := by linarith
    calc ((ξ : ℝ) + 1) ^ 2 * x * Λ ^ K ≤ (((ξ : ℝ) + 1) ^ 2 * x) ^ K * Λ ^ K := by
          gcongr
          calc ((ξ : ℝ) + 1) ^ 2 * x = (((ξ : ℝ) + 1) ^ 2 * x) ^ 1 := (pow_one _).symm
            _ ≤ _ := pow_le_pow_right₀ hx hK1
      _ = (((ξ : ℝ) + 1) ^ 2 * x * Λ) ^ K := by rw [mul_pow (((ξ : ℝ) + 1) ^ 2 * x)]
      _ ≤ ((N : ℝ) ^ (φq / 12)) ^ K := pow_le_pow_left₀ (by positivity) hP K
      _ = _ := expansion_rpow_pow hN0.le _ _
  have h2 : (q⁻¹) ^ (K - m) ≤ (N : ℝ) ^ (-φq * ((K : ℝ) - m)) := by
    calc (q⁻¹) ^ (K - m) ≤ ((N : ℝ) ^ (-φq)) ^ (K - m) := pow_le_pow_left₀ hqi0 hqi _
      _ = _ := by rw [expansion_rpow_pow hN0.le]; push_cast [hmK]; ring_nf
  calc ((ξ : ℝ) + 1) ^ 2 * (β * q ^ m) * (Λ * q⁻¹) ^ K =
        ((ξ : ℝ) + 1) ^ 2 * β * Λ ^ K * (q ^ m * (q⁻¹) ^ K) := by rw [mul_pow]; ring
    _ = ((ξ : ℝ) + 1) ^ 2 * β * Λ ^ K * (q⁻¹) ^ (K - m) := by rw [hsplit]
    _ ≤ ((ξ : ℝ) + 1) ^ 2 * (x * (N : ℝ) ^ (-r)) * Λ ^ K * (q⁻¹) ^ (K - m) := by gcongr
    _ = (N : ℝ) ^ (-r) * (((ξ : ℝ) + 1) ^ 2 * x * Λ ^ K) * (q⁻¹) ^ (K - m) := by ring
    _ ≤ (N : ℝ) ^ (-r) * (N : ℝ) ^ (φq / 12 * K) * (N : ℝ) ^ (-φq * ((K : ℝ) - m)) := by gcongr
    _ = (N : ℝ) ^ (-r + φq / 12 * K + -φq * ((K : ℝ) - m)) := by
        rw [Real.rpow_add hN0, Real.rpow_add hN0]
    _ ≤ _ := by
        refine Real.rpow_le_rpow_of_exponent_le hN ?_
        have := mul_le_mul_of_nonneg_left hexp hφq.le
        have e1 : φq * ((K : ℝ) / 12 - ((K : ℝ) - m)) = φq / 12 * K + -φq * ((K : ℝ) - m) := by ring
        have e2 : φq * (-(K : ℝ) / d) = -((K : ℝ) * φq / d) := by ring
        linarith

private lemma expansion_card_highIdx_le (s m0 ξ : ℕ) :
    ((highIdx s m0 ξ).card : ℝ) ≤ ((ξ : ℝ) + 1) * ((s : ℝ) + 1) ^ ξ := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, expansion_sum_highIdx]
  have hlev : ∀ k ∈ Finset.Icc (m0 + 1) ξ,
      ∑ κ ∈ Finset.Nat.antidiagonalTuple s k, ((1 : ℕ) : ℝ) ≤ ((s : ℝ) + 1) ^ ξ := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_one, mul_one]
    calc ((Finset.Nat.antidiagonalTuple s k).card : ℝ) ≤ (s : ℝ) ^ k := by
          exact_mod_cast card_antidiagonalTuple_le s k
      _ ≤ ((s : ℝ) + 1) ^ k := by gcongr; linarith
      _ ≤ _ := pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) s]) hk.2
  refine (Finset.sum_le_sum hlev).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
  have : ((ξ + 1 - (m0 + 1) : ℕ) : ℝ) ≤ (ξ : ℝ) + 1 := by
    have : ξ + 1 - (m0 + 1) ≤ ξ + 1 := Nat.sub_le _ _
    exact_mod_cast this
  gcongr

/-- `|E(-h)^k| ≤ (q⁻¹)^{k-m} E h^m` for an even `m ≤ k`, on the support `|h| ≤ q⁻¹`. -/
private lemma expansion_abs_moment_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {q : ℝ}
    (h : μ {x | q⁻¹ < |x|} = 0) (m k : ℕ) (hm : Even m) (hk : m ≤ k) :
    |∫ x, (-x) ^ k ∂μ| ≤ q⁻¹ ^ (k - m) * ∫ x, x ^ m ∂μ := by
  have h1 : ∀ᵐ x ∂μ, ¬ (q⁻¹ < |x|) := by
    rw [ae_iff]; simpa using h
  have hint : ∀ j : ℕ, Integrable (fun x : ℝ => x ^ j) μ := by
    intro j
    refine Integrable.of_bound (continuous_pow j).aestronglyMeasurable (|q⁻¹| ^ j) ?_
    filter_upwards [h1] with x hx
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg x) ((not_lt.mp hx).trans (le_abs_self _)) j
  rw [← integral_const_mul, ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_ae ?_ ((hint m).const_mul _) ?_
  · simpa [norm_neg] using (hint k).norm
  · filter_upwards [h1] with x hx
    have hx' : |x| ≤ q⁻¹ := not_lt.mp hx
    have e : ‖(-x) ^ k‖ = |x| ^ (k - m) * |x| ^ m := by
      rw [norm_pow, norm_neg, Real.norm_eq_abs, ← pow_add, Nat.sub_add_cancel hk]
    change ‖(-x) ^ k‖ ≤ q⁻¹ ^ (k - m) * x ^ m
    rw [e, ← hm.pow_abs x]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg x) hx' _) (by positivity)

/-- The moments `n_k = E(-h_e)^k` of a matched pair: `n_0 = 1`, `n_1 = 0`, and
`|n_k| ≤ max(C1, 1) N⁻¹ q^{-(k-2)}` for `k ≥ 2`. -/
private lemma expansion_moments {N : ℕ} {C1 q : ℝ} {Lv Lw : EntryLaws N}
    (h : MatchedPair C1 q Lv Lw) (hq : 0 < q) (e : Fin N ⊕ OffDiag N) :
    Lv.entryMoment e 0 = 1 ∧ Lv.entryMoment e 1 = 0 ∧
      ∀ k, 2 ≤ k → |Lv.entryMoment e k| ≤ max C1 1 / N * q⁻¹ ^ (k - 2) := by
  have hv := h.isProb_v.diag
  have hv' := h.isProb_v.off
  refine ⟨?_, ?_, fun k hk => ?_⟩
  · rcases e with i | p <;> simp [EntryLaws.entryMoment, EntryLaws.entry]
  · rcases e with i | p
    · simp only [EntryLaws.entryMoment, EntryLaws.entry, Sum.elim_inl, pow_one]
      rw [integral_neg, h.mean_diag i, neg_zero]
    · simp only [EntryLaws.entryMoment, EntryLaws.entry, Sum.elim_inr, pow_one]
      rw [integral_neg, h.mean_off p, neg_zero]
  · have hq' : 0 ≤ q⁻¹ ^ (k - 2) := pow_nonneg (inv_nonneg.2 hq.le) _
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    rcases e with i | p
    · simp only [EntryLaws.entryMoment, EntryLaws.entry, Sum.elim_inl]
      refine (expansion_abs_moment_le (h.supp_v.1 i) 2 k (by decide) hk).trans ?_
      rw [mul_comm]
      refine mul_le_mul_of_nonneg_right ((h.var_diag_le i).trans ?_) hq'
      exact div_le_div_of_nonneg_right (le_max_left _ _) hN
    · simp only [EntryLaws.entryMoment, EntryLaws.entry, Sum.elim_inr]
      refine (expansion_abs_moment_le (h.supp_v.2 p) 2 k (by decide) hk).trans ?_
      rw [mul_comm, h.var_off p, ← one_div]
      refine mul_le_mul_of_nonneg_right ?_ hq'
      exact div_le_div_of_nonneg_right (le_max_right _ _) hN

private lemma expansion_eventually_le_phi (A : ℝ) : ∀ᶠ N : ℕ in atTop, A ≤ phi N := by
  filter_upwards [eventually_ge_atTop 16,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop A] with N h16 hA
  exact hA.trans (log_le_phi h16)

/-- `φ / log N → ∞`: eventually `D log N ≤ φ`. -/
private lemma expansion_eventually_log_le (D : ℝ) :
    ∀ᶠ N : ℕ in atTop, D * Real.log N ≤ phi N := by
  set D' := max D 1
  have hD' : 1 ≤ D' := le_max_right _ _
  have hlogD : 0 ≤ Real.log D' := Real.log_nonneg hD'
  filter_upwards [eventually_ge_atTop 3, (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
    tendsto_natCast_atTop_atTop)).eventually_ge_atTop (Real.log D' + 1)] with N h3 hu
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast h3
  have hlogpos : 0 < Real.log N := Real.log_pos (by linarith)
  simp only [Function.comp] at hu
  set u := Real.log (Real.log N)
  have hlogN : Real.log N = Real.exp u := (Real.exp_log hlogpos).symm
  rw [phi_eq_exp h3]
  calc D * Real.log N ≤ D' * Real.log N := mul_le_mul_of_nonneg_right (le_max_left _ _) hlogpos.le
    _ = Real.exp (Real.log D' + u) := by
        rw [Real.exp_add, Real.exp_log (by linarith), ← hlogN]
    _ ≤ Real.exp (u ^ 2) := Real.exp_le_exp.2 (by nlinarith)

/-- The polynomial-in-`φ` quantities of the proof of (6.21) are below the powers of `N` they are
compared with, once `64 M² a⁴ φ⁹ ≤ N^{φq/12}` and `s + ξ + 1 ≤ a φ²`. -/
private lemma expansion_poly {N s ξ : ℕ} {M a φq q : ℝ} (hN1 : 1 ≤ (N : ℝ)) (hM1 : 1 ≤ M)
    (ha1 : 1 ≤ a) (hφ1 : 1 ≤ phi N) (hlogφ : Real.log N ≤ phi N)
    (hφq : 0 < φq) (hφq2 : 2 * φq ≤ 1) (hqN : (N : ℝ) ^ φq ≤ q)
    (hZa : (s : ℝ) + ξ + 1 ≤ a * phi N ^ 2)
    (hT : 64 * M ^ 2 * a ^ 4 * phi N ^ 9 ≤ (N : ℝ) ^ (φq / 12)) :
    ((ξ : ℝ) + 1) ^ 2 * (M * Real.log N) * (2 * M * ((s : ℝ) + 1) * ((ξ : ℝ) + 1)) ≤
        (N : ℝ) ^ (φq / 12) ∧
      8 * ((s : ℝ) + 1) * (2 * M * ((s : ℝ) + 1) * ((ξ : ℝ) + 1)) + 4 * ((s : ℝ) + ξ) ≤
        (N : ℝ) ^ (φq / 2) ∧
      32 * (1 + ((ξ : ℝ) + 1) ^ 3 * (M * Real.log N)) ≤ (N : ℝ) ^ (φq / 2) ∧
      8 * ((s + ξ : ℕ) : ℝ) ≤ q ∧ ((s + ξ + 1 : ℕ) : ℝ) ≤ N := by
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hξ0 : (0 : ℝ) ≤ ξ := Nat.cast_nonneg _
  have hs1 : (s : ℝ) + 1 ≤ a * phi N ^ 2 := by linarith
  have hξ1 : (ξ : ℝ) + 1 ≤ a * phi N ^ 2 := by linarith
  have hsξ : (s : ℝ) + ξ ≤ a * phi N ^ 2 := by linarith
  have hT2 : (N : ℝ) ^ (φq / 12) ≤ (N : ℝ) ^ (φq / 2) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hT3 : (N : ℝ) ^ (φq / 2) ≤ q :=
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)).trans hqN
  have hTN : (N : ℝ) ^ (φq / 12) ≤ N := by
    calc (N : ℝ) ^ (φq / 12) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = N := Real.rpow_one _
  have hMa : (1 : ℝ) ≤ M ^ 2 * a ^ 4 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM1)
    (one_le_pow₀ ha1)
  have hφ9 : phi N ^ 2 ≤ phi N ^ 9 := pow_le_pow_right₀ hφ1 (by norm_num)
  have hφ6 : phi N ^ 6 ≤ phi N ^ 9 := pow_le_pow_right₀ hφ1 (by norm_num)
  have hφ7 : phi N ^ 7 ≤ phi N ^ 9 := pow_le_pow_right₀ hφ1 (by norm_num)
  have hφ90 : 1 ≤ phi N ^ 9 := one_le_pow₀ hφ1
  have hφ0 : 0 ≤ phi N := by linarith
  have ha4 : a ≤ M ^ 2 * a ^ 4 := by
    have h1 : a ≤ a ^ 4 := by
      calc a = a ^ 1 := (pow_one a).symm
        _ ≤ a ^ 4 := pow_le_pow_right₀ ha1 (by norm_num)
    have h2 : a ^ 4 ≤ M ^ 2 * a ^ 4 := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hM1)
    linarith
  have hMa3 : M * a ^ 3 ≤ M ^ 2 * a ^ 4 := by
    have h1 : M ≤ M ^ 2 := by
      calc M = M ^ 1 := (pow_one M).symm
        _ ≤ M ^ 2 := pow_le_pow_right₀ hM1 (by norm_num)
    have h2 : a ^ 3 ≤ a ^ 4 := pow_le_pow_right₀ ha1 (by norm_num)
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  set Q : ℝ := M ^ 2 * a ^ 4 * phi N ^ 9 with hQdef
  have hQ : 64 * Q ≤ (N : ℝ) ^ (φq / 12) := by
    rw [hQdef, ← mul_assoc, ← mul_assoc]; exact hT
  have hQ1 : 1 ≤ Q := one_le_mul_of_one_le_of_one_le hMa hφ90
  have haQ : a * phi N ^ 2 ≤ Q := mul_le_mul ha4 hφ9 (by positivity) (by positivity)
  have hMaQ6 : M * a ^ 3 * phi N ^ 6 ≤ Q := mul_le_mul hMa3 hφ6 (by positivity) (by positivity)
  have hMaQ7 : M * a ^ 3 * phi N ^ 7 ≤ Q := mul_le_mul hMa3 hφ7 (by positivity) (by positivity)
  have hΛle : 2 * M * ((s : ℝ) + 1) * ((ξ : ℝ) + 1) ≤ 2 * M * a ^ 2 * phi N ^ 4 := by
    calc 2 * M * ((s : ℝ) + 1) * ((ξ : ℝ) + 1) ≤ 2 * M * (a * phi N ^ 2) * (a * phi N ^ 2) := by
          gcongr
      _ = _ := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc ((ξ : ℝ) + 1) ^ 2 * (M * Real.log N) * (2 * M * ((s : ℝ) + 1) * ((ξ : ℝ) + 1)) ≤
          (a * phi N ^ 2) ^ 2 * (M * phi N) * (2 * M * a ^ 2 * phi N ^ 4) := by gcongr
      _ = 2 * Q := by rw [hQdef]; ring
      _ ≤ 64 * Q := by linarith
      _ ≤ _ := hQ
  · refine le_trans ?_ (hQ.trans hT2)
    calc 8 * ((s : ℝ) + 1) * (2 * M * ((s : ℝ) + 1) * ((ξ : ℝ) + 1)) + 4 * ((s : ℝ) + ξ) ≤
          8 * (a * phi N ^ 2) * (2 * M * a ^ 2 * phi N ^ 4) + 4 * (a * phi N ^ 2) := by gcongr
      _ = 16 * (M * a ^ 3 * phi N ^ 6) + 4 * (a * phi N ^ 2) := by ring
      _ ≤ 64 * Q := by linarith
  · refine le_trans ?_ (hQ.trans hT2)
    calc 32 * (1 + ((ξ : ℝ) + 1) ^ 3 * (M * Real.log N)) ≤
          32 * (1 + (a * phi N ^ 2) ^ 3 * (M * phi N)) := by gcongr
      _ = 32 + 32 * (M * a ^ 3 * phi N ^ 7) := by ring
      _ ≤ 64 * Q := by linarith
  · push_cast
    refine le_trans ?_ ((hQ.trans hT2).trans hT3)
    calc 8 * ((s : ℝ) + ξ) ≤ 8 * (a * phi N ^ 2) := by gcongr
      _ ≤ 64 * Q := by linarith
  · push_cast
    refine le_trans ?_ (hQ.trans hTN)
    calc (s : ℝ) + ξ + 1 ≤ a * phi N ^ 2 := hZa
      _ ≤ 64 * Q := by linarith

/-- (6.22) for the interpolations of a matched pair: the coefficients `A_α` are bounded by
`coeffBound`, and by `(ξ + 1)² M log N (Λ/q)^{|α|}` with `Λ = 2 M (s + 1)(ξ + 1)`,
`M = max(C1, 1)`. -/
private lemma expansion_coeffs {N : ℕ} {C1 q φq : ℝ} {Lv Lw : EntryLaws N}
    (hmp : MatchedPair C1 q Lv Lw) (γ : ℕ) (hq0 : 0 < q) (hqsq : q ^ 2 ≤ N)
    (hqN : (N : ℝ) ^ φq ≤ q) (hφq : 0 < φq) (hN1 : 1 ≤ (N : ℝ)) (hlog1 : 1 ≤ Real.log N)
    (hC1 : 0 ≤ C1) (e : Fin N ⊕ OffDiag N) (s ξ : ℕ)
    (hP0 : ((ξ : ℝ) + 1) ^ 2 * (max C1 1 * Real.log N) *
      (2 * max C1 1 * ((s : ℝ) + 1) * ((ξ : ℝ) + 1)) ≤ (N : ℝ) ^ (φq / 12)) (α : Fin s → ℕ) :
    |expA s ξ (matchedOrder e) ((interp (lexPos N) γ Lv Lw).entryMoment e) α| ≤
        coeffBound N φq e (∑ t, α t) ∧
      |expA s ξ (matchedOrder e) ((interp (lexPos N) γ Lv Lw).entryMoment e) α| ≤
        ((ξ : ℝ) + 1) ^ 2 * (max C1 1 * Real.log N) *
          ((2 * max C1 1 * ((s : ℝ) + 1) * ((ξ : ℝ) + 1)) * q⁻¹) ^ (∑ t, α t) := by
  set M := max C1 1 with hMdef
  have hM1 : 1 ≤ M := le_max_right _ _
  have hN0r : (0 : ℝ) < N := by linarith
  have hqi0 : 0 ≤ q⁻¹ := inv_nonneg.2 hq0.le
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hξ0 : (0 : ℝ) ≤ ξ := Nat.cast_nonneg _
  have hmpL := hmp.interp γ
  obtain ⟨_, hn1, hnk⟩ := expansion_moments hmpL hq0 e
  set n := (interp (lexPos N) γ Lv Lw).entryMoment e with hndef
  have hNinv : (N : ℝ)⁻¹ ≤ q⁻¹ ^ 2 := by
    rw [inv_pow]; exact inv_anti₀ (by positivity) hqsq
  have hnM : ∀ k, 1 ≤ k → |n k| ≤ M * q⁻¹ ^ k := by
    intro k hk
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · obtain rfl : k = 1 := by omega
      rw [hn1, abs_zero]; positivity
    · refine (hnk k hk2).trans ?_
      calc M / N * q⁻¹ ^ (k - 2) = M * (N : ℝ)⁻¹ * q⁻¹ ^ (k - 2) := by ring
        _ ≤ M * q⁻¹ ^ 2 * q⁻¹ ^ (k - 2) := by gcongr
        _ = M * q⁻¹ ^ k := by rw [mul_assoc, ← pow_add]; congr 2; omega
  set Λ : ℝ := 2 * M * ((s : ℝ) + 1) * ((ξ : ℝ) + 1) with hΛdef
  have hΛ1 : 1 ≤ Λ := by
    have h1 : (1 : ℝ) ≤ ((s : ℝ) + 1) * ((ξ : ℝ) + 1) :=
      one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
    have h2 : (1 : ℝ) ≤ 2 * M := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ 2 * M * (((s : ℝ) + 1) * ((ξ : ℝ) + 1)) := mul_le_mul h2 h1 (by norm_num) (by linarith)
      _ = Λ := by rw [hΛdef]; ring
  have hnθ : ∀ c : ℕ, |n (c + 1)| * ((s : ℝ) * ξ) ^ (c + 1) ≤ (Λ * q⁻¹ / 2) ^ (c + 1) := by
    intro c
    have h1 := hnM (c + 1) (by omega)
    have hsξ' : (s : ℝ) * ξ * q⁻¹ ≤ ((s : ℝ) + 1) * ((ξ : ℝ) + 1) * q⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul (by linarith) (by linarith) hξ0 (by linarith)) hqi0
    calc |n (c + 1)| * ((s : ℝ) * ξ) ^ (c + 1) ≤ M * q⁻¹ ^ (c + 1) * ((s : ℝ) * ξ) ^ (c + 1) := by
          gcongr
      _ = M * ((s : ℝ) * ξ * q⁻¹) ^ (c + 1) := by ring
      _ ≤ M ^ (c + 1) * (((s : ℝ) + 1) * ((ξ : ℝ) + 1) * q⁻¹) ^ (c + 1) := by
          gcongr
          calc M = M ^ 1 := (pow_one M).symm
            _ ≤ M ^ (c + 1) := pow_le_pow_right₀ hM1 (by omega)
      _ = (Λ * q⁻¹ / 2) ^ (c + 1) := by rw [hΛdef, ← mul_pow]; ring_nf
  have hsρ : (s : ℝ) * q⁻¹ ≤ Λ * q⁻¹ := by
    refine mul_le_mul_of_nonneg_right ?_ hqi0
    calc (s : ℝ) = 1 * ((s : ℝ) + 0) * 1 := by ring
      _ ≤ 2 * M * ((s : ℝ) + 1) * ((ξ : ℝ) + 1) := by gcongr <;> linarith
      _ = Λ := by rw [hΛdef]
  have hθ0 : 0 ≤ Λ * q⁻¹ := by positivity
  have key : ∃ β : ℝ, 0 ≤ β ∧ (∀ k, matchedOrder e < k → |n k| ≤ β * q⁻¹ ^ k) ∧
      β ≤ M * Real.log N ∧ ∀ K : ℕ, matchedOrder e < K →
        ((ξ : ℝ) + 1) ^ 2 * β * (Λ * q⁻¹) ^ K ≤ coeffBound N φq e K := by
    rcases e with i | p
    · refine ⟨C1 / N * q ^ 2, by positivity, fun k hk => ?_, ?_, fun K hK => ?_⟩
      · simp only [matchedOrder] at hk
        have h := hmp.abs_entryMoment_diag_le hq0 γ i k (by omega)
        refine h.trans_eq ?_
        rw [mul_assoc, show q⁻¹ ^ (k - 2) = q ^ 2 * q⁻¹ ^ k by
          rw [show k = 2 + (k - 2) by omega, pow_add, ← mul_assoc,
            ← mul_pow, mul_inv_cancel₀ hq0.ne', one_pow, one_mul, Nat.add_sub_cancel_left]]
      · calc C1 / N * q ^ 2 ≤ M / N * N := by gcongr; exact le_max_left _ _
          _ = M := by field_simp
          _ ≤ M * Real.log N := le_mul_of_one_le_right (by linarith) hlog1
      · simp only [matchedOrder] at hK
        simp only [coeffBound]
        have hx : 1 ≤ ((ξ : ℝ) + 1) ^ 2 * M :=
          one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) hM1
        have hP' : ((ξ : ℝ) + 1) ^ 2 * M * Λ ≤ (N : ℝ) ^ (φq / 12) := by
          refine le_trans ?_ hP0
          have : M ≤ M * Real.log N := le_mul_of_one_le_right (by linarith) hlog1
          gcongr
        have hβ : C1 / N ≤ M * (N : ℝ) ^ (-(1 : ℝ)) := by
          rw [Real.rpow_neg_one, div_eq_mul_inv]; gcongr; exact le_max_left _ _
        have hexp : (K : ℝ) / 12 - ((K : ℝ) - ((2 : ℕ) : ℝ)) ≤ -(K : ℝ) / 4 := by
          have : (3 : ℝ) ≤ K := by exact_mod_cast hK
          push_cast
          linarith
        have := expansion_coeff_le (ξ := ξ) (K := K) (m := 2) (β := C1 / N) (x := M) (Λ := Λ)
          (q := q) (φq := φq) (r := 1) (d := 4) hN1 (by omega) (by omega) hβ hx hΛ1 hP' hq0 hqN
          hφq hexp
        exact this
    · refine ⟨C1 * Real.log N / N ^ 2 * q ^ 4, by positivity, fun k hk => ?_, ?_, fun K hK => ?_⟩
      · simp only [matchedOrder] at hk
        have h := hmp.abs_entryMoment_off_le hq0 γ p k (by omega)
        refine h.trans_eq ?_
        rw [mul_assoc, show q⁻¹ ^ (k - 4) = q ^ 4 * q⁻¹ ^ k by
          rw [show k = 4 + (k - 4) by omega, pow_add, ← mul_assoc,
            ← mul_pow, mul_inv_cancel₀ hq0.ne', one_pow, one_mul, Nat.add_sub_cancel_left]]
      · have hq4 : q ^ 4 ≤ (N : ℝ) ^ 2 := by
          calc q ^ 4 = (q ^ 2) ^ 2 := by ring
            _ ≤ (N : ℝ) ^ 2 := by gcongr
        calc C1 * Real.log N / N ^ 2 * q ^ 4 ≤ M * Real.log N / N ^ 2 * N ^ 2 := by
              gcongr
              exact le_max_left _ _
          _ = M * Real.log N := by field_simp
      · simp only [matchedOrder] at hK
        simp only [coeffBound]
        have hx : 1 ≤ ((ξ : ℝ) + 1) ^ 2 * (M * Real.log N) :=
          one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith))
            (one_le_mul_of_one_le_of_one_le hM1 hlog1)
        have hβ : C1 * Real.log N / N ^ 2 ≤ M * Real.log N * (N : ℝ) ^ (-(2 : ℝ)) := by
          rw [Real.rpow_neg hN0r.le, Real.rpow_two, div_eq_mul_inv]
          gcongr
          exact le_max_left _ _
        have hexp : (K : ℝ) / 12 - ((K : ℝ) - ((4 : ℕ) : ℝ)) ≤ -(K : ℝ) / 10 := by
          have : (5 : ℝ) ≤ K := by exact_mod_cast hK
          push_cast
          linarith
        have := expansion_coeff_le (ξ := ξ) (K := K) (m := 4) (β := C1 * Real.log N / N ^ 2)
          (x := M * Real.log N) (Λ := Λ) (q := q) (φq := φq) (r := 2) (d := 10) hN1 (by omega)
          (by omega) hβ hx hΛ1 hP0 hq0 hqN hφq hexp
        exact this
  obtain ⟨β, hβ0, hlead, hβM, hcoef⟩ := key
  have hAθ := expA_bound s ξ (matchedOrder e) n hθ0 hβ0 hqi0 hsρ hnθ hlead α
  refine ⟨?_, hAθ.trans (by gcongr)⟩
  by_cases hα : α ∈ highIdx s (matchedOrder e) ξ
  · exact hAθ.trans (hcoef _ ((expansion_mem_highIdx α).1 hα).1)
  · simp only [expA, hα, ↓reduceIte, abs_zero]
    rcases e with i | p <;> simp only [coeffBound] <;> positivity

/-- Assembly of the remainder of (6.21): `err 0 - Σ_α A_α err α` is at most `4^s N^{-ζ}` when the
good-event and the bad-event parts are each at most half of it. -/
private lemma expansion_final {N s ξ m0 : ℕ} (A : (Fin s → ℕ) → ℝ) (err : (Fin s → ℕ) → ℂ)
    {q Λ β W P ζ : ℝ} (hq0 : 0 < q) (hΛ : 0 ≤ Λ) (hβ : 0 ≤ β) (hW : 0 ≤ W) (hP : 0 ≤ P)
    (herr0 : ‖err 0‖ ≤ 4 ^ (s + 2) * (4 * (s : ℝ) / q) ^ (ξ + 1) + W * P)
    (herr : ∀ α ∈ highIdx s m0 ξ, ‖err α‖ ≤ 2 ^ (∑ t, α t) * 4 ^ (s + ∑ t, α t + 2) *
      (4 * ((s + ∑ t, α t : ℕ) : ℝ) / q) ^ (ξ - ∑ t, α t + 1) + W * P)
    (hAθ : ∀ α, |A α| ≤ ((ξ : ℝ) + 1) ^ 2 * β * (Λ * q⁻¹) ^ (∑ t, α t))
    (hA1 : ∀ α, |A α| ≤ 1)
    (hG : 16 * 4 ^ s * (1 + ((ξ : ℝ) + 1) ^ 3 * β) *
      ((8 * ((s : ℝ) + 1) * Λ + 4 * ((s : ℝ) + ξ)) * q⁻¹) ^ (ξ + 1) ≤
        1 / 2 * (4 ^ s * (N : ℝ) ^ (-ζ)))
    (hB : (1 + ((ξ : ℝ) + 1) * ((s : ℝ) + 1) ^ ξ) * (W * P) ≤ 1 / 2 * (N : ℝ) ^ (-ζ)) :
    ‖err 0 - ∑ α ∈ highIdx s m0 ξ, (A α : ℂ) * err α‖ ≤ 4 ^ s * (N : ℝ) ^ (-ζ) := by
  have hgood := expansion_good_sum_le s m0 ξ hq0 hΛ hβ A hAθ
  have hcard := expansion_card_highIdx_le s m0 ξ
  calc _ ≤ ‖err 0‖ + ∑ α ∈ highIdx s m0 ξ, |A α| * ‖err α‖ := by
        refine (norm_sub_le _ _).trans (add_le_add le_rfl ((norm_sum_le _ _).trans_eq ?_))
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (4 ^ (s + 2) * (4 * (s : ℝ) / q) ^ (ξ + 1) + W * P) +
        ∑ α ∈ highIdx s m0 ξ, |A α| *
          (2 ^ (∑ t, α t) * 4 ^ (s + ∑ t, α t + 2) *
            (4 * ((s + ∑ t, α t : ℕ) : ℝ) / q) ^ (ξ - ∑ t, α t + 1) + W * P) := by
        refine add_le_add herr0 (Finset.sum_le_sum fun α hα => ?_)
        exact mul_le_mul_of_nonneg_left (herr α hα) (abs_nonneg _)
    _ = (4 ^ (s + 2) * (4 * (s : ℝ) / q) ^ (ξ + 1) +
          ∑ α ∈ highIdx s m0 ξ, |A α| *
            (2 ^ (∑ t, α t) * 4 ^ (s + ∑ t, α t + 2) *
              (4 * ((s + ∑ t, α t : ℕ) : ℝ) / q) ^ (ξ - ∑ t, α t + 1))) +
        (1 + ∑ α ∈ highIdx s m0 ξ, |A α|) * (W * P) := by
        rw [add_mul, one_mul, Finset.sum_mul]
        simp only [mul_add, Finset.sum_add_distrib]
        ring
    _ ≤ 16 * 4 ^ s * (1 + ((ξ : ℝ) + 1) ^ 3 * β) *
          ((8 * ((s : ℝ) + 1) * Λ + 4 * ((s : ℝ) + ξ)) * q⁻¹) ^ (ξ + 1) +
        (1 + ((ξ : ℝ) + 1) * ((s : ℝ) + 1) ^ ξ) * (W * P) := by
        refine add_le_add hgood (mul_le_mul_of_nonneg_right ?_ (mul_nonneg hW hP))
        refine add_le_add le_rfl ((Finset.sum_le_sum fun α _ => hA1 α).trans ?_)
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact hcard
    _ ≤ 1 / 2 * (4 ^ s * (N : ℝ) ^ (-ζ)) + 1 / 2 * (N : ℝ) ^ (-ζ) := add_le_add hG hB
    _ ≤ 4 ^ s * (N : ℝ) ^ (-ζ) := by
        have h4 : (1 : ℝ) ≤ 4 ^ s := one_le_pow₀ (by norm_num)
        have h5 : 0 ≤ (N : ℝ) ^ (-ζ) := by positivity
        nlinarith

/-- Lemma 6.5, (6.21)–(6.23) in one statement (centred letters are words of kind
`gc`/`gcbar`): for `1 ≤ ζ ≤ φ²`, `s ≤ K_s φ²`, `ξ = ⌈2ζ/φq⌉`, the expectation of a word of length
`s` in `S` is the sum of the `k ≤ matchedOrder e` terms `n_k E A_k(R)`, plus `A_α E P_{γ,α}(word)`
for `matchedOrder e < |α| ≤ ξ`, up to `4^s N^{-ζ}`; `A` does not depend on the word or on `z`. -/
theorem expectation_expansion {C1 φq Ks : ℝ} (hφq : 0 < φq) (hKs : 0 < Ks) :
    ∃ C0 > (0 : ℝ), ∃ N0 : ℕ, ∀ N ≥ N0, ∀ L : EntryLaws N, PairInterpClass C1 φq N L →
      ∀ (e : Fin N ⊕ OffDiag N) (ζ : ℝ), 1 ≤ ζ → ζ ≤ phi N ^ 2 →
      ∀ s : ℕ, (s : ℝ) ≤ Ks * phi N ^ 2 →
      ∃ A : (Fin s → ℕ) → ℝ, (∀ α, |A α| ≤ coeffBound N φq e (∑ t, α t)) ∧
        ∀ z ∈ specDomain N C0, ∀ w : Word N, w.length = s →
          ‖(∫ ω, evalWord (resS z ω) (msc z) w ∂L.law)
            - (∑ k ∈ Finset.range (matchedOrder e + 1), (L.entryMoment e k : ℂ) *
                ∑ κ ∈ Finset.Nat.antidiagonalTuple s k,
                  ∫ ω, evalW (resR e z ω) (msc z) (wordP e (List.ofFn κ) w) ∂L.law)
            - ∑ α ∈ highIdx s (matchedOrder e) (xiOf ζ φq),
                (A α : ℂ) * ∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) w) ∂L.law‖
            ≤ 4 ^ s * (N : ℝ) ^ (-ζ) := by
  obtain ⟨C0, hC0, c, hc, C', hC', N1, hN1⟩ := highProb_goodEvent (C1 := C1) hφq
  set M : ℝ := max C1 1 with hMdef
  set a : ℝ := Ks + 2 / φq + 2 with hadef
  have hM1 : 1 ≤ M := le_max_right _ _
  have h2φ : 0 < 2 / φq := by positivity
  have ha1 : 1 ≤ a := by linarith
  have hev := ((eventually_ge_atTop N1).and (eventually_ge_atTop 16)).and
    (((expansion_eventually_le_phi (64 * M ^ 2 * a ^ 4)).and
      (phi_rpow_le_rpow 10 (by positivity : (0 : ℝ) < φq / 12))).and
      (expansion_eventually_log_le ((6 * a + 4 + C') / c)))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨C0, hC0, N0, fun N hN L hL e ζ hζ1 hζ2 s hs => ?_⟩
  obtain ⟨⟨hNN1, hN16⟩, ⟨hAφ, hφ10⟩, hDlog⟩ := hN0 N hN
  have hbad := hN1 N hNN1 L hL
  obtain ⟨Lv, Lw, q, γ, hmp, hqN, rfl⟩ := hL
  clear hev hN0 hN1
  -- facts on `N`, `φ` and `q`
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hN0r : (0 : ℝ) < N := by linarith
  have hN1r : (1 : ℝ) ≤ N := by linarith
  have hlog1 : 1 ≤ Real.log N := by
    have h1 : Real.log 16 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
    have h2 : (1 : ℝ) < Real.log 16 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast
      linarith
    linarith
  have hφlog : Real.log N ≤ phi N := log_le_phi hN16
  have hφ1 : 1 ≤ phi N := hlog1.trans hφlog
  have hq1 : 1 ≤ q := le_trans (Real.one_le_rpow hN1r hφq.le) hqN
  have hq0 : 0 < q := by linarith
  have hmpL := hmp.interp γ
  have hLp := hmpL.isProb_v
  have hn0 := (expansion_moments hmpL hq0 e).1
  -- `q² ≤ N`, `0 ≤ C1` and `2 φq ≤ 1`
  have hqsq : q ^ 2 ≤ N := by
    let p0 : OffDiag N := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.lt_def]⟩
    have := hLp.off p0
    have h := expansion_abs_moment_le (hmpL.supp_v.2 p0) 0 2 (by decide) (by norm_num)
    have h2 : ∫ x, (-x) ^ 2 ∂((interp (lexPos N) γ Lv Lw).off p0) = (N : ℝ)⁻¹ := by
      simp_rw [neg_sq]; exact hmpL.var_off p0
    rw [h2, abs_of_nonneg (by positivity)] at h
    simp only [pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one, Nat.sub_zero,
      inv_pow] at h
    exact (inv_le_inv₀ hN0r (by positivity)).1 h
  have hC1 : 0 ≤ C1 := by
    have := hLp.diag ⟨0, by omega⟩
    have h := hmpL.var_diag_le ⟨0, by omega⟩
    have h0 : 0 ≤ ∫ x, x ^ 2 ∂((interp (lexPos N) γ Lv Lw).diag ⟨0, by omega⟩) :=
      integral_nonneg fun x => sq_nonneg x
    have h3 := h0.trans h
    rw [div_nonneg_iff] at h3
    rcases h3 with h3 | h3
    · exact h3.1
    · linarith [h3.2]
  have hφq2 : 2 * φq ≤ 1 := by
    have h1 : (N : ℝ) ^ (φq * (2 : ℕ)) ≤ (N : ℝ) ^ (1 : ℝ) := by
      rw [← expansion_rpow_pow hN0r.le, Real.rpow_one]
      exact (pow_le_pow_left₀ (by positivity) hqN 2).trans hqsq
    have := (Real.rpow_le_rpow_left_iff (by linarith : (1 : ℝ) < N)).1 h1
    push_cast at this
    linarith
  -- the truncation order `ξ`
  have hξge : 2 * ζ / φq ≤ xiOf ζ φq := Nat.le_ceil _
  have hξlt : (xiOf ζ φq : ℝ) < 2 * ζ / φq + 1 := Nat.ceil_lt_add_one (by positivity)
  set ξ := xiOf ζ φq with hξdef
  have hφξ : 2 * ζ ≤ φq * ξ := by
    rw [div_le_iff₀ hφq] at hξge; linarith
  have hm0le : matchedOrder e ≤ 4 := by rcases e <;> simp [matchedOrder]
  have hξ4 : (4 : ℝ) ≤ ξ := by
    refine le_trans ?_ hξge
    rw [le_div_iff₀ hφq]; linarith
  have hm0ξ : matchedOrder e ≤ ξ := by
    have : 4 ≤ ξ := by exact_mod_cast hξ4
    omega
  have hZa : (s : ℝ) + ξ + 1 ≤ a * phi N ^ 2 := by
    have hφ2 : 1 ≤ phi N ^ 2 := one_le_pow₀ hφ1
    have hξR : (ξ : ℝ) ≤ 2 / φq * phi N ^ 2 + 1 := by
      have : 2 * ζ / φq ≤ 2 / φq * phi N ^ 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hφq]; linarith
      linarith
    have : (s : ℝ) + ξ + 1 ≤ Ks * phi N ^ 2 + 2 / φq * phi N ^ 2 + 2 * phi N ^ 2 := by
      linarith
    calc (s : ℝ) + ξ + 1 ≤ Ks * phi N ^ 2 + 2 / φq * phi N ^ 2 + 2 * phi N ^ 2 := this
      _ = a * phi N ^ 2 := by rw [hadef]; ring
  have hT : 64 * M ^ 2 * a ^ 4 * phi N ^ 9 ≤ (N : ℝ) ^ (φq / 12) := by
    have h10 : phi N ^ (10 : ℝ) = phi N ^ (10 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (phi N) 10
    calc 64 * M ^ 2 * a ^ 4 * phi N ^ 9 ≤ phi N * phi N ^ 9 := by gcongr
      _ = phi N ^ (10 : ℝ) := by rw [h10]; ring
      _ ≤ _ := hφ10
  obtain ⟨hP0, hΓ, hY, hsq, hZN⟩ := expansion_poly (s := s) (ξ := ξ) hN1r hM1 ha1 hφ1 hφlog hφq
    hφq2 hqN hZa hT
  -- the coefficients `A_α`
  have hA := expansion_coeffs hmp γ hq0 hqsq hqN hφq hN1r hlog1 hC1 e s ξ hP0
  set n := (interp (lexPos N) γ Lv Lw).entryMoment e with hndef
  have hcb1 : ∀ K : ℕ, coeffBound N φq e K ≤ 1 := by
    intro K
    have : (0 : ℝ) ≤ K * φq := by positivity
    rcases e with i | p <;> simp only [coeffBound] <;>
      refine Real.rpow_le_one_of_one_le_of_nonpos hN1r ?_
    · have := div_nonneg this (by norm_num : (0 : ℝ) ≤ 4); linarith
    · have := div_nonneg this (by norm_num : (0 : ℝ) ≤ 10); linarith
  refine ⟨expA s ξ (matchedOrder e) n, fun α => (hA α).1, fun z hz w hw => ?_⟩
  -- the expansion at `z` and `w`
  have hzim : 0 < z.im :=
    lt_of_le_of_lt (div_nonneg (Real.rpow_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg N) _) _)
      (Nat.cast_nonneg N)) hz.2.1
  have hB : 1 / z.im ≤ N := by
    have h1 : 1 ≤ phi N ^ C0 := Real.one_le_rpow hφ1 hC0.le
    have h2 : 1 / (N : ℝ) < z.im :=
      lt_of_le_of_lt (div_le_div_of_nonneg_right h1 hN0r.le) hz.2.1
    rw [div_le_iff₀ hzim]
    rw [div_lt_iff₀ hN0r] at h2
    linarith
  set X : (Fin s → ℕ) → ℂ := fun κ => ∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn κ) w)
    ∂(interp (lexPos N) γ Lv Lw).law with hXdef
  set Y : (Fin s → ℕ) → ℂ := fun κ => ∫ ω, evalW (resR e z ω) (msc z) (wordP e (List.ofFn κ) w)
    ∂(interp (lexPos N) γ Lv Lw).law with hYdef
  have hX0 : ∫ ω, evalWord (resS z ω) (msc z) w ∂(interp (lexPos N) γ Lv Lw).law = X 0 := by
    rw [hXdef]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    exact (expansion_evalW_wordP_zero _ _ e w hw).symm
  have hid := expansion_identity s ξ (matchedOrder e) n hm0ξ hn0 X Y
  set P := ((interp (lexPos N) γ Lv Lw).law (goodEvent N C0)ᶜ).toReal with hPdef
  set Wc : ℝ := (1 + ((ξ : ℝ) + 1) * ((s : ℝ) * ξ + 1) ^ ξ) * 2 ^ ξ * ((N : ℝ) + 1) ^ (s + ξ)
    with hWcdef
  have herr : ∀ κ : Fin s → ℕ, ∑ t, κ t ≤ ξ → ‖(X - (Y + expU ℂ s ξ n Y)) κ‖ ≤
      2 ^ (∑ t, κ t) * 4 ^ (s + ∑ t, κ t + 2) *
        (4 * ((s + ∑ t, κ t : ℕ) : ℝ) / q) ^ (ξ - ∑ t, κ t + 1) + Wc * P :=
    fun κ hκ => expansion_err_le hLp hq0 hq1 hmpL.supp_v hz hB e w hw ξ hsq κ hκ
  have herr0 : ‖(X - (Y + expU ℂ s ξ n Y)) 0‖ ≤
      4 ^ (s + 2) * (4 * (s : ℝ) / q) ^ (ξ + 1) + Wc * P := by
    have := herr 0 (by simp)
    simpa using this
  have hP0' : 0 ≤ P := ENNReal.toReal_nonneg
  have hWc0 : 0 ≤ Wc := by positivity
  have hPbound : P ≤ (N : ℝ) ^ (C' : ℝ) * Real.exp (-c * phi N ^ 3) := by
    have h3 : phi N ^ (3 : ℝ) = phi N ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast (phi N) 3
    rw [hPdef, Real.rpow_natCast, ← h3]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbad
  have hgood2 := expansion_good_le (s := s) (ξ := ξ) (ζ := ζ) hN1r hq0 hqN (by positivity) hΓ
    (by positivity) hY hφξ
  have hD : (6 * a + 4 + (C' : ℝ)) * Real.log N ≤ c * phi N := by
    have := mul_le_mul_of_nonneg_left hDlog hc.le
    rwa [← mul_assoc, mul_div_cancel₀ _ hc.ne'] at this
  have hbad2 := expansion_bad_le (s := s) (ξ := ξ) (a := a) hN16 hZN (by push_cast; exact hZa)
    hζ2 hφ1 hlog1 (Nat.cast_nonneg C') hD hPbound hP0'
  calc _ = ‖(X - (Y + expU ℂ s ξ n Y)) 0 - ∑ α ∈ highIdx s (matchedOrder e) ξ,
        (expA s ξ (matchedOrder e) n α : ℂ) * (X - (Y + expU ℂ s ξ n Y)) α‖ := by
        rw [hX0]; exact congrArg (fun x => ‖x‖) hid
    _ ≤ 4 ^ s * (N : ℝ) ^ (-ζ) :=
        expansion_final _ _ hq0 (by positivity) (by positivity) hWc0 hP0' herr0
          (fun α hα => herr α ((expansion_mem_highIdx α).1 hα).2) (fun α => (hA α).2)
          (fun α => (hA α).1.trans (hcb1 _)) hgood2 hbad2

/-! ### Compiled checks at concrete nondegenerate points

The good-event forms at `N = 16`: all diagonal entries `0`, all upper entries `1/64`, the entry
`e = (1, 2)` (`Fin 16` indices `0, 1`) with `v_e = 1/64 ≠ 0`, `q = 64`, `z = 10 i ∈ S(3)`,
`m = m_sc(z)`, the word `G_13 (G_22 - m)` (`s = 2`) and `κ = (1, 0)` (`8 (s + |κ|) = 24 ≤ q`).
Lemma 6.5 for the interpolations of the Rademacher laws against themselves. -/

open private mem_goodEvent_of_large_eta phi_sixteen_cube from WEdgeNS.Comparison.GoodEvent
open private sc_rad_instance from WEdgeNS.LocalLaw.SelfConsistent

/-- The upper entry `(1, 2)` of a `16 × 16` matrix. -/
private def expansion_e16 : Fin 16 ⊕ OffDiag 16 := Sum.inr ⟨(0, 1), by decide⟩

/-- Diagonal entries `0`, upper entries `1/64`. -/
private noncomputable def expansion_ω16 : Entries 16 := (fun _ => 0, fun _ => 1 / 64)

private noncomputable def expansion_z16 : ℂ := ⟨0, 10⟩

/-- The word `G_13 (G_22 - m)`. -/
private def expansion_w16 : Word 16 := [⟨.g, 0, 2⟩, ⟨.gc, 1, 1⟩]

private lemma expansion_ω16_good : expansion_ω16 ∈ goodEvent 16 3 :=
  mem_goodEvent_of_large_eta (by simpa using phi_sixteen_cube.1) _

private lemma expansion_z16_mem : expansion_z16 ∈ specDomain 16 3 :=
  ⟨by simp [expansion_z16], by simpa [expansion_z16] using phi_sixteen_cube.2,
    by simp [expansion_z16]⟩

private lemma expansion_msc_z16 : ‖msc expansion_z16‖ ≤ 1 :=
  (norm_msc_eq_inv_and_lt_one (by simp [expansion_z16])).2.le

private lemma expansion_v16 : entryVal expansion_e16 expansion_ω16 = 1 / 64 := rfl

/-- The hypotheses of the good-event forms hold together at the point above, with `v_e ≠ 0`. -/
example : expansion_ω16 ∈ goodEvent 16 3 ∧ expansion_z16 ∈ specDomain 16 3 ∧
    ‖msc expansion_z16‖ ≤ 1 ∧ |entryVal expansion_e16 expansion_ω16| ≤ (64 : ℝ)⁻¹ ∧
    entryVal expansion_e16 expansion_ω16 ≠ 0 ∧ expansion_w16.length = 2 ∧
    8 * ((2 + ∑ t, (![1, 0] : Fin 2 → ℕ) t : ℕ) : ℝ) ≤ 64 ∧ 8 * ((2 : ℕ) : ℝ) ≤ 64 := by
  refine ⟨expansion_ω16_good, expansion_z16_mem, expansion_msc_z16, ?_, ?_, rfl, ?_, ?_⟩
  · rw [expansion_v16]; norm_num
  · rw [expansion_v16]; norm_num
  · simp; norm_num
  · norm_num

/-- `norm_evalW_wordP_sub_expansion_le_of_good` at the point above, to order `n = 2`. -/
example :
    ‖evalW (resS expansion_z16 expansion_ω16) (msc expansion_z16)
        (wordP expansion_e16 (List.ofFn (![1, 0] : Fin 2 → ℕ)) expansion_w16) -
      ∑ c ∈ Finset.range (2 + 1), (((-entryVal expansion_e16 expansion_ω16) ^ c : ℝ) : ℂ) *
        ∑ l ∈ Finset.Nat.antidiagonalTuple 2 c,
          ((∏ t, Nat.choose ((![1, 0] : Fin 2 → ℕ) t + l t) (l t) : ℕ) : ℂ) *
            evalW (resR expansion_e16 expansion_z16 expansion_ω16) (msc expansion_z16)
              (wordP expansion_e16 (List.ofFn ((![1, 0] : Fin 2 → ℕ) + l)) expansion_w16)‖ ≤
      2 ^ (∑ t, (![1, 0] : Fin 2 → ℕ) t) * 4 ^ (2 + ∑ t, (![1, 0] : Fin 2 → ℕ) t + 2) *
        (4 * ((2 + ∑ t, (![1, 0] : Fin 2 → ℕ) t : ℕ) : ℝ) / 64) ^ (2 + 1) :=
  norm_evalW_wordP_sub_expansion_le_of_good expansion_ω16_good expansion_z16_mem expansion_e16
    expansion_msc_z16 (by norm_num) (by rw [expansion_v16]; norm_num) (s := 2) expansion_w16 rfl
    ![1, 0] (by simp; norm_num) 2

/-- `norm_evalWord_sub_expansion_le_of_good` at the point above, to order `n = 2`. -/
example :
    ‖evalWord (resS expansion_z16 expansion_ω16) (msc expansion_z16) expansion_w16 -
      ∑ c ∈ Finset.range (2 + 1), (((-entryVal expansion_e16 expansion_ω16) ^ c : ℝ) : ℂ) *
        ∑ κ ∈ Finset.Nat.antidiagonalTuple 2 c,
          evalW (resR expansion_e16 expansion_z16 expansion_ω16) (msc expansion_z16)
            (wordP expansion_e16 (List.ofFn κ) expansion_w16)‖ ≤
      4 ^ (2 + 2) * (4 * ((2 : ℕ) : ℝ) / 64) ^ (2 + 1) :=
  norm_evalWord_sub_expansion_le_of_good expansion_ω16_good expansion_z16_mem expansion_e16
    expansion_msc_z16 (by norm_num) (by rw [expansion_v16]; norm_num) (s := 2) expansion_w16 rfl
    (by norm_num) 2

/-- For large `N` the Rademacher laws against themselves are a matched pair with `C1 = 2` and
`q = N^{2/5}`. -/
private lemma expansion_matchedPair_radLaws :
    ∀ᶠ N : ℕ in atTop, MatchedPair 2 ((N : ℝ) ^ (2 / 5 : ℝ)) (radLaws N) (radLaws N) := by
  filter_upwards [sc_rad_instance 0 0, eventually_ge_atTop 32] with N hi h32
  have hgw := hi.1
  have hNpos : 0 < N := by omega
  have hlog : (1 : ℝ) / 2 ≤ Real.log N := by
    have h2 : Real.log 2 ≤ Real.log N :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ N))
    linarith [Real.log_two_gt_d9]
  refine ⟨hgw.isProb, hgw.isProb, hi.2.1, hi.2.1, hgw.mean_diag, hgw.mean_off, fun i => ?_,
    hgw.var_off, fun p => ?_, fun p k _ => rfl, fun i k _ => rfl⟩
  · have h := (abs_le.1 (hgw.var_diag i)).2
    rw [div_eq_mul_inv]
    linarith
  · rw [integral_pow_four_radLaws_off hNpos p, div_eq_mul_inv]
    have hinv : 0 < ((N : ℝ) ^ 2)⁻¹ := by positivity
    nlinarith

/-- The class `PairInterpClass 2 (2/5)` of Lemma 6.5 is nonempty for all large `N`: it contains
every interpolation `H_γ` of the Rademacher laws against themselves. -/
example : ∀ᶠ N : ℕ in atTop, ∀ γ : ℕ,
    PairInterpClass 2 (2 / 5) N (interp (lexPos N) γ (radLaws N) (radLaws N)) := by
  filter_upwards [expansion_matchedPair_radLaws] with N h γ
  exact ⟨radLaws N, radLaws N, _, γ, h, le_rfl, rfl⟩

/-- `expectation_expansion` for `C1 = 2`, `φq = 2/5`, `K_s = 1`, at every interpolation `H_γ` of
the Rademacher laws, every entry `e`, `ζ = 1` and words of length `s = 2`: all hypotheses hold for
all large `N`. -/
example : ∃ C0 > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ (γ : ℕ) (e : Fin N ⊕ OffDiag N),
    ∃ A : (Fin 2 → ℕ) → ℝ, (∀ α, |A α| ≤ coeffBound N (2 / 5) e (∑ t, α t)) ∧
      ∀ z ∈ specDomain N C0, ∀ w : Word N, w.length = 2 →
        ‖(∫ ω, evalWord (resS z ω) (msc z) w ∂(interp (lexPos N) γ (radLaws N) (radLaws N)).law)
          - (∑ k ∈ Finset.range (matchedOrder e + 1),
              ((interp (lexPos N) γ (radLaws N) (radLaws N)).entryMoment e k : ℂ) *
              ∑ κ ∈ Finset.Nat.antidiagonalTuple 2 k,
                ∫ ω, evalW (resR e z ω) (msc z) (wordP e (List.ofFn κ) w)
                  ∂(interp (lexPos N) γ (radLaws N) (radLaws N)).law)
          - ∑ α ∈ highIdx 2 (matchedOrder e) (xiOf 1 (2 / 5)),
              (A α : ℂ) * ∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) w)
                ∂(interp (lexPos N) γ (radLaws N) (radLaws N)).law‖
          ≤ 4 ^ 2 * (N : ℝ) ^ (-(1 : ℝ)) := by
  obtain ⟨C0, hC0, N0, h⟩ := expectation_expansion (C1 := 2) (φq := 2 / 5) (Ks := 1)
    (by norm_num) (by norm_num)
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [expansion_matchedPair_radLaws, eventually_ge_atTop N0,
    expansion_eventually_le_phi 2] with N hmp hN hφ γ e
  have hφ2 : (2 : ℝ) ≤ phi N ^ 2 := by nlinarith
  exact h N hN _ ⟨radLaws N, radLaws N, _, γ, hmp, le_rfl, rfl⟩ e 1 le_rfl (by linarith) 2
    (by push_cast; linarith)

#print axioms norm_evalW_wordP_sub_expansion_le_of_good
#print axioms norm_evalWord_sub_expansion_le_of_good
#print axioms expectation_expansion

end WEdgeNS
