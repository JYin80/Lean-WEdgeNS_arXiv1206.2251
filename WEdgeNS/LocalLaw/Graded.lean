import WEdgeNS.Probability.ProductSpace
import WEdgeNS.Semicircle.Bounds

/-!
# Resolvent entries of minors and their graded terms
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- `H^{(∅)} = H`. -/
private lemma graded_zeroRC_empty {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) : zeroRC ∅ H = H := by
  funext i j
  simp [zeroRC]

/-- (3.12) of [15] for the minor `H^{(V)}` and the index `a`. -/
private lemma graded_step {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (V : Finset (Fin N)) {x y a : Fin N} (hx : x ≠ a) (hy : y ≠ a) :
    resolventC (zeroRC V H) z x y = resolventC (zeroRC (insert a V) H) z x y +
      resolventC (zeroRC V H) z x a * resolventC (zeroRC V H) z a y /
        resolventC (zeroRC V H) z a a := by
  have h := resolventC_eq_minor_add (zeroRC_isHermitian hH V) hz hx hy
  rwa [zeroRC_zeroRC, ← Finset.insert_eq] at h

/-- Lemma 5.7 of [15], (5.33)–(5.34), with explicit bounds `o ≥ Λ_o`, `d ≥ Λ_d`; (5.32) is read
as `|U|(o + d) ≤ c1`. -/
theorem resolventC_zeroRC_sub_le : ∃ c1 > 0, ∃ C ≥ (1 : ℝ), ∀ {N : ℕ}
    {H : Matrix (Fin N) (Fin N) ℝ}, H.IsHermitian → ∀ {z : ℂ}, |z.re| ≤ 5 → 0 < z.im →
    z.im ≤ 10 → ∀ (o d : ℝ) (U : Finset (Fin N)), 0 ≤ o →
    (∀ i j, i ≠ j → ‖resolventC H z i j‖ ≤ o) → (∀ i, ‖resolventC H z i i - msc z‖ ≤ d) →
    o + d ≤ c1 → (U.card : ℝ) * (o + d) ≤ c1 → ∀ i j, i ∉ U → j ∉ U →
      ‖resolventC (zeroRC U H) z i j - (if i = j then msc z else 0)‖ ≤
          C * ((if i = j then d else 0) + o) ∧
        C⁻¹ ≤ ‖resolventC (zeroRC U H) z i i‖ := by
  obtain ⟨Cm, hCm, hmsc⟩ := msc_bounds
  have hCm0 : 0 < Cm := by linarith
  refine ⟨(8 * Cm)⁻¹, by positivity, 2 * Cm, by linarith, ?_⟩
  intro N H hH z hre hz hz' o d U ho hoff hdiag hod hU i j hi hj
  have hm : Cm⁻¹ ≤ ‖msc z‖ := (hmsc z hre hz hz').1.1
  have hd : 0 ≤ d := (norm_nonneg _).trans (hdiag i)
  have hUo : 8 * Cm * (U.card * o) ≤ 1 := by
    have h1 : (U.card : ℝ) * o ≤ U.card * (o + d) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    have h2 : 8 * Cm * (8 * Cm)⁻¹ = 1 := by field_simp
    nlinarith
  have hc0 : 7 / (8 * Cm) ≤ Cm⁻¹ - d - o := by
    have h2 : (8 * Cm)⁻¹ = Cm⁻¹ - 7 / (8 * Cm) := by field_simp; ring
    linarith
  -- lower bound on the diagonal of a minor whose entries are close to those of `G`
  have hlow : ∀ (V : Finset (Fin N)) (k : Fin N),
      ‖resolventC (zeroRC V H) z k k - resolventC H z k k‖ ≤ o →
        7 / (8 * Cm) ≤ ‖resolventC (zeroRC V H) z k k‖ := by
    intro V k hk
    have h1 := norm_sub_norm_le (msc z) (msc z - resolventC (zeroRC V H) z k k)
    have h2 : ‖msc z - resolventC (zeroRC V H) z k k‖ ≤ d + o := by
      calc ‖msc z - resolventC (zeroRC V H) z k k‖
          = ‖(resolventC H z k k - msc z) + (resolventC (zeroRC V H) z k k -
              resolventC H z k k)‖ := by rw [← norm_neg]; congr 1; ring
        _ ≤ d + o := (norm_add_le _ _).trans (add_le_add (hdiag k) hk)
    rw [sub_sub_cancel] at h1
    linarith
  -- the bootstrap of (5.35)–(5.38)
  have key : ∀ V ⊆ U, ∀ x y, x ∉ V → y ∉ V →
      ‖resolventC (zeroRC V H) z x y - resolventC H z x y‖ ≤ 8 * Cm * (V.card * o ^ 2) := by
    intro V
    induction V using Finset.induction_on with
    | empty =>
      intro _ x y _ _
      simp [graded_zeroRC_empty]
    | insert k V hk ih =>
      intro hV x y hx hy
      have hVU : V ⊆ U := (Finset.subset_insert k V).trans hV
      have hxk : x ≠ k := fun h => hx (h ▸ Finset.mem_insert_self k V)
      have hyk : y ≠ k := fun h => hy (h ▸ Finset.mem_insert_self k V)
      have hxV : x ∉ V := fun h => hx (Finset.mem_insert_of_mem h)
      have hyV : y ∉ V := fun h => hy (Finset.mem_insert_of_mem h)
      have hkU : k ∈ U := hV (Finset.mem_insert_self k V)
      have hVo : 8 * Cm * (V.card * o ^ 2) ≤ o := by
        have h1 : (V.card : ℝ) ≤ U.card := by exact_mod_cast Finset.card_le_card hVU
        have h2 : 8 * Cm * (V.card * o) ≤ 1 :=
          le_trans (by gcongr) hUo
        nlinarith
      have hxk' := (ih hVU x k hxV hk).trans hVo
      have hky' := (ih hVU k y hk hyV).trans hVo
      have hkk' := (ih hVU k k hk hk).trans hVo
      have hn1 : ‖resolventC (zeroRC V H) z x k‖ ≤ 2 * o := by
        have := norm_le_norm_add_norm_sub' (resolventC (zeroRC V H) z x k) (resolventC H z x k)
        linarith [hoff x k hxk]
      have hn2 : ‖resolventC (zeroRC V H) z k y‖ ≤ 2 * o := by
        have := norm_le_norm_add_norm_sub' (resolventC (zeroRC V H) z k y) (resolventC H z k y)
        linarith [hoff k y (Ne.symm hyk)]
      have hn3 := hlow V k hkk'
      have hpos : 0 < 7 / (8 * Cm) := by positivity
      have hratio : ‖resolventC (zeroRC V H) z x k * resolventC (zeroRC V H) z k y /
          resolventC (zeroRC V H) z k k‖ ≤ 8 * Cm * o ^ 2 := by
        rw [norm_div, norm_mul]
        calc ‖resolventC (zeroRC V H) z x k‖ * ‖resolventC (zeroRC V H) z k y‖ /
              ‖resolventC (zeroRC V H) z k k‖
            ≤ (2 * o) * (2 * o) / (7 / (8 * Cm)) := by
              gcongr
          _ ≤ 8 * Cm * o ^ 2 := by
              rw [div_le_iff₀ hpos]
              field_simp
              nlinarith [sq_nonneg o]
      have hid := graded_step hH hz V hxk hyk
      rw [Finset.card_insert_of_notMem hk]
      calc ‖resolventC (zeroRC (insert k V) H) z x y - resolventC H z x y‖
          = ‖(resolventC (zeroRC V H) z x y - resolventC H z x y) -
              resolventC (zeroRC V H) z x k * resolventC (zeroRC V H) z k y /
                resolventC (zeroRC V H) z k k‖ := by rw [hid]; ring_nf
        _ ≤ 8 * Cm * (V.card * o ^ 2) + 8 * Cm * o ^ 2 :=
            (norm_sub_le _ _).trans (add_le_add (ih hVU x y hxV hyV) hratio)
        _ = 8 * Cm * (((V.card + 1 : ℕ) : ℝ) * o ^ 2) := by push_cast; ring
  have hUo2 : 8 * Cm * (U.card * o ^ 2) ≤ o := by nlinarith
  have heU : ∀ x y, x ∉ U → y ∉ U →
      ‖resolventC (zeroRC U H) z x y - resolventC H z x y‖ ≤ o :=
    fun x y hx hy => (key U le_rfl x y hx hy).trans hUo2
  refine ⟨?_, ?_⟩
  · by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      have h1 : ‖resolventC (zeroRC U H) z i i - msc z‖ ≤ o + d := by
        calc ‖resolventC (zeroRC U H) z i i - msc z‖
            = ‖(resolventC (zeroRC U H) z i i - resolventC H z i i) +
                (resolventC H z i i - msc z)‖ := by ring_nf
          _ ≤ o + d := (norm_add_le _ _).trans (add_le_add (heU i i hi hi) (hdiag i))
      nlinarith
    · simp only [hij, ↓reduceIte, sub_zero, zero_add]
      have := norm_le_norm_add_norm_sub' (resolventC (zeroRC U H) z i j) (resolventC H z i j)
      nlinarith [hoff i j hij, heU i j hi hj]
  · have h1 := hlow U i (heU i i hi hi)
    have h2 : (2 * Cm)⁻¹ ≤ 7 / (8 * Cm) := by
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      field_simp
      norm_num
    linarith

/-! ### Expansion of `G^{S,U}_ij` into monomials (Definition 5.8, Lemma 5.9, (5.66)–(5.70) of [15])

The function `g V x y` stands for `G^{(V)}_xy`; its only property used here is (3.12) of [15].
A monomial is a list of factors, each an entry `g (V ∪ X) x y`, an inverse diagonal entry
`(g (V ∪ X) x x)⁻¹`, or the sign `-1`. -/

/-- A factor of a monomial of the form (5.39)–(5.40) of [15]. -/
private inductive GFac (N : ℕ) where
  | off (x y : Fin N) (X : Finset (Fin N))
  | inv (x : Fin N) (X : Finset (Fin N))
  | neg

section Expansion

variable {N : ℕ}

/-- The value of a factor at the set `V`. -/
private def facEval (g : Finset (Fin N) → Fin N → Fin N → ℂ) (V : Finset (Fin N)) :
    GFac N → ℂ
  | .off x y X => g (V ∪ X) x y
  | .inv x X => (g (V ∪ X) x x)⁻¹
  | .neg => -1

/-- The value of a monomial at the set `V`. -/
private def monoEval (g : Finset (Fin N) → Fin N → Fin N → ℂ) (V : Finset (Fin N))
    (fs : List (GFac N)) : ℂ :=
  (fs.map (facEval g V)).prod

/-- The factor with `a` added to its set. -/
private def facShift (a : Fin N) : GFac N → GFac N
  | .off x y X => .off x y (insert a X)
  | .inv x X => .inv x (insert a X)
  | .neg => .neg

/-- The difference of a factor in the direction `a`, as a list of monomials ((5.66)–(5.69) of
[15]). -/
private def facDeriv (a : Fin N) : GFac N → List (List (GFac N))
  | .off x y X => [[.off x a X, .off a y X, .inv a X]]
  | .inv x X => [[.neg, .off x a X, .off a x X, .inv a X, .inv x X, .inv x (insert a X)]]
  | .neg => []

/-- The difference of a monomial in the direction `a` ((5.70) of [15]). -/
private def monoDeriv (a : Fin N) : List (GFac N) → List (List (GFac N))
  | [] => []
  | f :: fs => (facDeriv a f).map (· ++ fs) ++ (monoDeriv a fs).map (facShift a f :: ·)

private lemma monoEval_nil (g : Finset (Fin N) → Fin N → Fin N → ℂ) (V : Finset (Fin N)) :
    monoEval g V [] = 1 := rfl

private lemma monoEval_cons (g : Finset (Fin N) → Fin N → Fin N → ℂ) (V : Finset (Fin N))
    (f : GFac N) (fs : List (GFac N)) :
    monoEval g V (f :: fs) = facEval g V f * monoEval g V fs := by
  simp [monoEval]

private lemma monoEval_append (g : Finset (Fin N) → Fin N → Fin N → ℂ) (V : Finset (Fin N))
    (fs gs : List (GFac N)) :
    monoEval g V (fs ++ gs) = monoEval g V fs * monoEval g V gs := by
  simp [monoEval]

private lemma facEval_shift (g : Finset (Fin N) → Fin N → Fin N → ℂ) (V : Finset (Fin N))
    (a : Fin N) (f : GFac N) : facEval g V (facShift a f) = facEval g (insert a V) f := by
  cases f <;> simp [facEval, facShift, Finset.insert_union, Finset.union_insert]

/-- The conditions under which (3.12) of [15] expands the difference of a factor. -/
private def facGood (g : Finset (Fin N) → Fin N → Fin N → ℂ) (a : Fin N) (V : Finset (Fin N)) :
    GFac N → Prop
  | .off x y _ => x ≠ a ∧ y ≠ a
  | .inv x X => x ≠ a ∧ g (V ∪ X) x x ≠ 0 ∧ g (insert a (V ∪ X)) x x ≠ 0
  | .neg => True

section Identity

variable {g : Finset (Fin N) → Fin N → Fin N → ℂ}
  (hg : ∀ V x y a, x ≠ a → y ≠ a → g V x y = g (insert a V) x y + g V x a * g V a y / g V a a)
include hg

private lemma facEval_sub {a : Fin N} {V : Finset (Fin N)} {f : GFac N} (hf : facGood g a V f) :
    facEval g V f - facEval g (insert a V) f = ((facDeriv a f).map (monoEval g V)).sum := by
  cases f with
  | off x y X =>
    obtain ⟨hx, hy⟩ := hf
    simp only [facEval, facDeriv, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      monoEval_cons, monoEval_nil, Finset.insert_union]
    rw [hg (V ∪ X) x y a hx hy]
    ring
  | inv x X =>
    obtain ⟨hx, hA, hB⟩ := hf
    simp only [facEval, facDeriv, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      monoEval_cons, monoEval_nil, Finset.insert_union, Finset.union_insert]
    have hAB := hg (V ∪ X) x x a hx hx
    field_simp
    linear_combination (-1 : ℂ) * hAB
  | neg => simp [facEval, facDeriv]

private lemma monoEval_sub {a : Fin N} {V : Finset (Fin N)} :
    ∀ {fs : List (GFac N)}, (∀ f ∈ fs, facGood g a V f) →
      monoEval g V fs - monoEval g (insert a V) fs = ((monoDeriv a fs).map (monoEval g V)).sum
  | [], _ => by simp [monoEval, monoDeriv]
  | f :: fs, hfs => by
    have h1 := facEval_sub hg (hfs f List.mem_cons_self)
    have h2 := monoEval_sub (fs := fs) fun f' hf' => hfs f' (List.mem_cons_of_mem f hf')
    simp only [monoDeriv, List.map_append, List.sum_append, List.map_map]
    have e1 : ((facDeriv a f).map (monoEval g V ∘ (· ++ fs))).sum =
        ((facDeriv a f).map (monoEval g V)).sum * monoEval g V fs := by
      rw [← List.sum_map_mul_right]
      congr 1
      exact List.map_congr_left fun t _ => by simp [monoEval_append]
    have e2 : ((monoDeriv a fs).map (monoEval g V ∘ (facShift a f :: ·))).sum =
        facEval g (insert a V) f * ((monoDeriv a fs).map (monoEval g V)).sum := by
      rw [← List.sum_map_mul_left]
      congr 1
      exact List.map_congr_left fun t _ => by simp [monoEval_cons, facEval_shift]
    rw [e1, e2, ← h1, ← h2, monoEval_cons, monoEval_cons]
    ring

end Identity

/-- The bound of a factor: `A` for an entry, `B` for an inverse diagonal entry. -/
private def facW (A B : ℝ) : GFac N → ℝ
  | .off _ _ _ => A
  | .inv _ _ => B
  | .neg => 1

/-- The bound of a monomial. -/
private def monoW (A B : ℝ) (fs : List (GFac N)) : ℝ :=
  (fs.map (facW A B)).prod

private lemma monoW_cons (A B : ℝ) (f : GFac N) (fs : List (GFac N)) :
    monoW A B (f :: fs) = facW A B f * monoW A B fs := by
  simp [monoW]

private lemma monoW_append (A B : ℝ) (fs gs : List (GFac N)) :
    monoW A B (fs ++ gs) = monoW A B fs * monoW A B gs := by
  simp [monoW]

private lemma facW_shift (A B : ℝ) (a : Fin N) (f : GFac N) :
    facW A B (facShift a f) = facW A B f := by
  cases f <;> rfl

private lemma facW_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (f : GFac N) : 0 ≤ facW A B f := by
  cases f <;> simp [facW, hA, hB]

private lemma monoW_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ fs : List (GFac N), 0 ≤ monoW A B fs
  | [] => by simp [monoW]
  | f :: fs => by
    rw [monoW_cons]
    exact mul_nonneg (facW_nonneg hA hB f) (monoW_nonneg hA hB fs)

private lemma facDeriv_weight {A B l : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h1 : A * B ≤ l)
    (h2 : A ^ 2 * B ^ 2 ≤ l) (a : Fin N) (f : GFac N) :
    ((facDeriv a f).map (monoW A B)).sum ≤ l * facW A B f := by
  cases f with
  | off x y X =>
    simp only [facDeriv, facW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      monoW, List.prod_cons, List.prod_nil]
    nlinarith [mul_le_mul_of_nonneg_left h1 hA]
  | inv x X =>
    simp only [facDeriv, facW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      monoW, List.prod_cons, List.prod_nil]
    nlinarith [mul_le_mul_of_nonneg_left h2 hB]
  | neg =>
    simp only [facDeriv, facW, List.map_nil, List.sum_nil, mul_one]
    nlinarith [mul_nonneg hA hB]

private lemma monoDeriv_weight {A B l : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h1 : A * B ≤ l)
    (h2 : A ^ 2 * B ^ 2 ≤ l) (a : Fin N) :
    ∀ fs : List (GFac N),
      ((monoDeriv a fs).map (monoW A B)).sum ≤ fs.length * l * monoW A B fs
  | [] => by simp [monoDeriv, monoW]
  | f :: fs => by
    have ih := monoDeriv_weight hA hB h1 h2 a fs
    have hf := facDeriv_weight hA hB h1 h2 a f
    simp only [monoDeriv, List.map_append, List.sum_append, List.map_map]
    have e1 : ((facDeriv a f).map (monoW A B ∘ (· ++ fs))).sum =
        ((facDeriv a f).map (monoW A B)).sum * monoW A B fs := by
      rw [← List.sum_map_mul_right]
      congr 1
      exact List.map_congr_left fun t _ => by simp [monoW_append]
    have e2 : ((monoDeriv a fs).map (monoW A B ∘ (facShift a f :: ·))).sum =
        facW A B f * ((monoDeriv a fs).map (monoW A B)).sum := by
      rw [← List.sum_map_mul_left]
      congr 1
      exact List.map_congr_left fun t _ => by simp [monoW_cons, facW_shift]
    rw [e1, e2, monoW_cons, List.length_cons]
    have hw := monoW_nonneg hA hB fs
    have hfw := facW_nonneg hA hB f
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hf hw, mul_le_mul_of_nonneg_left ih hfw]

private lemma monoDeriv_length (a : Fin N) :
    ∀ fs : List (GFac N), ∀ t ∈ monoDeriv a fs, t.length ≤ fs.length + 5
  | [], t, ht => by simp [monoDeriv] at ht
  | f :: fs, t, ht => by
    simp only [monoDeriv, List.mem_append, List.mem_map] at ht
    rcases ht with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · cases f with
      | off x y X =>
        simp only [facDeriv, List.mem_singleton] at hs
        subst hs
        simp
      | inv x X =>
        simp only [facDeriv, List.mem_singleton] at hs
        subst hs
        simp
      | neg => simp [facDeriv] at hs
    · have := monoDeriv_length a fs s hs
      simp only [List.length_cons]
      omega

/-- The admissibility of a factor: its indices lie outside `F ∪ X`, its set `X ⊆ S` is
disjoint from `F`, and an entry is off the diagonal. -/
private def facOk (S F : Finset (Fin N)) : GFac N → Prop
  | .off x y X => x ≠ y ∧ x ∉ F ∧ y ∉ F ∧ x ∉ X ∧ y ∉ X ∧ Disjoint X F ∧ X ⊆ S
  | .inv x X => x ∉ F ∧ x ∉ X ∧ Disjoint X F ∧ X ⊆ S
  | .neg => True

private lemma facOk_mono {S F F' : Finset (Fin N)} (hF : F' ⊆ F) {f : GFac N}
    (hf : facOk S F f) : facOk S F' f := by
  cases f with
  | off x y X =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hf
    exact ⟨h1, fun h => h2 (hF h), fun h => h3 (hF h), h4, h5, h6.mono_right hF, h7⟩
  | inv x X =>
    obtain ⟨h2, h4, h6, h7⟩ := hf
    exact ⟨fun h => h2 (hF h), h4, h6.mono_right hF, h7⟩
  | neg => trivial

private lemma facOk_shift {S F : Finset (Fin N)} {a : Fin N} (ha : a ∉ F) (haS : a ∈ S)
    {f : GFac N} (hf : facOk S (insert a F) f) : facOk S F (facShift a f) := by
  cases f with
  | off x y X =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hf
    simp only [Finset.mem_insert, not_or] at h2 h3
    refine ⟨h1, h2.2, h3.2, ?_, ?_, ?_, Finset.insert_subset haS h7⟩
    · simp [h2.1, h4]
    · simp [h3.1, h5]
    · exact Finset.disjoint_insert_left.mpr ⟨ha, h6.mono_right (Finset.subset_insert a F)⟩
  | inv x X =>
    obtain ⟨h2, h4, h6, h7⟩ := hf
    simp only [Finset.mem_insert, not_or] at h2
    refine ⟨h2.2, ?_, ?_, Finset.insert_subset haS h7⟩
    · simp [h2.1, h4]
    · exact Finset.disjoint_insert_left.mpr ⟨ha, h6.mono_right (Finset.subset_insert a F)⟩
  | neg => trivial

private lemma facOk_deriv {S F : Finset (Fin N)} {a : Fin N} (ha : a ∉ F) (haS : a ∈ S)
    {f : GFac N} (hf : facOk S (insert a F) f) :
    ∀ t ∈ facDeriv a f, ∀ f' ∈ t, facOk S F f' := by
  cases f with
  | off x y X =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hf
    simp only [Finset.mem_insert, not_or] at h2 h3
    have haX : a ∉ X := fun h => Finset.disjoint_left.mp h6 h (Finset.mem_insert_self a F)
    have h6' := h6.mono_right (Finset.subset_insert a F)
    intro t ht f' hf'
    simp only [facDeriv, List.mem_singleton] at ht
    subst ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
    rcases hf' with rfl | rfl | rfl
    · exact ⟨h2.1, h2.2, ha, h4, haX, h6', h7⟩
    · exact ⟨Ne.symm h3.1, ha, h3.2, haX, h5, h6', h7⟩
    · exact ⟨ha, haX, h6', h7⟩
  | inv x X =>
    obtain ⟨h2, h4, h6, h7⟩ := hf
    simp only [Finset.mem_insert, not_or] at h2
    have haX : a ∉ X := fun h => Finset.disjoint_left.mp h6 h (Finset.mem_insert_self a F)
    have h6' := h6.mono_right (Finset.subset_insert a F)
    intro t ht f' hf'
    simp only [facDeriv, List.mem_singleton] at ht
    subst ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
    rcases hf' with rfl | rfl | rfl | rfl | rfl | rfl
    · trivial
    · exact ⟨h2.1, h2.2, ha, h4, haX, h6', h7⟩
    · exact ⟨Ne.symm h2.1, ha, h2.2, haX, h4, h6', h7⟩
    · exact ⟨ha, haX, h6', h7⟩
    · exact ⟨h2.2, h4, h6', h7⟩
    · refine ⟨h2.2, ?_, ?_, Finset.insert_subset haS h7⟩
      · simp [h2.1, h4]
      · exact Finset.disjoint_insert_left.mpr ⟨ha, h6'⟩
  | neg => simp [facDeriv]

private lemma monoOk_deriv {S F : Finset (Fin N)} {a : Fin N} (ha : a ∉ F) (haS : a ∈ S) :
    ∀ {fs : List (GFac N)}, (∀ f ∈ fs, facOk S (insert a F) f) →
      ∀ t ∈ monoDeriv a fs, ∀ f' ∈ t, facOk S F f'
  | [], _, t, ht => by simp [monoDeriv] at ht
  | f :: fs, hfs, t, ht => by
    have hf := hfs f List.mem_cons_self
    have hrest : ∀ f' ∈ fs, facOk S (insert a F) f' :=
      fun f' hf' => hfs f' (List.mem_cons_of_mem f hf')
    simp only [monoDeriv, List.mem_append, List.mem_map] at ht
    rcases ht with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · intro f' hf'
      rcases List.mem_append.mp hf' with h | h
      · exact facOk_deriv ha haS hf s hs f' h
      · exact facOk_mono (Finset.subset_insert a F) (hrest f' h)
    · intro f' hf'
      rcases List.mem_cons.mp hf' with rfl | h
      · exact facOk_shift ha haS hf
      · exact monoOk_deriv ha haS hrest s hs f' h

/-- The alternating sum `Σ_{T ⊆ U} (-1)^{|T|} F(V ∪ T)`; `A^{S,U}` of (5.1) is its value at
`V = S \ U`. -/
private def gD (U : Finset (Fin N)) (F : Finset (Fin N) → ℂ) (V : Finset (Fin N)) : ℂ :=
  ∑ T ∈ U.powerset, ((-1 : ℤ) ^ T.card) • F (V ∪ T)

private lemma gD_empty (F : Finset (Fin N) → ℂ) (V : Finset (Fin N)) : gD ∅ F V = F V := by
  simp [gD]

private lemma gD_insert {U : Finset (Fin N)} {a : Fin N} (ha : a ∉ U) (F : Finset (Fin N) → ℂ)
    (V : Finset (Fin N)) :
    gD (insert a U) F V = gD U (fun V' => F V' - F (insert a V')) V := by
  unfold gD
  rw [Finset.sum_powerset_insert ha, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun T hT => ?_
  have haT : a ∉ T := fun h => ha (Finset.mem_powerset.mp hT h)
  rw [Finset.card_insert_of_notMem haT, Finset.union_insert, smul_sub, pow_succ]
  simp only [mul_neg, mul_one, neg_smul]
  abel

private lemma gD_congr {U : Finset (Fin N)} {F F' : Finset (Fin N) → ℂ} {V : Finset (Fin N)}
    (h : ∀ T ⊆ U, F (V ∪ T) = F' (V ∪ T)) : gD U F V = gD U F' V := by
  unfold gD
  exact Finset.sum_congr rfl fun T hT => by rw [h T (Finset.mem_powerset.mp hT)]

private lemma gD_listSum (U : Finset (Fin N)) (φ : List (GFac N) → Finset (Fin N) → ℂ)
    (V : Finset (Fin N)) :
    ∀ l : List (List (GFac N)),
      gD U (fun V' => (l.map (fun t => φ t V')).sum) V = (l.map (fun t => gD U (φ t) V)).sum
  | [] => by simp [gD]
  | t :: l => by
    rw [List.map_cons, List.sum_cons, ← gD_listSum U φ V l]
    simp [gD, Finset.sum_add_distrib, smul_add]

private lemma norm_listSum_le {ι : Type*} (f : ι → ℂ) :
    ∀ l : List ι, ‖(l.map f).sum‖ ≤ (l.map (fun t => ‖f t‖)).sum
  | [] => by simp
  | t :: l => by
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_listSum_le f l))

section Bound

variable {g : Finset (Fin N) → Fin N → Fin N → ℂ} {S : Finset (Fin N)} {A B : ℝ}
  (hoff : ∀ V ⊆ S, ∀ x y, x ∉ V → y ∉ V → x ≠ y → ‖g V x y‖ ≤ A)
  (hinv : ∀ V ⊆ S, ∀ x, x ∉ V → g V x x ≠ 0 ∧ ‖(g V x x)⁻¹‖ ≤ B)

include hoff hinv in
private lemma facEval_le {W : Finset (Fin N)} (hW : W ⊆ S) {f : GFac N} (hf : facOk S W f) :
    ‖facEval g W f‖ ≤ facW A B f := by
  cases f with
  | off x y X =>
    obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := hf
    exact hoff (W ∪ X) (Finset.union_subset hW h7) x y (by simp [h2, h4]) (by simp [h3, h5]) h1
  | inv x X =>
    obtain ⟨h2, h4, -, h7⟩ := hf
    exact (hinv (W ∪ X) (Finset.union_subset hW h7) x (by simp [h2, h4])).2
  | neg => simp [facEval, facW]

include hoff hinv in
private lemma monoEval_le {W : Finset (Fin N)} (hW : W ⊆ S) :
    ∀ {fs : List (GFac N)}, (∀ f ∈ fs, facOk S W f) → ‖monoEval g W fs‖ ≤ monoW A B fs
  | [], _ => by simp [monoEval, monoW]
  | f :: fs, hfs => by
    rw [monoEval_cons, monoW_cons, norm_mul]
    have h1 := facEval_le hoff hinv hW (hfs f List.mem_cons_self)
    have h2 := monoEval_le hW (fs := fs) fun f' hf' => hfs f' (List.mem_cons_of_mem f hf')
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)

include hinv in
private lemma facGood_of_ok {F V : Finset (Fin N)} {a : Fin N} (haS : a ∈ S) (hVF : V ⊆ F)
    (hVS : V ⊆ S) {f : GFac N} (hf : facOk S (insert a F) f) : facGood g a V f := by
  cases f with
  | off x y X =>
    obtain ⟨-, h2, h3, -⟩ := hf
    simp only [Finset.mem_insert, not_or] at h2 h3
    exact ⟨h2.1, h3.1⟩
  | inv x X =>
    obtain ⟨h2, h4, -, h7⟩ := hf
    simp only [Finset.mem_insert, not_or] at h2
    have hxV : x ∉ V := fun h => h2.2 (hVF h)
    refine ⟨h2.1, (hinv (V ∪ X) (Finset.union_subset hVS h7) x (by simp [hxV, h4])).1,
      (hinv _ (Finset.insert_subset haS (Finset.union_subset hVS h7)) x
        (by simp [hxV, h4, h2.1])).1⟩
  | neg => trivial

include hoff hinv in
/-- The bounds (5.75)–(5.76) of [15] on `Σ_{T ⊆ U} (-1)^{|T|} F(W ∪ T)` for a monomial `F`. -/
private lemma gD_monoEval_le
    (hg : ∀ V x y a, x ≠ a → y ≠ a → g V x y = g (insert a V) x y + g V x a * g V a y / g V a a)
    (hA : 0 ≤ A) (hB : 0 ≤ B) {l : ℝ} (h1 : A * B ≤ l) (h2 : A ^ 2 * B ^ 2 ≤ l)
    {W : Finset (Fin N)} (hWS : W ⊆ S) (U : Finset (Fin N)) :
    Disjoint W U → U ⊆ S → ∀ (L : ℝ) (fs : List (GFac N)), (∀ f ∈ fs, facOk S (W ∪ U) f) →
      (fs.length : ℝ) + 5 * U.card ≤ L →
        ‖gD U (fun V => monoEval g V fs) W‖ ≤ monoW A B fs * (l * L) ^ U.card := by
  have hl : 0 ≤ l := (mul_nonneg hA hB).trans h1
  induction U using Finset.induction_on with
  | empty =>
    intro _ _ L fs hok _
    rw [gD_empty, Finset.card_empty, pow_zero, mul_one]
    exact monoEval_le hoff hinv hWS fun f hf => by simpa using hok f hf
  | insert a U ha ih =>
    intro hdisj hUS L fs hok hL
    have haS : a ∈ S := hUS (Finset.mem_insert_self a U)
    have hUS' : U ⊆ S := (Finset.subset_insert a U).trans hUS
    have hdisj' : Disjoint W U := hdisj.mono_right (Finset.subset_insert a U)
    have haW : a ∉ W := fun h =>
      Finset.disjoint_left.mp hdisj h (Finset.mem_insert_self a U)
    have haF : a ∉ W ∪ U := by simp [haW, ha]
    have hok' : ∀ f ∈ fs, facOk S (insert a (W ∪ U)) f := by
      intro f hf
      have := hok f hf
      rwa [Finset.union_insert] at this
    have hcard : ((insert a U).card : ℝ) = U.card + 1 := by
      rw [Finset.card_insert_of_notMem ha]
      push_cast
      ring
    rw [gD_insert ha, gD_congr (F' := fun V => ((monoDeriv a fs).map (fun t => monoEval g V t)).sum)
      fun T hT => ?_]
    · rw [gD_listSum]
      have hL0 : (fs.length : ℝ) ≤ L := by
        rw [hcard] at hL
        have : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
        linarith
      have hpow : 0 ≤ (l * L) ^ U.card :=
        pow_nonneg (mul_nonneg hl ((Nat.cast_nonneg fs.length).trans hL0)) _
      calc ‖((monoDeriv a fs).map (fun t => gD U (fun V => monoEval g V t) W)).sum‖
          ≤ ((monoDeriv a fs).map (fun t => ‖gD U (fun V => monoEval g V t) W‖)).sum :=
            norm_listSum_le _ _
        _ ≤ ((monoDeriv a fs).map (fun t => monoW A B t * (l * L) ^ U.card)).sum := by
            refine List.sum_le_sum fun t ht => ih hdisj' hUS' L t
              (monoOk_deriv haF haS hok' t ht) ?_
            have h3 := monoDeriv_length a fs t ht
            have h4 : (t.length : ℝ) ≤ fs.length + 5 := by exact_mod_cast h3
            rw [hcard] at hL
            linarith
        _ = ((monoDeriv a fs).map (monoW A B)).sum * (l * L) ^ U.card :=
            List.sum_map_mul_right _ _ _
        _ ≤ (fs.length * l * monoW A B fs) * (l * L) ^ U.card :=
            mul_le_mul_of_nonneg_right (monoDeriv_weight hA hB h1 h2 a fs) hpow
        _ ≤ (L * l * monoW A B fs) * (l * L) ^ U.card := by
            refine mul_le_mul_of_nonneg_right ?_ hpow
            have := monoW_nonneg hA hB fs
            gcongr
        _ = monoW A B fs * (l * L) ^ (insert a U).card := by
            rw [Finset.card_insert_of_notMem ha, pow_succ]
            ring
    · have hTS : T ⊆ U := hT
      exact monoEval_sub hg fun f hf => facGood_of_ok hinv haS
        (Finset.union_subset_union le_rfl hTS)
        (Finset.union_subset hWS (hTS.trans hUS')) (hok' f hf)

end Bound

end Expansion

/-- The bound for `i ≠ j`: `C o (C² o (1 + 5m))^m ≤ (5 C² (m + 1) o)^(m + 1)`. -/
private lemma graded_arith_off {C o : ℝ} (hC : 1 ≤ C) (ho : 0 ≤ o) (m : ℕ) :
    C * o * 1 * (C ^ 2 * o * (1 + 5 * m)) ^ m ≤ (5 * C ^ 2 * (m + 1) * o) ^ (m + 1) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hC2 : C ≤ C ^ 2 := by nlinarith
  rw [show (5 * C ^ 2 * (m + 1) * o) ^ (m + 1) =
      (5 * C ^ 2 * (m + 1) * o) * (5 * C ^ 2 * (m + 1) * o) ^ m from pow_succ' _ _]
  have hK : 0 ≤ 5 * C ^ 2 * (m + 1) * o := by positivity
  have h1 : C * o * 1 ≤ 5 * C ^ 2 * (m + 1) * o := by
    rw [mul_one]
    exact mul_le_mul_of_nonneg_right (by nlinarith) ho
  have h2 : (C ^ 2 * o * (1 + 5 * m)) ^ m ≤ (5 * C ^ 2 * (m + 1) * o) ^ m := by
    refine pow_le_pow_left₀ (by positivity) ?_ m
    have : 0 ≤ C ^ 2 * o := by positivity
    nlinarith
  exact mul_le_mul h1 h2 (by positivity) hK

/-- The bound for `i = j`, `|U| = m + 1`:
`C³ o² (C² o (3 + 5m))^m ≤ (5 C² (m + 2) o)^(m + 2)`. -/
private lemma graded_arith_diag {C o : ℝ} (hC : 1 ≤ C) (ho : 0 ≤ o) (m : ℕ) :
    C * o * (C * o * (C * 1)) * (C ^ 2 * o * (3 + 5 * m)) ^ m ≤
      (5 * C ^ 2 * (((m + 1 : ℕ) : ℝ) + 1) * o) ^ (m + 1 + 1) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hC2 : C ≤ C ^ 2 := by nlinarith
  push_cast
  set K := 5 * C ^ 2 * ((m : ℝ) + 1 + 1) * o with hKdef
  have hK : 0 ≤ K := by positivity
  rw [show K ^ (m + 1 + 1) = K * (K * K ^ m) by ring]
  have h1 : C * o ≤ K := mul_le_mul_of_nonneg_right (by nlinarith) ho
  have h1' : C * o * (C * 1) ≤ K := by
    rw [mul_one, mul_comm, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (by nlinarith) ho
  have h2 : (C ^ 2 * o * (3 + 5 * m)) ^ m ≤ K ^ m := by
    refine pow_le_pow_left₀ (by positivity) ?_ m
    have : 0 ≤ C ^ 2 * o := by positivity
    rw [hKdef]
    nlinarith
  have h3 : C * o * (C * o * (C * 1)) ≤ K * K :=
    mul_le_mul h1 h1' (by positivity) hK
  calc C * o * (C * o * (C * 1)) * (C ^ 2 * o * (3 + 5 * m)) ^ m ≤ (K * K) * K ^ m :=
        mul_le_mul h3 h2 (by positivity) (by positivity)
    _ = K * (K * K ^ m) := by ring

/-- (5.73) of [15] with exponent `u = |U| + 1`, and (5.72) off the diagonal (`U = ∅`, `i ≠ j`);
(5.71) is read as `|S|(o + d) ≤ c1`. -/
theorem norm_gradedTerm_resolventC_le : ∃ c1 > 0, ∃ C > 0, ∀ {N : ℕ}
    {H : Matrix (Fin N) (Fin N) ℝ}, H.IsHermitian → ∀ {z : ℂ}, |z.re| ≤ 5 → 0 < z.im →
    z.im ≤ 10 → ∀ (o d : ℝ) (S U : Finset (Fin N)), 0 ≤ o →
    (∀ i j, i ≠ j → ‖resolventC H z i j‖ ≤ o) → (∀ i, ‖resolventC H z i i - msc z‖ ≤ d) →
    o + d ≤ c1 → (S.card : ℝ) * (o + d) ≤ c1 → U ⊆ S → ∀ i j, i ∉ S → j ∉ S →
      (U.Nonempty ∨ i ≠ j) →
      ‖gradedTerm (fun V => resolventC (zeroRC V H) z i j) S U‖ ≤
        (C * (U.card + 1) * o) ^ (U.card + 1) := by
  obtain ⟨c1, hc1, C, hC, hT1⟩ := resolventC_zeroRC_sub_le
  have hC0 : 0 < C := by linarith
  refine ⟨min c1 (C ^ 2)⁻¹, lt_min hc1 (by positivity), 5 * C ^ 2, by positivity, ?_⟩
  intro N H hH z hre hz hz' o d S U ho hoff hdiag hod hS hUS i j hi hj hne
  have hd : 0 ≤ d := (norm_nonneg _).trans (hdiag i)
  have hod1 : o + d ≤ c1 := hod.trans (min_le_left _ _)
  have hoC : C ^ 2 * o ≤ 1 := by
    have h1 : o ≤ (C ^ 2)⁻¹ := by linarith [min_le_right c1 (C ^ 2)⁻¹]
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg C)
    rwa [mul_inv_cancel₀ (by positivity)] at h2
  have hVS : ∀ V ⊆ S, (V.card : ℝ) * (o + d) ≤ c1 := by
    intro V hV
    have h1 : (V.card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card hV
    have h2 : (S.card : ℝ) * (o + d) ≤ c1 := hS.trans (min_le_left _ _)
    nlinarith
  set g : Finset (Fin N) → Fin N → Fin N → ℂ := fun V x y => resolventC (zeroRC V H) z x y
    with hgdef
  have hg : ∀ V x y a, x ≠ a → y ≠ a →
      g V x y = g (insert a V) x y + g V x a * g V a y / g V a a :=
    fun V x y a hx hy => graded_step hH hz V hx hy
  have hoff' : ∀ V ⊆ S, ∀ x y, x ∉ V → y ∉ V → x ≠ y → ‖g V x y‖ ≤ C * o := by
    intro V hV x y hx hy hxy
    have h := (hT1 hH hre hz hz' o d V ho hoff hdiag hod1 (hVS V hV) x y hx hy).1
    simpa [hxy] using h
  have hinv' : ∀ V ⊆ S, ∀ x, x ∉ V → g V x x ≠ 0 ∧ ‖(g V x x)⁻¹‖ ≤ C := by
    intro V hV x hx
    have h := (hT1 hH hre hz hz' o d V ho hoff hdiag hod1 (hVS V hV) x x hx hx).2
    have hpos : 0 < ‖g V x x‖ := lt_of_lt_of_le (by positivity) h
    refine ⟨norm_pos_iff.mp hpos, ?_⟩
    rw [norm_inv]
    exact inv_le_of_inv_le₀ hC0 h
  have hA : 0 ≤ C * o := by positivity
  have hB : 0 ≤ C := hC0.le
  have h1 : C * o * C ≤ C ^ 2 * o := by nlinarith
  have h2 : (C * o) ^ 2 * C ^ 2 ≤ C ^ 2 * o := by
    have : 0 ≤ C ^ 2 * o := by positivity
    nlinarith
  have hWS : S \ U ⊆ S := Finset.sdiff_subset
  have hdisj : Disjoint (S \ U) U := Finset.sdiff_disjoint
  have hWU : S \ U ∪ U = S := Finset.sdiff_union_of_subset hUS
  have hgt : gradedTerm (fun V => resolventC (zeroRC V H) z i j) S U =
      gD U (fun V => g V i j) (S \ U) := rfl
  rw [hgt]
  by_cases hij : i = j
  · subst hij
    obtain ⟨a, haU⟩ := hne.resolve_right (fun h => h rfl)
    have hU : insert a (U.erase a) = U := Finset.insert_erase haU
    have haU' : a ∉ U.erase a := Finset.notMem_erase a U
    have haS : a ∈ S := hUS haU
    have hia : i ≠ a := fun h => hi (h ▸ haS)
    have hcard : (U.erase a).card + 1 = U.card := Finset.card_erase_add_one haU
    have hstep := gD_insert haU' (fun V => g V i i) (S \ U)
    rw [hU] at hstep
    rw [hstep, gD_congr (F' := fun V => monoEval g V [.off i a ∅, .off a i ∅, .inv a ∅])
      fun T _ => ?_]
    · have hok : ∀ f ∈ [GFac.off i a ∅, .off a i ∅, .inv a ∅],
          facOk S (S \ U ∪ U.erase a) f := by
        have hiF : i ∉ S \ U ∪ U.erase a := fun h => hi (by
          rcases Finset.mem_union.mp h with h | h
          · exact Finset.sdiff_subset h
          · exact hUS (Finset.erase_subset a U h))
        have haF : a ∉ S \ U ∪ U.erase a := by simp [haU]
        intro f hf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl
        · exact ⟨hia, hiF, haF, by simp, by simp, by simp, by simp⟩
        · exact ⟨Ne.symm hia, haF, hiF, by simp, by simp, by simp, by simp⟩
        · exact ⟨haF, by simp, by simp, by simp⟩
      have hb := gD_monoEval_le hoff' hinv' hg hA hB h1 h2 hWS (U.erase a)
        (hdisj.mono_right (Finset.erase_subset a U)) ((Finset.erase_subset a U).trans hUS)
        (3 + 5 * (U.erase a).card) _ hok (by simp)
      have hw : monoW (C * o) C [GFac.off i a ∅, .off a i ∅, .inv a ∅] =
          C * o * (C * o * (C * 1)) := by simp [monoW, facW]
      rw [hw] at hb
      refine hb.trans ?_
      rw [← hcard]
      exact graded_arith_diag hC ho _
    · simp only [monoEval, facEval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        Finset.union_empty]
      rw [hg _ i i a hia hia]
      ring
  · rw [gD_congr (F' := fun V => monoEval g V [.off i j ∅]) fun T _ => by
      simp [monoEval, facEval]]
    have hok : ∀ f ∈ [GFac.off i j ∅], facOk S (S \ U ∪ U) f := by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf
      rw [hWU]
      exact ⟨hij, hi, hj, by simp, by simp, by simp, by simp⟩
    have hb := gD_monoEval_le hoff' hinv' hg hA hB h1 h2 hWS U hdisj hUS
      (1 + 5 * U.card) _ hok (by simp)
    have hw : monoW (C * o) C [GFac.off i j ∅] = C * o * 1 := by simp [monoW, facW]
    rw [hw] at hb
    exact hb.trans (graded_arith_off hC ho U.card)

/-! ### A nondegenerate point for both statements

`N = 4^n`, `H = (4/5) 2^{-n} R^{⊗ 2n}` with `R = [[1, 1], [1, -1]]`, so that `H² = 16/25` and
every entry of `H` has modulus `(4/5) 2^{-n}`. At `z = (16/15) i` one has `m_sc(z) = (3/5) i`
and `G = (9/16)(H + z)`, so that `o = d = (9/20) 2^{-n}`; `n` is chosen from `c1`. -/

/-- The entries of `R = [[1, 1], [1, -1]]`. -/
private def gradedSgn (x y : Fin 2) : ℝ := if x = 1 ∧ y = 1 then -1 else 1

private lemma gradedSgn_sum (x y : Fin 2) :
    ∑ w, gradedSgn x w * gradedSgn w y = if x = y then 2 else 0 := by
  fin_cases x <;> fin_cases y <;> norm_num [gradedSgn, Fin.sum_univ_two]

private lemma abs_prod_gradedSgn {n : ℕ} (x y : Fin n → Fin 2) :
    |∏ l, gradedSgn (x l) (y l)| = 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_eq_one fun l _ => by unfold gradedSgn; split_ifs <;> norm_num

/-- `(4/5) 2^{-n} R^{⊗ 2n}`, indexed by `Fin (2n) → Fin 2`. -/
private def gradedK (n : ℕ) : Matrix (Fin (2 * n) → Fin 2) (Fin (2 * n) → Fin 2) ℝ :=
  fun x y => 4 / 5 * ((2 : ℝ) ^ n)⁻¹ * ∏ l, gradedSgn (x l) (y l)

private lemma gradedK_mul (n : ℕ) : gradedK n * gradedK n = (16 / 25 : ℝ) • 1 := by
  ext x y
  simp only [Matrix.mul_apply, gradedK, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have h : ∀ w : Fin (2 * n) → Fin 2,
      4 / 5 * ((2 : ℝ) ^ n)⁻¹ * (∏ l, gradedSgn (x l) (w l)) *
        (4 / 5 * ((2 : ℝ) ^ n)⁻¹ * ∏ l, gradedSgn (w l) (y l)) =
      (16 / 25 * ((2 : ℝ) ^ n)⁻¹ ^ 2) * ∏ l, (gradedSgn (x l) (w l) * gradedSgn (w l) (y l)) := by
    intro w
    rw [Finset.prod_mul_distrib]
    ring
  rw [Finset.sum_congr rfl fun w _ => h w, ← Finset.mul_sum,
    ← Fintype.prod_sum (fun l (w : Fin 2) => gradedSgn (x l) w * gradedSgn w (y l))]
  simp only [gradedSgn_sum]
  by_cases hxy : x = y
  · subst hxy
    simp only [↓reduceIte, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_one]
    have h4 : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [pow_mul, show ((2 : ℝ) ^ 2) = 4 by norm_num, h4]
    field_simp
  · obtain ⟨l, hl⟩ : ∃ l, x l ≠ y l := by
      by_contra h
      push Not at h
      exact hxy (funext h)
    rw [Finset.prod_eq_zero (Finset.mem_univ l) (by simp [hl])]
    simp [hxy]

/-- `gradedK n` reindexed by `Fin (2^(2n))`. -/
private def gradedH (n : ℕ) : Matrix (Fin (2 ^ (2 * n))) (Fin (2 ^ (2 * n))) ℝ :=
  (gradedK n).submatrix finFunctionFinEquiv.symm finFunctionFinEquiv.symm

private lemma gradedH_isHermitian (n : ℕ) : (gradedH n).IsHermitian := by
  refine Matrix.IsHermitian.ext fun a b => ?_
  simp only [gradedH, Matrix.submatrix_apply, gradedK, star_trivial]
  congr 1
  exact Finset.prod_congr rfl fun l _ => by unfold gradedSgn; simp [and_comm]

private lemma gradedH_mul (n : ℕ) : gradedH n * gradedH n = (16 / 25 : ℝ) • 1 := by
  rw [gradedH, Matrix.submatrix_mul_equiv, gradedK_mul]
  ext a b
  simp [Matrix.one_apply]

private lemma abs_gradedH (n : ℕ) (a b : Fin (2 ^ (2 * n))) :
    |gradedH n a b| = 4 / 5 * ((2 : ℝ) ^ n)⁻¹ := by
  simp only [gradedH, Matrix.submatrix_apply, gradedK, abs_mul, abs_prod_gradedSgn, mul_one]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 4 / 5),
    abs_of_pos (by positivity : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹)]

/-- `G = (9/16)(H + z)` at `z = (16/15) i`. -/
private lemma gradedH_resolventC (n : ℕ) :
    resolventC (gradedH n) ((16 / 15 : ℂ) * Complex.I) =
      (9 / 16 : ℂ) • ((gradedH n).map (fun x : ℝ => (x : ℂ)) +
        ((16 / 15 : ℂ) * Complex.I) • (1 : Matrix (Fin (2 ^ (2 * n))) (Fin (2 ^ (2 * n))) ℂ)) := by
  unfold resolventC
  apply Matrix.inv_eq_right_inv
  set Hc := (gradedH n).map (fun x : ℝ => (x : ℂ)) with hHcdef
  have hHc : Hc * Hc = (16 / 25 : ℂ) • 1 := by
    have h2 : ((gradedH n) * (gradedH n)).map Complex.ofRealHom =
        ((16 / 25 : ℝ) • (1 : Matrix (Fin (2 ^ (2 * n))) (Fin (2 ^ (2 * n))) ℝ)).map
          Complex.ofRealHom := by
      rw [gradedH_mul]
    rw [Matrix.map_mul] at h2
    convert h2 using 1
    ext a b
    simp only [Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply, smul_eq_mul]
    split_ifs <;> simp
  set z : ℂ := (16 / 15 : ℂ) * Complex.I with hz
  have hzz : z * z = -(256 / 225 : ℂ) := by
    rw [hz]
    ring_nf
    rw [Complex.I_sq]
    ring
  calc (Hc - z • 1) * ((9 / 16 : ℂ) • (Hc + z • 1))
      = (9 / 16 : ℂ) • (Hc * Hc - (z * z) • 1) := by
        simp only [Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul,
          Matrix.one_mul, Matrix.mul_one]
        module
    _ = 1 := by
        rw [hHc, hzz, ← sub_smul, smul_smul]
        norm_num

private lemma graded_msc : msc ((16 / 15 : ℂ) * Complex.I) = (3 / 5 : ℂ) * Complex.I := by
  symm
  apply eq_msc_of_add_inv
  · simp
  · rw [show (16 / 15 : ℂ) * Complex.I + 3 / 5 * Complex.I = (5 / 3 : ℂ) * Complex.I by ring,
      mul_inv, Complex.inv_I]
    ring
  · simp

/-- For every `c > 0` the point above meets the hypotheses of both statements with
`o + d ≤ c`. -/
private lemma graded_witness {c : ℝ} (hc : 0 < c) :
    ∃ (N : ℕ) (H : Matrix (Fin N) (Fin N) ℝ) (o : ℝ) (a b u : Fin N), 4 ≤ N ∧ H.IsHermitian ∧
      0 < o ∧ o + o ≤ c ∧ a ≠ b ∧ a ≠ u ∧ b ≠ u ∧
      (∀ i j, i ≠ j → ‖resolventC H ((16 / 15 : ℂ) * Complex.I) i j‖ ≤ o) ∧
      (∀ i, ‖resolventC H ((16 / 15 : ℂ) * Complex.I) i i -
        msc ((16 / 15 : ℂ) * Complex.I)‖ ≤ o) := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt c⁻¹ (by norm_num : (1 : ℝ) < 2)
  have hN : 4 ≤ 2 ^ (2 * (k + 1)) :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * (k + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow : ((2 : ℝ) ^ (k + 1))⁻¹ < c := by
    rw [inv_lt_comm₀ (by positivity) hc, pow_succ]
    linarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]
  refine ⟨2 ^ (2 * (k + 1)), gradedH (k + 1), 9 / 20 * ((2 : ℝ) ^ (k + 1))⁻¹,
    ⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, hN, gradedH_isHermitian (k + 1),
    by positivity, by linarith, by simp [Fin.ext_iff], by simp [Fin.ext_iff],
    by simp [Fin.ext_iff], ?_, ?_⟩
  · intro i j hij
    rw [gradedH_resolventC]
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.map_apply, Matrix.one_apply, hij,
      ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_gradedH]
    norm_num
    ring_nf
    rfl
  · intro i
    rw [gradedH_resolventC, graded_msc]
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.map_apply, Matrix.one_apply,
      ↓reduceIte, smul_eq_mul]
    rw [show (9 / 16 : ℂ) * ((gradedH (k + 1) i i : ℂ) + 16 / 15 * Complex.I * 1) -
        3 / 5 * Complex.I = (9 / 16 : ℂ) * (gradedH (k + 1) i i : ℂ) by ring]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_gradedH]
    norm_num
    ring_nf
    rfl

example : ∃ c1 > 0, ∃ C ≥ (1 : ℝ), ∃ (N : ℕ) (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (o d : ℝ)
    (U : Finset (Fin N)) (i j : Fin N), 4 ≤ N ∧ H.IsHermitian ∧ |z.re| ≤ 5 ∧ 0 < z.im ∧
      z.im ≤ 10 ∧ 0 < o ∧ 0 < d ∧ (∀ i j, i ≠ j → ‖resolventC H z i j‖ ≤ o) ∧
      (∀ i, ‖resolventC H z i i - msc z‖ ≤ d) ∧ o + d ≤ c1 ∧ (U.card : ℝ) * (o + d) ≤ c1 ∧
      U.Nonempty ∧ i ∉ U ∧ j ∉ U ∧ i ≠ j ∧
      (‖resolventC (zeroRC U H) z i j - (if i = j then msc z else 0)‖ ≤
          C * ((if i = j then d else 0) + o) ∧
        C⁻¹ ≤ ‖resolventC (zeroRC U H) z i i‖) := by
  obtain ⟨c1, hc1, C, hC, h⟩ := resolventC_zeroRC_sub_le
  obtain ⟨N, H, o, a, b, u, hN, hH, ho, hoc, hab, hau, hbu, hoff, hdiag⟩ := graded_witness hc1
  have hz1 : |((16 / 15 : ℂ) * Complex.I).re| ≤ 5 := by simp
  have hz2 : 0 < ((16 / 15 : ℂ) * Complex.I).im := by norm_num
  have hz3 : ((16 / 15 : ℂ) * Complex.I).im ≤ 10 := by norm_num
  have hU : (({u} : Finset (Fin N)).card : ℝ) * (o + o) ≤ c1 := by simpa using hoc
  have hau' : a ∉ ({u} : Finset (Fin N)) := by simpa using hau
  have hbu' : b ∉ ({u} : Finset (Fin N)) := by simpa using hbu
  exact ⟨c1, hc1, C, hC, N, H, _, o, o, {u}, a, b, hN, hH, hz1, hz2, hz3, ho, ho, hoff, hdiag,
    hoc, hU, by simp, hau', hbu', hab,
    h hH hz1 hz2 hz3 o o {u} ho.le hoff hdiag hoc hU a b hau' hbu'⟩

example : ∃ c1 > 0, ∃ C > (0 : ℝ), ∃ (N : ℕ) (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (o d : ℝ)
    (S U : Finset (Fin N)) (i j : Fin N), 4 ≤ N ∧ H.IsHermitian ∧ |z.re| ≤ 5 ∧ 0 < z.im ∧
      z.im ≤ 10 ∧ 0 < o ∧ 0 < d ∧ (∀ i j, i ≠ j → ‖resolventC H z i j‖ ≤ o) ∧
      (∀ i, ‖resolventC H z i i - msc z‖ ≤ d) ∧ o + d ≤ c1 ∧ (S.card : ℝ) * (o + d) ≤ c1 ∧
      U ⊆ S ∧ U.Nonempty ∧ i ∉ S ∧ j ∉ S ∧ i ≠ j ∧
      ‖gradedTerm (fun V => resolventC (zeroRC V H) z i j) S U‖ ≤
        (C * (U.card + 1) * o) ^ (U.card + 1) := by
  obtain ⟨c1, hc1, C, hC, h⟩ := norm_gradedTerm_resolventC_le
  obtain ⟨N, H, o, a, b, u, hN, hH, ho, hoc, hab, hau, hbu, hoff, hdiag⟩ := graded_witness hc1
  have hz1 : |((16 / 15 : ℂ) * Complex.I).re| ≤ 5 := by simp
  have hz2 : 0 < ((16 / 15 : ℂ) * Complex.I).im := by norm_num
  have hz3 : ((16 / 15 : ℂ) * Complex.I).im ≤ 10 := by norm_num
  have hS : (({u} : Finset (Fin N)).card : ℝ) * (o + o) ≤ c1 := by simpa using hoc
  have hau' : a ∉ ({u} : Finset (Fin N)) := by simpa using hau
  have hbu' : b ∉ ({u} : Finset (Fin N)) := by simpa using hbu
  exact ⟨c1, hc1, C, hC, N, H, _, o, o, {u}, {u}, a, b, hN, hH, hz1, hz2, hz3, ho, ho, hoff,
    hdiag, hoc, hS, le_rfl, by simp, hau', hbu', hab,
    h hH hz1 hz2 hz3 o o {u} {u} ho.le hoff hdiag hoc hS le_rfl a b hau' hbu' (Or.inr hab)⟩

#print axioms resolventC_zeroRC_sub_le
#print axioms norm_gradedTerm_resolventC_le

end WEdgeNS
