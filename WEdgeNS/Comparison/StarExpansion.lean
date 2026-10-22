import WEdgeNS.Comparison.Monomial
import WEdgeNS.Resolvent.Expansion

/-!
# Expansions of resolvent words in one matrix entry
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-! ### Products with `I_γ` -/

/-- The complex matrix `I_γ` of (6.10) is the sum of the matrix units at the pairs of `e`. -/
private lemma starExpansion_entryMat_eq_sum {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    (entryMat e).map (fun x : ℝ => (x : ℂ)) =
      ((entryPairs e).map fun xy => Matrix.single xy.1 xy.2 (1 : ℂ)).sum := by
  rcases e with a | ⟨⟨a, b⟩, hab⟩
  · ext x y
    simp only [entryMat, entryPairs, Matrix.map_apply, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, Matrix.single_apply, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false]
    split_ifs <;> aesop
  · ext x y
    simp only [entryMat, entryPairs, Matrix.map_apply, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, Matrix.add_apply, Matrix.single_apply, List.mem_cons,
      Prod.mk.injEq, List.not_mem_nil, or_false]
    have hne : a ≠ b := ne_of_lt hab
    split_ifs <;> aesop

/-- Entry `(i, j)` of `A I_γ B` is the sum of `A_{ix} B_{yj}` over the pairs `(x, y)` of `e`. -/
private lemma starExpansion_mul_entryMat_mul_apply {N : ℕ} (e : Fin N ⊕ OffDiag N)
    (A B : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    (A * (entryMat e).map (fun x : ℝ => (x : ℂ)) * B) i j =
      ((entryPairs e).map fun xy => A i xy.1 * B xy.2 j).sum := by
  rw [starExpansion_entryMat_eq_sum]
  generalize entryPairs e = L
  induction L with
  | nil => simp
  | cons xy t ih =>
    rw [List.map_cons, List.sum_cons, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, ih,
      List.map_cons, List.sum_cons]
    congr 1
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

/-- If `|A_xy| ≤ a` and `|B_yj| ≤ β` for all `x, y`, then `|(A I_γ B)_ij| ≤ 2 a β`. -/
private lemma starExpansion_norm_mul_entryMat_mul_apply_le {N : ℕ} (e : Fin N ⊕ OffDiag N)
    {A B : Matrix (Fin N) (Fin N) ℂ} {a β : ℝ} (ha : 0 ≤ a) (hA : ∀ x y, ‖A x y‖ ≤ a)
    (j : Fin N) (hB : ∀ y, ‖B y j‖ ≤ β) (i : Fin N) :
    ‖(A * (entryMat e).map (fun x : ℝ => (x : ℂ)) * B) i j‖ ≤ 2 * a * β := by
  have hβ : 0 ≤ β := (norm_nonneg _).trans (hB i)
  rw [starExpansion_mul_entryMat_mul_apply]
  have h := norm_list_sum_le_length_mul (entryPairs e) (fun xy => A i xy.1 * B xy.2 j)
    (a * β) (fun xy _ => by rw [norm_mul]; exact mul_le_mul (hA _ _) (hB _) (norm_nonneg _) ha)
  have hl : ((entryPairs e).length : ℝ) ≤ 2 := by
    have : (entryPairs e).length ≤ 2 := by cases e <;> simp [entryPairs]
    exact_mod_cast this
  calc _ ≤ _ := h
    _ ≤ 2 * (a * β) := mul_le_mul_of_nonneg_right hl (mul_nonneg ha hβ)
    _ = 2 * a * β := by ring

/-- If `|R_xy| ≤ a` and `|S_xy| ≤ b`, every entry of `(R I_γ)^n S` is at most `(2a)^n b`. -/
private lemma starExpansion_norm_pow_mul_apply_le {N : ℕ} (e : Fin N ⊕ OffDiag N)
    {R S : Matrix (Fin N) (Fin N) ℂ} {a b : ℝ} (ha : 0 ≤ a) (hR : ∀ x y, ‖R x y‖ ≤ a)
    (hS : ∀ x y, ‖S x y‖ ≤ b) (n : ℕ) (i j : Fin N) :
    ‖((R * (entryMat e).map (fun x : ℝ => (x : ℂ))) ^ n * S) i j‖ ≤ (2 * a) ^ n * b := by
  induction n generalizing i with
  | zero => simpa using hS i j
  | succ n ih =>
    rw [pow_succ', Matrix.mul_assoc]
    calc _ ≤ 2 * a * ((2 * a) ^ n * b) :=
          starExpansion_norm_mul_entryMat_mul_apply_le e ha hR j (fun y => ih y) i
      _ = (2 * a) ^ (n + 1) * b := by ring

/-! ### Evaluation of formal words -/

/-- The chains of `k` steps with letters of kind `κ` evaluate to `((A I_γ)^k A)_ij`, where
`A_xy` is the value of the letter of kind `κ` at `(x, y)` (6.12). -/
private lemma starExpansion_evalW_starWords {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ)
    (e : Fin N ⊕ OffDiag N) (κ : LetterKind) (k : ℕ) (i j : Fin N) :
    evalW G m (starWords e κ k i j) =
      ((Matrix.of (fun x y => evalLetter G m ⟨κ, x, y⟩) *
          (entryMat e).map (fun x : ℝ => (x : ℂ))) ^ k *
        Matrix.of (fun x y => evalLetter G m ⟨κ, x, y⟩)) i j := by
  induction k generalizing i with
  | zero => simp [starWords, evalW, evalWord]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_assoc, starExpansion_mul_entryMat_mul_apply]
    simp only [starWords]
    rw [evalW_flatMap]
    congr 1
    refine List.map_congr_left fun xy _ => ?_
    rw [← ih xy.2]
    simp only [evalW, List.map_map, Function.comp_def, evalWord, List.map_cons, List.prod_cons]
    rw [List.sum_map_mul_left]
    rfl

/-- Entrywise conjugation commutes with `(G I_γ)^k G`, since `I_γ` is real. -/
private lemma starExpansion_star_pow_mul_apply {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ)
    (e : Fin N ⊕ OffDiag N) (k : ℕ) (i j : Fin N) :
    ((G.map star * (entryMat e).map (fun x : ℝ => (x : ℂ))) ^ k * G.map star) i j =
      star (((G * (entryMat e).map (fun x : ℝ => (x : ℂ))) ^ k * G) i j) := by
  set I := (entryMat e).map (fun x : ℝ => (x : ℂ)) with hIdef
  have hI : I.map (starRingEnd ℂ) = I := by
    ext x y
    simp [hIdef]
  have hG : G.map star = G.map (starRingEnd ℂ) := rfl
  have h : ((G * I) ^ k * G).map (starRingEnd ℂ) =
      (G.map (starRingEnd ℂ) * I) ^ k * G.map (starRingEnd ℂ) := by
    rw [← RingHom.mapMatrix_apply, map_mul, map_pow, map_mul, RingHom.mapMatrix_apply,
      RingHom.mapMatrix_apply, hI]
  rw [hG, ← h]
  simp

/-- `P_{γ,k} G_ij` evaluates to `((G I_γ)^k G)_ij`, i.e. `(G^{*(k+1)})_ij` (6.12)–(6.13). -/
theorem evalW_letterP_g {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ)
    (e : Fin N ⊕ OffDiag N) (k : ℕ) (i j : Fin N) :
    evalW G m (letterP e k ⟨.g, i, j⟩) =
      ((G * (entryMat e).map (fun x : ℝ => (x : ℂ))) ^ k * G) i j := by
  by_cases hk : k = 0
  · subst hk
    simp [letterP, evalW, evalWord, evalLetter]
  · have hL : letterP e k ⟨.g, i, j⟩ = starWords e .g k i j := by
      simp [letterP, hk, LetterKind.plain]
    rw [hL, starExpansion_evalW_starWords]
    rfl

/-- (6.13), (6.17) for every letter kind: `P_{γ,k}` of a letter evaluates to the same
letter of `(G I_γ)^k G`, centred (with `m`) only when `k = 0`. -/
theorem evalW_letterP {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (m : ℂ)
    (e : Fin N ⊕ OffDiag N) (k : ℕ) (ℓ : Letter N) :
    evalW G m (letterP e k ℓ) =
      evalLetter ((G * (entryMat e).map (fun x : ℝ => (x : ℂ))) ^ k * G)
        (if k = 0 then m else 0) ℓ := by
  by_cases hk : k = 0
  · subst hk
    simp [letterP, evalW, evalWord]
  · have hL : letterP e k ℓ = starWords e ℓ.kind.plain k ℓ.i ℓ.j := by simp [letterP, hk]
    rw [hL, starExpansion_evalW_starWords, ite_eq_right_iff.mpr (fun h => absurd h hk)]
    rcases ℓ with ⟨κ, i, j⟩
    cases κ
    · rfl
    · exact starExpansion_star_pow_mul_apply G e k i j
    · simp only [LetterKind.plain, evalLetter, ite_self, sub_zero]
      rfl
    · simp only [LetterKind.plain, evalLetter, ite_self, sub_zero]
      exact starExpansion_star_pow_mul_apply G e k i j

/-- `v I_γ` is real symmetric. -/
private lemma starExpansion_isHermitian_smul_entryMat {N : ℕ} (e : Fin N ⊕ OffDiag N) (v : ℝ) :
    (v • entryMat e).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, star_trivial, entryMat]
  congr 1
  rcases e with a | ⟨⟨a, b⟩, hab⟩ <;>
    simp only [entryPairs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] <;>
    exact if_congr (by tauto) rfl rfl

/-- (3.30), (6.47) entrywise for `V = v I_γ`:
`S_ij = Σ_{k ≤ n} (-v)^k ((R I_γ)^k R)_ij + (-v)^{n+1} ((R I_γ)^{n+1} S)_ij`. -/
private lemma starExpansion_resolventC_add_apply {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Q.IsHermitian) (e : Fin N ⊕ OffDiag N) (v : ℝ) {z : ℂ} (hz : 0 < z.im) (n : ℕ)
    (i j : Fin N) :
    resolventC (Q + v • entryMat e) z i j =
      ∑ k ∈ Finset.range (n + 1), (((-v) ^ k : ℝ) : ℂ) *
          ((resolventC Q z * (entryMat e).map (fun x : ℝ => (x : ℂ))) ^ k * resolventC Q z) i j +
        (((-v) ^ (n + 1) : ℝ) : ℂ) *
          ((resolventC Q z * (entryMat e).map (fun x : ℝ => (x : ℂ))) ^ (n + 1) *
            resolventC (Q + v • entryMat e) z) i j := by
  have hexp := resolventC_expansion_right hQ (starExpansion_isHermitian_smul_entryMat e v) hz n
  have hVc : (v • entryMat e).map (fun x : ℝ => (x : ℂ)) =
      (v : ℂ) • (entryMat e).map (fun x : ℝ => (x : ℂ)) := by
    ext x y
    simp
  rw [hVc, Matrix.mul_smul, ← neg_smul] at hexp
  simp only [smul_pow, Matrix.smul_mul] at hexp
  have h := congrFun (congrFun hexp i) j
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h
  rw [h]
  push_cast
  rfl

/-- (6.47)–(6.50) for one letter, as an exact identity: for `H = Q + v I_γ`,
`ℓ((H - z)⁻¹) = Σ_{k ≤ n} (-v)^k P_{γ,k} ℓ((Q - z)⁻¹) + (-v)^{n+1} ℓ((R I_γ)^{n+1} S)`. -/
theorem evalLetter_resolventC_add_eq {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Q.IsHermitian) (e : Fin N ⊕ OffDiag N) (v : ℝ) {z : ℂ} (hz : 0 < z.im) (m : ℂ)
    (n : ℕ) (ℓ : Letter N) :
    evalLetter (resolventC (Q + v • entryMat e) z) m ℓ =
      ∑ k ∈ Finset.range (n + 1),
          (((-v) ^ k : ℝ) : ℂ) * evalW (resolventC Q z) m (letterP e k ℓ) +
        (((-v) ^ (n + 1) : ℝ) : ℂ) *
          evalLetter ((resolventC Q z * (entryMat e).map (fun x : ℝ => (x : ℂ))) ^ (n + 1) *
            resolventC (Q + v • entryMat e) z) 0 ℓ := by
  have hent := starExpansion_resolventC_add_apply hQ e v hz n
  set I := (entryMat e).map (fun x : ℝ => (x : ℂ))
  set R := resolventC Q z
  set S := resolventC (Q + v • entryMat e) z
  rcases ℓ with ⟨κ, i, j⟩
  have hc : ∀ (k : ℕ) (r : ℂ), (if i = j then (if k = 0 then r else 0) else 0) =
      if k = 0 then (if i = j then r else 0) else 0 := by
    intro k r
    split_ifs <;> rfl
  have hgc : S i j - (if i = j then m else 0) =
      ∑ k ∈ Finset.range (n + 1), (((-v) ^ k : ℝ) : ℂ) *
          (((R * I) ^ k * R) i j - if i = j then (if k = 0 then m else 0) else 0) +
        (((-v) ^ (n + 1) : ℝ) : ℂ) * (((R * I) ^ (n + 1) * S) i j - if i = j then 0 else 0) := by
    rw [hent i j]
    simp only [hc, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_range, ite_self, sub_zero]
    simp only [Nat.zero_lt_succ, ↓reduceIte, pow_zero, Complex.ofReal_one, one_mul]
    ring
  simp only [evalW_letterP]
  cases κ
  · exact hent i j
  · simp only [evalLetter]
    rw [hent i j]
    simp [star_sum, Complex.conj_ofReal]
    rfl
  · simp only [evalLetter]
    exact hgc
  · simp only [evalLetter]
    rw [hgc]
    simp [star_sum, Complex.conj_ofReal]
    rfl

/-- A letter at centring `0` has the modulus of its entry. -/
private lemma starExpansion_norm_evalLetter_zero {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ)
    (ℓ : Letter N) : ‖evalLetter M 0 ℓ‖ = ‖M ℓ.i ℓ.j‖ := by
  rcases ℓ with ⟨κ, i, j⟩
  cases κ <;> simp [evalLetter]

/-- The remainder letter of (6.47): if every entry of `R` and of `S` is at most `2`,
every letter of `(R I_γ)^n S` is at most `2 · 4^n` (at most `2^n` chains of `n + 1` entries). -/
theorem norm_evalLetter_mul_entryMat_pow_le {N : ℕ} {R S : Matrix (Fin N) (Fin N) ℂ}
    (hR : ∀ i j, ‖R i j‖ ≤ 2) (hS : ∀ i j, ‖S i j‖ ≤ 2) (e : Fin N ⊕ OffDiag N) (n : ℕ)
    (ℓ : Letter N) :
    ‖evalLetter ((R * (entryMat e).map (fun x : ℝ => (x : ℂ))) ^ n * S) 0 ℓ‖ ≤ 2 * 4 ^ n := by
  rw [starExpansion_norm_evalLetter_zero]
  calc _ ≤ (2 * 2) ^ n * 2 :=
        starExpansion_norm_pow_mul_apply_le e (by norm_num) hR hS n ℓ.i ℓ.j
    _ = 2 * 4 ^ n := by norm_num; ring

/-! ### Bounds on single letters -/

/-- A letter is at most `B + 1` when `|G_ij| ≤ B` and `|m| ≤ 1`. -/
private lemma starExpansion_norm_evalLetter_le {N : ℕ} {G : Matrix (Fin N) (Fin N) ℂ} {m : ℂ}
    {B : ℝ} (hG : ∀ i j, ‖G i j‖ ≤ B) (hm : ‖m‖ ≤ 1) (ℓ : Letter N) :
    ‖evalLetter G m ℓ‖ ≤ B + 1 := by
  have h0 := hG ℓ.i ℓ.j
  have hc : ‖G ℓ.i ℓ.j - if ℓ.i = ℓ.j then m else 0‖ ≤ B + 1 := by
    refine (norm_sub_le _ _).trans ?_
    split_ifs <;> (try simp only [norm_zero]) <;> linarith
  rcases ℓ with ⟨κ, i, j⟩
  cases κ <;> simp only [evalLetter, norm_star]
  · linarith
  · linarith
  · exact hc
  · exact hc

/-- `P_{γ,k}` of a letter is at most `3 · 4^k` when `|G_ij| ≤ 2` and `|m| ≤ 1`. -/
private lemma starExpansion_norm_evalW_letterP_le {N : ℕ} {G : Matrix (Fin N) (Fin N) ℂ}
    {m : ℂ} (hG : ∀ i j, ‖G i j‖ ≤ 2) (hm : ‖m‖ ≤ 1) (e : Fin N ⊕ OffDiag N) (k : ℕ)
    (ℓ : Letter N) : ‖evalW G m (letterP e k ℓ)‖ ≤ 3 * 4 ^ k := by
  rw [evalW_letterP]
  by_cases hk : k = 0
  · subst hk
    have := starExpansion_norm_evalLetter_le hG hm ℓ
    simp only [pow_zero, Matrix.one_mul, ↓reduceIte]
    linarith
  · simp only [hk, ↓reduceIte]
    rw [starExpansion_norm_evalLetter_zero]
    have h4 : (0 : ℝ) < 4 ^ k := by positivity
    calc _ ≤ (2 * 2) ^ k * 2 := starExpansion_norm_pow_mul_apply_le e (by norm_num) hG hG k _ _
      _ ≤ 3 * 4 ^ k := by norm_num; linarith

/-- `P_{γ,k}` of a letter is at most `2^k (B + 1)^{k+1}` when `|G_ij| ≤ B` and `|m| ≤ 1`. -/
private lemma starExpansion_norm_evalW_letterP_le_of_le {N : ℕ} {G : Matrix (Fin N) (Fin N) ℂ}
    {m : ℂ} {B : ℝ} (hG : ∀ i j, ‖G i j‖ ≤ B) (hm : ‖m‖ ≤ 1) (e : Fin N ⊕ OffDiag N) (k : ℕ)
    (ℓ : Letter N) : ‖evalW G m (letterP e k ℓ)‖ ≤ 2 ^ k * (B + 1) ^ (k + 1) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hG ℓ.i ℓ.j)
  rw [evalW_letterP]
  by_cases hk : k = 0
  · subst hk
    have := starExpansion_norm_evalLetter_le hG hm ℓ
    simp only [pow_zero, ↓reduceIte, zero_add, pow_one, one_mul]
    exact this
  · simp only [hk, ↓reduceIte]
    rw [starExpansion_norm_evalLetter_zero]
    calc _ ≤ (2 * B) ^ k * B := starExpansion_norm_pow_mul_apply_le e hB hG hG k _ _
      _ ≤ (2 * (B + 1)) ^ k * (B + 1) := by gcongr <;> linarith
      _ = 2 ^ k * (B + 1) ^ (k + 1) := by rw [mul_pow, pow_succ]; ring

/-! ### Counting -/

/-- `C(k + n, n) ≤ (k + 1)^n`; in particular `|I^{k+1}_{·,n}| ≤ (k + 1)^n` (6.66). -/
private lemma starExpansion_choose_le (k : ℕ) : ∀ n : ℕ, (k + n).choose n ≤ (k + 1) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h := Nat.add_one_mul_choose_eq (k + n) n
    have h2 : (k + n + 1).choose (n + 1) * (n + 1) ≤ (k + 1) ^ (n + 1) * (n + 1) := by
      rw [← h]
      calc (k + n + 1) * (k + n).choose n ≤ ((k + 1) * (n + 1)) * (k + 1) ^ n :=
            Nat.mul_le_mul (by nlinarith) ih
        _ = (k + 1) ^ (n + 1) * (n + 1) := by ring
    rw [show k + (n + 1) = k + n + 1 by omega]
    exact Nat.le_of_mul_le_mul_right h2 (Nat.succ_pos n)

/-- `Σ_{a ≤ n} p^a q^{n-a+1} ≤ (p + q)^{n+1}` for `p, q ≥ 0`. -/
private lemma starExpansion_sum_pow_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (n : ℕ) :
    ∑ a ∈ Finset.range (n + 1), p ^ a * q ^ (n - a + 1) ≤ (p + q) ^ (n + 1) := by
  rw [add_pow]
  calc ∑ a ∈ Finset.range (n + 1), p ^ a * q ^ (n - a + 1)
      ≤ ∑ a ∈ Finset.range (n + 1), p ^ a * q ^ (n + 1 - a) * ((n + 1).choose a : ℝ) := by
        refine Finset.sum_le_sum fun a ha => ?_
        have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        rw [show n - a + 1 = n + 1 - a by omega]
        have h1 : (1 : ℝ) ≤ ((n + 1).choose a : ℝ) := by
          exact_mod_cast Nat.choose_pos (by omega)
        have h0 : 0 ≤ p ^ a * q ^ (n + 1 - a) := by positivity
        nlinarith
    _ ≤ ∑ a ∈ Finset.range (n + 1 + 1), p ^ a * q ^ (n + 1 - a) * ((n + 1).choose a : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
          (fun a _ _ => by positivity)

/-- Summing over `c ≤ n` and `a + b = c` is summing over `a ≤ n` and `b ≤ n - a`. -/
private lemma starExpansion_sum_antidiagonal {M : Type*} [AddCommMonoid M] (n : ℕ)
    (H : ℕ → ℕ → M) :
    ∑ c ∈ Finset.range (n + 1), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal c, H p.1 p.2 =
      ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n - a + 1), H a b := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => ⟨x.2.1, x.2.2⟩) (fun y _ => ⟨y.1 + y.2, (y.1, y.2)⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨c, a, b⟩ h
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal] at h ⊢
    omega
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal] at h ⊢
    exact ⟨by omega, trivial⟩
  · rintro ⟨c, a, b⟩ h
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal] at h
    obtain ⟨_, rfl⟩ := h
    rfl
  · rintro ⟨a, b⟩ _
    rfl
  · rintro ⟨c, a, b⟩ _
    rfl

/-- A tuple in `ℕ^{s+1}` with sum `c` is `(a, l')` with `a + b = c` and `l' ∈ ℕ^s` of sum `b`. -/
private lemma starExpansion_sum_antidiagonalTuple_succ {M : Type*} [AddCommMonoid M] (s c : ℕ)
    (f : (Fin (s + 1) → ℕ) → M) :
    ∑ l ∈ Finset.Nat.antidiagonalTuple (s + 1) c, f l =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal c,
        ∑ l ∈ Finset.Nat.antidiagonalTuple s p.2, f (Fin.cons p.1 l) := by
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij' (fun x _ => Fin.cons x.1.1 x.2)
    (fun l _ => ⟨(l 0, c - l 0), Fin.tail l⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨a, b⟩, l⟩ h
    simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal,
      Finset.Nat.mem_antidiagonalTuple] at h ⊢
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    omega
  · intro l h
    simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal,
      Finset.Nat.mem_antidiagonalTuple] at h ⊢
    rw [Fin.sum_univ_succ] at h
    refine ⟨by omega, ?_⟩
    simp only [Fin.tail]
    omega
  · rintro ⟨⟨a, b⟩, l⟩ h
    simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal,
      Finset.Nat.mem_antidiagonalTuple] at h
    simp only [Fin.cons_zero, Fin.tail_cons]
    obtain ⟨rfl, -⟩ := h
    simp
  · intro l _
    simp
  · intro x _
    rfl

/-! ### Expansion of one entry of `(S I_γ)^k S` -/

/-- (6.47), (6.63)–(6.66) for one entry of `(S I_γ)^k S`: if `S = R - v R I_γ S` and every entry of
`R` and of `S` is at most `2`, then every entry of
`(S I_γ)^k S - Σ_{a < M} (-v)^a C(k + a, a) (R I_γ)^{k+a} R` is at most
`2 · 4^k C(k + M, k) (4|v|)^M`. -/
private lemma starExpansion_norm_pow_sub_sum_le {N : ℕ} (e : Fin N ⊕ OffDiag N) (v : ℝ)
    {R S : Matrix (Fin N) (Fin N) ℂ}
    (hRS : S = R - (v : ℂ) • (R * (entryMat e).map (fun x : ℝ => (x : ℂ)) * S))
    (hR : ∀ i j, ‖R i j‖ ≤ 2) (hS : ∀ i j, ‖S i j‖ ≤ 2) (k M : ℕ) (i j : Fin N) :
    ‖((S * (entryMat e).map (fun x : ℝ => (x : ℂ))) ^ k * S -
        ∑ a ∈ Finset.range M, ((((-v) ^ a : ℝ) : ℂ) * ((Nat.choose (k + a) a : ℕ) : ℂ)) •
          ((R * (entryMat e).map (fun x : ℝ => (x : ℂ))) ^ (k + a) * R)) i j‖ ≤
      2 * 4 ^ k * ((Nat.choose (k + M) k : ℕ) : ℝ) * (4 * |v|) ^ M := by
  set I := (entryMat e).map (fun x : ℝ => (x : ℂ)) with hI
  set X := R * I with hX
  set A : ℕ → Matrix (Fin N) (Fin N) ℂ := fun k => (S * I) ^ k * S with hA
  set c : ℕ → ℕ → ℂ := fun k a => (((-v) ^ a : ℝ) : ℂ) * ((Nat.choose (k + a) a : ℕ) : ℂ)
    with hc
  set T : ℕ → ℕ → Matrix (Fin N) (Fin N) ℂ :=
    fun k M => ∑ a ∈ Finset.range M, c k a • (X ^ (k + a) * R) with hT
  have hXpow : ∀ p, X * (X ^ p * R) = X ^ (p + 1) * R := fun p => by
    rw [← Matrix.mul_assoc, ← pow_succ']
  have hA0 : A 0 = S := by simp [hA]
  have hAs : ∀ k, A (k + 1) = X * A k - (v : ℂ) • (X * A (k + 1)) := by
    intro k
    have h1 : A (k + 1) = S * I * A k := by simp only [hA, pow_succ', Matrix.mul_assoc]
    calc A (k + 1) = S * I * A k := h1
      _ = (R - (v : ℂ) • (X * S)) * I * A k := by rw [← hRS]
      _ = X * A k - (v : ℂ) • (X * (S * I * A k)) := by
          rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul]
          simp only [hX, Matrix.mul_assoc]
      _ = X * A k - (v : ℂ) • (X * A (k + 1)) := by rw [← h1]
  have hT0 : ∀ M, T 0 (M + 1) = R - (v : ℂ) • (X * T 0 M) := by
    intro M
    simp only [hT]
    rw [Finset.sum_range_succ', Matrix.mul_sum, Finset.smul_sum, sub_eq_add_neg,
      ← Finset.sum_neg_distrib, add_comm]
    congr 1
    · simp [hc]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Matrix.mul_smul, hXpow, smul_smul, ← neg_smul]
      congr 1
      simp only [hc]
      push_cast
      simp only [zero_add, Nat.choose_self, Nat.cast_one, mul_one]
      ring
  have hTs : ∀ k M, T (k + 1) (M + 1) = X * T k (M + 1) - (v : ℂ) • (X * T (k + 1) M) := by
    intro k M
    simp only [hT]
    rw [Finset.sum_range_succ', Finset.sum_range_succ', Matrix.mul_add, Matrix.mul_sum,
      Matrix.mul_sum, Finset.smul_sum]
    have e1 : ∀ a ∈ Finset.range M, c (k + 1) (a + 1) • (X ^ (k + 1 + (a + 1)) * R) =
        X * (c k (a + 1) • (X ^ (k + (a + 1)) * R)) -
          (v : ℂ) • (X * (c (k + 1) a • (X ^ (k + 1 + a) * R))) := by
      intro a _
      rw [Matrix.mul_smul, Matrix.mul_smul, hXpow, hXpow, smul_smul,
        show k + (a + 1) + 1 = k + 1 + (a + 1) by omega,
        show k + 1 + a + 1 = k + 1 + (a + 1) by omega, ← sub_smul]
      congr 1
      simp only [hc]
      rw [show k + 1 + (a + 1) = (k + 1 + a) + 1 by omega, Nat.choose_succ_succ',
        show k + (a + 1) = k + 1 + a by omega]
      push_cast
      ring
    have e0 : c (k + 1) 0 • (X ^ (k + 1 + 0) * R) = X * (c k 0 • (X ^ (k + 0) * R)) := by
      rw [Matrix.mul_smul, hXpow]
      simp [hc]
    rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, e0]
    abel
  have hD0 : ∀ M, A 0 - T 0 (M + 1) = -((v : ℂ) • (X * (A 0 - T 0 M))) := by
    intro M
    rw [hT0, hA0]
    nth_rewrite 1 [hRS]
    rw [Matrix.mul_sub, smul_sub]
    abel
  have hDs : ∀ k M, A (k + 1) - T (k + 1) (M + 1) =
      X * (A k - T k (M + 1)) - (v : ℂ) • (X * (A (k + 1) - T (k + 1) M)) := by
    intro k M
    rw [hTs]
    nth_rewrite 1 [hAs k]
    rw [Matrix.mul_sub, Matrix.mul_sub, smul_sub]
    abel
  have hstep : ∀ (D : Matrix (Fin N) (Fin N) ℂ) (β : ℝ), (∀ y, ‖D y j‖ ≤ β) →
      ∀ i, ‖(X * D) i j‖ ≤ 4 * β := fun D β hD i => by
    have := starExpansion_norm_mul_entryMat_mul_apply_le e (a := 2) (by norm_num) hR j hD i
    linarith
  have hv : 0 ≤ |v| := abs_nonneg v
  have key : ∀ k M i, ‖(A k - T k M) i j‖ ≤
      2 * 4 ^ k * ((Nat.choose (k + M) k : ℕ) : ℝ) * (4 * |v|) ^ M := by
    intro k
    induction k with
    | zero =>
      intro M
      induction M with
      | zero =>
        intro i
        simpa [hT, hA0] using hS i j
      | succ M ih =>
        intro i
        rw [hD0, Matrix.neg_apply, norm_neg, Matrix.smul_apply, smul_eq_mul, norm_mul,
          Complex.norm_real, Real.norm_eq_abs]
        have h1 := hstep _ _ ih i
        simp only [zero_add, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one] at h1 ⊢
        calc |v| * ‖(X * (A 0 - T 0 M)) i j‖ ≤ |v| * (4 * (2 * (4 * |v|) ^ M)) := by gcongr
          _ = 2 * (4 * |v|) ^ (M + 1) := by ring
    | succ k ihk =>
      intro M
      induction M with
      | zero =>
        intro i
        have h1 := starExpansion_norm_pow_mul_apply_le e (a := 2) (by norm_num) hS hS (k + 1) i j
        simp only [hT, Finset.range_zero, Finset.sum_empty, sub_zero, add_zero,
          Nat.choose_self, Nat.cast_one, mul_one, pow_zero]
        calc _ ≤ (2 * 2) ^ (k + 1) * 2 := h1
          _ = 2 * 4 ^ (k + 1) := by norm_num; ring
      | succ M ihM =>
        intro i
        rw [hDs, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        have h1 := hstep _ _ (ihk (M + 1)) i
        have h2 := hstep _ _ ihM i
        have hch : (((k + 1 + (M + 1)).choose (k + 1) : ℕ) : ℝ) =
            (((k + (M + 1)).choose k : ℕ) : ℝ) + (((k + 1 + M).choose (k + 1) : ℕ) : ℝ) := by
          rw [show k + 1 + (M + 1) = (k + M + 1) + 1 by omega, Nat.choose_succ_succ',
            show k + (M + 1) = k + M + 1 by omega, show k + 1 + M = k + M + 1 by omega]
          push_cast
          ring
        calc ‖(X * (A k - T k (M + 1))) i j - (v : ℂ) * (X * (A (k + 1) - T (k + 1) M)) i j‖
            ≤ ‖(X * (A k - T k (M + 1))) i j‖ + |v| * ‖(X * (A (k + 1) - T (k + 1) M)) i j‖ := by
              refine (norm_sub_le _ _).trans ?_
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          _ ≤ 4 * (2 * 4 ^ k * (((k + (M + 1)).choose k : ℕ) : ℝ) * (4 * |v|) ^ (M + 1)) +
              |v| * (4 * (2 * 4 ^ (k + 1) * (((k + 1 + M).choose (k + 1) : ℕ) : ℝ) *
                (4 * |v|) ^ M)) := by gcongr
          _ = 2 * 4 ^ (k + 1) * ((((k + (M + 1)).choose k : ℕ) : ℝ) +
                (((k + 1 + M).choose (k + 1) : ℕ) : ℝ)) * (4 * |v|) ^ (M + 1) := by ring
          _ = _ := by rw [hch]
  exact key k M i

/-- (6.47)–(6.50), (6.63)–(6.66) for one letter: `P_{γ,k} ℓ(S)` minus its expansion
`Σ_{a ≤ n} (-v)^a C(k + a, a) P_{γ,k+a} ℓ(R)` is at most `2 · 4^k (4 (k + 1) |v|)^{n+1}`, when
every entry of `R = (Q - z)⁻¹` and of `S = (Q + v I_γ - z)⁻¹` is at most `2`. -/
private lemma starExpansion_norm_evalW_letterP_sub_le {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Q.IsHermitian) (e : Fin N ⊕ OffDiag N) (v : ℝ) {z : ℂ} (hz : 0 < z.im) (m : ℂ)
    (hS : ∀ i j, ‖resolventC (Q + v • entryMat e) z i j‖ ≤ 2)
    (hR : ∀ i j, ‖resolventC Q z i j‖ ≤ 2) (k n : ℕ) (ℓ : Letter N) :
    ‖evalW (resolventC (Q + v • entryMat e) z) m (letterP e k ℓ) -
        ∑ a ∈ Finset.range (n + 1), (((-v) ^ a : ℝ) : ℂ) * ((Nat.choose (k + a) a : ℕ) : ℂ) *
          evalW (resolventC Q z) m (letterP e (k + a) ℓ)‖ ≤
      2 * 4 ^ k * (4 * ((k + 1 : ℕ) : ℝ) * |v|) ^ (n + 1) := by
  by_cases hk : k = 0
  · subst hk
    have h0 : evalW (resolventC (Q + v • entryMat e) z) m (letterP e 0 ℓ) =
        evalLetter (resolventC (Q + v • entryMat e) z) m ℓ := by
      simp [letterP, evalW, evalWord]
    rw [h0, evalLetter_resolventC_add_eq hQ e v hz m n ℓ]
    simp only [zero_add, Nat.choose_self, Nat.cast_one, mul_one, add_sub_cancel_left]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_neg]
    have h1 := norm_evalLetter_mul_entryMat_pow_le hR hS e (n + 1) ℓ
    calc _ ≤ |v| ^ (n + 1) * (2 * 4 ^ (n + 1)) := by gcongr
      _ = _ := by ring
  · set S := resolventC (Q + v • entryMat e) z with hSdef
    set R := resolventC Q z with hRdef
    have hRS : S = R - (v : ℂ) • (R * (entryMat e).map (fun x : ℝ => (x : ℂ)) * S) := by
      ext i j
      have := starExpansion_resolventC_add_apply hQ e v hz 0 i j
      rw [← hSdef, ← hRdef] at this
      simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, pow_one,
        Complex.ofReal_one, one_mul] at this
      rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      conv_lhs => rw [this]
      push_cast
      ring
    have hD := starExpansion_norm_pow_sub_sum_le e v hRS hR hS k (n + 1) ℓ.i ℓ.j
    simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at hD
    have hka : ∀ a, ¬(k + a = 0) := fun a => by omega
    simp only [evalW_letterP, hk, hka, ↓reduceIte]
    have hch := starExpansion_choose_le k (n + 1)
    have hbound : 2 * 4 ^ k * ((Nat.choose (k + (n + 1)) k : ℕ) : ℝ) * (4 * |v|) ^ (n + 1) ≤
        2 * 4 ^ k * (4 * ((k + 1 : ℕ) : ℝ) * |v|) ^ (n + 1) := by
      rw [Nat.choose_symm_add]
      have h2 : ((Nat.choose (k + (n + 1)) (n + 1) : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ (n + 1) := by
        exact_mod_cast hch
      calc _ ≤ 2 * 4 ^ k * ((k + 1 : ℕ) : ℝ) ^ (n + 1) * (4 * |v|) ^ (n + 1) := by gcongr
        _ = _ := by rw [mul_pow, mul_pow, mul_pow]; ring
    refine le_trans ?_ (hD.trans hbound)
    rcases ℓ with ⟨κ, i, j⟩
    cases κ <;> simp only [evalLetter, ite_self, sub_zero] <;>
      first
      | exact le_rfl
      | (rw [← norm_star]; simp [star_sum, Complex.conj_ofReal])

/-! ### Expansion of words -/

/-- The main term of (6.65) for the word `ℓ :: w` splits over the order `a` of the first letter:
the coefficient of the first letter is `(-v)^a C(κ_0 + a, a)`, and the rest is the main term of
`w` truncated at order `n - a`. -/
private lemma starExpansion_main_cons {N : ℕ} (e : Fin N ⊕ OffDiag N) (v : ℝ)
    (R : Matrix (Fin N) (Fin N) ℂ) (m : ℂ) {s : ℕ} (ℓ : Letter N) (w : Word N)
    (κ : Fin (s + 1) → ℕ) (n : ℕ) :
    ∑ c ∈ Finset.range (n + 1), (((-v) ^ c : ℝ) : ℂ) *
        ∑ l ∈ Finset.Nat.antidiagonalTuple (s + 1) c,
          ((∏ t, Nat.choose (κ t + l t) (l t) : ℕ) : ℂ) *
            evalW R m (wordP e (List.ofFn (κ + l)) (ℓ :: w)) =
      ∑ a ∈ Finset.range (n + 1),
        (((-v) ^ a : ℝ) : ℂ) * ((Nat.choose (κ 0 + a) a : ℕ) : ℂ) *
            evalW R m (letterP e (κ 0 + a) ℓ) *
          ∑ c ∈ Finset.range (n - a + 1), (((-v) ^ c : ℝ) : ℂ) *
            ∑ l ∈ Finset.Nat.antidiagonalTuple s c,
              ((∏ t, Nat.choose ((fun t => κ t.succ) t + l t) (l t) : ℕ) : ℂ) *
                evalW R m (wordP e (List.ofFn ((fun t => κ t.succ) + l)) w) := by
  have hterm : ∀ (a : ℕ) (l : Fin s → ℕ),
      ((∏ t, Nat.choose (κ t + (Fin.cons a l : Fin (s + 1) → ℕ) t)
          ((Fin.cons a l : Fin (s + 1) → ℕ) t) : ℕ) : ℂ) *
        evalW R m (wordP e (List.ofFn (κ + (Fin.cons a l : Fin (s + 1) → ℕ))) (ℓ :: w)) =
      ((Nat.choose (κ 0 + a) a : ℕ) : ℂ) * evalW R m (letterP e (κ 0 + a) ℓ) *
        (((∏ t, Nat.choose ((fun t => κ t.succ) t + l t) (l t) : ℕ) : ℂ) *
          evalW R m (wordP e (List.ofFn ((fun t => κ t.succ) + l)) w)) := by
    intro a l
    rw [Fin.prod_univ_succ, List.ofFn_succ, evalW_wordP_cons]
    have h1 : (fun i : Fin s => (κ + (Fin.cons a l : Fin (s + 1) → ℕ)) i.succ) =
        (fun t => κ t.succ) + l := by
      funext t
      simp
    have h2 : (κ + (Fin.cons a l : Fin (s + 1) → ℕ)) 0 = κ 0 + a := by simp
    rw [h1, h2]
    simp only [Fin.cons_zero, Fin.cons_succ]
    push_cast
    ring
  set H : ℕ → ℕ → ℂ := fun a b => (((-v) ^ a : ℝ) : ℂ) * ((Nat.choose (κ 0 + a) a : ℕ) : ℂ) *
            evalW R m (letterP e (κ 0 + a) ℓ) *
          ((((-v) ^ b : ℝ) : ℂ) * ∑ l ∈ Finset.Nat.antidiagonalTuple s b,
              ((∏ t, Nat.choose ((fun t => κ t.succ) t + l t) (l t) : ℕ) : ℂ) *
                evalW R m (wordP e (List.ofFn ((fun t => κ t.succ) + l)) w)) with hH
  have key : ∀ c ∈ Finset.range (n + 1), (((-v) ^ c : ℝ) : ℂ) *
        ∑ l ∈ Finset.Nat.antidiagonalTuple (s + 1) c,
          ((∏ t, Nat.choose (κ t + l t) (l t) : ℕ) : ℂ) *
            evalW R m (wordP e (List.ofFn (κ + l)) (ℓ :: w)) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal c, H p.1 p.2 := by
    intro c _
    rw [starExpansion_sum_antidiagonalTuple_succ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    simp only [hterm, hH]
    rw [← hp, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    push_cast
    ring
  rw [Finset.sum_congr rfl key, starExpansion_sum_antidiagonal n H]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]

/-- `y Y - Σ_a t_a M_a = (y - Σ_a t_a) Y + Σ_a t_a (Y - M_a)`, bounded termwise. -/
private lemma starExpansion_norm_mul_sub_sum_le (y Y : ℂ) (t M : ℕ → ℂ) (n : ℕ) {ρ β : ℝ}
    {τ ε : ℕ → ℝ} (h1 : ‖y - ∑ a ∈ Finset.range (n + 1), t a‖ ≤ ρ) (h2 : ‖Y‖ ≤ β)
    (h3 : ∀ a ∈ Finset.range (n + 1), ‖t a‖ ≤ τ a)
    (h4 : ∀ a ∈ Finset.range (n + 1), ‖Y - M a‖ ≤ ε a) :
    ‖y * Y - ∑ a ∈ Finset.range (n + 1), t a * M a‖ ≤
      ρ * β + ∑ a ∈ Finset.range (n + 1), τ a * ε a := by
  have hid : y * Y - ∑ a ∈ Finset.range (n + 1), t a * M a =
      (y - ∑ a ∈ Finset.range (n + 1), t a) * Y +
        ∑ a ∈ Finset.range (n + 1), t a * (Y - M a) := by
    simp only [mul_sub, Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]
    ring
  rw [hid]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha => ?_)
    rw [norm_mul]
    exact mul_le_mul (h3 a ha) (h4 a ha) (norm_nonneg _) ((norm_nonneg _).trans (h3 a ha))

/-- The arithmetic of the word remainder: with `p = k + 1` letters at the first position and
`q = s + K` letters in the rest, the two error terms add up to at most
`2^{k+K} 4^{(s+1)+(k+K)+2} (4 (p + q) x)^{n+1}`. -/
private lemma starExpansion_arith (k K s n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    2 * 4 ^ k * (4 * ((k + 1 : ℕ) : ℝ) * x) ^ (n + 1) * 4 ^ (s + K + 1) +
        ∑ a ∈ Finset.range (n + 1), (3 * 4 ^ k * (4 * ((k + 1 : ℕ) : ℝ) * x) ^ a) *
          (2 ^ K * 4 ^ (s + K + 2) * (4 * ((s + K : ℕ) : ℝ) * x) ^ (n - a + 1)) ≤
      2 ^ (k + K) * 4 ^ (s + 1 + (k + K) + 2) *
        (4 * ((s + 1 + (k + K) : ℕ) : ℝ) * x) ^ (n + 1) := by
  have hpq : ((s + 1 + (k + K) : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) + ((s + K : ℕ) : ℝ) := by
    push_cast
    ring
  have hp0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ ((s + K : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [hpq]
  generalize ((k + 1 : ℕ) : ℝ) = p at *
  generalize ((s + K : ℕ) : ℝ) = q at *
  have hsum : ∑ a ∈ Finset.range (n + 1), (3 * 4 ^ k * (4 * p * x) ^ a) *
        (2 ^ K * 4 ^ (s + K + 2) * (4 * q * x) ^ (n - a + 1)) =
      3 * 4 ^ k * 2 ^ K * 4 ^ (s + K + 2) * (4 * x) ^ (n + 1) *
        ∑ a ∈ Finset.range (n + 1), p ^ a * q ^ (n - a + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have h : n + 1 = a + (n - a + 1) := by
      have := Finset.mem_range.mp ha
      omega
    rw [h]
    ring
  have hS := starExpansion_sum_pow_le hp0 hq0 n
  have hpz : (4 * p * x) ^ (n + 1) ≤ (4 * (p + q) * x) ^ (n + 1) :=
    pow_le_pow_left₀ (mul_nonneg (mul_nonneg (by norm_num) hp0) hx)
      (by nlinarith [mul_nonneg hq0 hx]) (n + 1)
  have hZ : (4 * x) ^ (n + 1) * (p + q) ^ (n + 1) = (4 * (p + q) * x) ^ (n + 1) := by
    rw [← mul_pow]
    ring_nf
  have hZ0 : 0 ≤ (4 * (p + q) * x) ^ (n + 1) :=
    pow_nonneg (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hp0 hq0)) hx) _
  have hC : (0 : ℝ) ≤ 3 * 4 ^ k * 2 ^ K * 4 ^ (s + K + 2) := by positivity
  have hx4 : (0 : ℝ) ≤ (4 * x) ^ (n + 1) := pow_nonneg (by linarith) _
  rw [hsum]
  have hA : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
  have hB : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hW : 0 ≤ (4 : ℝ) ^ k * 4 ^ (s + K) * (4 * (p + q) * x) ^ (n + 1) := by positivity
  have hc : (8 + 48 * (2 : ℝ) ^ K) ≤ 64 * 2 ^ K * 2 ^ k := by nlinarith
  calc _ ≤ 2 * 4 ^ k * (4 * (p + q) * x) ^ (n + 1) * 4 ^ (s + K + 1) +
        3 * 4 ^ k * 2 ^ K * 4 ^ (s + K + 2) * ((4 * x) ^ (n + 1) * (p + q) ^ (n + 1)) := by
        refine add_le_add ?_ ?_
        · have h4 : (0 : ℝ) ≤ 2 * 4 ^ k := by positivity
          have h5 : (0 : ℝ) ≤ 4 ^ (s + K + 1) := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpz h4) h5
        · rw [mul_assoc (3 * 4 ^ k * 2 ^ K * 4 ^ (s + K + 2))]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS hx4) hC
    _ = (8 + 48 * 2 ^ K) * (4 ^ k * 4 ^ (s + K) * (4 * (p + q) * x) ^ (n + 1)) := by
        rw [hZ]
        ring
    _ ≤ (64 * 2 ^ K * 2 ^ k) * (4 ^ k * 4 ^ (s + K) * (4 * (p + q) * x) ^ (n + 1)) :=
        mul_le_mul_of_nonneg_right hc hW
    _ = _ := by ring

/-- (6.52), (6.55)–(6.58), (6.63)–(6.66) for arbitrary matrices `S`, `R` with entries at most `2`,
given the expansion of every single letter with remainder `2 · 4^k (4 (k + 1) |v|)^{n+1}`. -/
private lemma starExpansion_norm_evalW_wordP_sub_le {N : ℕ} (e : Fin N ⊕ OffDiag N) (v : ℝ)
    {S R : Matrix (Fin N) (Fin N) ℂ} {m : ℂ} (hm : ‖m‖ ≤ 1) (hS : ∀ i j, ‖S i j‖ ≤ 2)
    (hR : ∀ i j, ‖R i j‖ ≤ 2)
    (hL : ∀ (k n : ℕ) (ℓ : Letter N), ‖evalW S m (letterP e k ℓ) -
        ∑ a ∈ Finset.range (n + 1), (((-v) ^ a : ℝ) : ℂ) * ((Nat.choose (k + a) a : ℕ) : ℂ) *
          evalW R m (letterP e (k + a) ℓ)‖ ≤
      2 * 4 ^ k * (4 * ((k + 1 : ℕ) : ℝ) * |v|) ^ (n + 1)) :
    ∀ (s : ℕ) (w : Word N), w.length = s → ∀ (κ : Fin s → ℕ) (n : ℕ),
      ‖evalW S m (wordP e (List.ofFn κ) w) -
          ∑ c ∈ Finset.range (n + 1), (((-v) ^ c : ℝ) : ℂ) *
            ∑ l ∈ Finset.Nat.antidiagonalTuple s c,
              ((∏ t, Nat.choose (κ t + l t) (l t) : ℕ) : ℂ) *
                evalW R m (wordP e (List.ofFn (κ + l)) w)‖ ≤
        2 ^ (∑ t, κ t) * 4 ^ (s + ∑ t, κ t + 2) *
          (4 * ((s + ∑ t, κ t : ℕ) : ℝ) * |v|) ^ (n + 1) := by
  intro s
  induction s with
  | zero =>
    intro w hw κ n
    have hw0 : w = [] := List.length_eq_zero_iff.mp hw
    subst hw0
    rw [Finset.sum_range_succ']
    simp [wordP, evalW, evalWord, Finset.Nat.antidiagonalTuple_zero_succ]
  | succ s ih =>
    intro w hw κ n
    obtain ⟨ℓ, w', rfl⟩ : ∃ ℓ w', w = ℓ :: w' := by
      match w, hw with
      | ℓ :: w', _ => exact ⟨ℓ, w', rfl⟩
    have hw' : w'.length = s := by simpa using hw
    rw [starExpansion_main_cons, List.ofFn_succ, evalW_wordP_cons,
      Fin.sum_univ_succ κ]
    have h2 : ‖evalW S m (wordP e (List.ofFn fun t : Fin s => κ t.succ) w')‖ ≤
        4 ^ (s + ∑ t : Fin s, κ t.succ + 1) := by
      have := norm_evalW_wordP_le hS hm e (List.ofFn fun t : Fin s => κ t.succ) w'
        (by simp [hw'])
      rwa [hw', List.sum_ofFn] at this
    have h3 : ∀ a ∈ Finset.range (n + 1),
        ‖(((-v) ^ a : ℝ) : ℂ) * ((Nat.choose (κ 0 + a) a : ℕ) : ℂ) *
            evalW R m (letterP e (κ 0 + a) ℓ)‖ ≤
          3 * 4 ^ (κ 0) * (4 * ((κ 0 + 1 : ℕ) : ℝ) * |v|) ^ a := by
      intro a _
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs, abs_pow,
        abs_neg]
      have hc : ((Nat.choose (κ 0 + a) a : ℕ) : ℝ) ≤ ((κ 0 + 1 : ℕ) : ℝ) ^ a := by
        exact_mod_cast starExpansion_choose_le (κ 0) a
      have hα := starExpansion_norm_evalW_letterP_le hR hm e (κ 0 + a) ℓ
      calc _ ≤ |v| ^ a * ((κ 0 + 1 : ℕ) : ℝ) ^ a * (3 * 4 ^ (κ 0 + a)) := by gcongr
        _ = _ := by rw [mul_pow, mul_pow, pow_add]; ring
    have h4 : ∀ a ∈ Finset.range (n + 1),
        ‖evalW S m (wordP e (List.ofFn fun t : Fin s => κ t.succ) w') -
            ∑ c ∈ Finset.range (n - a + 1), (((-v) ^ c : ℝ) : ℂ) *
              ∑ l ∈ Finset.Nat.antidiagonalTuple s c,
                ((∏ t, Nat.choose ((fun t => κ t.succ) t + l t) (l t) : ℕ) : ℂ) *
                  evalW R m (wordP e (List.ofFn ((fun t => κ t.succ) + l)) w')‖ ≤
          2 ^ (∑ t : Fin s, κ t.succ) * 4 ^ (s + ∑ t : Fin s, κ t.succ + 2) *
            (4 * ((s + ∑ t : Fin s, κ t.succ : ℕ) : ℝ) * |v|) ^ (n - a + 1) :=
      fun a _ => ih w' hw' (fun t => κ t.succ) (n - a)
    refine (starExpansion_norm_mul_sub_sum_le _ _ _ _ n (hL (κ 0) n ℓ) h2 h3 h4).trans ?_
    exact starExpansion_arith (κ 0) (∑ t : Fin s, κ t.succ) s n (abs_nonneg v)

/-- (6.52), (6.55)–(6.58), (6.63)–(6.66), deterministic: the `P_{γ,κ}` image of a word
of length `s` in `S = (Q + v I_γ - z)⁻¹`, expanded in `R = (Q - z)⁻¹` to order `n`. The coefficient
of `(-v)^{|l|} P_{γ,κ+l}(word)(R)` is `∏_t C(κ_t + l_t, l_t) = ∏_t |I^{κ_t+1}_{·,l_t}|` (6.66).
With `K = |κ|`, `|R_ij|, |S_ij| ≤ 2`, `|m| ≤ 1` and `8 (s + K) |v| ≤ 1`, the remainder is at most
`2^K 4^{s+K+2} (4 (s + K) |v|)^{n+1}`. -/
theorem norm_evalW_wordP_sub_expansion_le {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Q.IsHermitian) (e : Fin N ⊕ OffDiag N) (v : ℝ) {z : ℂ} (hz : 0 < z.im) {m : ℂ}
    (hm : ‖m‖ ≤ 1) (hS : ∀ i j, ‖resolventC (Q + v • entryMat e) z i j‖ ≤ 2)
    (hR : ∀ i j, ‖resolventC Q z i j‖ ≤ 2) {s : ℕ} (w : Word N) (hw : w.length = s)
    (κ : Fin s → ℕ) (hv : 8 * ((s + ∑ t, κ t : ℕ) : ℝ) * |v| ≤ 1) (n : ℕ) :
    ‖evalW (resolventC (Q + v • entryMat e) z) m (wordP e (List.ofFn κ) w) -
        ∑ c ∈ Finset.range (n + 1), (((-v) ^ c : ℝ) : ℂ) *
          ∑ l ∈ Finset.Nat.antidiagonalTuple s c,
            ((∏ t, Nat.choose (κ t + l t) (l t) : ℕ) : ℂ) *
              evalW (resolventC Q z) m (wordP e (List.ofFn (κ + l)) w)‖ ≤
      2 ^ (∑ t, κ t) * 4 ^ (s + ∑ t, κ t + 2) *
        (4 * ((s + ∑ t, κ t : ℕ) : ℝ) * |v|) ^ (n + 1) := by
  have _ := hv
  exact starExpansion_norm_evalW_wordP_sub_le e v hm hS hR
    (starExpansion_norm_evalW_letterP_sub_le hQ e v hz m hS hR) s w hw κ n

/-- The bound (6.2) on words, for the complement of the good event: if `|G_ij| ≤ B`
and `|m| ≤ 1`, every `P_{γ,k}` image of a word of length `s` is at most
`2^{|k|} (B + 1)^{s + |k|}`. -/
theorem norm_evalW_wordP_le_of_le {N : ℕ} {G : Matrix (Fin N) (Fin N) ℂ} {m : ℂ} {B : ℝ}
    (hG : ∀ i j, ‖G i j‖ ≤ B) (hm : ‖m‖ ≤ 1) (e : Fin N ⊕ OffDiag N) (k : List ℕ)
    (w : Word N) (hk : k.length = w.length) :
    ‖evalW G m (wordP e k w)‖ ≤ 2 ^ k.sum * (B + 1) ^ (w.length + k.sum) := by
  induction w generalizing k with
  | nil =>
    have : k = [] := List.length_eq_zero_iff.mp (by simpa using hk)
    subst this
    simp [wordP, evalW, evalWord]
  | cons ℓ w ih =>
    obtain ⟨k0, ks, rfl⟩ : ∃ k0 ks, k = k0 :: ks := by
      match k, hk with
      | k0 :: ks, _ => exact ⟨k0, ks, rfl⟩
    have hB : 0 ≤ B := (norm_nonneg _).trans (hG ℓ.i ℓ.j)
    rw [evalW_wordP_cons, norm_mul]
    have h1 := starExpansion_norm_evalW_letterP_le_of_le hG hm e k0 ℓ
    have h2 := ih ks (by simpa using hk)
    calc _ ≤ (2 ^ k0 * (B + 1) ^ (k0 + 1)) * (2 ^ ks.sum * (B + 1) ^ (w.length + ks.sum)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (by positivity) (pow_nonneg (by linarith) _))
      _ = _ := by rw [List.length_cons, List.sum_cons]; ring

/-! ### Compiled checks at a concrete nondegenerate point

`N = 2`, the entry `e = (1, 2)` (`Fin 2` indices `0, 1`), `v = 1/32`, `Q = diag(1/4, -1/4)`,
`z = i/2`, `m = i (√17 - 1)/4 = m_sc(i/2)`, the word `(G_11 - m) conj G_12` (`s = 2`) and
`κ = (1, 0)` (`K = 1`, `8 (s + K) |v| = 3/4`). -/

/-- The upper entry `(1, 2)` of a `2 × 2` matrix. -/
private def e2 : Fin 2 ⊕ OffDiag 2 := Sum.inr ⟨(0, 1), by decide⟩

/-- `H = [[1/4, 1/32], [1/32, -1/4]]`: diagonal `±1/4`, swapped entry `v = 1/32`. -/
private noncomputable def ω2 : Entries 2 := (![1 / 4, -1 / 4], fun _ => 1 / 32)

private noncomputable def z2 : ℂ := ⟨0, 1 / 2⟩

/-- `m_sc(i/2) = i (√17 - 1)/4`. -/
private noncomputable def m2 : ℂ := (((Real.sqrt 17 - 1) / 4 : ℝ) : ℂ) * Complex.I

private lemma entryVal_e2 : entryVal e2 ω2 = 1 / 32 := rfl

private lemma z2_im : 0 < z2.im := by simp [z2]

/-- `m = i (√17 - 1)/4` solves `m² + z m + 1 = 0` at `z = i/2`, has `Im m > 0` and `|m| ≤ 1`. -/
private lemma m2_spec : m2 ^ 2 + z2 * m2 + 1 = 0 ∧ 0 < m2.im ∧ ‖m2‖ ≤ 1 := by
  have h17 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have h4 : 4 < Real.sqrt 17 := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h5 : Real.sqrt 17 < 5 := by
    rw [show (5 : ℝ) = Real.sqrt 25 by
      rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · apply Complex.ext <;> simp [m2, z2, sq]
    nlinarith
  · simp [m2]
    linarith
  · rw [m2, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith

/-- Every entry of a resolvent at `z = i/2` is at most `1 / Im z = 2`. -/
private lemma norm_resolventC_z2_le {H : Matrix (Fin 2) (Fin 2) ℝ} (hH : H.IsHermitian)
    (i j : Fin 2) : ‖resolventC H z2 i j‖ ≤ 2 :=
  (norm_resolventC_apply_le hH z2_im i j).trans_eq (by simp [z2])

/-- The hypotheses of `evalLetter_resolventC_add_eq` and of `norm_evalW_wordP_sub_expansion_le`
hold together at the point above: `Q` Hermitian and nonzero, `Im z > 0`, `|m| ≤ 1`, all entries of
`S` and `R` at most `2`, the word of length `2`, `8 (s + K)|v| ≤ 1`, and `v ≠ 0`. -/
example : (symOfEntries (zeroEntry e2 ω2)).IsHermitian ∧ 0 < z2.im ∧ ‖m2‖ ≤ 1 ∧
    (∀ i j, ‖resolventC (symOfEntries (zeroEntry e2 ω2) + entryVal e2 ω2 • entryMat e2) z2 i j‖
      ≤ 2) ∧
    (∀ i j, ‖resolventC (symOfEntries (zeroEntry e2 ω2)) z2 i j‖ ≤ 2) ∧
    ([⟨.gc, 0, 0⟩, ⟨.gbar, 0, 1⟩] : Word 2).length = 2 ∧
    8 * ((2 + ∑ t, (![1, 0] : Fin 2 → ℕ) t : ℕ) : ℝ) * |entryVal e2 ω2| ≤ 1 ∧
    entryVal e2 ω2 ≠ 0 ∧ symOfEntries (zeroEntry e2 ω2) 0 0 = 1 / 4 := by
  refine ⟨symOfEntries_isHermitian _, z2_im, m2_spec.2.2, ?_,
    norm_resolventC_z2_le (symOfEntries_isHermitian _), rfl, ?_, ?_, ?_⟩
  · rw [← symOfEntries_eq_zeroEntry_add]
    exact norm_resolventC_z2_le (symOfEntries_isHermitian _)
  · rw [entryVal_e2]; simp [Fin.sum_univ_two]; norm_num
  · rw [entryVal_e2]; norm_num
  · simp [symOfEntries, zeroEntry, e2, ω2]

/-- `norm_evalW_wordP_sub_expansion_le` at the point above, to order `n = 2`. -/
example :
    ‖evalW (resolventC (symOfEntries (zeroEntry e2 ω2) + entryVal e2 ω2 • entryMat e2) z2) m2
        (wordP e2 (List.ofFn (![1, 0] : Fin 2 → ℕ)) [⟨.gc, 0, 0⟩, ⟨.gbar, 0, 1⟩]) -
      ∑ c ∈ Finset.range (2 + 1), (((-entryVal e2 ω2) ^ c : ℝ) : ℂ) *
        ∑ l ∈ Finset.Nat.antidiagonalTuple 2 c,
          ((∏ t, Nat.choose ((![1, 0] : Fin 2 → ℕ) t + l t) (l t) : ℕ) : ℂ) *
            evalW (resolventC (symOfEntries (zeroEntry e2 ω2)) z2) m2
              (wordP e2 (List.ofFn ((![1, 0] : Fin 2 → ℕ) + l)) [⟨.gc, 0, 0⟩, ⟨.gbar, 0, 1⟩])‖ ≤
      2 ^ (∑ t, (![1, 0] : Fin 2 → ℕ) t) * 4 ^ (2 + ∑ t, (![1, 0] : Fin 2 → ℕ) t + 2) *
        (4 * ((2 + ∑ t, (![1, 0] : Fin 2 → ℕ) t : ℕ) : ℝ) * |entryVal e2 ω2|) ^ (2 + 1) := by
  have hS : ∀ i j, ‖resolventC (symOfEntries (zeroEntry e2 ω2) + entryVal e2 ω2 • entryMat e2)
      z2 i j‖ ≤ 2 := by
    rw [← symOfEntries_eq_zeroEntry_add]
    exact norm_resolventC_z2_le (symOfEntries_isHermitian _)
  have hv : 8 * ((2 + ∑ t, (![1, 0] : Fin 2 → ℕ) t : ℕ) : ℝ) * |entryVal e2 ω2| ≤ 1 := by
    rw [entryVal_e2]; simp [Fin.sum_univ_two]; norm_num
  exact norm_evalW_wordP_sub_expansion_le (Q := symOfEntries (zeroEntry e2 ω2))
    (symOfEntries_isHermitian _) e2 (entryVal e2 ω2) z2_im m2_spec.2.2 hS
    (norm_resolventC_z2_le (symOfEntries_isHermitian _)) (s := 2)
    [⟨.gc, 0, 0⟩, ⟨.gbar, 0, 1⟩] rfl (![1, 0] : Fin 2 → ℕ) hv 2

/-- All entries of `S = (Q + v I_γ - z)⁻¹` at the point above are at most `2`. -/
private lemma norm_resolventC_add_z2_le (i j : Fin 2) :
    ‖resolventC (symOfEntries (zeroEntry e2 ω2) + entryVal e2 ω2 • entryMat e2) z2 i j‖ ≤ 2 := by
  rw [← symOfEntries_eq_zeroEntry_add]
  exact norm_resolventC_z2_le (symOfEntries_isHermitian _) i j

/-- `evalLetter_resolventC_add_eq` at the point above for the centred letter `G_11 - m`, to order
`n = 1`. -/
example :
    evalLetter (resolventC (symOfEntries (zeroEntry e2 ω2) + entryVal e2 ω2 • entryMat e2) z2) m2
        ⟨.gc, 0, 0⟩ =
      ∑ k ∈ Finset.range (1 + 1), (((-entryVal e2 ω2) ^ k : ℝ) : ℂ) *
          evalW (resolventC (symOfEntries (zeroEntry e2 ω2)) z2) m2 (letterP e2 k ⟨.gc, 0, 0⟩) +
        (((-entryVal e2 ω2) ^ (1 + 1) : ℝ) : ℂ) *
          evalLetter ((resolventC (symOfEntries (zeroEntry e2 ω2)) z2 *
              (entryMat e2).map (fun x : ℝ => (x : ℂ))) ^ (1 + 1) *
            resolventC (symOfEntries (zeroEntry e2 ω2) + entryVal e2 ω2 • entryMat e2) z2) 0
            ⟨.gc, 0, 0⟩ :=
  evalLetter_resolventC_add_eq (Q := symOfEntries (zeroEntry e2 ω2)) (symOfEntries_isHermitian _)
    e2 (entryVal e2 ω2) z2_im m2 1 ⟨.gc, 0, 0⟩

/-- `norm_evalLetter_mul_entryMat_pow_le` for the remainder letter of the expansion above. -/
example :
    ‖evalLetter ((resolventC (symOfEntries (zeroEntry e2 ω2)) z2 *
          (entryMat e2).map (fun x : ℝ => (x : ℂ))) ^ (1 + 1) *
        resolventC (symOfEntries (zeroEntry e2 ω2) + entryVal e2 ω2 • entryMat e2) z2) 0
        ⟨.gc, 0, 0⟩‖ ≤ 2 * 4 ^ (1 + 1) :=
  norm_evalLetter_mul_entryMat_pow_le (norm_resolventC_z2_le (symOfEntries_isHermitian _))
    norm_resolventC_add_z2_le e2 (1 + 1) ⟨.gc, 0, 0⟩

/-- `evalW_letterP_g` and `evalW_letterP` at `k = 2` for `R = (Q - z)⁻¹` at the point above. -/
example :
    evalW (resolventC (symOfEntries (zeroEntry e2 ω2)) z2) m2 (letterP e2 2 ⟨.g, 0, 0⟩) =
      ((resolventC (symOfEntries (zeroEntry e2 ω2)) z2 *
          (entryMat e2).map (fun x : ℝ => (x : ℂ))) ^ 2 *
        resolventC (symOfEntries (zeroEntry e2 ω2)) z2) 0 0 ∧
    evalW (resolventC (symOfEntries (zeroEntry e2 ω2)) z2) m2 (letterP e2 2 ⟨.gcbar, 0, 0⟩) =
      evalLetter ((resolventC (symOfEntries (zeroEntry e2 ω2)) z2 *
          (entryMat e2).map (fun x : ℝ => (x : ℂ))) ^ 2 *
        resolventC (symOfEntries (zeroEntry e2 ω2)) z2) (if 2 = 0 then m2 else 0)
        ⟨.gcbar, 0, 0⟩ :=
  ⟨evalW_letterP_g (resolventC (symOfEntries (zeroEntry e2 ω2)) z2) m2 e2 2 0 0,
    evalW_letterP (resolventC (symOfEntries (zeroEntry e2 ω2)) z2) m2 e2 2 ⟨.gcbar, 0, 0⟩⟩

/-- `norm_evalW_wordP_le_of_le` with `B = 2` for `S` at the point above, the word
`(G_11 - m) conj G_12` and `k = (2, 3)`. -/
example :
    ‖evalW (resolventC (symOfEntries (zeroEntry e2 ω2) + entryVal e2 ω2 • entryMat e2) z2) m2
        (wordP e2 [2, 3] [⟨.gc, 0, 0⟩, ⟨.gbar, 0, 1⟩])‖ ≤
      2 ^ [2, 3].sum * ((2 : ℝ) + 1) ^
        (([⟨.gc, 0, 0⟩, ⟨.gbar, 0, 1⟩] : Word 2).length + [2, 3].sum) :=
  norm_evalW_wordP_le_of_le norm_resolventC_add_z2_le m2_spec.2.2 e2 [2, 3]
    [⟨.gc, 0, 0⟩, ⟨.gbar, 0, 1⟩] rfl

/-- At `κ = 0` the coefficient `∏_t C(κ_t + l_t, l_t)` is `1` and `κ + l = l`, so the expansion
at `κ = 0` has the coefficients of the expansion of a single word. -/
example {s : ℕ} (l : Fin s → ℕ) :
    (∏ t, Nat.choose ((0 : Fin s → ℕ) t + l t) (l t) : ℕ) = 1 ∧ (0 : Fin s → ℕ) + l = l := by
  simp

#print axioms evalW_letterP_g
#print axioms evalW_letterP
#print axioms evalLetter_resolventC_add_eq
#print axioms norm_evalLetter_mul_entryMat_pow_le
#print axioms norm_evalW_wordP_sub_expansion_le
#print axioms norm_evalW_wordP_le_of_le

end WEdgeNS
