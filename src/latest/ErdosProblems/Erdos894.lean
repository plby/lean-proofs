/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 894.
https://www.erdosproblems.com/forum/thread/894

Informal authors:
- Yuval Peres
- Wilhelm Schlag

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos894.md
-/
/-
This is a Lean formalization of the affirmative resolution of Erdős Problem 894.
For a positive lacunary sequence of natural numbers, it constructs a finite
colouring of `ℕ` having no monochromatic difference in the sequence.

The proof follows the elementary argument recorded in the introduction of
Peres--Schlag, "Two Erdős problems on lacunary sequences: chromatic number and
Diophantine approximation", Bull. Lond. Math. Soc. 42 (2010), 295--300.
-/

import Mathlib

open Set Filter

namespace Erdos894

/-- A sequence of positive natural numbers is lacunary if its consecutive
terms grow by a fixed real factor strictly larger than one. -/
def IsLacunary (n : ℕ → ℕ) : Prop :=
  (∀ k, 0 < n k) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ k, (1 + ε) * (n k : ℝ) ≤ n (k + 1)

/-- The exact finite-colouring conclusion in Erdős Problem 894. -/
def HasAvoidingColoring (n : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, ∃ color : ℕ → Fin C,
    ∀ a b : ℕ, a - b ∈ Set.range n → color a ≠ color b

/-! ## A separated rotation for a sequence with ratio at least four -/

/-- Integer indices of recursively nested middle-half intervals. -/
private noncomputable def intervalIndex (n : ℕ → ℕ) : ℕ → ℤ
  | 0 => 0
  | k + 1 =>
      ⌊(n (k + 1) : ℝ) *
          (((intervalIndex n k : ℤ) : ℝ) + 1 / 4) / (n k : ℝ)⌋ + 1

private noncomputable def lowerEndpoint (n : ℕ → ℕ) (k : ℕ) : ℝ :=
  (((intervalIndex n k : ℤ) : ℝ) + 1 / 4) / (n k : ℝ)

private noncomputable def upperEndpoint (n : ℕ → ℕ) (k : ℕ) : ℝ :=
  (((intervalIndex n k : ℤ) : ℝ) + 3 / 4) / (n k : ℝ)

private lemma intervalIndex_succ (n : ℕ → ℕ) (k : ℕ) :
    intervalIndex n (k + 1) =
      ⌊(n (k + 1) : ℝ) * lowerEndpoint n k⌋ + 1 := by
  simp [intervalIndex, lowerEndpoint, mul_div_assoc]

/-- A positive sequence satisfying `4 * n k ≤ n (k+1)` admits a real rotation
whose every sampled fractional part lies in the closed middle half
`[1/4, 3/4]` of the circle. -/
lemma exists_separated_rotation_of_four_mul_le (n : ℕ → ℕ)
    (hn : ∀ k, 0 < n k) (hgrow : ∀ k, 4 * n k ≤ n (k + 1)) :
    ∃ θ : ℝ, ∀ k,
      1 / 4 ≤ Int.fract (θ * n k) ∧ Int.fract (θ * n k) ≤ 3 / 4 := by
  have hlohi (k : ℕ) : lowerEndpoint n k ≤ upperEndpoint n k := by
    unfold lowerEndpoint upperEndpoint
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    norm_num
  have hnreal (k : ℕ) : (0 : ℝ) < (n k : ℝ) := by
    exact_mod_cast hn k
  have hnreal' (k : ℕ) : (0 : ℝ) < (n (k + 1) : ℝ) := hnreal _
  have hnext (k : ℕ) :
      Icc (lowerEndpoint n (k + 1)) (upperEndpoint n (k + 1)) ⊆
        Icc (lowerEndpoint n k) (upperEndpoint n k) := by
    have hwidth :
        lowerEndpoint n k + 2 / (n (k + 1) : ℝ) ≤ upperEndpoint n k := by
      have hg : (4 : ℝ) * n k ≤ n (k + 1) := by
        exact_mod_cast hgrow k
      have hdiv :
          2 / (n (k + 1) : ℝ) ≤ (1 / 2) / (n k : ℝ) := by
        rw [div_le_div_iff₀ (hnreal' k) (hnreal k)]
        nlinarith
      calc
        lowerEndpoint n k + 2 / (n (k + 1) : ℝ)
            ≤ lowerEndpoint n k + (1 / 2) / (n k : ℝ) := by gcongr
        _ = upperEndpoint n k := by
          simp only [lowerEndpoint, upperEndpoint]
          field_simp
          ring
    have hlower : lowerEndpoint n k ≤ lowerEndpoint n (k + 1) := by
      change lowerEndpoint n k ≤
        (((intervalIndex n (k + 1) : ℤ) : ℝ) + 1 / 4) /
          (n (k + 1) : ℝ)
      rw [intervalIndex_succ]
      apply (le_div_iff₀ (hnreal' k)).2
      have hf := Int.lt_floor_add_one ((n (k + 1) : ℝ) * lowerEndpoint n k)
      push_cast at hf ⊢
      nlinarith [hnreal' k]
    have hupper : upperEndpoint n (k + 1) ≤ upperEndpoint n k := by
      change
        (((intervalIndex n (k + 1) : ℤ) : ℝ) + 3 / 4) /
            (n (k + 1) : ℝ) ≤ upperEndpoint n k
      rw [intervalIndex_succ]
      apply (div_le_iff₀ (hnreal' k)).2
      have hf := Int.floor_le ((n (k + 1) : ℝ) * lowerEndpoint n k)
      have hw :
          (n (k + 1) : ℝ) * lowerEndpoint n k + 2 ≤
            (n (k + 1) : ℝ) * upperEndpoint n k := by
        calc
          (n (k + 1) : ℝ) * lowerEndpoint n k + 2 =
              (n (k + 1) : ℝ) *
                (lowerEndpoint n k + 2 / (n (k + 1) : ℝ)) := by
                  field_simp [Nat.add_comm, ne_of_gt (hnreal' k)]
          _ ≤ (n (k + 1) : ℝ) * upperEndpoint n k :=
            mul_le_mul_of_nonneg_left hwidth (le_of_lt (hnreal' k))
      push_cast at hf ⊢
      nlinarith
    intro x hx
    exact ⟨hlower.trans hx.1, hx.2.trans hupper⟩
  have hInter :
      (⋂ k, Icc (lowerEndpoint n k) (upperEndpoint n k)).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun k => Icc (lowerEndpoint n k) (upperEndpoint n k)) hnext
      (fun k => Set.nonempty_Icc.2 (hlohi k)) isCompact_Icc (fun _ => isClosed_Icc)
  obtain ⟨θ, hθ⟩ := hInter
  refine ⟨θ, fun k => ?_⟩
  have hθk : θ ∈ Icc (lowerEndpoint n k) (upperEndpoint n k) :=
    Set.mem_iInter.1 hθ k
  have hm :
      1 / 4 ≤ θ * n k - (intervalIndex n k : ℤ) ∧
        θ * n k - (intervalIndex n k : ℤ) ≤ 3 / 4 := by
    constructor
    · have hbound := hθk.1
      rw [lowerEndpoint] at hbound
      have hmul := (div_le_iff₀ (hnreal k)).1 hbound
      nlinarith
    · have hbound := hθk.2
      rw [upperEndpoint] at hbound
      have hmul := (le_div_iff₀ (hnreal k)).1 hbound
      nlinarith
  have hfract :
      Int.fract (θ * n k) = θ * n k - (intervalIndex n k : ℤ) := by
    rw [← Int.fract_sub_intCast]
    apply Int.fract_eq_self.2
    constructor <;> nlinarith [hm.1, hm.2]
  rw [hfract]
  exact hm

/-! ## Four-colouring from one separated rotation -/

/-- The quarter of the unit interval containing the fractional part of
`θ * a`. -/
noncomputable def quarterColor (θ : ℝ) (a : ℕ) : Fin 4 :=
  ⟨⌊4 * Int.fract (θ * a)⌋₊, by
    rw [Nat.floor_lt (mul_nonneg (by norm_num) (Int.fract_nonneg _))]
    norm_num
    exact Int.fract_lt_one _⟩

/-- If `θ * (a-b)` lies in the middle half of the circle, `a` and `b` have
different quarter colours. -/
lemma quarterColor_ne_of_separated (θ : ℝ) (a b : ℕ) (_hba : b ≤ a)
    (hsep : 1 / 4 ≤ Int.fract (θ * (a - b)) ∧
      Int.fract (θ * (a - b)) ≤ 3 / 4) :
    quarterColor θ a ≠ quarterColor θ b := by
  intro hc
  have hfloor :
      ⌊4 * Int.fract (θ * a)⌋₊ = ⌊4 * Int.fract (θ * b)⌋₊ :=
    Fin.ext_iff.mp hc
  let fa := Int.fract (θ * a)
  let fb := Int.fract (θ * b)
  change ⌊4 * fa⌋₊ = ⌊4 * fb⌋₊ at hfloor
  have hfa0 : 0 ≤ fa := Int.fract_nonneg _
  have hfb0 : 0 ≤ fb := Int.fract_nonneg _
  have hfaUpper := Nat.lt_floor_add_one (4 * fa)
  have hfbUpper := Nat.lt_floor_add_one (4 * fb)
  have hfaLower : (↑⌊4 * fa⌋₊ : ℝ) ≤ 4 * fa :=
    Nat.floor_le (mul_nonneg (by norm_num) hfa0)
  have hfbLower : (↑⌊4 * fb⌋₊ : ℝ) ≤ 4 * fb :=
    Nat.floor_le (mul_nonneg (by norm_num) hfb0)
  have habs : -(1 / 4) < fa - fb ∧ fa - fb < 1 / 4 := by
    constructor
    · rw [← hfloor] at hfbUpper
      nlinarith [hfaLower]
    · rw [hfloor] at hfaUpper
      nlinarith [hfbLower]
  have hfracteq : Int.fract (θ * (a - b)) = Int.fract (fa - fb) := by
    apply Int.fract_eq_fract.2
    refine ⟨⌊(θ * a : ℝ)⌋ - ⌊(θ * b : ℝ)⌋, ?_⟩
    calc
      θ * ((a : ℝ) - b) - (fa - fb) =
          (θ * a - fa) - (θ * b - fb) := by ring
      _ = (⌊(θ * a : ℝ)⌋ : ℝ) - (⌊(θ * b : ℝ)⌋ : ℝ) := by
        dsimp only [fa, fb]
        rw [Int.self_sub_fract, Int.self_sub_fract]
      _ = (↑(⌊(θ * a : ℝ)⌋ - ⌊(θ * b : ℝ)⌋) : ℝ) := by
        push_cast
        ring
  rw [hfracteq] at hsep
  by_cases hfbfa : fb ≤ fa
  · have hsmall : 0 ≤ fa - fb ∧ fa - fb < 1 := by
      constructor <;> nlinarith [habs.1, habs.2]
    rw [Int.fract_eq_self.2 hsmall] at hsep
    nlinarith [habs.1, habs.2]
  · have hsmall : 0 ≤ fa - fb + 1 ∧ fa - fb + 1 < 1 := by
      constructor <;> nlinarith [habs.1, habs.2]
    have hfract : Int.fract (fa - fb) = fa - fb + 1 := by
      apply Int.fract_eq_iff.2
      refine ⟨hsmall.1, hsmall.2, -1, ?_⟩
      norm_num
    rw [hfract] at hsep
    nlinarith [habs.1, habs.2]

/-! ## Splitting a general lacunary sequence into high-ratio subsequences -/

/-- Iterating a one-step real growth estimate. -/
lemma lacunary_iterate (n : ℕ → ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hgrow : ∀ k, q * n k ≤ n (k + 1)) (k r : ℕ) :
    q ^ r * n k ≤ n (k + r) := by
  induction r with
  | zero => simp
  | succ r ihr =>
      calc
        q ^ (r + 1) * n k = q * (q ^ r * n k) := by
          rw [pow_succ]
          ring
        _ ≤ q * n (k + r) := mul_le_mul_of_nonneg_left ihr hq
        _ ≤ n (k + r + 1) := hgrow (k + r)
        _ = n (k + (r + 1)) := by congr 1

/-- Finitely many rotations suffice to separate every member of a positive
`q`-lacunary sequence, for every `q > 1`. -/
lemma exists_separated_family_of_lacunary (n : ℕ → ℕ) (hn : ∀ k, 0 < n k)
    (q : ℝ) (hq : 1 < q) (hgrow : ∀ k, q * n k ≤ n (k + 1)) :
    ∃ r : ℕ, 0 < r ∧ ∃ θ : Fin r → ℝ, ∀ k, ∃ j : Fin r,
      1 / 4 ≤ Int.fract (θ j * n k) ∧ Int.fract (θ j * n k) ≤ 3 / 4 := by
  obtain ⟨r, hrpow⟩ := pow_unbounded_of_one_lt (4 : ℝ) hq
  have hr : 0 < r := by
    by_contra! hr0
    have : r = 0 := Nat.eq_zero_of_le_zero hr0
    subst r
    norm_num at hrpow
  let subseq (j : Fin r) (t : ℕ) := n (j.val + r * t)
  have hnsub (j : Fin r) (t : ℕ) : 0 < subseq j t := hn _
  have hgsub (j : Fin r) (t : ℕ) : 4 * subseq j t ≤ subseq j (t + 1) := by
    have hiter := lacunary_iterate n q (by linarith) hgrow (j.val + r * t) r
    have hnonneg : (0 : ℝ) ≤ n (j.val + r * t) := Nat.cast_nonneg _
    have hp :
        (4 : ℝ) * n (j.val + r * t) ≤ q ^ r * n (j.val + r * t) :=
      mul_le_mul_of_nonneg_right hrpow.le hnonneg
    dsimp only [subseq]
    have hreal :
        (4 : ℝ) * n (j.val + r * t) ≤ (n (j.val + r * (t + 1)) : ℝ) :=
      hp.trans (by
        simpa [mul_add, add_assoc, add_comm, add_left_comm] using hiter)
    exact_mod_cast hreal
  have hsep (j : Fin r) : ∃ θ : ℝ, ∀ t,
      1 / 4 ≤ Int.fract (θ * subseq j t) ∧
        Int.fract (θ * subseq j t) ≤ 3 / 4 :=
    exists_separated_rotation_of_four_mul_le (subseq j) (hnsub j) (hgsub j)
  let θ (j : Fin r) := Classical.choose (hsep j)
  refine ⟨r, hr, θ, fun k ↦ ?_⟩
  let j : Fin r := ⟨k % r, Nat.mod_lt k hr⟩
  refine ⟨j, ?_⟩
  have hθ := Classical.choose_spec (hsep j) (k / r)
  have hindex : j.val + r * (k / r) = k := Nat.mod_add_div k r
  simpa only [θ, subseq, hindex] using hθ

/-! ## Assembly of the finite product colouring -/

/-- A finite separated family of rotations yields the required finite
colouring. -/
lemma hasAvoidingColoring_of_separatedFamily (n : ℕ → ℕ) (hn : ∀ k, 0 < n k)
    {r : ℕ} (_hr : 0 < r) (θ : Fin r → ℝ)
    (hsep : ∀ k, ∃ j : Fin r,
      1 / 4 ≤ Int.fract (θ j * n k) ∧ Int.fract (θ j * n k) ≤ 3 / 4) :
    HasAvoidingColoring n := by
  let e := Fintype.equivFin (Fin r → Fin 4)
  refine ⟨Fintype.card (Fin r → Fin 4),
    fun a ↦ e (fun j ↦ quarterColor (θ j) a), ?_⟩
  intro a b hab hcolor
  obtain ⟨k, hk⟩ := hab
  have hba : b ≤ a := by
    by_contra hnot
    have habzero : a - b = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hnot)
    have hnkzero : n k = 0 := hk.trans habzero
    exact (Nat.ne_of_gt (hn k)) hnkzero
  obtain ⟨j, hj⟩ := hsep k
  have hdiff : a - b = n k := hk.symm
  have hj' :
      1 / 4 ≤ Int.fract (θ j * (a - b)) ∧
        Int.fract (θ j * (a - b)) ≤ 3 / 4 := by
    have hcast : (a : ℝ) - b = (n k : ℝ) := by
      rw [← Nat.cast_sub hba, hdiff]
    simpa only [hcast] using hj
  have hne := quarterColor_ne_of_separated (θ j) a b hba hj'
  have hvec :
      (fun j ↦ quarterColor (θ j) a) =
        (fun j ↦ quarterColor (θ j) b) := e.injective hcolor
  exact hne (congrFun hvec j)

/-- **Erdős Problem 894.** Every positive lacunary sequence admits a finite
colouring of the natural numbers with no monochromatic difference belonging
to the sequence. -/
theorem erdos_894 {n : ℕ → ℕ} (hn : IsLacunary n) :
    HasAvoidingColoring n := by
  obtain ⟨hpos, ε, hε, hgrow⟩ := hn
  obtain ⟨r, hr, θ, hsep⟩ :=
    exists_separated_family_of_lacunary n hpos (1 + ε) (by linarith) hgrow
  exact hasAvoidingColoring_of_separatedFamily n hpos hr θ hsep

#print axioms erdos_894

end Erdos894
