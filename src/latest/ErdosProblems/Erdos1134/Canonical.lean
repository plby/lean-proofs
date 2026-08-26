/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
MIT License

Copyright (c) 2026 Axiom Math.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Modified for this repository and Lean/Mathlib 4.33.0.
-/
/-
Erdős Problem 1134.
Informal proof: D. J. Crampin and A. J. W. Hilton.
Formal proof: AxiomProver, published by Axiom Math.
Source: https://www.erdosproblems.com/1134#post-7068
https://github.com/AxiomMath/erdos-public/blob/3ccf48c78b9df4aa26e1b2f90058bdd3f61da1ab/Erdos/Erdos1134/solution.lean
Original Lean version: 4.27.0.
Original Mathlib commit: a3a10db0e9d66acbebf76c5e6a135066525ac900.
-/
import ErdosProblems.Erdos1134.Definitions

namespace Erdos1134

-- Non-terminal operation type: f₆ or gₖ
inductive NTOp
  | f6 : NTOp                    -- x ↦ 6x + 1, multiplier 6
  | gk : ℕ → NTOp               -- x ↦ (3·2^k)x + (3·2^k - 2), multiplier 3·2^k
deriving DecidableEq

def NTOp.mult : NTOp → ℕ
  | .f6 => 6
  | .gk k => 3 * 2 ^ k

def NTOp.apply : NTOp → ℕ → ℕ
  | .f6, x => 6 * x + 1
  | .gk k, x => 3 * 2 ^ k * x + (3 * 2 ^ k - 2)

-- Apply a list of non-terminal operations left-to-right (leftmost = innermost)
def applyNTOps : List NTOp → ℕ → ℕ
  | [], x => x
  | op :: rest, x => applyNTOps rest (op.apply x)

def ntOpsMult : List NTOp → ℕ
  | [] => 1
  | op :: rest => op.mult * ntOpsMult rest

-- A canonical word: a list of non-terminal ops plus an OUTER terminal f₂ exponent
structure CanonWord where
  ops : List NTOp     -- non-terminal operations (applied first, left-to-right)
  terminal : ℕ        -- OUTER exponent t for terminal f₂^t (applied LAST)

-- Apply a canonical word to input x:
-- First apply the non-terminal ops left-to-right, then apply f₂^t (outer terminal)
def CanonWord.apply (w : CanonWord) (x : ℕ) : ℕ :=
  let y := applyNTOps w.ops x
  2 ^ w.terminal * y + (2 ^ w.terminal - 1)

-- Multiplier of a canonical word
def CanonWord.mult (w : CanonWord) : ℕ :=
  ntOpsMult w.ops * 2 ^ w.terminal

lemma applyNTOps_append (ops1 ops2 : List NTOp) (x : ℕ) :
    applyNTOps (ops1 ++ ops2) x = applyNTOps ops2 (applyNTOps ops1 x) := by
  induction ops1 generalizing x with
  | nil => simp [applyNTOps]
  | cons op rest ih => simp [applyNTOps, ih]

lemma ntOpsMult_append (ops1 ops2 : List NTOp) :
    ntOpsMult (ops1 ++ ops2) = ntOpsMult ops1 * ntOpsMult ops2 := by
  induction ops1 with
  | nil => simp [ntOpsMult]
  | cons op rest ih => simp [ntOpsMult, ih, mul_assoc]

-- Countable instances (needed for Dirichlet series tsum)
instance : Countable NTOp := by
  exact Function.Injective.countable
    (f := fun op => match op with | .f6 => Sum.inl () | .gk k => Sum.inr k)
    (by
      intro a b h
      match a, b with
      | .f6, .f6 => rfl
      | .gk m, .gk n => exact congrArg _ (Sum.inr.inj h))

instance : Countable CanonWord :=
  (Equiv.mk (fun w => (w.ops, w.terminal)) (fun p => ⟨p.1, p.2⟩)
    (fun _ => rfl) (fun _ => rfl)).injective.countable

-- Multiplier is always positive
lemma ntOpsMult_pos (ops : List NTOp) : 0 < ntOpsMult ops := by
  induction ops with
  | nil => simp [ntOpsMult]
  | cons op rest ih =>
    simp only [ntOpsMult]
    apply Nat.mul_pos
    · cases op with
      | f6 => decide
      | gk k => exact Nat.mul_pos (by omega) (by positivity)
    · exact ih

lemma canonword_mult_pos (w : CanonWord) : 0 < w.mult := by
  exact Nat.mul_pos (ntOpsMult_pos w.ops) (by positivity)

lemma f6_f2t_identity (y t' : ℕ) :
    6 * (2 ^ (t' + 1) * y + (2 ^ (t' + 1) - 1)) + 1 =
    4 * (3 * 2 ^ t' * y + (3 * 2 ^ t' - 2)) + 3 := by
  have hp : 1 ≤ 2 ^ t' := Nat.one_le_pow t' 2 (by omega)
  have h1 : 2 ^ (t' + 1) = 2 * 2 ^ t' := by ring
  have h2 : 2 * 2 ^ t' * y = 2 * (2 ^ t' * y) := by ring
  have h3 : 3 * 2 ^ t' * y = 3 * (2 ^ t' * y) := by ring
  have h4 : 3 * 2 ^ t' = 3 * (2 ^ t') := by ring
  rw [h1, h2, h3, h4]
  set p := 2 ^ t'
  omega

lemma canonical_path_exists (a : ℕ) (ha : ErdosSetA a) :
    ∃ w : CanonWord, w.apply 1 = a := by
  induction ha with
  | base =>
    -- a = 1: use ⟨[], 0⟩
    exact ⟨⟨[], 0⟩, by simp [CanonWord.apply, applyNTOps]⟩
  | double_plus_one x _ ih =>
    -- a = 2x+1: increment outer terminal
    obtain ⟨⟨ops, t⟩, hw⟩ := ih
    refine ⟨⟨ops, t + 1⟩, ?_⟩
    simp only [CanonWord.apply] at hw ⊢
    set y := applyNTOps ops 1
    set p := 2 ^ t
    have hp : 1 ≤ p := Nat.one_le_pow t 2 (by omega)
    have h1 : 2 ^ (t + 1) = 2 * p := by ring
    rw [h1]
    have h2 : 2 * p * y + (2 * p - 1) = 2 * (p * y + (p - 1)) + 1 := by
      have : 2 * p * y = 2 * (p * y) := by ring
      rw [this]; set q := p * y; omega
    rw [h2, hw]
  | triple_plus_one x _ ih =>
    -- a = 3x+1: absorb outer terminal into gk, reset terminal to 0
    obtain ⟨⟨ops, t⟩, hw⟩ := ih
    refine ⟨⟨ops ++ [NTOp.gk t], 0⟩, ?_⟩
    simp only [CanonWord.apply] at hw ⊢
    rw [applyNTOps_append]
    simp only [applyNTOps, NTOp.apply]
    set y := applyNTOps ops 1
    set p := 2 ^ t
    have hp : 1 ≤ p := Nat.one_le_pow t 2 (by omega)
    have h1 : 3 * p * y + (3 * p - 2) = 3 * (p * y + (p - 1)) + 1 := by
      have : 3 * p * y = 3 * (p * y) := by ring
      rw [this]; set q := p * y; omega
    omega
  | sextuple_plus_one x _ ih =>
    -- a = 6x+1: case split on terminal
    obtain ⟨⟨ops, t⟩, hw⟩ := ih
    match t with
    | 0 =>
      -- t = 0: append f6, terminal stays 0
      refine ⟨⟨ops ++ [NTOp.f6], 0⟩, ?_⟩
      simp only [CanonWord.apply] at hw ⊢
      rw [applyNTOps_append]
      simp only [applyNTOps, NTOp.apply]
      omega
    | t' + 1 =>
      -- t ≥ 1: use f6_f2t_identity to get ⟨ops ++ [gk t'], 2⟩
      refine ⟨⟨ops ++ [NTOp.gk t'], 2⟩, ?_⟩
      simp only [CanonWord.apply] at hw ⊢
      rw [applyNTOps_append]
      simp only [applyNTOps, NTOp.apply]
      set y := applyNTOps ops 1
      have hf6 := f6_f2t_identity y t'
      omega

lemma ntop_apply_succ_le (op : NTOp) (x : ℕ) :
    op.apply x + 1 ≤ op.mult * (x + 1) := by
  cases op with
  | f6 => simp [NTOp.apply, NTOp.mult]; omega
  | gk k =>
    simp only [NTOp.apply, NTOp.mult]
    have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
    have h2p : 2 ≤ 3 * 2 ^ k := by omega
    have lhs_eq : 3 * 2 ^ k * x + (3 * 2 ^ k - 2) + 1 = 3 * 2 ^ k * x + (3 * 2 ^ k - 1) := by omega
    have rhs_eq : 3 * 2 ^ k * (x + 1) = 3 * 2 ^ k * x + 3 * 2 ^ k := by ring
    rw [lhs_eq, rhs_eq]; omega

lemma ntop_apply_ge (op : NTOp) (x : ℕ) :
    op.mult * x ≤ op.apply x := by
  cases op with
  | f6 => simp [NTOp.apply, NTOp.mult]
  | gk k => simp [NTOp.apply, NTOp.mult]

lemma applyNTOps_succ_le (ops : List NTOp) (x : ℕ) :
    applyNTOps ops x + 1 ≤ ntOpsMult ops * (x + 1) := by
  induction ops generalizing x with
  | nil => simp [applyNTOps, ntOpsMult]
  | cons op rest ih =>
    simp only [applyNTOps, ntOpsMult]
    calc applyNTOps rest (op.apply x) + 1
        ≤ ntOpsMult rest * (op.apply x + 1) := ih (op.apply x)
      _ ≤ ntOpsMult rest * (op.mult * (x + 1)) := Nat.mul_le_mul_left _ (ntop_apply_succ_le op x)
      _ = op.mult * ntOpsMult rest * (x + 1) := by ring

lemma applyNTOps_ge (ops : List NTOp) (x : ℕ) :
    ntOpsMult ops * x ≤ applyNTOps ops x := by
  induction ops generalizing x with
  | nil => simp [applyNTOps, ntOpsMult]
  | cons op rest ih =>
    simp only [applyNTOps, ntOpsMult]
    calc op.mult * ntOpsMult rest * x
        = ntOpsMult rest * (op.mult * x) := by ring
      _ ≤ ntOpsMult rest * op.apply x := Nat.mul_le_mul_left _ (ntop_apply_ge op x)
      _ ≤ applyNTOps rest (op.apply x) := ih (op.apply x)

lemma value_le_twice_mult (w : CanonWord) :
    w.apply 1 + 1 ≤ 2 * w.mult := by
  simp only [CanonWord.apply, CanonWord.mult]
  set y := applyNTOps w.ops 1
  set p := 2 ^ w.terminal
  have hp : 1 ≤ p := Nat.one_le_pow w.terminal 2 (by omega)
  have lhs_eq : p * y + (p - 1) + 1 = p * (y + 1) := by
    have : p * (y + 1) = p * y + p := by ring
    omega
  have rhs_eq : 2 * (ntOpsMult w.ops * p) = p * (2 * ntOpsMult w.ops) := by ring
  rw [lhs_eq, rhs_eq]
  apply Nat.mul_le_mul_left
  have := applyNTOps_succ_le w.ops 1
  linarith

lemma value_ge_mult (w : CanonWord) :
    w.mult ≤ w.apply 1 := by
  simp only [CanonWord.apply, CanonWord.mult]
  set y := applyNTOps w.ops 1
  set p := 2 ^ w.terminal
  have hp : 1 ≤ p := Nat.one_le_pow w.terminal 2 (by omega)
  have hge := applyNTOps_ge w.ops 1
  simp only [mul_one] at hge
  calc ntOpsMult w.ops * p ≤ y * p := Nat.mul_le_mul_right p hge
    _ = p * y := by ring
    _ ≤ p * y + (p - 1) := Nat.le_add_right _ _

lemma rankin_trick {α : Type*} (F : Finset α) (f : α → ℕ) (N : ℕ) (s : ℝ)
    (hs : 0 < s)
    (hf : ∀ a ∈ F, 0 < f a ∧ f a ≤ N) :
    (F.card : ℝ) ≤ (N : ℝ) ^ s * F.sum (fun a => ((f a : ℝ) ^ (-s))) := by
  calc (F.card : ℝ)
      = F.sum (fun _ => (1 : ℝ)) := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ F.sum (fun a => (N : ℝ) ^ s * ((f a : ℝ) ^ (-s))) := by
        apply Finset.sum_le_sum
        intro a ha
        obtain ⟨hfa_pos, hfa_le⟩ := hf a ha
        have hfa_cast_pos : (0 : ℝ) < (f a : ℝ) := Nat.cast_pos.mpr hfa_pos
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        rw [le_mul_inv_iff₀ (Real.rpow_pos_of_pos hfa_cast_pos s)]
        rw [one_mul]
        exact Real.rpow_le_rpow (le_of_lt hfa_cast_pos) (Nat.cast_le.mpr hfa_le) (le_of_lt hs)
    _ = (N : ℝ) ^ s * F.sum (fun a => ((f a : ℝ) ^ (-s))) := by
        rw [← Finset.mul_sum]

lemma erdos_injection_canonical (N : ℕ) :
    ∃ (W : Finset CanonWord),
      Set.ncard (Set.ofPred ErdosSetA ∩ Set.Iic N) ≤ W.card ∧
      ∀ w ∈ W, 0 < w.mult ∧ w.mult ≤ N := by
  classical
  set S := Set.ofPred ErdosSetA ∩ Set.Iic N with hS_def
  have hS_finite : S.Finite := Set.Finite.subset (Set.finite_Iic N) Set.inter_subset_right
  let g : ℕ → CanonWord := fun a =>
    if h : ErdosSetA a then (canonical_path_exists a h).choose else ⟨[], 0⟩
  have g_spec : ∀ a (ha : ErdosSetA a), (g a).apply 1 = a := by
    intro a ha
    change (if h : ErdosSetA a then (canonical_path_exists a h).choose else ⟨[], 0⟩).apply 1 = a
    rw [dif_pos ha]
    exact (canonical_path_exists a ha).choose_spec
  have g_inj : Set.InjOn g S := by
    intro a ha b hb hab
    have ha' : ErdosSetA a := ha.1
    have hb' : ErdosSetA b := hb.1
    have : (g a).apply 1 = (g b).apply 1 := by rw [hab]
    rw [g_spec a ha', g_spec b hb'] at this
    exact this
  have himg_finite : (g '' S).Finite := hS_finite.image g
  refine ⟨himg_finite.toFinset, ?_, ?_⟩
  · have h1 : S.ncard = (g '' S).ncard := g_inj.ncard_image.symm
    have h2 : (g '' S).ncard = himg_finite.toFinset.card :=
      Set.ncard_eq_toFinset_card _ himg_finite
    omega
  · intro w hw
    rw [Set.Finite.mem_toFinset] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    have ha_A : ErdosSetA a := ha.1
    have ha_le : a ≤ N := ha.2
    constructor
    · exact canonword_mult_pos (g a)
    · calc (g a).mult ≤ (g a).apply 1 := value_ge_mult (g a)
        _ = a := g_spec a ha_A
        _ ≤ N := ha_le

end Erdos1134
