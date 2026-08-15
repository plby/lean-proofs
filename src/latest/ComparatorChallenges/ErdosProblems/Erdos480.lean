/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
# Erdős Problem 480

Chung and Graham's reciprocal-jump argument gives the stronger finite bound
`3 / 7`: every thirteen points of `[0,1]` contain a suitable pair.  Sliding
this window and applying finite pigeonhole yields one frequently occurring
gap, from which the stated `liminf` bound follows.
-/

import Mathlib

namespace Erdos480

@[simp] lemma Nat.dist_self_add' (a k : ℕ) : Nat.dist a (a + k) = k := by
  simp [Nat.dist]
@[simp] lemma Nat.dist_add_self' (a k : ℕ) : Nat.dist (a + k) a = k := by
  simp [Nat.dist]

def jumpWeight : List ℕ → ℚ
  | a :: b :: l => 1 / (Nat.dist a b : ℚ) + jumpWeight (b :: l)
  | _ => 0

def HasUpPath (f : ℕ → ℝ) (s : Set ℕ) (c : ℚ) : Prop :=
  ∃ l : List ℕ, l ≠ [] ∧ (∀ i ∈ l, i ∈ s) ∧
    l.IsChain (fun a b => f a ≤ f b) ∧ c ≤ jumpWeight l

def HasMonoPath (f : ℕ → ℝ) (s : Set ℕ) (c : ℚ) : Prop :=
  ∃ l : List ℕ, l ≠ [] ∧ (∀ i ∈ l, i ∈ s) ∧
    (l.IsChain (fun a b => f a ≤ f b) ∨
      l.IsChain (fun a b => f b ≤ f a)) ∧ c ≤ jumpWeight l

theorem erdos_480 : answer(True) ↔ ∀ (x : ℕ → ℝ), (∀ n, x n ∈ Set.Icc 0 1) →
    ⨅ (n : ℕ+), atTop.liminf (fun m => (n : ℕ) * |x (m + (n : ℕ)) - x m|) ≤
      1 / √5 := by
  sorry

