/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.OuterEnergy
import ErdosProblems.Erdos980.External.Erdos822.RefinedCollisionFiber

/-!
# Summing fixed-cofactor collision bounds

This file is deliberately analytic-free.  It turns any real-valued
majorant for every off-diagonal cofactor fiber into a bound for the full
shifted-totient collision energy, while keeping the exact diagonal term.
-/

namespace Erdos822

open scoped BigOperators Finset

theorem outerInputs_card_le_succ
    (B : ℕ → Finset ℕ) (x : ℕ) :
    (outerInputs B x).card ≤ x + 1 := by
  calc
    (outerInputs B x).card ≤ (Finset.range (x + 1)).card := by
      apply Finset.card_le_card
      intro n hn
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (outerInputs_bounded B x n hn)
    _ = x + 1 := Finset.card_range _

/-- A pointwise real majorant for every off-diagonal fixed-cofactor fiber
sums to a majorant for the explicit off-diagonal energy. -/
theorem offDiagonalOuterCollisionEnergy_cast_le_sum_majorant
    (B : ℕ → Finset ℕ) (x : ℕ) (G : ℕ → ℕ → ℝ)
    (hG : ∀ m ∈ B x, ∀ m' ∈ (B x).erase m,
      ((outerCollisionPairs x m m').card : ℝ) ≤ G m m') :
    (offDiagonalOuterCollisionEnergy B x : ℝ) ≤
      ∑ m ∈ B x, ∑ m' ∈ (B x).erase m, G m m' := by
  unfold offDiagonalOuterCollisionEnergy
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro m hm
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro m' hm'
  exact hG m hm m' hm'

/-- The diagonal/off-diagonal decomposition plus a summed fiber majorant
gives a full real collision-energy bound. -/
theorem collisionEnergy_outerInputs_cast_le_card_add_sum_majorant
    (B : ℕ → Finset ℕ) (x : ℕ) (G : ℕ → ℕ → ℝ)
    (hpos : ∀ m ∈ B x, 0 < m)
    (hlarge : ∀ m ∈ B x, ∀ p ∈ outerPrimes x m, m < p)
    (hG : ∀ m ∈ B x, ∀ m' ∈ (B x).erase m,
      ((outerCollisionPairs x m m').card : ℝ) ≤ G m m') :
    (collisionEnergy (outerInputs B x) shiftedTotient : ℝ) ≤
      ((outerInputs B x).card : ℝ) +
        ∑ m ∈ B x, ∑ m' ∈ (B x).erase m, G m m' := by
  rw [collisionEnergy_outerInputs_eq_card_add_offDiagonal B x hpos hlarge]
  push_cast
  simpa [add_comm] using
    (add_le_add_left
      (offDiagonalOuterCollisionEnergy_cast_le_sum_majorant B x G hG)
      ((outerInputs B x).card : ℝ))

/-- If the summed off-diagonal majorant is linear, then the whole energy is
linear with only a fixed additive allowance for the diagonal cardinality. -/
theorem collisionEnergy_outerInputs_cast_le_of_sum_majorant
    (B : ℕ → Finset ℕ) (x : ℕ) (G : ℕ → ℕ → ℝ) (C : ℝ)
    (hx : 1 ≤ x)
    (hpos : ∀ m ∈ B x, 0 < m)
    (hlarge : ∀ m ∈ B x, ∀ p ∈ outerPrimes x m, m < p)
    (hG : ∀ m ∈ B x, ∀ m' ∈ (B x).erase m,
      ((outerCollisionPairs x m m').card : ℝ) ≤ G m m')
    (hsum : ∑ m ∈ B x, ∑ m' ∈ (B x).erase m, G m m' ≤
      C * (x : ℝ)) :
    (collisionEnergy (outerInputs B x) shiftedTotient : ℝ) ≤
      (C + 2) * (x : ℝ) := by
  have henergy :=
    collisionEnergy_outerInputs_cast_le_card_add_sum_majorant
      B x G hpos hlarge hG
  have hcard : ((outerInputs B x).card : ℝ) ≤ (x : ℝ) + 1 := by
    exact_mod_cast outerInputs_card_le_succ B x
  calc
    (collisionEnergy (outerInputs B x) shiftedTotient : ℝ) ≤
        ((outerInputs B x).card : ℝ) +
          ∑ m ∈ B x, ∑ m' ∈ (B x).erase m, G m m' := henergy
    _ ≤ ((x : ℝ) + 1) + C * (x : ℝ) :=
      add_le_add hcard hsum
    _ ≤ (C + 2) * (x : ℝ) := by
      have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
      nlinarith

end Erdos822
