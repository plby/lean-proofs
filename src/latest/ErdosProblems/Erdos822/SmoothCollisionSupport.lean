/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SmoothPreservingCofactors

/-!
# Smooth classes support every B1 collision fiber

The B1 preservation statement is pointwise in a chosen pair of outer
primes.  Energy sums use the proposition that the whole fixed-cofactor
collision fiber is nonempty.  This file records the exact conversion and
the resulting vanishing of every cross-class fiber.
-/

namespace Erdos822

/-- A nonempty collision fiber between B1 cofactors lies in one smooth
cofactor class. -/
theorem smoothPart_eq_of_nonempty_outerCollisionPairs_smoothPreserving
    {N x y m m' : ℕ}
    (hm : m ∈ smoothPreservingOddCofactors N y)
    (hm' : m' ∈ smoothPreservingOddCofactors N y)
    (hlarge : ∀ p ∈ outerPrimes x m, m < p)
    (hlarge' : ∀ p ∈ outerPrimes x m', m' < p)
    (hy : ∀ p ∈ outerPrimes x m, y < p)
    (hy' : ∀ p ∈ outerPrimes x m', y < p)
    (hne : (outerCollisionPairs x m m').Nonempty) :
    smoothPart m y = smoothPart m' y := by
  obtain ⟨⟨p, p'⟩, hpp'⟩ := hne
  rw [mem_outerCollisionPairs_iff] at hpp'
  exact smoothPart_eq_of_outer_collision_smoothPreserving
    hm hm' hpp'.1 hpp'.2.1
    (hlarge p hpp'.1) (hlarge' p' hpp'.2.1)
    (hy p hpp'.1) (hy' p' hpp'.2.1) hpp'.2.2

/-- Distinct smooth classes have no outer collision fiber once both
cofactors satisfy B1. -/
theorem outerCollisionPairs_eq_empty_of_smoothPart_ne_smoothPreserving
    {N x y m m' : ℕ}
    (hm : m ∈ smoothPreservingOddCofactors N y)
    (hm' : m' ∈ smoothPreservingOddCofactors N y)
    (hlarge : ∀ p ∈ outerPrimes x m, m < p)
    (hlarge' : ∀ p ∈ outerPrimes x m', m' < p)
    (hy : ∀ p ∈ outerPrimes x m, y < p)
    (hy' : ∀ p ∈ outerPrimes x m', y < p)
    (hclass : smoothPart m y ≠ smoothPart m' y) :
    outerCollisionPairs x m m' = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hne
  exact hclass
    (smoothPart_eq_of_nonempty_outerCollisionPairs_smoothPreserving
      hm hm' hlarge hlarge' hy hy' hne)

end Erdos822
