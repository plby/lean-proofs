/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SmoothCommonDivisor
import ErdosProblems.Erdos822.CollisionEquation
import ErdosProblems.Erdos822.SmoothTotientPreserving

/-!
# Cofactors with the B1 smooth-preservation property

The source argument needs one exact local property of a cofactor: every
small prime power one step beyond its exponent in the cofactor already
divides its totient.  This finite predicate is the honest B1 interface.  It
implies that adjoining an outer prime preserves the smooth part of the
shifted value, hence collisions stay in one smooth class.
-/

namespace Erdos822

/-- Odd raw cofactors satisfying the exact smooth-preservation condition. -/
noncomputable def smoothPreservingOddCofactors (N y : ℕ) : Finset ℕ := by
  classical
  exact (oddRawCofactors N).filter fun m => SmoothTotientPreserving m y

@[simp]
theorem mem_smoothPreservingOddCofactors_iff
    {N y m : ℕ} :
    m ∈ smoothPreservingOddCofactors N y ↔
      m ∈ oddRawCofactors N ∧ SmoothTotientPreserving m y := by
  simp [smoothPreservingOddCofactors]

theorem smoothPreservingOddCofactors_subset_oddRaw (N y : ℕ) :
    smoothPreservingOddCofactors N y ⊆ oddRawCofactors N := by
  intro m hm
  exact (mem_smoothPreservingOddCofactors_iff.mp hm).1

/-- The shifted coefficient has the same smooth part as a B1 cofactor. -/
theorem smoothPart_shiftedTotient_eq_of_smoothPreserving
    {N y m : ℕ} (hm : m ∈ smoothPreservingOddCofactors N y) :
    smoothPart (shiftedTotient m) y = smoothPart m y := by
  have hmraw := (mem_smoothPreservingOddCofactors_iff.mp hm).1
  apply smoothPart_shiftedTotient_eq (oddRawCofactors_pos hmraw)
  exact (mem_smoothPreservingOddCofactors_iff.mp hm).2

/-- Adjoining a genuine outer prime also preserves the smooth part. -/
theorem smoothPart_shiftedTotient_outer_eq_of_smoothPreserving
    {N x y m p : ℕ}
    (hm : m ∈ smoothPreservingOddCofactors N y)
    (hp : p ∈ outerPrimes x m)
    (hmp : m < p) (hyp : y < p) :
    smoothPart (shiftedTotient (m * p)) y = smoothPart m y := by
  have hmraw := (mem_smoothPreservingOddCofactors_iff.mp hm).1
  exact smoothPart_shiftedTotient_mul_prime_eq
    (oddRawCofactors_pos hmraw)
    (mem_outerPrimes_iff.mp hp).2.2 hmp hyp
    (mem_smoothPreservingOddCofactors_iff.mp hm).2

/-- A collision between B1 cofactors stays in one smooth cofactor class. -/
theorem smoothPart_eq_of_outer_collision_smoothPreserving
    {N x y m m' p p' : ℕ}
    (hm : m ∈ smoothPreservingOddCofactors N y)
    (hm' : m' ∈ smoothPreservingOddCofactors N y)
    (hp : p ∈ outerPrimes x m) (hp' : p' ∈ outerPrimes x m')
    (hmp : m < p) (hm'p' : m' < p')
    (hyp : y < p) (hyp' : y < p')
    (hcollision :
      shiftedTotient (m * p) = shiftedTotient (m' * p')) :
    smoothPart m y = smoothPart m' y := by
  have h := congrArg (fun n => smoothPart n y) hcollision
  rw [smoothPart_shiftedTotient_outer_eq_of_smoothPreserving
        hm hp hmp hyp,
      smoothPart_shiftedTotient_outer_eq_of_smoothPreserving
        hm' hp' hm'p' hyp'] at h
  exact h

end Erdos822
