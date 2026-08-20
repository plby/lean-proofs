/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.ReducedCollision
import ErdosProblems.Erdos980.External.Erdos822.SlopeAwareEuler

/-!
# Controlling the deleted-slope Euler factors

The primitive slopes are quotients of the two shifted totients by their
common gcd.  Consequently every prime deleted from the affine sieve already
divides one of the two original shifted coefficients.  This is the precise
bridge from the finite sieve to condition (B5) in the GIL construction.
-/

namespace Erdos822

open scoped BigOperators

/-- Reciprocal mass, in a finite sieve interval, of primes dividing the
shifted totient coefficient attached to m. -/
noncomputable def shiftedTotientReciprocalMass (m z y : ℕ) : ℝ :=
  ∑ p ∈ Erdos851.sievePrimes z y,
    if p ∣ shiftedTotient m then (1 : ℝ) / p else 0

/-- A prime dividing the left primitive slope already divides the original
left shifted coefficient. -/
theorem dvd_shiftedTotient_of_dvd_reducedCollisionLeft
    {m m' p : ℕ} (hp : p ∣ reducedCollisionLeft m m') :
    p ∣ shiftedTotient m := by
  unfold reducedCollisionLeft at hp
  exact hp.trans (Nat.div_dvd_of_dvd
    (Nat.gcd_dvd_left (shiftedTotient m) (shiftedTotient m')))

/-- The symmetric statement for the right primitive slope. -/
theorem dvd_shiftedTotient_of_dvd_reducedCollisionRight
    {m m' p : ℕ} (hp : p ∣ reducedCollisionRight m m') :
    p ∣ shiftedTotient m' := by
  unfold reducedCollisionRight at hp
  exact hp.trans (Nat.div_dvd_of_dvd
    (Nat.gcd_dvd_right (shiftedTotient m) (shiftedTotient m')))

/-- The reciprocal mass of deleted slope primes is bounded by the two
shifted-coefficient prime masses. -/
theorem slopeReciprocalMass_reducedCollision_le_shiftedTotientMass
    (m m' z y : ℕ) :
    slopeReciprocalMass
        (reducedCollisionRight m m') (reducedCollisionLeft m m') z y ≤
      shiftedTotientReciprocalMass m z y +
        shiftedTotientReciprocalMass m' z y := by
  unfold slopeReciprocalMass shiftedTotientReciprocalMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  by_cases hleft : p ∣ reducedCollisionLeft m m'
  · have hshift : p ∣ shiftedTotient m :=
      dvd_shiftedTotient_of_dvd_reducedCollisionLeft hleft
    simp [hleft, hshift]
    positivity
  · by_cases hright : p ∣ reducedCollisionRight m m'
    · have hshift : p ∣ shiftedTotient m' :=
        dvd_shiftedTotient_of_dvd_reducedCollisionRight hright
      simp [hleft, hright, hshift]
      positivity
    · simp [hleft, hright]
      positivity

/-- In particular, a uniform bound on the two shifted prime masses gives a
uniform exponential bound for every slope-prime loss in the fixed-cofactor
fiber sieve. -/
theorem slopePrimeLoss_reducedCollision_le_exp_shiftedTotientMass
    (h m m' z y : ℕ) (hz : 2 ≤ z) :
    slopePrimeLoss h
        (reducedCollisionRight m m') (reducedCollisionLeft m m') z y ≤
      Real.exp
        (6 * (shiftedTotientReciprocalMass m z y +
          shiftedTotientReciprocalMass m' z y)) := by
  calc
    slopePrimeLoss h
        (reducedCollisionRight m m') (reducedCollisionLeft m m') z y ≤
        Real.exp
          (6 * slopeReciprocalMass
            (reducedCollisionRight m m') (reducedCollisionLeft m m') z y) :=
      slopePrimeLoss_le_exp_slopeReciprocalMass _ _ _ _ _ hz
    _ ≤ Real.exp
          (6 * (shiftedTotientReciprocalMass m z y +
            shiftedTotientReciprocalMass m' z y)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left
        (slopeReciprocalMass_reducedCollision_le_shiftedTotientMass
          m m' z y) (by norm_num)

end Erdos822
