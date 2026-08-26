/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.CollisionEquation
import ErdosProblems.Erdos822.OuterCollisionPairs
import ErdosProblems.Erdos822.ShiftedCoefficient

/-!
# Divisibility forced by a nonempty collision fiber

The common shifted coefficient is not merely a gcd weight.  If an outer
collision exists, it divides the totient difference, and hence also the
cofactor difference.  This is the arithmetic support restriction behind the
large/medium/small common-divisor decomposition.
-/

namespace Erdos822

/-- A nonempty outer collision forces the common shifted coefficient to
divide the absolute totient difference. -/
theorem shiftedCoefficientGcd_dvd_totientNatAbs_of_nonempty
    {x m m' : ℕ}
    (hm : 0 < m) (hm' : 0 < m')
    (hlarge : ∀ p ∈ outerPrimes x m, m < p)
    (hlarge' : ∀ p ∈ outerPrimes x m', m' < p)
    (hne : (outerCollisionPairs x m m').Nonempty) :
    shiftedCoefficientGcd m m' ∣
      ((Nat.totient m : ℤ) - Nat.totient m').natAbs := by
  obtain ⟨⟨p, p'⟩, hpairs⟩ := hne
  rw [mem_outerCollisionPairs_iff] at hpairs
  have hZ :
      (shiftedCoefficientGcd m m' : ℤ) ∣
        (Nat.totient m : ℤ) - Nat.totient m' :=
    int_dvd_totient_sub_of_outer_collision
      hpairs.1 hpairs.2.1 hm hm'
      (hlarge p hpairs.1) (hlarge' p' hpairs.2.1)
      (by
        unfold shiftedCoefficientGcd
        exact Nat.gcd_dvd_left _ _)
      (by
        unfold shiftedCoefficientGcd
        exact Nat.gcd_dvd_right _ _)
      hpairs.2.2
  simpa using (Int.natAbs_dvd_natAbs.mpr hZ)

/-- Therefore a nonempty outer collision forces the common shifted
coefficient to divide the distance between the two cofactors. -/
theorem shiftedCoefficientGcd_dvd_dist_of_nonempty
    {x m m' : ℕ}
    (hm : 0 < m) (hm' : 0 < m')
    (hlarge : ∀ p ∈ outerPrimes x m, m < p)
    (hlarge' : ∀ p ∈ outerPrimes x m', m' < p)
    (hne : (outerCollisionPairs x m m').Nonempty) :
    shiftedCoefficientGcd m m' ∣ Nat.dist m m' := by
  have htotZ :
      (shiftedCoefficientGcd m m' : ℤ) ∣
        (Nat.totient m : ℤ) - Nat.totient m' := by
    apply Int.natAbs_dvd_natAbs.mp
    simpa using shiftedCoefficientGcd_dvd_totientNatAbs_of_nonempty
      hm hm' hlarge hlarge' hne
  have hleft :
      (shiftedCoefficientGcd m m' : ℤ) ∣ (shiftedTotient m : ℤ) := by
    exact Int.natCast_dvd_natCast.mpr (by
      unfold shiftedCoefficientGcd
      exact Nat.gcd_dvd_left _ _)
  have hright :
      (shiftedCoefficientGcd m m' : ℤ) ∣ (shiftedTotient m' : ℤ) := by
    exact Int.natCast_dvd_natCast.mpr (by
      unfold shiftedCoefficientGcd
      exact Nat.gcd_dvd_right _ _)
  have hshiftZ :
      (shiftedCoefficientGcd m m' : ℤ) ∣
        (shiftedTotient m : ℤ) - shiftedTotient m' :=
    dvd_sub hleft hright
  have hdistZ :
      (shiftedCoefficientGcd m m' : ℤ) ∣
        (m : ℤ) - m' := by
    have hEq :
        ((shiftedTotient m : ℤ) - shiftedTotient m') -
            ((Nat.totient m : ℤ) - Nat.totient m') =
          (m : ℤ) - m' := by
      simp [shiftedTotient]
      ring
    rw [← hEq]
    exact dvd_sub hshiftZ htotZ
  have habs :
      shiftedCoefficientGcd m m' ∣
        ((m : ℤ) - m').natAbs :=
    by simpa using (Int.natAbs_dvd_natAbs.mpr hdistZ)
  by_cases hle : m ≤ m'
  · rw [Int.natAbs_natCast_sub_natCast_of_le hle] at habs
    rw [Nat.dist_eq_sub_of_le hle]
    exact habs
  · have hrev : m' ≤ m := by omega
    rw [Int.natAbs_natCast_sub_natCast_of_ge hrev] at habs
    rw [Nat.dist_eq_sub_of_le_right hrev]
    exact habs

end Erdos822
