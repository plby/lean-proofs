/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.ReducedCollision

/-!
# Determinant of a primitive collision fiber

Although a least collision supplies the two constant prime terms in the
affine parameterization, its determinant is independent of that choice: it
is the totient difference divided by the common shifted-totient gcd.
-/

namespace Erdos822

/-- Absolute totient difference after dividing by the common shifted
coefficient gcd. -/
def reducedTotientDet (m m' : ℕ) : ℕ :=
  ((Nat.totient m : ℤ) - Nat.totient m').natAbs /
    Nat.gcd (shiftedTotient m) (shiftedTotient m')

theorem affineDetNat_reducedCollision_eq_reducedTotientDet_of_collision
    {x m m' q q' : ℕ}
    (hq : q ∈ outerPrimes x m) (hq' : q' ∈ outerPrimes x m')
    (hm : 0 < m) (hm' : 0 < m')
    (hmq : m < q) (hm'q' : m' < q')
    (hcollision : shiftedTotient (m * q) = shiftedTotient (m' * q')) :
    affineDetNat (reducedCollisionRight m m') q
        (reducedCollisionLeft m m') q' =
      reducedTotientDet m m' := by
  let g := Nat.gcd (shiftedTotient m) (shiftedTotient m')
  have hg : 0 < g :=
    Nat.gcd_pos_of_pos_left _ (shiftedTotient_pos_of_pos hm)
  have hleft :
      reducedCollisionLeft m m' * g = shiftedTotient m := by
    unfold reducedCollisionLeft
    exact Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hright :
      reducedCollisionRight m m' * g = shiftedTotient m' := by
    unfold reducedCollisionRight
    exact Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  have hlin :=
    outer_collision_linear_eq_int hq hq' hm hm' hmq hm'q' hcollision
  have hrawZ :
      (shiftedTotient m : ℤ) * q + Nat.totient m' =
        (shiftedTotient m' : ℤ) * q' + Nat.totient m := by
    linarith
  have hmulZ :
      (g : ℤ) *
          ((reducedCollisionLeft m m' : ℤ) * q -
            (reducedCollisionRight m m' : ℤ) * q') =
        (Nat.totient m : ℤ) - Nat.totient m' := by
    have hleftZ : (shiftedTotient m : ℤ) =
        (reducedCollisionLeft m m' : ℤ) * g := by
      exact_mod_cast hleft.symm
    have hrightZ : (shiftedTotient m' : ℤ) =
        (reducedCollisionRight m m' : ℤ) * g := by
      exact_mod_cast hright.symm
    rw [hleftZ, hrightZ] at hrawZ
    linarith
  have habs := congrArg Int.natAbs hmulZ
  have hneg :
      (reducedCollisionLeft m m' : ℤ) * q -
          (reducedCollisionRight m m' : ℤ) * q' =
        -((reducedCollisionRight m m' : ℤ) * q' -
          (reducedCollisionLeft m m' : ℤ) * q) := by
    ring
  have hmulNat :
      g * affineDetNat (reducedCollisionRight m m') q
          (reducedCollisionLeft m m') q' =
        ((Nat.totient m : ℤ) - Nat.totient m').natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_natCast, hneg, Int.natAbs_neg] at habs
    simpa [affineDetNat, Nat.mul_comm] using habs
  unfold reducedTotientDet
  exact Nat.eq_div_of_mul_eq_right hg.ne' hmulNat

end Erdos822
