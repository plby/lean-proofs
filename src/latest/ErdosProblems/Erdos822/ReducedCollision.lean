/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.OddCofactorLayers
import ErdosProblems.Erdos822.LinearPrimePairs

/-!
# Primitive coefficients from two outer collisions

Two collisions with the same cofactor pair have the same affine constant
terms.  Subtracting them removes those constants; dividing the two
coefficients by their gcd produces exactly the primitive natural equation
handled by LinearPrimePairs.
-/

namespace Erdos822

/-- Left primitive coefficient attached to a cofactor pair. -/
def reducedCollisionLeft (m m' : ℕ) : ℕ :=
  shiftedTotient m / Nat.gcd (shiftedTotient m) (shiftedTotient m')

/-- Right primitive coefficient attached to a cofactor pair. -/
def reducedCollisionRight (m m' : ℕ) : ℕ :=
  shiftedTotient m' / Nat.gcd (shiftedTotient m) (shiftedTotient m')

theorem shiftedTotient_pos_of_pos {m : ℕ} (hm : 0 < m) :
    0 < shiftedTotient m := by
  exact hm.trans_le (Nat.le_add_right m (Nat.totient m))

theorem reducedCollisionLeft_pos {m m' : ℕ}
    (hm : 0 < m) (hm' : 0 < m') :
    0 < reducedCollisionLeft m m' := by
  unfold reducedCollisionLeft
  apply Nat.div_pos
  · exact Nat.gcd_le_left _ (shiftedTotient_pos_of_pos hm)
  · exact Nat.gcd_pos_of_pos_left _ (shiftedTotient_pos_of_pos hm)

theorem reducedCollisionRight_pos {m m' : ℕ}
    (hm : 0 < m) (hm' : 0 < m') :
    0 < reducedCollisionRight m m' := by
  unfold reducedCollisionRight
  apply Nat.div_pos
  · exact Nat.gcd_le_right _ (shiftedTotient_pos_of_pos hm')
  · exact Nat.gcd_pos_of_pos_right _ (shiftedTotient_pos_of_pos hm')

theorem reducedCollision_coprime {m m' : ℕ}
    (hm : 0 < m) (hm' : 0 < m') :
    (reducedCollisionLeft m m').Coprime
      (reducedCollisionRight m m') := by
  unfold reducedCollisionLeft reducedCollisionRight
  apply Nat.coprime_div_gcd_div_gcd
  exact Nat.gcd_pos_of_pos_right _
    (shiftedTotient_pos_of_pos hm')

/-- Two outer collisions with the same cofactor pair yield the primitive
ordered linear equation in the two outer primes. -/
theorem reduced_linear_eq_of_two_outer_collisions
    {x m m' p p' q q' : ℕ}
    (hp : p ∈ outerPrimes x m) (hp' : p' ∈ outerPrimes x m')
    (hq : q ∈ outerPrimes x m) (hq' : q' ∈ outerPrimes x m')
    (hm : 0 < m) (hm' : 0 < m')
    (hmp : m < p) (hm'p' : m' < p')
    (hmq : m < q) (hm'q' : m' < q')
    (hcollision : shiftedTotient (m * p) = shiftedTotient (m' * p'))
    (hbase : shiftedTotient (m * q) = shiftedTotient (m' * q')) :
    reducedCollisionLeft m m' * p + reducedCollisionRight m m' * q' =
      reducedCollisionLeft m m' * q + reducedCollisionRight m m' * p' := by
  have hlin :=
    outer_collision_linear_eq_int hp hp' hm hm' hmp hm'p' hcollision
  have hlinBase :=
    outer_collision_linear_eq_int hq hq' hm hm' hmq hm'q' hbase
  have hrawZ :
      (shiftedTotient m : ℤ) * p + shiftedTotient m' * q' =
        (shiftedTotient m : ℤ) * q + shiftedTotient m' * p' := by
    linarith
  have hraw :
      shiftedTotient m * p + shiftedTotient m' * q' =
        shiftedTotient m * q + shiftedTotient m' * p' := by
    exact_mod_cast hrawZ
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
  apply Nat.mul_left_cancel hg
  calc
    g * (reducedCollisionLeft m m' * p +
        reducedCollisionRight m m' * q') =
        shiftedTotient m * p + shiftedTotient m' * q' := by
      rw [← hleft, ← hright]
      ring
    _ = shiftedTotient m * q + shiftedTotient m' * p' := hraw
    _ = g * (reducedCollisionLeft m m' * q +
        reducedCollisionRight m m' * p') := by
      rw [← hleft, ← hright]
      ring

end Erdos822
