/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PowerVortexLevelBounds

/-!
# Fixed coefficients in the sharp localized master bound

At multiplier two, the A2 coefficient is a fixed natural constant times the
terminal root cardinality.  Factoring it this way is the form needed by the
common-base power arithmetic.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- The part of the localized A2 coefficient independent of all vortex
cardinalities. -/
def powerLocalizedRootedThreatCoefficient (q ell M : ℕ) : ℕ :=
  ∑ j : IndexedThreatOrder q,
    (j.1 + 1) ^ ell *
      ((2 ^ M + 1) * exactBankVortexOrderCoefficient q ell) *
        2 ^ (j.1 - 2)

lemma localizedRootedThreatVortexA2LargeCoefficient_two_eq
    {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}
    (W : Vortex V (m + 1)) (q M : ℕ) :
    localizedRootedThreatVortexA2LargeCoefficient W q M 2 0 =
      (powerLocalizedRootedThreatCoefficient q (m + 1) M : ℝ≥0) *
        W.terminalSize := by
  unfold localizedRootedThreatVortexA2LargeCoefficient
    powerLocalizedRootedThreatCoefficient
  rw [Nat.cast_sum]
  rw [Finset.sum_mul]
  apply sum_congr rfl
  intro j _hj
  simp only [Nat.sub_zero]
  push_cast
  ring

/-- Fully explicit form of the packaged localized master extension bound. -/
theorem InitialPowerVortexPackage.localizedMasterExtensionBound_power
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (i : Fin ell) (p : ℝ≥0) (hp : p ≤ 1)
    (hbank : (subsetsUpToCard P.B q).card ≤ (P.W.U 0).card)
    (e : DistinctPair (Fin n)) :
    HasExtensionBound
      (fun z : LocalizedRootedThreatWitness (Fin n)
          (absorberErdosForbiddenConfigurationsOn q P.B)
          e.1.1 e.1.2 (P.W.U i.succ) ↦
        localizedRootedThreatRemainder z)
      (masterUnionTriangleWeight P.W i.succ p)
      (((P.W.U i.succ).card : ℝ≥0) *
        (powerLocalizedRootedThreatCoefficient q (i.val + 1)
          (12 * (q + 2) ^ 2) : ℝ≥0) *
            ((P.W.U i.succ).card : ℝ≥0)) := by
  have hraw := P.localizedMasterExtensionBound i p hp hbank e
  rw [localizedRootedThreatVortexA2LargeCoefficient_two_eq,
    Vortex.prefix_terminalSize] at hraw
  simpa only [mul_assoc] using hraw

end

end Erdos207
