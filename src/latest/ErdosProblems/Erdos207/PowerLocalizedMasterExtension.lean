/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PowerBankSubsetAbsorption

/-!
# The sharp localized master-extension bound for a power vortex package

This file packages the bank-independent A2 count in exactly the form used by
the first and later compressed transitions.  All structural hypotheses are
discharged from `InitialPowerVortexPackage`; the only remaining numerical
input is the already isolated bounded-bank absorption inequality.
-/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

/-- Every positive level of a packaged separated power vortex is disjoint
from the non-root support of the absorber graph. -/
theorem InitialPowerVortexPackage.firstLevel_graphSeparated
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hell : 0 < ell) :
    ∀ x ∈ P.W.U 1, x ∉ P.X → x ∉ graphSupportFinset P.H := by
  have hone : (1 : Fin (ell + 1)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_one', Fin.val_zero] at hv
    rw [Nat.mod_eq_of_lt (by omega : 1 < ell + 1)] at hv
    omega
  have hsep : AbsorberSeparatedLevel P.H P.X P.B (P.W.U 1) := by
    rw [P.vortex_eq]
    exact separatedCardinalVortex_separated P.H P.X P.B
      (powerFreeSize t step ell)
      (powerFreeSize_antitone t step ell P.base_ge_one) hone
  intro x hx hxX
  exact (hsep.2 x hx hxX).1

/-- The explicit localized rooted-threat bound needed by a master update at
any positive endpoint of the packaged vortex. -/
theorem InitialPowerVortexPackage.localizedMasterExtensionBound
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
        localizedRootedThreatVortexA2LargeCoefficient
          (P.W.prefix i.succ) q (12 * (q + 2) ^ 2) 2 0) := by
  have hell : 0 < ell := Nat.zero_lt_of_lt i.isLt
  apply localizedRootedThreatRemainder_hasExtensionBound_masterUnion_A2
    P.W P.H P.X P.B i p hp P.localization
      (P.firstLevel_graphSeparated hell) P.nonempty hbank e.2

end

end Erdos207
