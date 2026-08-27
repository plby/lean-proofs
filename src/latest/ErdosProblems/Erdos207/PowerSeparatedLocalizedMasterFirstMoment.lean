/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PowerBankSubsetAbsorption
import ErdosProblems.Erdos207.VortexSeparatedLocalizedRootedThreatWeight
import ErdosProblems.Erdos207.LocalizedMasterUnionRootedThreatWeight

/-!
# Linear empty-root bounds for a power-vortex master weight

The first-moment rooted tail only asks for the extension weight at the empty
planted root.  Empty remainders and the sharp WS4 estimate then give a bound
linear in the current vortex level, in contrast to the deliberately coarser
all-root A2 bound.
-/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

/-- The fixed coefficient multiplying the current level cardinality in the
empty-root estimate at a positive power-vortex endpoint. -/
def powerLocalizedRootedFirstCoefficient (q m M : ℕ) : ℝ≥0 :=
  1 + localizedNonemptyRootedThreatSharpCoefficient m q M 2

/-- The packaged power vortex supplies a linear empty-root extension bound
for the exact master-union point weight at every positive endpoint. -/
theorem InitialPowerVortexPackage.localizedMasterFirstMomentBound
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (i : Fin ell) (p : ℝ≥0) (hp : p ≤ 1)
    (hbank : (subsetsUpToCard P.B q).card ≤ (P.W.U 0).card)
    (e : DistinctPair (Fin n)) :
    extensionWeight
        (fun z : LocalizedRootedThreatWitness (Fin n)
            (absorberErdosForbiddenConfigurationsOn q P.B)
            e.1.1 e.1.2 (P.W.U i.succ) ↦
          localizedRootedThreatRemainder z)
        (masterUnionTriangleWeight P.W i.succ p) ∅ ≤
      ((P.W.U i.succ).card : ℝ≥0) *
        powerLocalizedRootedFirstCoefficient q i.val
          (12 * (q + 2) ^ 2) := by
  have hell : 0 < ell := Nat.zero_lt_of_lt i.isLt
  have hsepFull : AbsorberSeparatedLevel P.H P.X P.B (P.W.U 1) := by
    rw [P.vortex_eq]
    exact separatedCardinalVortex_separated P.H P.X P.B
      (powerFreeSize t step ell)
      (powerFreeSize_antitone t step ell P.base_ge_one)
      (by
        intro hone
        have hv := congrArg Fin.val hone
        simp only [Fin.val_one', Fin.val_zero] at hv
        rw [Nat.mod_eq_of_lt (by omega : 1 < ell + 1)] at hv
        omega)
  have hembOne : vortexPrefixEmbedding i.succ
      (1 : Fin (i.succ.val + 1)) = (1 : Fin (ell + 1)) := by
    have hsrc : ((1 : Fin (i.succ.val + 1)).val) = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt (by
        have hisucc : 0 < i.succ.val := by
          simp only [Fin.val_succ]
          omega
        omega)
    have htgt : ((1 : Fin (ell + 1)).val) = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt (by omega)
    apply Fin.ext
    rw [vortexPrefixEmbedding_val, hsrc, htgt]
  have hsepPrefix : AbsorberSeparatedLevel P.H P.X P.B
      ((P.W.prefix i.succ).U 1) := by
    simpa only [Vortex.prefix_U, hembOne] using hsepFull
  have houter : ∀ j : Fin (i.val + 1),
      0 < ((P.W.prefix i.succ).U j.castSucc).card := by
    intro j
    exact card_pos.mpr (P.nonempty _)
  have hterminal : 0 < (P.W.prefix i.succ).terminalSize := by
    rw [P.W.prefix_terminalSize i.succ]
    exact card_pos.mpr (P.nonempty i.succ)
  have hembZero : vortexPrefixEmbedding i.succ
      (0 : Fin (i.succ.val + 1)) = (0 : Fin (ell + 1)) := by
    apply Fin.ext
    rfl
  have hbankPrefix : (subsetsUpToCard P.B q).card ≤
      ((P.W.prefix i.succ).U 0).card := by
    simpa only [Vortex.prefix_U, hembZero] using hbank
  have hvortex :=
    extensionWeight_localizedRootedThreat_vortex_empty_le_level_sharp
      (P.W.prefix i.succ) P.H P.X P.B 2 P.localization hsepPrefix
      houter hterminal hbankPrefix (P.W.U i.succ) e.2
  calc
    extensionWeight
          (fun z : LocalizedRootedThreatWitness (Fin n)
              (absorberErdosForbiddenConfigurationsOn q P.B)
              e.1.1 e.1.2 (P.W.U i.succ) ↦
            localizedRootedThreatRemainder z)
          (masterUnionTriangleWeight P.W i.succ p) ∅ ≤
        extensionWeight
          (fun z : LocalizedRootedThreatWitness (Fin n)
              (absorberErdosForbiddenConfigurationsOn q P.B)
              e.1.1 e.1.2 (P.W.U i.succ) ↦
            localizedRootedThreatRemainder z)
          (vortexTripleWeight (P.W.prefix i.succ) 2) ∅ :=
      extensionWeight_mono_pointwise _
        (masterUnionTriangleWeight_le_prefix_vortex_two
          P.W i.succ p hp P.nonempty) ∅
    _ ≤ ((P.W.U i.succ).card : ℝ≥0) *
        powerLocalizedRootedFirstCoefficient q i.val
          (12 * (q + 2) ^ 2) := by
      simpa only [powerLocalizedRootedFirstCoefficient] using hvortex

end

end Erdos207
