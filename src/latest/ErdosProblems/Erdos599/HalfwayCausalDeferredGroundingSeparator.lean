/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCausalSection9Rows
import ErdosProblems.Erdos599.DeferredGroundingCanonicalSeparatorArm

/-!
# Deferred separator grounding on the actual causal Section 9 ladder

These are exact specializations to `CausalSection9Rows.finalLadder`, driven
by the preferred vertices produced by the causal row rule.  In particular,
the statements do not replace that ladder by a separately chosen canonical
ladder.  The ambient-hindrance theorem deliberately retains the one genuine
remaining obligation: construction of a separator switch/prune output for
each popular separator.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace CausalSection9Rows

/-- The exact final causal Section 9 ladder has a popular separator whenever
its deferred obstruction set is stationary. -/
theorem finalLadder_deferredPopularAuxiliary_popularSeparator_nonempty
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (hL : DWeb.KappaLadder.Deferred.IsKappaHindrance
      (finalLadder Gamma kappa hkappa hGamma seed hseed)) :
    Nonempty (Popular.PopularSeparator
      (DWeb.KappaLadder.Deferred.popularAuxiliaryIndexed
        (finalLadder Gamma kappa hkappa hGamma seed hseed) hL)) := by
  let hsucc : aleph0 ≤ succ kappa := hkappa.trans (le_succ kappa)
  let preferred :=
    (rule Gamma kappa hkappa hGamma seed hseed).preferred hsucc
  have hregular : (succ kappa).IsRegular := Cardinal.isRegular_succ hkappa
  have huncountable : aleph0 < succ kappa :=
    hkappa.trans_lt (lt_succ kappa)
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (hGamma hxy).1 hy
  simpa only [finalLadder, preferred, hsucc] using
    DWeb.KappaLadder.Deferred.canonicalDeferredLadder_popularAuxiliary_popularSeparator_nonempty
      preferred hregular huncountable hNoEnter hL

/-- Separator-arm-only grounding adapter for the exact final causal ladder.
No equal-index constructor is required; the displayed separator output is
the remaining Section 8 geometric obligation. -/
theorem finalLadder_exists_hindrance_of_separatorSwitchPruneOutput
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (hL : DWeb.KappaLadder.Deferred.IsKappaHindrance
      (finalLadder Gamma kappa hkappa hGamma seed hseed))
    (Hseparator : ∀ S : Popular.PopularSeparator
        (DWeb.KappaLadder.Deferred.popularAuxiliaryIndexed
          (finalLadder Gamma kappa hkappa hGamma seed hseed) hL),
      Nonempty (DWeb.KappaLadder.Deferred.SeparatorSwitchPruneOutput
        (finalLadder Gamma kappa hkappa hGamma seed hseed) hL S
        (DWeb.KappaLadder.Deferred.selectionControls
          (finalLadder Gamma kappa hkappa hGamma seed hseed) hL S))) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  let hsucc : aleph0 ≤ succ kappa := hkappa.trans (le_succ kappa)
  let preferred :=
    (rule Gamma kappa hkappa hGamma seed hseed).preferred hsucc
  have hregular : (succ kappa).IsRegular := Cardinal.isRegular_succ hkappa
  have huncountable : aleph0 < succ kappa :=
    hkappa.trans_lt (lt_succ kappa)
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (hGamma hxy).1 hy
  simpa only [finalLadder, preferred, hsucc] using
    DWeb.KappaLadder.Deferred.canonicalDeferredLadder_exists_hindrance_of_separatorSwitchPruneOutput
      preferred hregular huncountable hNoEnter hL Hseparator

end CausalSection9Rows
end Erdos599.Blueprint.LinkageBlueprint

#print axioms
  Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows.finalLadder_deferredPopularAuxiliary_popularSeparator_nonempty
#print axioms
  Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows.finalLadder_exists_hindrance_of_separatorSwitchPruneOutput
