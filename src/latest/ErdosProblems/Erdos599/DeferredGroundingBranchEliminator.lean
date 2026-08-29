/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingChronology
import ErdosProblems.Erdos599.DeferredGroundingControls
import ErdosProblems.Erdos599.DeferredGroundingSelectedNonstationarity
import ErdosProblems.Erdos599.DeferredGroundingSwitchOutput

/-!
# Honest branch interface for deferred Section 8 grounding

This is the single proposition-level target left by the deferred migration.
It exposes only the substantive geometric constructors: successor-roof
transport, collision controls for every popular separator, and the final
Lambda-to-Gamma switch/prune compilation.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The stationary record set in the equal-index arm. -/
def equalGroundIndices
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (P : Popular.XSWarp
      (popularAuxiliaryInput L hL.legal).lambda
      (popularAuxiliaryInput L hL.legal).lambda.target) :
    Set (Ladder.Stage kappa) :=
  Popular.initialIndicesOf (popularAuxiliaryIndexed L hL)
      ((popularAuxiliaryIndexed L hL).equalSubwarp P).paths
      ((popularAuxiliaryIndexed L hL).equalSubwarp P).starts_in_source ∩
    phiGround L

/-- The constructor obligation for Assertions 8.19--8.20. -/
def HasSelectionControls
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L) : Prop :=
  ∀ S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL),
    Nonempty (GroundingSelection.Controls S)

/-- The remaining Lambda-to-Gamma compiler, with one output for each of the
two possible Section 8 branches. -/
structure SwitchPruneCompiler
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L) : Prop where
  equal : ∀
      (P : Popular.XSWarp
        (popularAuxiliaryInput L hL.legal).lambda
        (popularAuxiliaryInput L hL.legal).lambda.target),
    Stationary.IsStationaryBelow kappa (equalGroundIndices L hL P) →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W
  separator : ∀
      (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)),
    Nonempty (SeparatorSwitchPruneOutput L hL S
      (selectionControls L hL S))

/-- The strongest honest deferred branch eliminator.  Once the three
geometric constructor interfaces are supplied, the conclusion is the
ordinary hindrance required by `RegularExtension`. -/
theorem IsKappaHindrance.exists_hindrance_of_section8Constructors
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (Hroof : Lemma717SuccessorRoofTransport L hL.legal)
    (Hswitch : SwitchPruneCompiler L hL) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  rcases groundEqual_or_separator_of_successorRoofTransport
      L hL Hroof with ⟨P, hP⟩ | hseparator
  · exact Hswitch.equal P hP
  · obtain ⟨S⟩ := hseparator
    obtain ⟨O⟩ := Hswitch.separator S
    exact exists_hindrance_of_stationarySwitchOutput
      hL.legal.regular hL.legal.uncountable
      (IsKappaHindrance.phiGround_isStationary L hL)
      O.toStationaryOutput

/-- The concrete deferred collision controls discharge their internal
regressivity, countability, disjointness, and meeting obligations
unconditionally.  The Lambda-to-Gamma switch/prune compiler remains
responsible for coverage of decoded collisions, including the equal-origin
ladder case. -/
theorem IsKappaHindrance.exists_hindrance_of_section8SwitchCompiler
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (Hroof : Lemma717SuccessorRoofTransport L hL.legal)
    (Hswitch : SwitchPruneCompiler L hL) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W :=
  hL.exists_hindrance_of_section8Constructors L Hroof Hswitch

end Deferred
end KappaLadder
end DWeb
end Erdos599
