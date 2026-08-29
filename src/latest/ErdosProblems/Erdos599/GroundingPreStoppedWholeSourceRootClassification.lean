/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedBackwardSelfNormalizedOutcome
import ErdosProblems.Erdos599.GroundingPreStoppedInessentialBoundaryReduction

/-!
# Classifying whole-source pre-stopped root failures

A boundary point which is not rooted from any original source is, in
particular, not rooted from the source set with the reserved record's initial
vertex removed.  Thus the construction-specific owner recursion applies to a
whole-source obstruction without any additional geometric assumption.

The wrapper in this file deliberately retains the stronger original
obstruction.  In particular, a terminal hanging-component leaf cannot be
silently treated as a reserved-source accident: its failure of reachability
from the entire source remains available to the eventual equal/exchange
repair.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822WholeSourceRootObstruction

/-- Forget the stronger whole-source assertion only for the purpose of
running the already established construction-specific root classifier. -/
def toReservedObstruction
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822WholeSourceRootObstruction hL S R) :
    L.Assertion822PreStoppedRootObstruction hL S R where
  boundary := O.boundary
  boundary_mem := O.boundary_mem
  not_rooted := by
    rintro ⟨a, ha, hab⟩
    exact O.not_rooted ⟨a, ha.1, hab⟩

/-- The full-source obstruction classified by the well-founded self-backward
normalizer, while retaining the stronger obstruction as part of the result. -/
structure BackwardSelfNormalizedClassification
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822WholeSourceRootObstruction hL S R) : Prop where
  outcome :
    (O.toReservedObstruction).BackwardSelfNormalizedFirstFragmentRootFailureOutcome

/-- Every whole-source root obstruction enters the same genuine well-founded
owner recursion as the reserved-source obstruction. -/
theorem backwardSelfNormalizedClassification
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822WholeSourceRootObstruction hL S R) :
    O.BackwardSelfNormalizedClassification := by
  exact {
    outcome :=
      O.toReservedObstruction.backwardSelfNormalizedFirstFragmentRootFailureOutcome }

end Assertion822WholeSourceRootObstruction
end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822WholeSourceRootObstruction.toReservedObstruction
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822WholeSourceRootObstruction.backwardSelfNormalizedClassification
