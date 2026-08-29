/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingNormalizedTheorem
import ErdosProblems.Erdos599.GroundingEqualMaximalActiveSupply

/-!
# Final grounding interface with a target-only equal boundary

The stationary equal branch uses the essential terminal cut as its boundary.
The collision hull is retained only as an avoidance and ownership carrier for
the maximal route supply; it is not added to the boundary.  This avoids the
false component-antichain claim for the target-plus-collision-hull cut.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection

/-- The exact remaining global geometry of the target-only stationary equal
branch.  Every other field of the maximal repaired relation—adjacency,
bi-uniqueness, terminal sinks, and omission of the reserved source—is
discharged by `GroundingEqualMaximalActiveSupply`. -/
structure TargetOnlyEqualRooting
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance) where
  sourceRooted : ∀
    (P : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target),
    (∀ p ∈ P.paths, (EqualInput L hL).IsTargetPure p) →
    Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source) →
    ∀
      (q : FinitePath (EqualInput L hL).lambda.graph)
      (hq : q ∈ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths)
      (Q : Popular.XSWarp
        (EqualInput L hL).lambda (EqualInput L hL).lambda.target),
      Q.paths ⊆ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths →
      (∀ p ∈ Q.paths, (EqualInput L hL).IsTargetPure p) →
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp Q).paths
          ((L.popularAuxiliaryIndexed hL).equalSubwarp Q).starts_in_source) →
      Q.paths.PairwiseDisjoint (EqualInput L hL).decodedVertexCarrier →
      (∀ p ∈ Q.paths,
        Disjoint p.support (collisionCarrier (EqualInput L hL) q)) →
      ∀ R : L.ReservedGroundedParent hL q
          (((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source hq),
      ∀ M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
          (EqualInput L hL)
          ((EqualInput L hL).lambda.source \ {q.start})
          (collisionCarrier (EqualInput L hL) q),
      Q.paths ⊆ M.paths →
      ∀ b ∈ (EqualInput L hL).terminalCut,
        ∃ a ∈ Gamma.source,
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
              (EqualInput L hL)
              (ReservedMaximalDecodedActiveSupply.toXSWarp M)) a b

namespace TargetOnlyEqualRooting

variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}

/-- Compile target-only terminal-cut rooting to the equal-branch hindrance. -/
theorem exists_hindrance
    (G : TargetOnlyEqualRooting L hL)
    (P : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (hpure : ∀ p ∈ P.paths, (EqualInput L hL).IsTargetPure p)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  apply
    L.exists_hindrance_of_targetPure_stationary_equalSubwarp_of_maximalDecoded_sourceRooted
      hL P hpure hstat
  intro q hq Q hQP hQpure hQstat hQdisjoint hQavoid R M hQM
  exact G.sourceRooted P hpure hstat q hq Q hQP hQpure hQstat
    hQdisjoint hQavoid R M hQM

end TargetOnlyEqualRooting

/-- Final source-faithful grounding assembly.  The equal boundary is the
target-only essential terminal cut, while the separator branch uses the
whole-parent-normalized pre-stopped compiler. -/
theorem exists_hindrance_of_targetOnlyEqualRooting_and_normalizedPreStoppedRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (equal : TargetOnlyEqualRooting L hL)
    (repairs : NormalizedPreStoppedRepairs L hL) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply
    L.exists_hindrance_of_targetPureEqualGrounding_and_normalizedPreStoppedRepairs
      hL
  · intro P hpure hstat
    exact equal.exists_hindrance P hpure hstat
  · exact repairs

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.TargetOnlyEqualRooting.exists_hindrance
#print axioms
  Erdos599.DWeb.KappaLadder.exists_hindrance_of_targetOnlyEqualRooting_and_normalizedPreStoppedRepairs
