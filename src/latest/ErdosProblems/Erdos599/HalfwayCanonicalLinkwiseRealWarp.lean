/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayLiteralContactCompletion
import ErdosProblems.Erdos599.HalfwayLiteralContactGeometry

/-!
# Real-warp realization of the canonical linkwise transaction

The canonical linkwise relation retains precisely the forward edges of the
literal fractured assignment.  Those edges form a subrelation of the honest
recombined warp.  Hence they are bi-unique, contain no directed cycle or
reverse ray, and—under finite character of the recombined warp—contain no
forward ray.  The standard orientation decomposition therefore realizes
them as an honest finite-character warp with the exact endpoint carrier.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating
open Alternating.RelationDecomposition

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {X : Set V} {kappa : Cardinal.{u}}

namespace FracturedAssignmentPeel.BracketFracturedAssignment

variable {Z : FracturedWarp Gamma}

/-- The canonical linkwise transaction has an exact finite-character real
warp realization; no endpoint-clean or contact-segmentation hypothesis is
used. -/
theorem exists_canonicalLinkwiseRealWarp
    (B : FracturedAssignmentPeel.BracketFracturedAssignment Z Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.edgeWarp) :
    Nonempty (LiteralContactRealWarp
      (B.canonicalLinkwiseGeometry (X := X) (kappa := kappa))) := by
  let E : Set (V × V) := B.retainedForwardEdges
  let C : Set V := B.retainedForwardCarrier
  have hgraph : E ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
    intro e he
    exact familyEdges_subset_adj Z.edgeWarp
      (B.retainedForwardEdges_subset_familyEdges he)
  have hendpoints : ∀ e ∈ E, e.1 ∈ C ∧ e.2 ∈ C := by
    intro e he
    exact B.retainedForwardEdges_endpoints e he
  have hcycle : ¬ ContainsDirectedCycle E :=
    B.retainedForwardEdges_acyclic
  have hreverse : ¬ ContainsReverseDirectedRay E :=
    B.retainedForwardEdges_no_reverse_ray
  have hnray : ¬ ContainsDirectedRay E := by
    rintro ⟨R, hR⟩
    exact Alternating.familyEdges_not_containsDirectedRay
      Z.edgeWarp_isWarp hZfinite
      ⟨R, hR.trans B.retainedForwardEdges_subset_familyEdges⟩
  obtain ⟨O, hOE, hOC⟩ :=
    PathFilterComponents.exists_forwardOrientation_exact E C hgraph
      hendpoints B.retainedForwardEdges_biunique hcycle hreverse
  have hOfinite : Gamma.HasFiniteCharacter O.rootPaths :=
    Erdos599.Alternating.RelationDecomposition.DWeb.forwardOrientation_rootPaths_finite_of_noRay
      Gamma O (by rwa [hOE])
  have hreal : relationRealEdges (Gamma := Gamma) E = E := by
    ext e
    constructor
    · exact fun he ↦ he.1
    · exact fun he ↦ ⟨he, hgraph he⟩
  refine ⟨{
    paths := O.rootPaths
    isWarp := O.rootPaths_pairwiseDisjoint
    finiteCharacter := hOfinite
    edge_eq := ?_
    carrier_eq := ?_ }⟩
  · change relationRealEdges (Gamma := Gamma)
        (B.linkwiseRetainedEdges (X := X) (kappa := kappa)) =
      familyEdges O.rootPaths
    rw [B.linkwiseRetainedEdges_eq_retainedForwardEdges]
    change relationRealEdges (Gamma := Gamma) E = familyEdges O.rootPaths
    rw [hreal]
    change E = O.rootPathEdges
    rw [O.rootPathEdges_eq, hOE]
  · change B.retainedForwardCarrier = Gamma.vertexSet O.rootPaths
    rw [PathFilterComponents.ForwardOrientation.vertexSet_rootPaths Gamma O,
      hOC]

end FracturedAssignmentPeel.BracketFracturedAssignment

end LinkageBlueprint
end Blueprint
end Erdos599
