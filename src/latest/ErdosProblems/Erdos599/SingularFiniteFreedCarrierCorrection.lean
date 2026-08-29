/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularFiniteCarrierRoofLocalization

/-!
# The finite correction datum left by a local target-linkage exchange

A finite-support replacement of a target linkage may free old carrier
vertices, so an old residual wave need not literally remain a wave.  The
preceding localization theorem says that those freed vertices are the only
possible new roof defect.  This file records two further facts needed by a
finite repair: when the old and new linkages have the same prescribed source
set in a normalized web, the freed carrier is disjoint from the ambient (and
hence the residual) source; and for a local exchange it is finite.

The final theorem packages the exact positive output.  The old residual
frontier together with a finite source-disjoint defect roofs every source of
the new residual web.  A downstream finite/lower-cardinal repair therefore
only has to absorb that displayed defect.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteFreedCarrierCorrection

open DWeb
open SingularEndpointCarrierSplit
open SingularFiniteCarrierRoofLocalization

universe u

variable {V : Type u}

/-- Two normalized target linkages with the same prescribed initial set
cannot differ on an ambient source vertex.  In particular, the part of the
old carrier freed by replacing it with the new carrier is source-disjoint. -/
theorem disjoint_source_freedCarrier_of_targetLinkage_update
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P Q : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hQ : IsLinkageBetween G A G.target Q) :
    Disjoint G.source (G.vertexSet P \ G.vertexSet Q) := by
  rw [Set.disjoint_left]
  rintro x hxSource ⟨hxP, hxNotQ⟩
  have hxA : x ∈ A := by
    rw [← vertexSet_inter_source_eq_initial hNorm hA hP]
    exact ⟨hxP, hxSource⟩
  apply hxNotQ
  have hxQSource : x ∈ G.vertexSet Q ∩ G.source := by
    rw [vertexSet_inter_source_eq_initial hNorm hA hQ]
    exact hxA
  exact hxQSource.1

/-- Residual-source form of
`disjoint_source_freedCarrier_of_targetLinkage_update`. -/
theorem disjoint_deleteSource_freedCarrier_of_targetLinkage_update
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P Q : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hQ : IsLinkageBetween G A G.target Q) :
    Disjoint (G.delete (G.vertexSet Q)).source
      (G.vertexSet P \ G.vertexSet Q) := by
  rw [Set.disjoint_left]
  intro x hxDelete hxFreed
  exact Set.disjoint_left.1
    (disjoint_source_freedCarrier_of_targetLinkage_update
      hNorm hA hP hQ) hxDelete.1 hxFreed

/-- Exact finite roof-defect package for a finite-support target-linkage
exchange.  Here `R` is the literally retained part of the linkage, while
`T` and `Q` are respectively its old and new finite moving blocks.

No safety of the replacement is assumed or concluded.  Instead the theorem
exhibits the only remaining correction obligation as the finite,
source-disjoint set `F` of freed old carrier vertices. -/
theorem exists_finite_sourceDisjoint_roofDefect_of_localTargetLinkageExchange
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source)
    {R T Q : Set G.DPath}
    (hOld : IsLinkageBetween G A G.target (R ∪ T))
    (hNew : IsLinkageBetween G A G.target (R ∪ Q))
    (hlocal : (G.vertexSet (T ∪ Q)).Finite)
    {U : Set ((G.delete (G.vertexSet (R ∪ T))).DPath)}
    (hU : (G.delete (G.vertexSet (R ∪ T))).IsWave U) :
    ∃ F : Set V,
      F = G.vertexSet (R ∪ T) \ G.vertexSet (R ∪ Q) ∧
      F.Finite ∧
      Disjoint (G.delete (G.vertexSet (R ∪ Q))).source F ∧
      (G.delete (G.vertexSet (R ∪ Q))).source ⊆
        (G.delete (G.vertexSet (R ∪ Q))).roof
          ((G.delete (G.vertexSet (R ∪ T))).terminalFrontier U ∪ F) := by
  let F := G.vertexSet (R ∪ T) \ G.vertexSet (R ∪ Q)
  refine ⟨F, rfl, ?_, ?_, ?_⟩
  · exact freedCarrier_finite_of_localExchange G hlocal
  · exact disjoint_deleteSource_freedCarrier_of_targetLinkage_update
      hNorm hA hOld hNew
  · exact source_subset_roof_frontier_union_freedCarrier
      G (G.vertexSet (R ∪ T)) (G.vertexSet (R ∪ Q)) hU

/-- Once a finite repair roofs the explicit defect produced above, the
rerouted residual warp is a genuine wave in the new carrier deletion.  This
is the direct consumer form used after the lower-cardinal correction. -/
theorem residualWave_of_localTargetLinkageExchange_of_freedCarrier_roofed
    (G : DWeb V) {R T Q : Set G.DPath}
    {U : Set ((G.delete (G.vertexSet (R ∪ T))).DPath)}
    (hU : (G.delete (G.vertexSet (R ∪ T))).IsWave U)
    {W : Set ((G.delete (G.vertexSet (R ∪ Q))).DPath)}
    (hWwarp : (G.delete (G.vertexSet (R ∪ Q))).IsWarp W)
    (hWinitial :
      (G.delete (G.vertexSet (R ∪ Q))).initialSet W ⊆
        (G.delete (G.vertexSet (R ∪ Q))).source)
    (hfrontier :
      (G.delete (G.vertexSet (R ∪ T))).terminalFrontier U ⊆
        (G.delete (G.vertexSet (R ∪ Q))).terminalFrontier W)
    (hfreed : G.vertexSet (R ∪ T) \ G.vertexSet (R ∪ Q) ⊆
      (G.delete (G.vertexSet (R ∪ Q))).roof
        ((G.delete (G.vertexSet (R ∪ Q))).terminalFrontier W)) :
    (G.delete (G.vertexSet (R ∪ Q))).IsWave W := by
  exact isWave_of_freedCarrier_roofed
    G (G.vertexSet (R ∪ T)) (G.vertexSet (R ∪ Q))
      hU hWwarp hWinitial hfrontier hfreed

#print axioms disjoint_source_freedCarrier_of_targetLinkage_update
#print axioms disjoint_deleteSource_freedCarrier_of_targetLinkage_update
#print axioms exists_finite_sourceDisjoint_roofDefect_of_localTargetLinkageExchange
#print axioms residualWave_of_localTargetLinkageExchange_of_freedCarrier_roofed

end SingularFiniteFreedCarrierCorrection
end CardinalInduction
end Erdos599
