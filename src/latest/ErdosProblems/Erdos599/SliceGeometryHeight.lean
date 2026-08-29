/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderSliceGeometry
import ErdosProblems.Erdos599.HeightRoofBridge

/-!
# Height-roof transport from marker-independent slice geometry

The exact iterated quotient identity and essential later frontier require
only the geometric fields, not the old marker eligibility predicate.
-/

namespace Erdos599.DWeb.KappaLadder

open Set Cardinal
open CardinalInduction SliceCandidate

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}
  {L : G.KappaLadder kappa}

theorem SliceGeometry.heightRoofGeometry (hL : L.SliceGeometry) : HeightRoofGeometry L :=
  ⟨hL.waveRungs, hL.roofMaximalRungs, hL.exactSuccessorArrows,
    hL.roofsSourceAtStages, hL.frontierChronology⟩

theorem SliceGeometry.stageWeb_laterFrontier_isEssential (hL : L.SliceGeometry)
    (hNoEnter : G.NoEdgeEnters G.source)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta < beta) :
    (L.stageWeb delta).essential (L.frontier beta) = L.frontier beta := by
  let Q := L.stageWeb delta
  let T := L.frontier beta
  have hsourceRoof : Q.source ⊆ Q.roof T := by
    intro x hx
    have hxG : x ∈ G.roof T := hL.frontierChronology hdeltaBeta hx
    exact roof_subset_of_adj_imp G Q rfl
      (fun {_ _} e ↦ G.quotient_adj_imp
        ((G.quotient (G.terminalFrontier (L.warpAt delta))).essentialPart_adj_imp e)) T hxG
  have hessentialUnion : Q.essential (Q.source ∪ T) = Q.essential T := by
    rw [Set.union_comm]
    exact RelationalRoof.essential_union_eq_of_subset_roof Q.graph.Adj Q.target hsourceRoof
  have hstage := stageWeb_quotient_essentialPart_eq_of_geometry
    hL.heightRoofGeometry hNoEnter hdeltaBeta
  apply Set.Subset.antisymm (Q.essential_subset T)
  intro x hxT
  have hxStage : x ∈ ((Q.quotient T).essentialPart).source := by
    rw [hstage]
    exact hxT
  have hxUnion : x ∈ Q.essential (Q.source ∪ T) := by
    rw [DWeb.essentialPart_source, DWeb.quotient_source] at hxStage
    exact hxStage.1
  rwa [hessentialUnion] at hxUnion

#print axioms SliceGeometry.heightRoofGeometry
#print axioms SliceGeometry.stageWeb_laterFrontier_isEssential

end Erdos599.DWeb.KappaLadder
