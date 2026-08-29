/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayGroupedClubStage
import ErdosProblems.Erdos599.HalfwayContactBoundary
import ErdosProblems.Erdos599.HalfwayLinkageFirstBoundary

/-!
# From a literal contact relation to the final club boundary

The endpoint-covered Claim-2 compiler constructs a mixed relation in the
imaginary graph.  Its surviving real edges must still be realized as an
honest finite-character warp.  This file records that source-level
realization and derives the exact root/sink formulas and absence of a
forward ray.  It then feeds those derived facts through the checked
constant-stage scheduler and `HalfwayContactBoundary`.

No `ContactSegmentation` or endpoint-clean assignment is used here.  The
only path representation retained is the actual real warp of the compiled
literal relation.
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
variable {kappa : Cardinal.{u}}

/-- An honest real-warp realization of the surviving real part of a
literal endpoint-covered contact transaction. -/
structure LiteralContactRealWarp
    (L : LiteralContactTransactionGeometry
      (Gamma := Gamma) (Y := Y) (kappa := kappa)) where
  paths : Set Gamma.DPath
  isWarp : Gamma.IsWarp paths
  finiteCharacter : Gamma.HasFiniteCharacter paths
  edge_eq : relationRealEdges (Gamma := Gamma) L.edge = familyEdges paths
  carrier_eq : L.carrier = Gamma.vertexSet paths

namespace LiteralContactRealWarp

variable {L : LiteralContactTransactionGeometry
  (Gamma := Gamma) (Y := Y) (kappa := kappa)}

/-- The roots of the surviving real relation are exactly the initials of
its honest real-warp realization. -/
theorem realRoots_eq_initialSet (P : LiteralContactRealWarp L) :
    {x | x ∈ L.carrier ∧
      ¬ ∃ y, (y, x) ∈ relationRealEdges (Gamma := Gamma) L.edge} =
      Gamma.initialSet P.paths := by
  rw [P.carrier_eq, P.edge_eq]
  exact (isWarp_initialSet_eq_noIncoming P.isWarp).symm

/-- The sinks of the surviving real relation are exactly the finite
terminal frontier of its honest real-warp realization. -/
theorem realSinks_eq_terminalFrontier (P : LiteralContactRealWarp L) :
    {x | x ∈ L.carrier ∧
      ¬ ∃ y, (x, y) ∈ relationRealEdges (Gamma := Gamma) L.edge} =
      Gamma.terminalFrontier P.paths := by
  rw [P.carrier_eq, P.edge_eq]
  exact (isWarp_terminalFrontier_eq_noOutgoing P.isWarp).symm

/-- Finite character of the realized real warp excludes a surviving
forward ray. -/
theorem realEdges_noDirectedRay (P : LiteralContactRealWarp L) :
    ¬ ContainsDirectedRay
      (relationRealEdges (Gamma := Gamma) L.edge) := by
  rw [P.edge_eq]
  exact Alternating.familyEdges_not_containsDirectedRay
    P.isWarp P.finiteCharacter

end LiteralContactRealWarp

namespace LiteralContactTransactionGeometry

variable {C : ClubStageGeometry Gamma Y kappa (Order.succ kappa)}
variable {W : LinkageBlueprint Gamma Y kappa} {u : V}

/-- Any checked literal transaction whose surviving real edges lie in a
finite-character warp has an exact real-warp realization on its *whole*
carrier.  In particular, vertices incident only with deleted imaginary
edges are retained as trivial paths.  This is the form needed after the
inside relation and the endpoint-covered linkwise relation have been
spliced: the containing warp controls forward rays, while the structural
fields of `L` control cycles, reverse rays, and local incidence. -/
theorem exists_realWarp_of_realEdges_subset_finiteWarp
    (L : LiteralContactTransactionGeometry
      (Gamma := Gamma) (Y := Y) (kappa := kappa))
    (P : Set Gamma.DPath) (hP : Gamma.IsWarp P)
    (hPfinite : Gamma.HasFiniteCharacter P)
    (hreal : relationRealEdges (Gamma := Gamma) L.edge ⊆
      familyEdges P) :
    Nonempty (LiteralContactRealWarp L) := by
  let E : Set (V × V) := relationRealEdges (Gamma := Gamma) L.edge
  have hgraph : E ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
    intro e he
    exact he.2
  have hendpoints : ∀ e ∈ E,
      e.1 ∈ L.carrier ∧ e.2 ∈ L.carrier := by
    intro e he
    exact L.endpoints_mem_carrier e he.1
  have hbiunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E) := by
    constructor
    · intro a b c hac hbc
      exact L.biunique.1 hac.1 hbc.1
    · intro a b c hab hac
      exact L.biunique.2 hab.1 hac.1
  have hcycle : ¬ ContainsDirectedCycle E := by
    rintro ⟨c, hc⟩
    exact L.acyclic ⟨c, hc.trans (fun _ he ↦ he.1)⟩
  have hreverse : ¬ ContainsReverseDirectedRay E := by
    rintro ⟨r, hr⟩
    exact L.no_reverse_ray ⟨r, fun i ↦ (hr i).1⟩
  have hnray : ¬ ContainsDirectedRay E := by
    rintro ⟨r, hr⟩
    exact Alternating.familyEdges_not_containsDirectedRay hP hPfinite
      ⟨r, hr.trans (fun _ he ↦ hreal he)⟩
  obtain ⟨O, hOE, hOC⟩ :=
    PathFilterComponents.exists_forwardOrientation_exact E L.carrier hgraph
      hendpoints hbiunique hcycle hreverse
  have hOfinite : Gamma.HasFiniteCharacter O.rootPaths :=
    DWeb.forwardOrientation_rootPaths_finite_of_noRay Gamma O (by
      rwa [hOE])
  refine ⟨{
    paths := O.rootPaths
    isWarp := O.rootPaths_pairwiseDisjoint
    finiteCharacter := hOfinite
    edge_eq := ?_
    carrier_eq := ?_ }⟩
  · change E = familyEdges O.rootPaths
    change E = O.rootPathEdges
    rw [O.rootPathEdges_eq, hOE]
  · rw [PathFilterComponents.ForwardOrientation.vertexSet_rootPaths Gamma O,
      hOC]

/-- Once a literal transaction has been installed as actual club-stage
data and its real part has been realized as a finite-character warp, the
exact path-family boundary equations compile to the scheduler boundary.

The output contains the concrete `SuccessorClubStageRun`, rather than a
repackaged final certificate.  The root and sink relations and the no-ray
condition are all derived from `P`. -/
theorem exists_successorRun_with_frontierBoundary
    (L : LiteralContactTransactionGeometry
      (Gamma := Gamma) (Y := Y) (kappa := kappa))
    (D : ClubStageUnionData C W (emptyFracturedAssignment Gamma Y) u)
    (hDedge : D.inside = L.edge)
    (hDcarrier : D.carrier = L.carrier)
    (resolve : ∀ x,
      x ∈ D.carrier →
      (¬ ∃ y, (x, y) ∈ relationRealEdges (Gamma := Gamma) D.inside) →
      x ∉ Gamma.target →
      Nonempty (EmbeddedTransactionTargetRoute D x))
    (P : LiteralContactRealWarp L)
    (hkappa : aleph0 ≤ kappa)
    {A0 : Set V}
    (href : Y = C.selectedReference)
    (hdesignatedSource : A0 ⊆ Gamma.source)
    (hdesignatedInitial : A0 ⊆ Gamma.initialSet P.paths)
    (hsource :
      Gamma.initialSet P.paths ∪
          Gamma.initialSet
            (referencePathsMeeting Y C.newSlice \
              referencePathsMeeting Y L.carrier) =
        Gamma.source)
    (hterminal :
      Gamma.terminalFrontier P.paths ∪
          Gamma.terminalFrontier
            (referencePathsMeeting Y C.newSlice \
              referencePathsMeeting Y L.carrier) =
        C.newSlice) :
    ∃ R : SuccessorClubStageRun C,
      CardinalInduction.HalfwayScheduler.RankedClubFrontierBoundary C
        (R.toCofinalRun hkappa).rankedFairGlobalRelation A0 := by
  let T : SingleGlobalClubStageTransaction C :=
    L.toSingleGlobalClubStageTransaction D resolve
  let R : SuccessorClubStageRun C := T.successorRun
  have hrealEdge : T.realEdge =
      relationRealEdges (Gamma := Gamma) L.edge := by
    simp only [SingleGlobalClubStageTransaction.realEdge, T,
      LiteralContactTransactionGeometry.toSingleGlobalClubStageTransaction,
      assignedFiniteEdges_emptyFracturedAssignment, Set.union_empty,
      hDedge]
  have hrealCarrier : T.data.carrier = L.carrier := by
    simpa only [T,
      LiteralContactTransactionGeometry.toSingleGlobalClubStageTransaction]
      using hDcarrier
  refine ⟨R, R.rankedClubFrontierBoundary_of_noDirectedRay hkappa href
    hdesignatedSource ?_ ?_ ?_ ?_⟩
  · simpa only [R, SingleGlobalClubStageTransaction.successorRun_finalEdge,
      SingleGlobalClubStageTransaction.successorRun_finalCarrier,
      hrealEdge, hrealCarrier, P.realRoots_eq_initialSet] using
      hdesignatedInitial
  · simpa only [R, SingleGlobalClubStageTransaction.successorRun_finalEdge,
      SingleGlobalClubStageTransaction.successorRun_finalCarrier,
      hrealEdge, hrealCarrier, P.realRoots_eq_initialSet] using hsource
  · simpa only [R, SingleGlobalClubStageTransaction.successorRun_finalEdge,
      SingleGlobalClubStageTransaction.successorRun_finalCarrier,
      hrealEdge, hrealCarrier, P.realSinks_eq_terminalFrontier] using hterminal
  · simpa only [R, SingleGlobalClubStageTransaction.successorRun_finalEdge,
      hrealEdge] using P.realEdges_noDirectedRay

end LiteralContactTransactionGeometry

end LinkageBlueprint
end Blueprint
end Erdos599
