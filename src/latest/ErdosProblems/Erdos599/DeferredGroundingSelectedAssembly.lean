/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingBranchEliminator
import ErdosProblems.Erdos599.GroundingSelectedDecoder

/-!
# Simultaneous assembly of the selected Section 8 routes

`GroundingSelectedDecoder` decodes one selected auxiliary path at a time,
and `LambdaCutCompression` turns a reduced decoded run into one alternating
path.  Assertion 8.22, however, applies *all* selected routes to the limiting
ladder warp at once.  It is not sound to replace that simultaneous switch by
a family of unrelated pointwise `SwitchData.RealizedBy` witnesses.

This file defines the literal simultaneous switched edge relation and
packages the remaining geometric realization, finite descent, boundary, and
unused-record conclusions in one checked certificate.  The last theorem is
the exact projection from such certificates to the `SwitchPruneCompiler`
consumed by the deferred branch eliminator.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath
open _root_.Erdos599.PopularGroundingBridge

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

private abbrev AuxInput
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L) :=
  popularAuxiliaryInput L hL.legal

private abbrev AuxIndexed
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L) :=
  popularAuxiliaryIndexed L hL

private abbrev AuxRequest
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (AuxIndexed L hL)) :=
  Request (AuxInput L hL) S.cut

/-! ## The reduced selected family -/

/-- A reduced-run presentation for every path selected by the control-aware
recursion.  This is the precise pathwise premise needed by
`LambdaCutCompression`; no global switching conclusion is hidden in it. -/
structure SelectedReducedRunFamily
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (AuxIndexed L hL))
    (K : GroundingSelection.Controls S) : Type (u + 1) where
  presentation : ∀ r : AuxRequest L hL S,
    (AuxInput L hL).CutReducedRunPresentation
      (GroundingSelectedDecoder.selectedCutMicroTrace S K r)

/-- The compressed alternating path attached to a selected request. -/
noncomputable def SelectedReducedRunFamily.compressedPath
    {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
    {S : Popular.PopularSeparator (AuxIndexed L hL)}
    {K : GroundingSelection.Controls S}
    (R : SelectedReducedRunFamily L hL S K)
    (r : AuxRequest L hL S) : Alternating.AltPath Gamma.graph :=
  ((R.presentation r).toCutAlternatingCompression).path

theorem SelectedReducedRunFamily.compressedPath_edgeSet
    {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
    {S : Popular.PopularSeparator (AuxIndexed L hL)}
    {K : GroundingSelection.Controls S}
    (R : SelectedReducedRunFamily L hL S K)
    (r : AuxRequest L hL S) :
    (R.compressedPath r).edgeSet =
      (AuxInput L hL).decodedRouteEdges
        (GroundingAssembly.selectedPath (AuxIndexed L hL) S K r) :=
  (R.presentation r).toCutAlternatingCompression.edgeSet_eq_decodedRouteEdges

theorem SelectedReducedRunFamily.decodedSwitchData_eq
    {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
    {S : Popular.PopularSeparator (AuxIndexed L hL)}
    {K : GroundingSelection.Controls S}
    (R : SelectedReducedRunFamily L hL S K)
    (r : AuxRequest L hL S) :
    (AuxInput L hL).decodedSwitchData
        (GroundingAssembly.selectedPath (AuxIndexed L hL) S K r) =
      Alternating.Cyclowarp.application
        (AuxInput L hL).ladder.paths (R.compressedPath r) :=
  (R.presentation r).toCutAlternatingCompression.switchData_eq

/-! ## The literal simultaneous switch -/

/-- The union of all original directed edges traversed by the selected
decoded routes. -/
def selectedDecodedRouteEdges
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (AuxIndexed L hL))
    (K : GroundingSelection.Controls S) : Set (V × V) :=
  ⋃ r : AuxRequest L hL S,
    (AuxInput L hL).decodedRouteEdges
      (GroundingAssembly.selectedPath (AuxIndexed L hL) S K r)

theorem selectedDecodedRouteEdges_subset_adj
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (AuxIndexed L hL))
    (K : GroundingSelection.Controls S) :
    selectedDecodedRouteEdges L hL S K ⊆
      {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  simp only [selectedDecodedRouteEdges, Set.mem_iUnion] at he
  obtain ⟨r, her⟩ := he
  exact (AuxInput L hL).decodedRouteEdges_subset_adj
    (GroundingAssembly.selectedPath (AuxIndexed L hL) S K r) her

/-- The raw result of applying all selected decoded routes simultaneously
to the limiting ladder warp. -/
def simultaneousSelectedSwitchData
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (AuxIndexed L hL))
    (K : GroundingSelection.Controls S) : Alternating.SwitchData Gamma where
  edges := Alternating.edgeSymmDiff
    (Alternating.familyEdges (AuxInput L hL).ladder.paths)
    (selectedDecodedRouteEdges L hL S K)
  edges_in_graph := by
    intro e he
    rcases he with he | he
    · exact Alternating.familyEdges_subset_adj _ he.1
    · exact selectedDecodedRouteEdges_subset_adj L hL S K he.1
  isolated := Alternating.isolatedVertices (AuxInput L hL).ladder.paths

@[simp]
theorem simultaneousSelectedSwitchData_edges
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (AuxIndexed L hL))
    (K : GroundingSelection.Controls S) :
    (simultaneousSelectedSwitchData L hL S K).edges =
      Alternating.edgeSymmDiff
        (Alternating.familyEdges (AuxInput L hL).ladder.paths)
        (selectedDecodedRouteEdges L hL S K) :=
  rfl

@[simp]
theorem simultaneousSelectedSwitchData_isolated
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (AuxIndexed L hL))
    (K : GroundingSelection.Controls S) :
    (simultaneousSelectedSwitchData L hL S K).isolated =
      Alternating.isolatedVertices (AuxInput L hL).ladder.paths :=
  rfl

theorem SelectedReducedRunFamily.selectedDecodedRouteEdges_eq
    {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
    {S : Popular.PopularSeparator (AuxIndexed L hL)}
    {K : GroundingSelection.Controls S}
    (R : SelectedReducedRunFamily L hL S K) :
    selectedDecodedRouteEdges L hL S K =
      ⋃ r : AuxRequest L hL S, (R.compressedPath r).edgeSet := by
  ext e
  simp only [selectedDecodedRouteEdges, Set.mem_iUnion]
  constructor
  · rintro ⟨r, her⟩
    exact ⟨r, (R.compressedPath_edgeSet r).symm ▸ her⟩
  · rintro ⟨r, her⟩
    exact ⟨r, R.compressedPath_edgeSet r ▸ her⟩

/-! ## Honest simultaneous realization and pruning -/

/-- The non-pathwise content of Assertion 8.22.  `realized` is a *single*
warp realization of the simultaneous symmetric difference, not a collection
of pointwise realizations.  The other fields state exactly the boundary and
unused-record facts needed after pruning at `BB`. -/
structure SimultaneousSelectedSwitchRealization
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (AuxIndexed L hL))
    (K : GroundingSelection.Controls S) : Type (u + 1) where
  paths : Set Gamma.DPath
  realized : (simultaneousSelectedSwitchData L hL S K).RealizedBy paths
  initialSet_subset : Gamma.initialSet paths ⊆ Gamma.source
  terminalFrontier_eq : Gamma.terminalFrontier paths =
    GroundingCut.BB (AuxInput L hL) S.cut
  unused_record_inessential : ∀ a,
    a ∈ phiGround L \
      Popular.initialIndicesOf (AuxIndexed L hL)
        (GroundingAssembly.selectedWarp (AuxIndexed L hL) S K).paths
        (GroundingAssembly.selectedWarp (AuxIndexed L hL) S K).starts_in_source →
      ∃ p : Gamma.DPath,
        L.chosen a = some p ∧ p ∈ Gamma.inessentialPaths paths

theorem SimultaneousSelectedSwitchRealization.isWarp
    {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
    {S : Popular.PopularSeparator (AuxIndexed L hL)}
    {K : GroundingSelection.Controls S}
    (W : SimultaneousSelectedSwitchRealization L hL S K) :
    Gamma.IsWarp W.paths :=
  W.realized.1

/-- The two checked pieces of the separator branch used by the public
switch/prune output: genuine simultaneous realization and finite descent.

An exact `CutReducedRunPresentation` is intentionally not stored here.
Projected original vertices can repeat even when the selected Lambda path
is simple, and the switch/prune projection never consumes such a premise. -/
structure SelectedSwitchPruneCertificate
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (AuxIndexed L hL))
    (K : GroundingSelection.Controls S) : Type (u + 1) where
  descent : GroundingCut.FiniteDescentDecoder (AuxInput L hL) S.cut
  switch : SimultaneousSelectedSwitchRealization L hL S K

/-- A fully assembled selected-route certificate is exactly strong enough
to produce the canonical-`BB` switch/prune output. -/
def SelectedSwitchPruneCertificate.toGroundingCutSwitchPruneOutput
    {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
    {S : Popular.PopularSeparator (AuxIndexed L hL)}
    {K : GroundingSelection.Controls S}
    (C : SelectedSwitchPruneCertificate L hL S K) :
    GroundingCutSwitchPruneOutput L hL S K where
  descent := C.descent
  paths := C.switch.paths
  isWarp := C.switch.isWarp
  initialSet_subset := C.switch.initialSet_subset
  terminalFrontier_eq := C.switch.terminalFrontier_eq
  unused_record_inessential := C.switch.unused_record_inessential

/-- Projection to the public separator arm of the deferred branch compiler. -/
def SelectedSwitchPruneCertificate.toSeparatorSwitchPruneOutput
    {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
    {S : Popular.PopularSeparator (AuxIndexed L hL)}
    {K : GroundingSelection.Controls S}
    (C : SelectedSwitchPruneCertificate L hL S K) :
    SeparatorSwitchPruneOutput L hL S K :=
  C.toGroundingCutSwitchPruneOutput.toSeparatorSwitchPruneOutput

/-- Assemble the exact `SwitchPruneCompiler` used by
`exists_hindrance_of_section8SwitchCompiler`.  The equal-index branch is
kept separate because it is not built from the control-aware selected warp;
the separator branch is now supplied by the explicit selected-route
certificate above. -/
def switchPruneCompiler_of_selectedCertificates
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (Hequal : ∀
      (P : Popular.XSWarp
        (AuxInput L hL).lambda (AuxInput L hL).lambda.target),
      Stationary.IsStationaryBelow kappa (equalGroundIndices L hL P) →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (Hselected : ∀
      (S : Popular.PopularSeparator (AuxIndexed L hL)),
        Nonempty (SelectedSwitchPruneCertificate L hL S
          (selectionControls L hL S))) :
    SwitchPruneCompiler L hL where
  equal := Hequal
  separator := by
    intro S
    obtain ⟨C⟩ := Hselected S
    exact ⟨C.toSeparatorSwitchPruneOutput⟩

end Deferred
end KappaLadder
end DWeb
end Erdos599
