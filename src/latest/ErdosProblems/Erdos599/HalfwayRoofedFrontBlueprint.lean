/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Halfway930OldSliceMacroBridge
import ErdosProblems.Erdos599.HalfwayRoofedTailAttachment

/-!
# The roofed front blueprint of the closed 9.30--9.31 transaction

The closed old-slice transaction contains a canonical inside family.  This
family, rather than the larger auxiliary closed set, is the honest roofed
front track: it is a warp in the imaginary graph, all its edges are original,
its terminal set is `kappa`-small and lies on the later club frontier, and it
retains the exact source-boundary cover supplied by the spliced interval row.

No old-real-edge survival is asserted here.  That is the separate joint-
survivor obligation needed to combine this source-faithful front track with
the monotone real-edge track.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace ClosedOldSlice930MacroTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {W : LinkageBlueprint Gamma C.selectedReference kappa}
variable {z : V}

/-- The canonical roofed path family carried by the closed interval macro. -/
def roofedFrontBlueprint
    (Q : ClosedOldSlice930MacroTransaction C W z) :
    LinkageBlueprint Gamma C.selectedReference kappa :=
  Q.macroTransaction.inside.insideFamily

@[simp] theorem roofedFrontBlueprint_vertexSet
    (Q : ClosedOldSlice930MacroTransaction C W z) :
    Q.roofedFrontBlueprint.vertexSet =
      Q.macroTransaction.inside.insideFamily.vertexSet :=
  rfl

@[simp] theorem roofedFrontBlueprint_edgeSet
    (Q : ClosedOldSlice930MacroTransaction C W z) :
    Q.roofedFrontBlueprint.edgeSet =
      Q.macroTransaction.inside.insideFamily.edgeSet :=
  rfl

@[simp] theorem roofedFrontBlueprint_initialSet
    (Q : ClosedOldSlice930MacroTransaction C W z) :
    Q.roofedFrontBlueprint.initialSet =
      Q.macroTransaction.inside.insideFamily.initialSet :=
  rfl

@[simp] theorem roofedFrontBlueprint_terminalSet
    (Q : ClosedOldSlice930MacroTransaction C W z) :
    Q.roofedFrontBlueprint.terminalSet =
      Q.macroTransaction.inside.insideFamily.terminalSet :=
  rfl

/-- The front track lies in the selected later roof. -/
theorem roofedFrontBlueprint_vertexSet_subset_outerRoof
    (Q : ClosedOldSlice930MacroTransaction C W z) :
    Q.roofedFrontBlueprint.vertexSet ⊆ C.outerRoof :=
  Q.carrier_subset_outerRoof

/-- Every edge of the front track is an edge of the original web. -/
theorem roofedFrontBlueprint_isEdgeReal
    (Q : ClosedOldSlice930MacroTransaction C W z) :
    Q.roofedFrontBlueprint.IsEdgeReal := by
  intro e he
  apply Q.macroTailEdge_real
  apply Or.inl
  rw [Q.macroTransaction.macroEdge_eq_inside]
  exact he

/-- The exact terminal set of the roofed front lies on the later slice. -/
theorem roofedFrontBlueprint_terminalSet_subset_newSlice
    (Q : ClosedOldSlice930MacroTransaction C W z) :
    Q.roofedFrontBlueprint.terminalSet ⊆ C.newSlice := by
  intro x hx
  apply Q.sink_subset_newSlice
  rw [Q.roofedFrontBlueprint.terminalSet_eq_no_outgoing] at hx
  refine ⟨hx.1, ?_⟩
  rintro ⟨y, hxy⟩
  exact hx.2 ⟨y, by
    rw [Q.macroTransaction.macroEdge_eq_inside] at hxy
    exact hxy⟩

/-- The front track has at most `kappa` paths. -/
theorem mk_roofedFrontBlueprint_paths_le
    (Q : ClosedOldSlice930MacroTransaction C W z) :
    #Q.roofedFrontBlueprint.paths ≤ kappa := by
  exact (mk_paths_le_mk_vertexSet_by_initial Q.roofedFrontBlueprint).trans
    Q.mk_carrier_le

/-- Hence its exact terminal set is also `kappa`-small. -/
theorem mk_roofedFrontBlueprint_terminalSet_le
    (Q : ClosedOldSlice930MacroTransaction C W z) :
    #Q.roofedFrontBlueprint.terminalSet ≤ kappa := by
  refine (Cardinal.mk_subtype_mono ?_).trans Q.mk_carrier_le
  intro x hx
  exact ⟨Classical.choose hx, (Classical.choose_spec hx).1,
    (imaginaryWeb Gamma C.selectedReference kappa).terminal_mem_support
      (Classical.choose_spec hx).2⟩

/-- The canonical inside family retains the exact initial-boundary cover of
the honest spliced interval row.  This is deliberately stated for that row's
literal initial set, which may include ladder markers in addition to ambient
sources. -/
theorem roofedFrontBlueprint_covers_splicedInitialBoundary
    (Q : ClosedOldSlice930MacroTransaction C W z) :
    Gamma.initialSet Q.intervalTransaction.interval.splicedIntervalRow ⊆
      Q.roofedFrontBlueprint.initialSet ∪
        Gamma.initialSet
          (referencePathsMeeting C.selectedReference C.newSlice \
            referencePathsMeeting C.selectedReference
              Q.roofedFrontBlueprint.vertexSet) := by
  apply Q.macroTransaction.inside.macroCoversSource
    Q.intervalTransaction.interval.splicedIntervalRow_tight.1.isWarp
    Q.intervalTransaction.interval.splicedIntervalRow_tight.1.finiteCharacter
    Q.intervalTransaction.closed.interval_closed
    Q.intervalTransaction.closed.reference_closed
  · rw [Q.macroTransaction.outside_eq]
  · rfl
  · exact Q.intervalTransaction.interval.terminalFrontier_splicedIntervalRow_subset_newSlice

/-- Existential front-track package in the exact shape consumed by the
bounded target-tail attachment. -/
theorem exists_roofedFrontBlueprint
    (Q : ClosedOldSlice930MacroTransaction C W z) :
    ∃ A : Set V,
      ∃ U : LinkageBlueprint Gamma C.selectedReference kappa,
        U.vertexSet ⊆ C.outerRoof ∧
        U.terminalSet = A ∧
        A ⊆ C.newSlice ∧
        #A ≤ kappa ∧
        U.IsEdgeReal := by
  exact ⟨Q.roofedFrontBlueprint.terminalSet, Q.roofedFrontBlueprint,
    Q.roofedFrontBlueprint_vertexSet_subset_outerRoof, rfl,
    Q.roofedFrontBlueprint_terminalSet_subset_newSlice,
    Q.mk_roofedFrontBlueprint_terminalSet_le,
    Q.roofedFrontBlueprint_isEdgeReal⟩

/-- Attach one simultaneous family of genuine target tails to the exact
roofed front.  The attachment preserves the front track's literal initial
boundary; it does not assert preservation of the incoming old blueprint's
unrelated real edges. -/
theorem exists_targetResolvedRoofedFrontBlueprint
    (Q : ClosedOldSlice930MacroTransaction C W z)
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa) :
    ∃ U : LinkageBlueprint Gamma C.selectedReference kappa,
      U.initialSet = Q.roofedFrontBlueprint.initialSet ∧
        U.terminalSet ⊆ Gamma.target ∧
        U.IsEdgeReal := by
  exact C.exists_edgeRealTargetAttachmentAcrossReference hlower hext
    Q.roofedFrontBlueprint
    Q.roofedFrontBlueprint_vertexSet_subset_outerRoof
    (A := Q.roofedFrontBlueprint.terminalSet) rfl
    Q.roofedFrontBlueprint_terminalSet_subset_newSlice
    Q.mk_roofedFrontBlueprint_terminalSet_le
    Q.roofedFrontBlueprint_isEdgeReal

end ClosedOldSlice930MacroTransaction

#print axioms
  ClosedOldSlice930MacroTransaction.roofedFrontBlueprint_isEdgeReal
#print axioms
  ClosedOldSlice930MacroTransaction.roofedFrontBlueprint_covers_splicedInitialBoundary
#print axioms
  ClosedOldSlice930MacroTransaction.exists_roofedFrontBlueprint
#print axioms
  ClosedOldSlice930MacroTransaction.exists_targetResolvedRoofedFrontBlueprint

end LinkageBlueprint
end Blueprint
end Erdos599
