/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaRawSwitchRealization

/-!
# Raw switching at the entry of a final cut-edge gadget

The final backward edge is omitted from the word but already deleted from
the reference. This file proves the exact cancellation at the actual cut,
retaining the companion-preserving degree and signed-balance conclusions.
-/

noncomputable section

namespace Erdos599
namespace PopularAuxiliary.Input

open Set DirectedPath Alternating

universe u

variable {V I : Type u} {Gamma : DWeb V}
variable (L : PopularAuxiliary.Input Gamma I)

/-- The proper raw signed prefix stopping before the last backward gadget. -/
def rawEdgeEntrySteps (p : FinitePath L.lambda.graph) (u v : V)
    (hfinish : p.finish = .edge u v) : List (SignedEdge V) :=
  properSignedSteps (L.decodeWalkStepsEdgeEntry p u v hfinish)

theorem decodeProperSteps_eq_edgeEntry_append
    (p : FinitePath L.lambda.graph) (hs : p.start ∈ L.lambda.source)
    (u v : V) (hfinish : p.finish = .edge u v) :
    L.decodeProperSteps p = L.rawEdgeEntrySteps p u v hfinish ++
      [SignedEdge.backward (u, v)] := by
  have hmem : LambdaVertex.edge u v ∈ p.support := hfinish ▸ p.finish_mem_support
  have hne : u ≠ v := L.raw_familyEdge_ne
    (L.edgeNode_mem_familyEdges_of_start_in_source p hs hmem)
  rw [decodeProperSteps, L.decodeWalkSteps_eq_edgeEntry_append p u v hfinish,
    properSignedSteps_append]
  simp [rawEdgeEntrySteps, properSignedSteps, hne]

theorem rawEdgeEntrySteps_forwardEdges
    (p : FinitePath L.lambda.graph) (hs : p.start ∈ L.lambda.source)
    (u v : V) (hfinish : p.finish = .edge u v) :
    directedSignedEdgeSet .forward (L.rawEdgeEntrySteps p u v hfinish) =
      L.properSelectedConnectorEdges p := by
  rw [← decodeProperSteps_forwardEdges,
    L.decodeProperSteps_eq_edgeEntry_append p hs u v hfinish,
    directedSignedEdgeSet_append]
  simp [directedSignedEdgeSet]

theorem rawEdgeEntrySteps_backward_partition
    (p : FinitePath L.lambda.graph) (hs : p.start ∈ L.lambda.source)
    (u v : V) (hfinish : p.finish = .edge u v) :
    L.representedEdges p =
      directedSignedEdgeSet .backward (L.rawEdgeEntrySteps p u v hfinish) ∪ {(u, v)} := by
  rw [← decodeProperSteps_backwardEdges p hs,
    L.decodeProperSteps_eq_edgeEntry_append p hs u v hfinish,
    directedSignedEdgeSet_append]
  simp [directedSignedEdgeSet]

variable {L}

theorem HasBoundaryIncidence.rawEdgeEntrySteps_nodup
    (hL : L.HasBoundaryIncidence)
    (p : FinitePath L.lambda.graph) (hs : p.start ∈ L.lambda.source)
    (u v : V) (hfinish : p.finish = .edge u v) :
    (L.rawEdgeEntrySteps p u v hfinish).Nodup := by
  have h := hL.decodeProperSteps_nodup p
  rw [L.decodeProperSteps_eq_edgeEntry_append p hs u v hfinish] at h
  exact (List.nodup_append.1 h).1

theorem HasBoundaryIncidence.rawEdgeEntrySteps_omits_cut_edge
    (hL : L.HasBoundaryIncidence)
    (p : FinitePath L.lambda.graph) (hs : p.start ∈ L.lambda.source)
    (u v : V) (hfinish : p.finish = .edge u v) :
    (u, v) ∉ directedSignedEdgeSet .backward (L.rawEdgeEntrySteps p u v hfinish) := by
  rintro ⟨s, hsEntry, hd, he⟩
  have hsEq : s = SignedEdge.backward (u, v) := by
    cases s with
    | mk edge direction =>
        cases hd
        cases he
        rfl
  have h := hL.decodeProperSteps_nodup p
  rw [L.decodeProperSteps_eq_edgeEntry_append p hs u v hfinish] at h
  exact (List.nodup_append.1 h).2.2 s hsEntry
    (SignedEdge.backward (u, v)) (by simp) hsEq

/-- The actual cut switch. It differs from the exit switch by using the
cut-deleted reference and the word which stops before the final gadget. -/
def rawEdgeEntrySwitchedEdges (p : FinitePath L.lambda.graph) (u v : V)
    (hfinish : p.finish = .edge u v) (C : Set (V × V)) : Set (V × V) :=
  ((L.familyEdges \ C) \
    directedSignedEdgeSet .backward (L.rawEdgeEntrySteps p u v hfinish)) ∪
      L.properSelectedConnectorEdges p

theorem rawEdgeEntrySwitchedEdges_subset_raw
    (p : FinitePath L.lambda.graph) (hs : p.start ∈ L.lambda.source)
    (u v : V) (hfinish : p.finish = .edge u v) (C : Set (V × V))
    (heC : (u, v) ∈ C) :
    rawEdgeEntrySwitchedEdges p u v hfinish C ⊆ L.rawSwitchedEdges p := by
  intro e he
  rcases he with ⟨⟨heRef, heNotC⟩, heNotB⟩ | heF
  · left
    refine ⟨heRef, ?_⟩
    rw [L.rawEdgeEntrySteps_backward_partition p hs u v hfinish]
    rintro (heB | heLast)
    · exact heNotB heB
    · have heEq : e = (u, v) := Set.mem_singleton_iff.1 heLast
      exact heNotC (heEq.symm ▸ heC)
  · exact Or.inr heF

/-- Every backward edge of the head-stopping word survives the original
cut, provided no other cut gadget occurs on the selected path. -/
theorem HasBoundaryIncidence.rawEdgeEntry_backward_subset_cut_reference
    (hL : L.HasBoundaryIncidence)
    (p : FinitePath L.lambda.graph) (hs : p.start ∈ L.lambda.source)
    (u v : V) (hfinish : p.finish = .edge u v) (C : Set (V × V))
    (hcut : ∀ e ∈ C, LambdaVertex.edge e.1 e.2 ∈ p.support → e = (u, v)) :
    directedSignedEdgeSet .backward (L.rawEdgeEntrySteps p u v hfinish) ⊆
      L.familyEdges \ C := by
  intro e he
  have hrepresented : e ∈ L.representedEdges p := by
    rw [L.rawEdgeEntrySteps_backward_partition p hs u v hfinish]
    exact Or.inl he
  refine ⟨hrepresented.2, ?_⟩
  intro heC
  have heEq : e = (u, v) := hcut e heC hrepresented.1
  exact hL.rawEdgeEntrySteps_omits_cut_edge p hs u v hfinish (heEq ▸ he)

/-- Exact degree and boundary accounting for an ordinary-source route
stopped at the head of its final cut edge. -/
theorem HasBoundaryIncidence.rawEdgeEntrySwitch_biUnique_and_balance
    (hL : L.HasBoundaryIncidence)
    (p : FinitePath L.lambda.graph) (hs : p.start ∈ L.lambda.source)
    {s : V} (hstart : p.start = .old s)
    (u v : V) (hfinish : p.finish = .edge u v) (C : Set (V × V))
    (heC : (u, v) ∈ C)
    (hcut : ∀ e ∈ C, LambdaVertex.edge e.1 e.2 ∈ p.support → e = (u, v)) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ rawEdgeEntrySwitchedEdges p u v hfinish C) ∧
    ∀ x, edgeBalance (rawEdgeEntrySwitchedEdges p u v hfinish C) x =
      edgeBalance (L.familyEdges \ C) x + propInt (x = s) - propInt (x = v) := by
  let R := directedSignedEdgeSet .backward (L.rawEdgeEntrySteps p u v hfinish)
  have hR := hL.rawEdgeEntry_backward_subset_cut_reference p hs u v hfinish C hcut
  have hbase : Relator.BiUnique (fun x y ↦ (x, y) ∈ L.familyEdges \ C) :=
    ⟨fun _ _ _ h₁ h₂ ↦ L.raw_familyEdges_biUnique.1 h₁.1 h₂.1,
      fun _ _ _ h₁ h₂ ↦ L.raw_familyEdges_biUnique.2 h₁.1 h₂.1⟩
  have hsub := rawEdgeEntrySwitchedEdges_subset_raw p hs u v hfinish C heC
  have hraw := hL.rawSwitchedEdges_biUnique_of_start_old p hs hstart
  have hbi : Relator.BiUnique
      (fun x y ↦ (x, y) ∈ rawEdgeEntrySwitchedEdges p u v hfinish C) :=
    ⟨fun _ _ _ h₁ h₂ ↦ hraw.1 (hsub h₁) (hsub h₂),
      fun _ _ _ h₁ h₂ ↦ hraw.2 (hsub h₁) (hsub h₂)⟩
  refine ⟨hbi, ?_⟩
  intro x
  have hentry : L.gadgetEntry p.start = some s := by rw [hstart]; rfl
  have hexit : L.gadgetExit p.finish = some u := by rw [hfinish]; rfl
  have hrun : RunsFromTo s u (L.decodeProperSteps p) :=
    (L.decodeWalkSteps_runs_from_entry p.walk hentry hexit).filter_selfLoops
  rw [L.decodeProperSteps_eq_edgeEntry_append p hs u v hfinish] at hrun
  have hprefix : RunsFromTo s v (L.rawEdgeEntrySteps p u v hfinish) :=
    RunsFromTo.init_of_append_singleton hrun
  have hF : Relator.BiUnique (fun a b ↦ (a, b) ∈
      directedSignedEdgeSet .forward (L.rawEdgeEntrySteps p u v hfinish)) := by
    rw [L.rawEdgeEntrySteps_forwardEdges p hs u v hfinish]
    exact ⟨hL.properSelectedConnectorEdges_leftUnique p,
      hL.properSelectedConnectorEdges_rightUnique_of_no_proxy p
        (no_proxy_of_start_old p hs hstart)⟩
  have hB : Relator.BiUnique (fun a b ↦ (a, b) ∈ R) :=
    ⟨fun _ _ _ h₁ h₂ ↦ hbase.1 (hR h₁) (hR h₂),
      fun _ _ _ h₁ h₂ ↦ hbase.2 (hR h₁) (hR h₂)⟩
  have hdelta := hprefix.edgeBalance_forward_sub_backward
    (hL.rawEdgeEntrySteps_nodup p hs u v hfinish) hF hB x
  rw [L.rawEdgeEntrySteps_forwardEdges p hs u v hfinish] at hdelta
  have hdisj : Disjoint ((L.familyEdges \ C) \ R) (L.properSelectedConnectorEdges p) := by
    apply Set.disjoint_left.2
    intro e he hforward
    exact Set.disjoint_left.1
      (hL.connectorEdges_disjoint_familyEdges_of_start_old p hs hstart)
      (L.selectedConnectorEdges_subset_connectorEdges p hforward.1) he.1.1
  have hcalc := edgeBalance_sdiff_union_eq_add_sub hR hbase.2 hbase.1
    hbi.2 hbi.1 hdisj x
  change edgeBalance (((L.familyEdges \ C) \ R) ∪
    L.properSelectedConnectorEdges p) x =
      edgeBalance (L.familyEdges \ C) x + edgeBalance (L.properSelectedConnectorEdges p) x -
        edgeBalance R x at hcalc
  change edgeBalance (((L.familyEdges \ C) \ R) ∪
    L.properSelectedConnectorEdges p) x = _
  change edgeBalance (L.properSelectedConnectorEdges p) x - edgeBalance R x = _ at hdelta
  omega

end PopularAuxiliary.Input
end Erdos599

#print axioms
  Erdos599.PopularAuxiliary.Input.HasBoundaryIncidence.rawEdgeEntrySteps_omits_cut_edge
#print axioms
  Erdos599.PopularAuxiliary.Input.HasBoundaryIncidence.rawEdgeEntrySwitch_biUnique_and_balance
