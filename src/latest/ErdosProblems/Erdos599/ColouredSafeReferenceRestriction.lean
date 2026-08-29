/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceSwitch

/-!
# Literal promotion from a reference-owner-closed carrier

Retain exactly the reference members contained in a carrier. If the carrier
contains whole owners at each of its vertices, every supported safe word
promotes to the original reference with all incidences and intervals intact.
No forward-owner closure or induced-boundary purity is asserted.
-/

noncomputable section

namespace Erdos599.Alternating

open Set DirectedPath SwitchingCore

universe u

variable {V : Type u} {Gamma : DWeb V}

def referencePathsInCarrier (Y : Set Gamma.DPath) (C : Set V) : Set Gamma.DPath :=
  {p | p ∈ Y ∧ p.support ⊆ C}

theorem referencePathsInCarrier_edges_subset (Y : Set Gamma.DPath) (C : Set V) :
    familyEdges (referencePathsInCarrier Y C) ⊆ familyEdges Y := by
  intro e he
  simp only [familyEdges, Set.mem_iUnion] at he ⊢
  obtain ⟨p, hp, hep⟩ := he
  exact ⟨p, hp.1, hep⟩

theorem mem_referencePathsInCarrier_of_support_contact
    {Y : Set Gamma.DPath} (hY : Gamma.IsWarp Y) {C : Set V}
    (hclosed : ∀ x ∈ C, coveredPathSupport hY x ⊆ C)
    {p : Gamma.DPath} (hp : p ∈ Y) {x : V}
    (hxp : x ∈ p.support) (hxC : x ∈ C) :
    p ∈ referencePathsInCarrier Y C := by
  refine ⟨hp, ?_⟩
  have howner := hclosed x hxC
  rw [coveredPathSupport_eq_of_mem hY hp hxp] at howner
  exact howner

theorem referenceEdge_mem_carrier_of_endpoint
    {Y : Set Gamma.DPath} (hY : Gamma.IsWarp Y) {C : Set V}
    (hclosed : ∀ x ∈ C, coveredPathSupport hY x ⊆ C)
    {e : V × V} (he : e ∈ familyEdges Y)
    (hcontact : e.1 ∈ C ∨ e.2 ∈ C) :
    e ∈ familyEdges (referencePathsInCarrier Y C) := by
  simp only [familyEdges, Set.mem_iUnion] at he ⊢
  obtain ⟨p, hp, hep⟩ := he
  refine ⟨p, ?_, hep⟩
  rcases hcontact with hx | hy
  · exact mem_referencePathsInCarrier_of_support_contact hY hclosed hp
      (p.edgeSet_subset_support_prod hep).1 hx
  · exact mem_referencePathsInCarrier_of_support_contact hY hclosed hp
      (p.edgeSet_subset_support_prod hep).2 hy

namespace FiniteColouredOccurrenceWord

variable {W W' Y Y' : Set Gamma.DPath}

/-- Retype actual edge ownership without changing any chronological data. -/
def retypeEdges (Q : FiniteColouredOccurrenceWord W Y)
    (hW : familyEdges W ⊆ familyEdges W')
    (hY : familyEdges Y ⊆ familyEdges Y') :
    FiniteColouredOccurrenceWord W' Y' where
  length := Q.length
  vertex := Q.vertex
  direction := Q.direction
  actualEdge_spec := by
    intro i
    cases hdir : Q.direction i with
    | forward => exact hW (by simpa only [hdir] using Q.actualEdge_spec i)
    | backward => exact hY (by simpa only [hdir] using Q.actualEdge_spec i)
  occurrence_injective := Q.occurrence_injective

@[simp] theorem retypeEdges_forwardEdges (Q : FiniteColouredOccurrenceWord W Y)
    (hW : familyEdges W ⊆ familyEdges W')
    (hY : familyEdges Y ⊆ familyEdges Y') :
    (Q.retypeEdges hW hY).forwardEdges = Q.forwardEdges := rfl

@[simp] theorem retypeEdges_backwardEdges (Q : FiniteColouredOccurrenceWord W Y)
    (hW : familyEdges W ⊆ familyEdges W')
    (hY : familyEdges Y ⊆ familyEdges Y') :
    (Q.retypeEdges hW hY).backwardEdges = Q.backwardEdges := rfl

theorem forwardEdges_endpoints_mem_vertexSet
    (Q : FiniteColouredOccurrenceWord W Y) {e : V × V}
    (he : e ∈ Q.forwardEdges) : e.1 ∈ Q.vertexSet ∧ e.2 ∈ Q.vertexSet := by
  obtain ⟨i, rfl⟩ := he
  rw [Q.forwardEdge_eq]
  exact ⟨⟨i.1.castSucc, rfl⟩, ⟨i.1.succ, rfl⟩⟩

theorem backwardEdges_endpoints_mem_vertexSet
    (Q : FiniteColouredOccurrenceWord W Y) {e : V × V}
    (he : e ∈ Q.backwardEdges) : e.1 ∈ Q.vertexSet ∧ e.2 ∈ Q.vertexSet := by
  obtain ⟨i, rfl⟩ := he
  rw [Q.backwardEdge_eq]
  exact ⟨⟨i.1.succ, rfl⟩, ⟨i.1.castSucc, rfl⟩⟩

/-- Literal interval safeness promotes from a reference-owner-closed carrier.
The forward warp is allowed to be any edge subrelation of the original. -/
theorem IsIntervalSafe.retype_from_referenceCarrier
    {Y W W' : Set Gamma.DPath} (hY : Gamma.IsWarp Y)
    {C : Set V}
    (hclosed : ∀ x ∈ C, coveredPathSupport hY x ⊆ C)
    (hW : familyEdges W ⊆ familyEdges W')
    {Q : FiniteColouredOccurrenceWord W (referencePathsInCarrier Y C)}
    (hQ : Q.IsIntervalSafe) (hQC : Q.vertexSet ⊆ C) :
    (Q.retypeEdges hW (referencePathsInCarrier_edges_subset Y C)).IsIntervalSafe := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b x hax hbx
    change (a, x) ∈ Q.forwardEdges at hax
    change (b, x) ∈ Q.backwardEdges
    apply hQ.incoming_removed hax
    exact referenceEdge_mem_carrier_of_endpoint hY hclosed hbx
      (Or.inr (hQC (Q.forwardEdges_endpoints_mem_vertexSet hax).2))
  · intro x a b hxa hxb
    change (x, a) ∈ Q.forwardEdges at hxa
    change (x, b) ∈ Q.backwardEdges
    apply hQ.outgoing_removed hxa
    exact referenceEdge_mem_carrier_of_endpoint hY hclosed hxb
      (Or.inl (hQC (Q.forwardEdges_endpoints_mem_vertexSet hxa).1))
  · intro p hpY
    change IsEdgeInterval (Q.backwardEdges ∩ p.edgeSet) p
    by_cases hpC : p.support ⊆ C
    · exact hQ.intervals p ⟨hpY, hpC⟩
    · left
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro e he
      have heC := hQC (Q.backwardEdges_endpoints_mem_vertexSet he.1).1
      exact hpC (mem_referencePathsInCarrier_of_support_contact
        hY hclosed hpY (p.edgeSet_subset_support_prod he.2).1 heC).2
  · intro x y hxy
    change (x, y) ∈ Q.forwardEdges at hxy
    have hlocal := hQ.endpoint_pure hxy
    have hends := Q.forwardEdges_endpoints_mem_vertexSet hxy
    constructor
    · rintro ⟨p, hpY, hpStart⟩
      apply hlocal.1
      refine ⟨p, ?_, hpStart⟩
      exact mem_referencePathsInCarrier_of_support_contact hY hclosed hpY
        (hpStart ▸ p.initial_mem_support) (hQC hends.2)
    · rintro ⟨p, hpY, hpFinish⟩
      apply hlocal.2
      refine ⟨p, ?_, hpFinish⟩
      have hxP : x ∈ p.support := by
        cases p with
        | inl q =>
            have hx : q.finish = x := Option.some.inj hpFinish
            exact hx ▸ q.finish_mem_support
        | inr r => cases hpFinish
      exact mem_referencePathsInCarrier_of_support_contact hY hclosed hpY
        hxP (hQC hends.1)

#print axioms IsIntervalSafe.retype_from_referenceCarrier

end FiniteColouredOccurrenceWord
end Erdos599.Alternating
