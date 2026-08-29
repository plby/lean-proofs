/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceFiniteReachability
import ErdosProblems.Erdos599.OffReferenceEndpointNormalization

/-!
# No artificial safe terminals in a finite search restriction

The whole forward owner of a safely reached off-reference endpoint belongs
to the search carrier. Consequently a restriction containing that carrier
cannot turn such an endpoint into a new sink. This is not global closure
of the carrier under all forward owners.
-/

noncomputable section

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath SwitchingCore

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- The whole original forward owner of an off-reference safe endpoint is
in the common search carrier of its original source. -/
theorem safe_endpoint_owner_subset_safeSearchCarrier
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    (total : FiniteColouredOccurrenceWord W Y)
    (htotal : total.IsIntervalSafe)
    (hfirst : total.vertex 0 ∈ Gamma.initialSet W)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlastMem : total.vertex (Fin.last total.length) ∈ Gamma.vertexSet W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y) :
    coveredPathSupport hW (total.vertex (Fin.last total.length)) ⊆
      safeSearchCarrier hW hY (initialSet_subset_vertexSet W hfirst) := by
  obtain ⟨P, hreach, hlast⟩ := exists_reachable_normalizedEndpointNode
    hW hY hWfin hYfin total htotal hfirst hfirstOff hlastMem hlastOff
  have hcarrier :
      coveredPathSupport hW (P.word.vertex (Fin.last P.word.length)) ⊆
        safeSearchCarrier hW hY (initialSet_subset_vertexSet W hfirst) := by
    intro x hx
    exact extensionCarrier_subset_safeSearchCarrier hW hY
      (initialSet_subset_vertexSet W hfirst) hreach (Or.inr (Or.inl hx))
  simpa only [hlast] using hcarrier

/-- Restricting the original forward edges to a region containing the safe
search carrier does not remove outgoing edges at a safely reached endpoint. -/
theorem hasOutgoing_restriction_iff_at_safe_endpoint
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    (total : FiniteColouredOccurrenceWord W Y)
    (htotal : total.IsIntervalSafe)
    (hfirst : total.vertex 0 ∈ Gamma.initialSet W)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlastMem : total.vertex (Fin.last total.length) ∈ Gamma.vertexSet W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y)
    (C : Set V)
    (hC : safeSearchCarrier hW hY (initialSet_subset_vertexSet W hfirst) ⊆ C) :
    HasOutgoing (familyEdges W ∩ (C ×ˢ C))
        (total.vertex (Fin.last total.length)) ↔
      HasOutgoing (familyEdges W) (total.vertex (Fin.last total.length)) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, hx.1⟩
  · rintro ⟨x, hx⟩
    have hownerC := (safe_endpoint_owner_subset_safeSearchCarrier
      hW hY hWfin hYfin total htotal hfirst hfirstOff hlastMem hlastOff).trans hC
    have hedge := hx
    simp only [familyEdges, Set.mem_iUnion] at hedge
    obtain ⟨p, hpW, hep⟩ := hedge
    have hlastP := (p.edgeSet_subset_support_prod hep).1
    have hxP := (p.edgeSet_subset_support_prod hep).2
    have hcover := coveredPathSupport_eq_of_mem hW hpW hlastP
    rw [hcover] at hownerC
    exact ⟨x, hx, hownerC hlastP, hownerC hxP⟩

/-- A safely reached off-reference endpoint which is a sink after the
finite-region restriction was already an original forward terminal. -/
theorem mem_terminalFrontier_of_restricted_sink_at_safe_endpoint
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    (total : FiniteColouredOccurrenceWord W Y)
    (htotal : total.IsIntervalSafe)
    (hfirst : total.vertex 0 ∈ Gamma.initialSet W)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlastMem : total.vertex (Fin.last total.length) ∈ Gamma.vertexSet W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y)
    (C : Set V)
    (hC : safeSearchCarrier hW hY (initialSet_subset_vertexSet W hfirst) ⊆ C)
    (hsink : ¬HasOutgoing (familyEdges W ∩ (C ×ˢ C))
      (total.vertex (Fin.last total.length))) :
    total.vertex (Fin.last total.length) ∈ Gamma.terminalFrontier W := by
  rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hW hWfin]
  refine ⟨hlastMem, ?_⟩
  intro hout
  exact hsink ((hasOutgoing_restriction_iff_at_safe_endpoint
    hW hY hWfin hYfin total htotal hfirst hfirstOff hlastMem hlastOff C hC).mpr hout)

#print axioms safe_endpoint_owner_subset_safeSearchCarrier
#print axioms hasOutgoing_restriction_iff_at_safe_endpoint
#print axioms mem_terminalFrontier_of_restricted_sink_at_safe_endpoint

end Erdos599.Alternating.FiniteColouredOccurrenceWord
