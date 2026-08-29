/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceHallBoundary

/-!
# Exact global removed boundaries of complete safe-word families

Both endpoints of a complete word lie outside the reference warp. Its
forward and backward balances therefore agree on the reference carrier.
At a nonzero boundary of the union removed relation, incidence removal and
endpoint purity force the same boundary of the union forward relation.

No local prefix-continuation or aggregate Hall sign is assumed.
-/

noncomputable section

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath SwitchingCore

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

theorem edgeBalances_eq_on_reference_of_endpoints_outside
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (Q : FiniteColouredOccurrenceWord W Y)
    (hfirst : Q.vertex 0 ∉ Gamma.vertexSet Y)
    (hlast : Q.vertex (Fin.last Q.length) ∉ Gamma.vertexSet Y)
    {x : V} (hx : x ∈ Gamma.vertexSet Y) :
    edgeBalance Q.forwardEdges x = edgeBalance Q.backwardEdges x := by
  have hxs : x ≠ Q.vertex 0 := fun h ↦ hfirst (h ▸ hx)
  have hxt : x ≠ Q.vertex (Fin.last Q.length) := fun h ↦ hlast (h ▸ hx)
  have hb := Q.edgeBalance_forward_sub_backward hW hY x
  simp only [propInt, hxs, hxt, if_false, sub_self] at hb
  omega

/-- A global lower removed boundary has an actual complete word which
supplies the corresponding positive forward boundary. -/
theorem exists_word_forward_lowerBoundary_of_backward_lowerBoundary
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {A : Set (FiniteColouredOccurrenceWord W Y)}
    (hfirstOff : ∀ Q ∈ A, Q.vertex 0 ∉ Gamma.vertexSet Y)
    (hlastOff : ∀ Q ∈ A, Q.vertex (Fin.last Q.length) ∉ Gamma.vertexSet Y)
    {x : V} (hout : HasOutgoing (familyBackwardEdges A) x)
    (hnoIn : ¬HasIncoming (familyBackwardEdges A) x) :
    ∃ Q ∈ A, HasOutgoing Q.forwardEdges x ∧ ¬HasIncoming Q.forwardEdges x := by
  obtain ⟨y, hxy⟩ := hout
  have hxY := (familyEdges_subset_vertexSet_prod Y
    (familyBackwardEdges_subset_familyEdges A hxy)).1
  obtain ⟨Q, hQA, hxyQ⟩ := mem_familyBackwardEdges_iff.mp hxy
  have hQnoIn : ¬HasIncoming Q.backwardEdges x := by
    rintro ⟨z, hzx⟩
    exact hnoIn ⟨z, mem_familyBackwardEdges_iff.mpr ⟨Q, hQA, hzx⟩⟩
  have hQR : edgeBalance Q.backwardEdges x = 1 :=
    edgeBalance_eq_one_iff.mpr ⟨⟨y, hxyQ⟩, hQnoIn⟩
  have hQF := (edgeBalances_eq_on_reference_of_endpoints_outside hW hY Q
    (hfirstOff Q hQA) (hlastOff Q hQA) hxY).trans hQR
  exact ⟨Q, hQA, edgeBalance_eq_one_iff.mp hQF⟩

/-- The complete-word witness at a global upper removed boundary. -/
theorem exists_word_forward_upperBoundary_of_backward_upperBoundary
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {A : Set (FiniteColouredOccurrenceWord W Y)}
    (hfirstOff : ∀ Q ∈ A, Q.vertex 0 ∉ Gamma.vertexSet Y)
    (hlastOff : ∀ Q ∈ A, Q.vertex (Fin.last Q.length) ∉ Gamma.vertexSet Y)
    {x : V} (hin : HasIncoming (familyBackwardEdges A) x)
    (hnoOut : ¬HasOutgoing (familyBackwardEdges A) x) :
    ∃ Q ∈ A, HasIncoming Q.forwardEdges x ∧ ¬HasOutgoing Q.forwardEdges x := by
  obtain ⟨y, hyx⟩ := hin
  have hxY := (familyEdges_subset_vertexSet_prod Y
    (familyBackwardEdges_subset_familyEdges A hyx)).2
  obtain ⟨Q, hQA, hyxQ⟩ := mem_familyBackwardEdges_iff.mp hyx
  have hQnoOut : ¬HasOutgoing Q.backwardEdges x := by
    rintro ⟨z, hxz⟩
    exact hnoOut ⟨z, mem_familyBackwardEdges_iff.mpr ⟨Q, hQA, hxz⟩⟩
  have hQR : edgeBalance Q.backwardEdges x = -1 :=
    edgeBalance_eq_neg_one_iff.mpr ⟨⟨y, hyxQ⟩, hQnoOut⟩
  have hQF := (edgeBalances_eq_on_reference_of_endpoints_outside hW hY Q
    (hfirstOff Q hQA) (hlastOff Q hQA) hxY).trans hQR
  exact ⟨Q, hQA, edgeBalance_eq_neg_one_iff.mp hQF⟩

/-- A positive boundary of the global removed union is a positive boundary
of the global forward union. Completeness is essential here. -/
theorem family_forward_positive_of_backward_positive
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {A : Set (FiniteColouredOccurrenceWord W Y)}
    (hsafe : ∀ Q ∈ A, Q.IsIntervalSafe)
    (hends : ∀ Q ∈ A, Q.vertex 0 ∉ Gamma.vertexSet Y ∧
      Q.vertex (Fin.last Q.length) ∉ Gamma.vertexSet Y)
    {x : V} (hx : edgeBalance (familyBackwardEdges A) x = 1) :
    edgeBalance (familyForwardEdges A) x = 1 := by
  obtain ⟨houtR, hnoInR⟩ := edgeBalance_eq_one_iff.mp hx
  obtain ⟨Q, hQA, ⟨z, hxz⟩, _⟩ :=
    exists_word_forward_lowerBoundary_of_backward_lowerBoundary hW hY
      (fun Q hQ ↦ (hends Q hQ).1) (fun Q hQ ↦ (hends Q hQ).2) houtR hnoInR
  obtain ⟨y, hxy⟩ := houtR
  have hxyY := familyBackwardEdges_subset_familyEdges A hxy
  have hxY := (familyEdges_subset_vertexSet_prod Y hxyY).1
  apply edgeBalance_eq_one_iff.mpr
  refine ⟨⟨z, mem_familyForwardEdges_iff.mpr ⟨Q, hQA, hxz⟩⟩, ?_⟩
  rintro ⟨a, hax⟩
  have hnoInY : ¬HasIncoming (familyEdges Y) x := by
    rintro ⟨b, hbx⟩
    exact hnoInR ⟨b, family_incoming_removed hsafe hax hbx⟩
  have hxInitial : x ∈ Gamma.initialSet Y := by
    rw [initialSet_eq_vertexSet_diff_hasIncoming hY hYfin]
    exact ⟨hxY, hnoInY⟩
  exact (family_endpoint_pure hsafe hax).1 hxInitial

/-- The dual exact boundary fact at a global upper removed boundary. -/
theorem family_forward_negative_of_backward_negative
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {A : Set (FiniteColouredOccurrenceWord W Y)}
    (hsafe : ∀ Q ∈ A, Q.IsIntervalSafe)
    (hends : ∀ Q ∈ A, Q.vertex 0 ∉ Gamma.vertexSet Y ∧
      Q.vertex (Fin.last Q.length) ∉ Gamma.vertexSet Y)
    {x : V} (hx : edgeBalance (familyBackwardEdges A) x = -1) :
    edgeBalance (familyForwardEdges A) x = -1 := by
  obtain ⟨hinR, hnoOutR⟩ := edgeBalance_eq_neg_one_iff.mp hx
  obtain ⟨Q, hQA, ⟨z, hzx⟩, _⟩ :=
    exists_word_forward_upperBoundary_of_backward_upperBoundary hW hY
      (fun Q hQ ↦ (hends Q hQ).1) (fun Q hQ ↦ (hends Q hQ).2) hinR hnoOutR
  obtain ⟨y, hyx⟩ := hinR
  have hyxY := familyBackwardEdges_subset_familyEdges A hyx
  have hxY := (familyEdges_subset_vertexSet_prod Y hyxY).2
  apply edgeBalance_eq_neg_one_iff.mpr
  refine ⟨⟨z, mem_familyForwardEdges_iff.mpr ⟨Q, hQA, hzx⟩⟩, ?_⟩
  rintro ⟨a, hxa⟩
  have hnoOutY : ¬HasOutgoing (familyEdges Y) x := by
    rintro ⟨b, hxb⟩
    exact hnoOutR ⟨b, family_outgoing_removed hsafe hxa hxb⟩
  have hxTerminal : x ∈ Gamma.terminalFrontier Y := by
    rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hY hYfin]
    exact ⟨hxY, hnoOutY⟩
  exact (family_endpoint_pure hsafe hxa).2 hxTerminal

#print axioms edgeBalances_eq_on_reference_of_endpoints_outside
#print axioms exists_word_forward_lowerBoundary_of_backward_lowerBoundary
#print axioms exists_word_forward_upperBoundary_of_backward_upperBoundary
#print axioms family_forward_positive_of_backward_positive
#print axioms family_forward_negative_of_backward_negative

end Erdos599.Alternating.FiniteColouredOccurrenceWord
