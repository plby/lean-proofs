/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerCarriers

/-!
# A stationary family of uncut records

The bad records are exactly those whose source belongs to the popular cut
or whose original owner contains a cut reference edge. The concrete
source-carrier paths make their indices nonstationary. Subtracting these
indices leaves a stationary family whose sources avoid the cut and whose
reference owners are entirely uncut, as required by fragmentwise grounding.
-/

noncomputable section

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I) {kappa : Cardinal.{u}}

/-- Physical reference edges whose gadgets lie in the auxiliary cut. -/
def cutEdges (C : Set L.Vertex) : Set (V × V) :=
  {e | ∃ he : e ∈ familyEdges L.reference.paths, Vertex.edge ⟨e, he⟩ ∈ C}

theorem cutEdges_subset_reference (C : Set L.Vertex) :
    L.cutEdges C ⊆ familyEdges L.reference.paths := by
  rintro e ⟨he, _⟩
  exact he

/-- Cut membership at a record source or at an edge of its original owner. -/
def badRecords (C : Set L.Vertex) : Set I :=
  {i | Vertex.source i ∈ C ∨ ((L.record i).edgeSet ∩ L.cutEdges C).Nonempty}

theorem recordCarrier_meets_cut_iff (C : Set L.Vertex) (i : I) :
    (L.recordCarrier i ∩ C).Nonempty ↔ i ∈ L.badRecords C := by
  constructor
  · rintro ⟨a, ha, haC⟩
    cases a with
    | source j =>
        change j = i at ha
        exact Or.inl (ha ▸ haC)
    | marker y => exact ha.elim
    | off x => exact ha.elim
    | edge e => exact Or.inr ⟨e.1, ha, e.2, haC⟩
  · rintro (hi | ⟨e, hei, heY, heC⟩)
    · exact ⟨.source i, rfl, hi⟩
    · exact ⟨.edge ⟨e, heY⟩, hei, heC⟩

def badRecordIndices (U : Popular.KappaIndexed L.web kappa)
    (C : Set L.Vertex) : Set (Stationary.Below kappa) :=
  {a | ∃ i : I, U.f (L.sourceEquiv i) = a ∧ i ∈ L.badRecords C}

theorem badRecordIndices_eq_carrierContactIndices
    (U : Popular.KappaIndexed L.web kappa) (C : Set L.Vertex) :
    L.badRecordIndices U C = L.sourceCarriers.cutContactIndices U C := by
  ext a
  constructor
  · rintro ⟨i, hi, hbad⟩
    refine ⟨L.sourceEquiv i, hi, ?_⟩
    change (L.recordCarrier (L.sourceEquiv.symm (L.sourceEquiv i)) ∩ C).Nonempty
    rw [Equiv.symm_apply_apply]
    exact (L.recordCarrier_meets_cut_iff C i).mpr hbad
  · rintro ⟨x, hx, hcontact⟩
    refine ⟨L.sourceEquiv.symm x, ?_, ?_⟩
    · rwa [Equiv.apply_symm_apply]
    · exact (L.recordCarrier_meets_cut_iff C (L.sourceEquiv.symm x)).mp hcontact

theorem badRecordIndices_nonstationary (U : Popular.KappaIndexed L.web kappa)
    (S : Popular.PopularSeparator U) :
    ¬ Stationary.IsStationaryBelow kappa (L.badRecordIndices U S.cut) := by
  rw [L.badRecordIndices_eq_carrierContactIndices]
  exact L.sourceCarriers.cutContactIndices_nonstationary U S.cut S.not_strongly_popular

def goodRecordIndices (U : Popular.KappaIndexed L.web kappa)
    (C : Set L.Vertex) : Set (Stationary.Below kappa) :=
  Set.range U.f \ L.badRecordIndices U C

theorem goodRecordIndices_stationary (U : Popular.KappaIndexed L.web kappa)
    (S : Popular.PopularSeparator U) :
    Stationary.IsStationaryBelow kappa (L.goodRecordIndices U S.cut) :=
  PopularSwitching.stationary_diff_of_stationary_of_nonstationary
    U.regular U.uncountable U.f_range_stationary (L.badRecordIndices_nonstationary U S)

/-- Every surviving index has an actual record whose source is outside
the cut and no original reference edge of whose owner is cut. -/
theorem exists_uncut_record_of_mem_goodRecordIndices
    (U : Popular.KappaIndexed L.web kappa) (C : Set L.Vertex)
    {a : Stationary.Below kappa} (ha : a ∈ L.goodRecordIndices U C) :
    ∃ i : I, U.f (L.sourceEquiv i) = a ∧ Vertex.source i ∉ C ∧
      Disjoint (L.record i).edgeSet (L.cutEdges C) := by
  obtain ⟨x, hx⟩ := ha.1
  let i := L.sourceEquiv.symm x
  have hi : U.f (L.sourceEquiv i) = a := by
    simpa only [i, Equiv.apply_symm_apply] using hx
  refine ⟨i, hi, ?_, Set.disjoint_left.mpr ?_⟩
  · intro hsource
    exact ha.2 ⟨i, hi, Or.inl hsource⟩
  · intro e hei heC
    exact ha.2 ⟨i, hi, Or.inr ⟨e, hei, heC⟩⟩

#print axioms badRecordIndices_nonstationary
#print axioms goodRecordIndices_stationary
#print axioms exists_uncut_record_of_mem_goodRecordIndices

end Erdos599.GroundingAllMarkerAuxiliary.Input
