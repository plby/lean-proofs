/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayContactTransaction

/-!
# Contact transactions grouped by a recombined owner

Occurrence projection can identify the incoming and outgoing copies of one
cut vertex.  The corresponding selected sources need not be equal: they can
belong to consecutive fragments of one recombined path.  Thus projected
contact chains must be grouped by a recombined owner rather than indexed
globally by their literal assignment source.

This file gives the exact generic compiler.  Common contacts determine a
common group; bi-uniqueness and a traversal rank are proved within a group.
Those local statements imply a bi-unique, acyclic, reverse-ray-free global
relation and hence an honest `ForwardOrientation`.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating
open Alternating.RelationDecomposition

universe u v

variable {V : Type u}
variable {Gamma : DWeb V} {Y closureFamily : Set Gamma.DPath}
variable {X before innerRoof outerRoof : Set V}
variable {kappa : Cardinal.{u}}

/-- The contact chains together with their recombined owner.

`contact_groups_agree` is the projection-provenance theorem: two literal
sources whose projected routes use the same contact belong to one recombined
owner.  It intentionally does not claim that the sources are equal.
`grouped_biunique` is then a local statement about the single concatenated
chain of that owner, not a global conclusion repackaged as an assumption. -/
structure GroupedContactSegmentedAssignment
    {Z : Set Gamma.DPath} (A : SimultaneousAssignment Z Y)
    (X before innerRoof outerRoof : Set V)
    (closureFamily : Set Gamma.DPath) (G : Type v) where
  segmentation : ∀ s, ContactSegmentation (Y := Y) (A.assigned s) X before
    innerRoof outerRoof closureFamily
  group : {z : V // z ∈ Gamma.initialSet Z \ Gamma.initialSet Y} → G
  contact_groups_agree : ∀ s t x,
    x ∈ (segmentation s).contactSet →
    x ∈ (segmentation t).contactSet → group s = group t
  grouped_biunique : ∀ g,
    Relator.BiUnique (fun x y ↦ ∃ s, group s = g ∧
      (x, y) ∈ (segmentation s).compressedOutsideEdges)
  localRank : G → V → Nat
  localRank_step : ∀ s {x y},
    (x, y) ∈ (segmentation s).compressedOutsideEdges →
      localRank (group s) x < localRank (group s) y

namespace GroupedContactSegmentedAssignment

variable {Z : Set Gamma.DPath} {A : SimultaneousAssignment Z Y}
variable {G : Type v}

/-- The public relation is still a relation on the original vertices; group
tags are retained only as proof provenance. -/
def edge
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G) : Set (V × V) :=
  ⋃ s, (S.segmentation s).compressedOutsideEdges

/-- Every compressed interval is a Claim-2 imaginary edge. -/
theorem edge_subset_imaginaryGraph
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa) :
    S.edge ⊆ {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  intro e he
  simp only [edge, Set.mem_iUnion] at he
  obtain ⟨s, he⟩ := he
  exact (S.segmentation s).compressedOutsideEdges_subset_imaginaryGraph
    hclosed he

/-- Group-local bi-uniqueness and common-contact ownership imply global
bi-uniqueness. -/
theorem edge_biunique
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ S.edge) := by
  constructor
  · intro a b c hac hbc
    simp only [edge, Set.mem_iUnion] at hac hbc
    obtain ⟨s, hac⟩ := hac
    obtain ⟨t, hbc⟩ := hbc
    have hcs :=
      (S.segmentation s).endpoints_mem_contactSet_of_mem_compressedOutsideEdges
        hac |>.2
    have hct :=
      (S.segmentation t).endpoints_mem_contactSet_of_mem_compressedOutsideEdges
        hbc |>.2
    have hgroup : S.group s = S.group t :=
      S.contact_groups_agree s t c hcs hct
    exact (S.grouped_biunique (S.group s)).1
      ⟨s, rfl, hac⟩ ⟨t, hgroup.symm, hbc⟩
  · intro a b c hab hac
    simp only [edge, Set.mem_iUnion] at hab hac
    obtain ⟨s, hab⟩ := hab
    obtain ⟨t, hac⟩ := hac
    have has :=
      (S.segmentation s).endpoints_mem_contactSet_of_mem_compressedOutsideEdges
        hab |>.1
    have hat :=
      (S.segmentation t).endpoints_mem_contactSet_of_mem_compressedOutsideEdges
        hac |>.1
    have hgroup : S.group s = S.group t :=
      S.contact_groups_agree s t a has hat
    exact (S.grouped_biunique (S.group s)).2
      ⟨s, rfl, hab⟩ ⟨t, hgroup.symm, hac⟩

/-- The group owning a contact, if the contact occurs.  The value is
independent of the chosen source by `contact_groups_agree`. -/
noncomputable def contactGroup
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G) (x : V) : Option G := by
  classical
  exact if h : ∃ s, x ∈ (S.segmentation s).contactSet then
      some (S.group (Classical.choose h))
    else none

theorem contactGroup_eq_some_of_mem
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G)
    (s : {z : V // z ∈ Gamma.initialSet Z \ Gamma.initialSet Y})
    {x : V} (hx : x ∈ (S.segmentation s).contactSet) :
    S.contactGroup x = some (S.group s) := by
  rw [contactGroup, dif_pos ⟨s, hx⟩]
  congr 1
  exact S.contact_groups_agree (Classical.choose
    (show ∃ t, x ∈ (S.segmentation t).contactSet from ⟨s, hx⟩)) s x
      (Classical.choose_spec
        (show ∃ t, x ∈ (S.segmentation t).contactSet from ⟨s, hx⟩)) hx

/-- The global rank uses the local rank of the uniquely determined contact
group and is zero away from all contacts. -/
noncomputable def rank
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G) (x : V) : Nat :=
  match S.contactGroup x with
  | none => 0
  | some g => S.localRank g x

theorem rank_lt_of_mem_edge
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G) {x y : V} (hxy : (x, y) ∈ S.edge) :
    S.rank x < S.rank y := by
  simp only [edge, Set.mem_iUnion] at hxy
  obtain ⟨s, hxy⟩ := hxy
  have hx :=
    (S.segmentation s).endpoints_mem_contactSet_of_mem_compressedOutsideEdges
      hxy |>.1
  have hy :=
    (S.segmentation s).endpoints_mem_contactSet_of_mem_compressedOutsideEdges
      hxy |>.2
  simp only [rank, S.contactGroup_eq_some_of_mem s hx,
    S.contactGroup_eq_some_of_mem s hy]
  exact S.localRank_step s hxy

theorem edge_acyclic
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G) :
    ¬ ContainsDirectedCycle S.edge :=
  Alternating.GenericSimultaneousSwitch.not_containsDirectedCycle_of_wellFoundedRank
    S.edge S.rank S.rank_lt_of_mem_edge

theorem edge_no_reverse_ray
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G) :
    ¬ ContainsReverseDirectedRay S.edge :=
  Alternating.GenericSimultaneousSwitch.not_containsReverseDirectedRay_of_wellFoundedRank
    S.edge S.rank S.rank_lt_of_mem_edge

/-- The grouped relation has an honest forward orientation on every carrier
containing its endpoints. -/
theorem exists_forwardOrientation
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa)
    (carrier : Set V)
    (hendpoints : ∀ e ∈ S.edge, e.1 ∈ carrier ∧ e.2 ∈ carrier) :
    ∃ O : ForwardOrientation (imaginaryGraph Gamma Y kappa), O.edge = S.edge :=
  ForwardOrientation.exists_forwardOrientation S.edge carrier
    (S.edge_subset_imaginaryGraph hclosed) hendpoints S.edge_biunique
      S.edge_acyclic S.edge_no_reverse_ray

end GroupedContactSegmentedAssignment

end LinkageBlueprint
end Blueprint
end Erdos599
