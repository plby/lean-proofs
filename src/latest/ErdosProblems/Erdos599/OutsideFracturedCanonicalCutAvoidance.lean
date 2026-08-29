/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.OutsideFracturedCanonicalBoundary
import ErdosProblems.Erdos599.FracturedCanonicalSafeProjection
import ErdosProblems.Erdos599.ColouredOccurrenceBoundaryAvoidance

/-!
# Literal cut avoidance of canonical projected occurrence words

An outside fractured member meets the cut only at its endpoints. Its
canonical lift has only the corresponding endpoint-role copies there.
Exposed honest-warp boundaries cannot be internal word occurrences, so
projected finite/infinite words meet the cut only at their endpoint(s).
-/

namespace Erdos599.Blueprint.LinkageBlueprint

open Set DirectedPath Alternating FracturedDuplication FracturedAssignmentPeel
open FracturedCanonicalBoundary FracturedCanonicalSafeProjection
open Alternating.FracturedCanonicalFiniteLift
open Alternating.FracturedCanonicalOccurrenceProjection
open ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath} {X : Set V}

namespace OutsideFracturedWarp

/-- A singleton outside member cannot lie in the cut: a cut initial would
have an outgoing outside edge, but no fractured edge meets a singleton. -/
theorem singleton_not_mem_cut (F : OutsideFracturedWarp W X) {x : V}
    (hx : x ∈ singletonVertices F.holes) : x ∉ X := by
  intro hxX
  have hinit : x ∈ Gamma.initialSet F.holes.paths :=
    ⟨Gamma.trivialPath x, hx, Gamma.initial_trivialPath x⟩
  rw [F.initialSet_eq] at hinit
  rcases hinit with ⟨_, y, hxy⟩ | ⟨_, hxOff, _⟩
  · have hxyEdge : (x, y) ∈ familyEdges F.holes.edgeWarp := by
      rwa [F.edgeWarp_familyEdges]
    exact (edge_not_incident_singletonVertex F.holes hx hxyEdge).1 rfl
  · exact hxOff hxX

/-- The literal fractured members cannot contain an internal cut vertex;
this follows from the exact cut initial set, not an extra stored field. -/
theorem finite_support_inter_cut_subset_endpoints (F : OutsideFracturedWarp W X)
    (p : FinitePath Gamma.graph) (hp : (.inl p : Gamma.DPath) ∈ F.holes.paths) :
    p.support ∩ X ⊆ {p.start, p.finish} := by
  rintro x ⟨hxp, hxX⟩
  by_cases hxstart : x = p.start
  · exact Or.inl hxstart
  by_cases hxfinish : x = p.finish
  · exact Or.inr hxfinish
  obtain ⟨y, hxy⟩ := FinitePath.exists_edge_from_of_mem_of_ne_finish p hxp hxfinish
  have hxyOutside : (x, y) ∈ outsideFamilyEdges W X := by
    rw [← F.familyEdges_eq]
    exact Set.mem_iUnion.mpr ⟨.inl p, Set.mem_iUnion.mpr ⟨hp, hxy⟩⟩
  have hxInitial : x ∈ Gamma.initialSet F.holes.paths := by
    rw [F.initialSet_eq]
    exact Or.inl ⟨hxX, y, hxyOutside⟩
  obtain ⟨q, hq, hqx⟩ := hxInitial
  have hpq : (.inl p : Gamma.DPath) ≠ q := by
    rintro rfl
    exact hxstart hqx.symm
  have hxq : x ∈ q.support := hqx ▸ q.initial_mem_support
  have hmeet : ¬Disjoint (Path.support (.inl p : Gamma.DPath)) q.support := by
    exact Set.not_disjoint_iff.mpr ⟨x, hxp, hxq⟩
  obtain ⟨_, _, hleft | hright⟩ := F.holes.allowed_intersection hp hq hpq hmeet
  · obtain ⟨t, _, hpt, hinter⟩ := hleft
    have hxt : x = t := by
      have hx : x ∈ ({t} : Set V) := hinter ▸ (show x ∈ _ ∩ _ from ⟨hxp, hxq⟩)
      exact hx
    exact False.elim (hxstart (hxt.trans hpt.symm))
  · obtain ⟨t, hpt, hqt, _⟩ := hright
    have htx : t = x := hqt.symm.trans hqx
    change some p.finish = some t at hpt
    exact False.elim (hxfinish (htx.symm.trans (Option.some.inj hpt).symm))

/-- Above a cut vertex the canonical active lift has only an actual initial
or an actual terminal. Its plain internal copies never lie above the cut. -/
theorem canonicalActiveLift_cut_boundary (F : OutsideFracturedWarp W X) :
    (web Gamma F.holes).vertexSet (canonicalActiveLift F.holes) ∩
        (project ⁻¹' X) ⊆
      (web Gamma F.holes).initialSet (canonicalActiveLift F.holes) ∪
        (web Gamma F.holes).terminalFrontier (canonicalActiveLift F.holes) := by
  rintro z ⟨⟨P, ⟨p, hp, hne, rfl⟩, hz⟩, hzX⟩
  change z ∈ (lift F.holes p hne).support at hz
  have hproject : project z ∈ p.support := by
    rw [← project_image_lift_support F.holes p hne]
    exact ⟨z, hz, rfl⟩
  rcases F.finite_support_inter_cut_subset_endpoints p hp ⟨hproject, hzX⟩ with
    hstart | hfinish
  · left
    have hzstart := eq_outgoing_start_of_mem_lift_support_of_project_eq
      F.holes p hne hz hstart
    refine ⟨.inl (lift F.holes p hne), lift_mem_liftedActiveFinitePaths F.holes hp hne, ?_⟩
    exact hzstart.symm
  · right
    have hzfinish := eq_incoming_finish_of_mem_lift_support_of_project_eq
      F.holes p hne hz hfinish
    refine ⟨.inl (lift F.holes p hne), lift_mem_liftedActiveFinitePaths F.holes hp hne, ?_⟩
    exact congrArg some hzfinish.symm

theorem canonicalReference_cut_disjoint (F : OutsideFracturedWarp W X)
    (hX : Disjoint X (Gamma.vertexSet Y)) :
    Disjoint (project ⁻¹' X)
      ((web Gamma F.holes).vertexSet (canonicalPeeledReferenceLift F.holes Y)) := by
  rw [Set.disjoint_left]
  intro z hzX hzY
  obtain ⟨p, hp, hzp⟩ :=
    project_mem_vertexSet_activeReference_of_mem_canonicalLift F.holes Y hzY
  exact Set.disjoint_left.mp hX hzX ⟨p, activeReference_subset F.holes Y hp, hzp⟩

theorem finiteCanonicalWord_inter_cut_subset_endpoints (F : OutsideFracturedWarp W X)
    (hX : Disjoint X (Gamma.vertexSet Y))
    (Q : FiniteColouredOccurrenceWord
      (canonicalActiveLift F.holes) (canonicalPeeledReferenceLift F.holes Y))
    (hfirst : Q.vertex 0 ∈ (web Gamma F.holes).initialSet
      (canonicalActiveLift F.holes)) :
    Q.vertexSet ∩ (project ⁻¹' X) ⊆
      {Q.vertex 0, Q.vertex (Fin.last Q.length)} := by
  apply Q.vertexSet_inter_subset_endpoints (liftedActiveFinitePaths_isWarp F.holes)
    (liftedActiveFinitePaths_hasFiniteCharacter F.holes) (F.canonicalReference_cut_disjoint hX)
  rintro z ⟨hzQ, hzX⟩
  have hcarrier := Q.vertexSet_subset_forward_union_reference
    (Or.inl (initialSet_subset_vertexSet _ hfirst)) hzQ
  rcases hcarrier with hzW | hzY
  · exact F.canonicalActiveLift_cut_boundary ⟨hzW, hzX⟩
  · exact False.elim (Set.disjoint_left.mp (F.canonicalReference_cut_disjoint hX) hzX hzY)

theorem infiniteCanonicalWord_inter_cut_subset_initial (F : OutsideFracturedWarp W X)
    (hX : Disjoint X (Gamma.vertexSet Y))
    (Q : InfiniteColouredOccurrenceWord
      (canonicalActiveLift F.holes) (canonicalPeeledReferenceLift F.holes Y)) :
    Q.vertexSet ∩ (project ⁻¹' X) ⊆ {Q.vertex 0} := by
  apply Q.vertexSet_inter_subset_initial (liftedActiveFinitePaths_isWarp F.holes)
    (liftedActiveFinitePaths_hasFiniteCharacter F.holes) (F.canonicalReference_cut_disjoint hX)
  rintro z ⟨hzQ, hzX⟩
  rcases Q.vertexSet_subset_forward_union_reference hzQ with hzW | hzY
  · exact F.canonicalActiveLift_cut_boundary ⟨hzW, hzX⟩
  · exact False.elim (Set.disjoint_left.mp (F.canonicalReference_cut_disjoint hX) hzX hzY)

end OutsideFracturedWarp

namespace FracturedCanonicalSafeProjection

/-- An edge leaving an active lifted initial is a genuine original edge,
not a connector in the discarded initial block. -/
theorem edge_from_initial_projects_ne (Z : FracturedWarp Gamma)
    {z w : Vertex V} (hz : z ∈ (web Gamma Z).initialSet (canonicalActiveLift Z))
    (he : (z, w) ∈ familyEdges (canonicalActiveLift Z)) : project z ≠ project w := by
  obtain ⟨P, heP⟩ := Set.mem_iUnion.mp he
  obtain ⟨hP, heP⟩ := Set.mem_iUnion.mp heP
  obtain ⟨p, hp, hne, rfl⟩ := hP
  change (z, w) ∈ (lift Z p hne).edgeSet at heP
  have hpLift := lift_mem_liftedActiveFinitePaths Z hp hne
  have hzstart : z = (lift Z p hne).start :=
    finite_support_inter_initialSet_of_isWarp (liftedActiveFinitePaths_isWarp Z)
      hpLift ⟨(FinitePath.edgeSet_subset_support_prod _ heP).1, hz⟩
  have hzrole : z = outgoing p.start := hzstart.trans (lift_start Z p hne)
  intro hproject
  have hwproject : project w = p.start :=
    hproject.symm.trans (congrArg project hzrole)
  have hwrole := eq_outgoing_start_of_mem_lift_support_of_project_eq Z p hne
    (FinitePath.edgeSet_subset_support_prod _ heP).2 hwproject
  have hwz : w = z := hwrole.trans hzrole.symm
  exact ColouredResidualPortContinuation.not_self_mem_familyEdges
    (canonicalActiveLift Z) z (hwz ▸ he)

/-- Connector deletion does not erase the first genuine edge of an active
source-to-terminal word. -/
theorem finiteSafeProjection_length_pos (Z : FracturedWarp Gamma)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (Q : FiniteColouredOccurrenceWord
      (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y))
    (hfirst : Q.vertex 0 ∈ (web Gamma Z).initialSet (canonicalActiveLift Z))
    (hfirstOff : Q.vertex 0 ∉ (web Gamma Z).vertexSet (canonicalPeeledReferenceLift Z Y))
    (hlast : Q.vertex (Fin.last Q.length) ∈
      (web Gamma Z).terminalFrontier (canonicalActiveLift Z)) :
    0 < (finiteSafeProjection Z hYfinite Q).length := by
  have hpos : 0 < Q.length := by
    by_contra hn
    have hzero : Q.length = 0 := by omega
    have heq : Q.vertex 0 = Q.vertex (Fin.last Q.length) :=
      congrArg Q.vertex (Fin.ext (by simp [hzero]))
    obtain ⟨a, _, ha⟩ := initial_data_canonicalActiveLift Z hfirst
    obtain ⟨b, _, hb⟩ := terminal_data_canonicalActiveLift Z hlast
    have hrole := congrArg Prod.snd (ha.symm.trans (heq.trans hb))
    cases hrole
  let i : Fin Q.length := ⟨0, hpos⟩
  have hi : i.castSucc = 0 := Fin.ext rfl
  have he := Q.actualEdge_spec i
  have hproper : project (Q.vertex i.castSucc) ≠ project (Q.vertex i.succ) := by
    cases hd : Q.direction i with
    | forward =>
      simp only [hd] at he
      apply edge_from_initial_projects_ne Z (by simpa only [hi] using hfirst) he
    | backward =>
      simp only [hd] at he
      exact False.elim (hfirstOff (by
        simpa only [hi] using
          (familyEdges_subset_vertexSet_prod (canonicalPeeledReferenceLift Z Y) he).2))
  change 0 < (FiniteColouredOccurrenceWord.ConnectorDeletion.properSteps Q.vertex project).card
  apply Finset.card_pos.mpr
  exact ⟨i, by simpa [FiniteColouredOccurrenceWord.ConnectorDeletion.properSteps] using hproper⟩

theorem finiteSafeProjection_vertexSet_subset (Z : FracturedWarp Gamma)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (Q : FiniteColouredOccurrenceWord
      (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y)) :
    (finiteSafeProjection Z hYfinite Q).vertexSet ⊆ project '' Q.vertexSet := by
  rintro x ⟨i, rfl⟩
  exact FiniteColouredOccurrenceWord.ConnectorDeletion.vertex_mem_image Q.vertex project i

theorem infiniteSafeProjection_vertexSet_subset (Z : FracturedWarp Gamma)
    (hY : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (Q : InfiniteColouredOccurrenceWord
      (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y)) :
    (infiniteSafeProjection Z hY hYfinite Q).vertexSet ⊆ project '' Q.vertexSet := by
  rintro x ⟨i, rfl⟩
  exact ⟨Q.vertex (Q.properIndex project i), ⟨_, rfl⟩, rfl⟩

end FracturedCanonicalSafeProjection

namespace OutsideFracturedWarp

/-- The actual finite projected word has no internal cut vertex. -/
theorem finiteSafeProjection_inter_cut_subset_endpoints (F : OutsideFracturedWarp W X)
    (hYfinite : Gamma.HasFiniteCharacter Y) (hX : Disjoint X (Gamma.vertexSet Y))
    (Q : FiniteColouredOccurrenceWord
      (canonicalActiveLift F.holes) (canonicalPeeledReferenceLift F.holes Y))
    (hfirst : Q.vertex 0 ∈ (web Gamma F.holes).initialSet
      (canonicalActiveLift F.holes)) :
    (finiteSafeProjection F.holes hYfinite Q).vertexSet ∩ X ⊆
      {project (Q.vertex 0), project (Q.vertex (Fin.last Q.length))} := by
  rintro x ⟨hx, hxX⟩
  obtain ⟨z, hzQ, rfl⟩ := finiteSafeProjection_vertexSet_subset F.holes hYfinite Q hx
  rcases F.finiteCanonicalWord_inter_cut_subset_endpoints hX Q hfirst ⟨hzQ, hxX⟩ with
    hfirst | hlast
  · exact Or.inl (congrArg project hfirst)
  · exact Or.inr (congrArg project hlast)

/-- The actual infinite projected word has no cut vertex after its initial. -/
theorem infiniteSafeProjection_inter_cut_subset_initial (F : OutsideFracturedWarp W X)
    (hY : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hX : Disjoint X (Gamma.vertexSet Y))
    (Q : InfiniteColouredOccurrenceWord
      (canonicalActiveLift F.holes) (canonicalPeeledReferenceLift F.holes Y)) :
    (infiniteSafeProjection F.holes hY hYfinite Q).vertexSet ∩ X ⊆
      {project (Q.vertex 0)} := by
  rintro x ⟨hx, hxX⟩
  obtain ⟨z, hzQ, rfl⟩ := infiniteSafeProjection_vertexSet_subset F.holes hY hYfinite Q hx
  exact congrArg project (F.infiniteCanonicalWord_inter_cut_subset_initial hX Q ⟨hzQ, hxX⟩)

/-- A nonempty downstairs word cannot remain inside the cut: its first
edge is either an outside edge or a reference edge disjoint from the cut. -/
theorem finiteWord_not_vertexSet_subset_cut (F : OutsideFracturedWarp W X)
    (hX : Disjoint X (Gamma.vertexSet Y))
    (Q : FiniteColouredOccurrenceWord F.holes.edgeWarp Y) (hpos : 0 < Q.length) :
    ¬ Q.vertexSet ⊆ X := by
  intro hsubset
  let i : Fin Q.length := ⟨0, hpos⟩
  have hx : Q.vertex i.castSucc ∈ X := hsubset ⟨_, rfl⟩
  have hy : Q.vertex i.succ ∈ X := hsubset ⟨_, rfl⟩
  have he := Q.actualEdge_spec i
  cases hd : Q.direction i with
  | forward =>
    simp only [hd] at he
    rw [F.edgeWarp_familyEdges] at he
    exact he.2 ⟨hx, hy⟩
  | backward =>
    simp only [hd] at he
    exact Set.disjoint_left.mp hX hx (familyEdges_subset_vertexSet_prod Y he).2

theorem infiniteWord_not_vertexSet_subset_cut (F : OutsideFracturedWarp W X)
    (hX : Disjoint X (Gamma.vertexSet Y))
    (Q : InfiniteColouredOccurrenceWord F.holes.edgeWarp Y) :
    ¬ Q.vertexSet ⊆ X := by
  intro hsubset
  have hx : Q.vertex 0 ∈ X := hsubset ⟨0, rfl⟩
  have hy : Q.vertex 1 ∈ X := hsubset ⟨1, rfl⟩
  have he := Q.actualEdge_spec 0
  cases hd : Q.direction 0 with
  | forward =>
    simp only [hd] at he
    rw [F.edgeWarp_familyEdges] at he
    exact he.2 ⟨hx, hy⟩
  | backward =>
    simp only [hd] at he
    exact Set.disjoint_left.mp hX hx (familyEdges_subset_vertexSet_prod Y he).2

/-- A canonical active finite projection genuinely leaves the cut. -/
theorem finiteSafeProjection_not_vertexSet_subset_cut (F : OutsideFracturedWarp W X)
    (hYfinite : Gamma.HasFiniteCharacter Y) (hX : Disjoint X (Gamma.vertexSet Y))
    (Q : FiniteColouredOccurrenceWord
      (canonicalActiveLift F.holes) (canonicalPeeledReferenceLift F.holes Y))
    (hfirst : Q.vertex 0 ∈ (web Gamma F.holes).initialSet (canonicalActiveLift F.holes))
    (hfirstOff : Q.vertex 0 ∉ (web Gamma F.holes).vertexSet
      (canonicalPeeledReferenceLift F.holes Y))
    (hlast : Q.vertex (Fin.last Q.length) ∈
      (web Gamma F.holes).terminalFrontier (canonicalActiveLift F.holes)) :
    ¬ (finiteSafeProjection F.holes hYfinite Q).vertexSet ⊆ X :=
  F.finiteWord_not_vertexSet_subset_cut hX _
    (finiteSafeProjection_length_pos F.holes hYfinite Q hfirst hfirstOff hlast)

end OutsideFracturedWarp

#print axioms OutsideFracturedWarp.finite_support_inter_cut_subset_endpoints
#print axioms OutsideFracturedWarp.finiteSafeProjection_inter_cut_subset_endpoints
#print axioms OutsideFracturedWarp.infiniteSafeProjection_inter_cut_subset_initial
#print axioms FracturedCanonicalSafeProjection.finiteSafeProjection_length_pos
#print axioms OutsideFracturedWarp.finiteSafeProjection_not_vertexSet_subset_cut
#print axioms OutsideFracturedWarp.singleton_not_mem_cut

end Erdos599.Blueprint.LinkageBlueprint
