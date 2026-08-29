/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointBlueprint
import ErdosProblems.Erdos599.SliceSpliceSource

/-!
# The initial endpoint-pruned blueprint

The trivial family on the designated source set is a blueprint at the zero
ladder stage. The original limiting reference covers every remaining source:
normalization prevents its owner from meeting a different source vertex.
Unhinderedness is used for the actual zero-frontier identity. No membership
of zero in the supplied avoiding club is claimed.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeEndpointBlueprint

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint
open _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable (C : ClubStageGeometry Gamma Y kappa (succ kappa))

abbrev initialStage : Stage (succ kappa) := ⟨0, C.legal.regular.ord_pos⟩

def initialFamily (A0 : Set V) : Set (web C).DPath := (web C).trivialPath '' A0

@[simp] theorem vertexSet_initialFamily (A0 : Set V) :
    (web C).vertexSet (initialFamily C A0) = A0 :=
  (web C).vertexSet_trivialPaths A0

@[simp] theorem initialSet_initialFamily (A0 : Set V) :
    (web C).initialSet (initialFamily C A0) = A0 :=
  (web C).initialSet_trivialPaths A0

@[simp] theorem terminalFrontier_initialFamily (A0 : Set V) :
    (web C).terminalFrontier (initialFamily C A0) = A0 :=
  (web C).terminalFrontier_trivialPaths A0

theorem isWarp_initialFamily (A0 : Set V) : (web C).IsWarp (initialFamily C A0) :=
  (web C).isWarp_trivialPaths A0

theorem hasFiniteCharacter_initialFamily (A0 : Set V) :
    (web C).HasFiniteCharacter (initialFamily C A0) := by
  rintro p ⟨x, _hx, rfl⟩
  exact ⟨FinitePath.trivial (web C).graph x, rfl⟩

@[simp] theorem familyEdges_initialFamily (A0 : Set V) :
    familyEdges (initialFamily C A0) = ∅ := by
  apply Set.Subset.antisymm ?_ (Set.empty_subset _)
  intro e he
  simp only [familyEdges, Set.mem_iUnion] at he
  obtain ⟨p, hp, hep⟩ := he
  obtain ⟨x, _hx, rfl⟩ := hp
  simp [DWeb.trivialPath, Path.trivial, FinitePath.edgeSet,
    FinitePath.trivial, Walk.edgeSet] at hep

theorem frontier_initialStage (hGamma : Gamma.IsUnhindered) :
    C.ladder.frontier (initialStage C) = Gamma.source :=
  CardinalInduction.SliceSpliceSource.frontier_zero_eq_source_of_initialStage
    C.normalized hGamma C.legal.regular C.legal.initialStage

/-- The zero-stage trivial wave gives actual limiting owners for all original
sources. It is not assumed that these are the only limiting initials. -/
theorem source_subset_initialSet_reference :
    Gamma.source ⊆ Gamma.initialSet C.ladder.limitWarp := by
  have hzero : C.ladder.warpAt (initialStage C) = Gamma.trivialWave :=
    C.legal.initialStage
  have h := ColouredSafeReferenceLocalization.initialSet_stage_subset_limit
    (a := initialStage C) C.legal
  rw [hzero, Gamma.initialSet_trivialWave] at h
  exact h

theorem initialFamily_covers_source {A0 : Set V} (hA0 : A0 ⊆ Gamma.source)
    (hGamma : Gamma.IsUnhindered) :
    Gamma.source ⊆ (web C).initialSet (initialFamily C A0) ∪ Gamma.initialSet
      (referencePathsMeeting C.ladder.limitWarp (C.ladder.frontier (initialStage C)) \
        referencePathsMeeting C.ladder.limitWarp ((web C).vertexSet (initialFamily C A0))) := by
  rw [initialSet_initialFamily, vertexSet_initialFamily, frontier_initialStage C hGamma]
  intro x hx
  by_cases hxA0 : x ∈ A0
  · exact Or.inl hxA0
  · obtain ⟨p, hp, hpx⟩ := source_subset_initialSet_reference C hx
    refine Or.inr ⟨p, ⟨⟨hp, x, ?_, hx⟩, ?_⟩, hpx⟩
    · exact hpx ▸ p.initial_mem_support
    · rintro ⟨_hp, z, hzp, hzA0⟩
      have hnorm : Gamma.IsNormalized := C.normalized
      have hzx : z = x := (hnorm.eq_initial_of_mem_path p hzp (hA0 hzA0)).trans hpx
      exact hxA0 (hzx ▸ hzA0)

/-- The actual initial state in the endpoint-pruned graph, with the full
reference source condition proved rather than postulated. -/
theorem initialFamily_isBlueprint {A0 : Set V} (hA0 : A0 ⊆ Gamma.source)
    (hcard : #A0 ≤ kappa) (hGamma : Gamma.IsUnhindered) :
    IsBlueprint C (initialStage C) (initialFamily C A0) := by
  apply of_roofed_fields (isWarp_initialFamily C A0)
  · rw [vertexSet_initialFamily, frontier_initialStage C hGamma]
    exact hA0.trans (Gamma.subset_roof Gamma.source)
  · exact initialFamily_covers_source C hA0 hGamma
  · simpa only [vertexSet_initialFamily] using hcard
  · intro r hr
    obtain ⟨p, hp⟩ := hasFiniteCharacter_initialFamily C A0 hr
    cases hp
  · rw [terminalFrontier_initialFamily, frontier_initialStage C hGamma]
    exact hA0.trans Set.subset_union_right

#print axioms familyEdges_initialFamily
#print axioms frontier_initialStage
#print axioms source_subset_initialSet_reference
#print axioms initialFamily_covers_source
#print axioms initialFamily_isBlueprint

end Erdos599.Blueprint.ColouredSafeEndpointBlueprint
