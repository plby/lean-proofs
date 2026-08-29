/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CardinalInduction
import ErdosProblems.Erdos599.SingularCardinal

/-!
# Erdős Problem 599: closed-set linkage assembly

This file isolates the last, purely combinatorial, assembly in the regular
and singular extension arguments.  A linkage `P` is constructed inside a
closed set `Z`, while `F` is the old linkage of the complementary sources.
Closure under competitors in the *combined* family `P ∪ F` guarantees that
an `F`-path whose initial vertex lies outside `Z` cannot meet a `P`-path.
Keeping precisely those outside paths and adjoining them to `P` therefore
gives a linkage of the whole source.

It is important that the closure is taken in `P ∪ F`, not merely in `F`.
The latter does not notice a point of `Z` which is not the initial vertex of
an `F`-path and is consequently insufficient for this assembly.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularClosureAssembly

universe u

open DirectedPath

variable {V : Type u}

/-- The paths of the old complementary linkage whose initial vertices stay
outside the closed set. -/
def outsidePaths (Γ : DWeb V) (F : Set Γ.DPath) (Z : Set V) : Set Γ.DPath :=
  {p | p ∈ F ∧ p.initial ∉ Z}

@[simp]
theorem mem_outsidePaths {Γ : DWeb V} {F : Set Γ.DPath} {Z : Set V}
    {p : Γ.DPath} :
    p ∈ outsidePaths Γ F Z ↔ p ∈ F ∧ p.initial ∉ Z :=
  Iff.rfl

/-- Competitor closure of the source vertices of `P` makes every retained
old path disjoint from the complete vertex set of `P`.

This is the exact point at which the singular-cardinal competitor closure
feeds the final linkage assembly. -/
theorem outsidePaths_disjoint_vertexSet_of_carrier
    (Γ : DWeb V) (Z : Set V) (P F W : Set Γ.DPath)
    (hP : IsLinkageBetween Γ (Γ.source ∩ Z) Γ.target P)
    (hFsub : F ⊆ W)
    (hcarrier : ∀ p ∈ P, ∃ q ∈ W,
      q.initial = p.initial ∧ p.support ⊆ q.support)
    (hclosed :
      Γ.competitorClosure W (Γ.source ∩ Z) ⊆ Z) :
    ∀ p ∈ outsidePaths Γ F Z, Disjoint p.support (Γ.vertexSet P) := by
  intro p hp
  rw [Set.disjoint_left]
  intro x hxp hxP
  obtain ⟨q, hqP, hxq⟩ := hxP
  have hqinitial : q.initial ∈ Γ.source ∩ Z := by
    have hqinitial' : q.initial ∈ Γ.initialSet P := ⟨q, hqP, rfl⟩
    simpa only [hP.initialSet_eq] using hqinitial'
  obtain ⟨q', hq'W, hq'initial, hqq'⟩ := hcarrier q hqP
  apply hp.2
  apply hclosed
  refine ⟨q.initial, hqinitial, q', hq'W, hq'initial,
    p, hFsub hp.1, rfl, ?_⟩
  exact Set.not_disjoint_iff.2 ⟨x, hqq' hxq, hxp⟩

/-- Specialization where the competitor family is literally `P ∪ F`. -/
theorem outsidePaths_disjoint_vertexSet
    (Γ : DWeb V) (Z : Set V) (P F : Set Γ.DPath)
    (hP : IsLinkageBetween Γ (Γ.source ∩ Z) Γ.target P)
    (hclosed :
      Γ.competitorClosure (P ∪ F) (Γ.source ∩ Z) ⊆ Z) :
    ∀ p ∈ outsidePaths Γ F Z, Disjoint p.support (Γ.vertexSet P) := by
  apply outsidePaths_disjoint_vertexSet_of_carrier Γ Z P F (P ∪ F) hP
    (fun _ hp => Or.inr hp)
  · intro p hp
    exact ⟨p, Or.inl hp, rfl, Set.Subset.rfl⟩
  · exact hclosed

/-- The designated source set is contained in the vertex set of the new
linkage. -/
theorem designatedSource_subset_vertexSet
    (Γ : DWeb V) (A₀ Z : Set V) (P : Set Γ.DPath)
    (hA₀ : A₀ ⊆ Z)
    (hP : IsLinkageBetween Γ (Γ.source ∩ Z) Γ.target P) :
    A₀ ∩ Γ.source ⊆ Γ.vertexSet P := by
  intro a ha
  have hainitial : a ∈ Γ.initialSet P := by
    rw [hP.initialSet_eq]
    exact ⟨ha.2, hA₀ ha.1⟩
  obtain ⟨p, hpP, hpa⟩ := hainitial
  exact ⟨p, hpP, hpa ▸ p.initial_mem_support⟩

/-- Closed-set assembly at the level of the canonical linkage predicate.

The closure hypothesis is stated only for the smaller seed
`source ∩ Z`; closure starting from all of `Z` is supplied as a corollary
below. -/
theorem linkageBetween_union_outside_of_disjoint
    (Γ : DWeb V) (A₀ Z : Set V) (P F : Set Γ.DPath)
    (hA₀ : A₀ ⊆ Z)
    (hP : IsLinkageBetween Γ (Γ.source ∩ Z) Γ.target P)
    (hPZ : Γ.vertexSet P ⊆ Z)
    (hF : IsLinkageBetween Γ (Γ.source \ A₀) Γ.target F)
    (houtside : ∀ p ∈ outsidePaths Γ F Z,
      Disjoint p.support (Γ.vertexSet P)) :
    IsLinkageBetween Γ Γ.source Γ.target
      (P ∪ outsidePaths Γ F Z) := by
  have hA₀sourceP : A₀ ∩ Γ.source ⊆ Γ.vertexSet P :=
    designatedSource_subset_vertexSet Γ A₀ Z P hA₀ hP
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    rcases hp with hpP | hpO
    · rcases hq with hqP | hqO
      · exact hP.isWarp hpP hqP hpq
      · change Disjoint p.support q.support
        rw [Set.disjoint_left]
        intro x hxp hxq
        exact Set.disjoint_left.1 (houtside q hqO) hxq ⟨p, hpP, hxp⟩
    · rcases hq with hqP | hqO
      · change Disjoint p.support q.support
        rw [Set.disjoint_left]
        intro x hxp hxq
        exact Set.disjoint_left.1 (houtside p hpO) hxp ⟨q, hqP, hxq⟩
      · exact hF.isWarp hpO.1 hqO.1 hpq
  · intro p hp
    rcases hp with hpP | hpO
    · exact hP.finiteCharacter hpP
    · exact hF.finiteCharacter hpO.1
  · ext x
    constructor
    · rintro ⟨p, hpP | hpO, rfl⟩
      · have hx : p.initial ∈ Γ.initialSet P := ⟨p, hpP, rfl⟩
        rw [hP.initialSet_eq] at hx
        exact hx.1
      · have hx : p.initial ∈ Γ.initialSet F := ⟨p, hpO.1, rfl⟩
        rw [hF.initialSet_eq] at hx
        exact hx.1
    · intro hxsource
      by_cases hxZ : x ∈ Z
      · have hxP : x ∈ Γ.initialSet P := by
          rw [hP.initialSet_eq]
          exact ⟨hxsource, hxZ⟩
        obtain ⟨p, hpP, hpinit⟩ := hxP
        exact ⟨p, Or.inl hpP, hpinit⟩
      · have hxA₀ : x ∉ A₀ := fun hxA₀ => hxZ (hA₀ hxA₀)
        have hxF : x ∈ Γ.initialSet F := by
          rw [hF.initialSet_eq]
          exact ⟨hxsource, hxA₀⟩
        obtain ⟨p, hpF, hpinit⟩ := hxF
        refine ⟨p, Or.inr ⟨hpF, ?_⟩, hpinit⟩
        simpa only [hpinit] using hxZ
  · intro x hx
    obtain ⟨p, hpP | hpO, hpterm⟩ := hx
    · exact hP.terminalFrontier_subset ⟨p, hpP, hpterm⟩
    · exact hF.terminalFrontier_subset ⟨p, hpO.1, hpterm⟩
  · intro p hp
    rcases hp with hpP | hpO
    · rcases hP.endpointPure p hpP with ⟨q, rfl, hends, hsource⟩
      have hqZ : q.support ⊆ Z := by
        intro x hx
        exact hPZ ⟨Sum.inl q, hpP, hx⟩
      refine ⟨q, rfl, ?_, ?_⟩
      · rw [← hends]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_union]
        constructor
        · rintro ⟨hxs, hxsour | hxtarget⟩
          · exact ⟨hxs, Or.inl ⟨hxsour, hqZ hxs⟩⟩
          · exact ⟨hxs, Or.inr hxtarget⟩
        · rintro ⟨hxs, ⟨hxsour, -⟩ | hxtarget⟩
          · exact ⟨hxs, Or.inl hxsour⟩
          · exact ⟨hxs, Or.inr hxtarget⟩
      · rw [← hsource]
        ext x
        simp only [Set.mem_inter_iff]
        constructor
        · rintro ⟨hxs, hxsour⟩
          exact ⟨hxs, hxsour, hqZ hxs⟩
        · rintro ⟨hxs, hxsour, -⟩
          exact ⟨hxs, hxsour⟩
    · rcases hF.endpointPure p hpO.1 with ⟨q, hpq, hends, hsource⟩
      have hpDisjointA₀source : Disjoint p.support (A₀ ∩ Γ.source) :=
        (houtside p hpO).mono_right hA₀sourceP
      subst p
      refine ⟨q, rfl, ?_, ?_⟩
      · rw [← hends]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff]
        constructor
        · rintro ⟨hxs, hxsour | hxtarget⟩
          · exact ⟨hxs, Or.inl ⟨hxsour,
              fun hxA₀ => Set.disjoint_left.1 hpDisjointA₀source hxs
                ⟨hxA₀, hxsour⟩⟩⟩
          · exact ⟨hxs, Or.inr hxtarget⟩
        · rintro ⟨hxs, ⟨hxsour, -⟩ | hxtarget⟩
          · exact ⟨hxs, Or.inl hxsour⟩
          · exact ⟨hxs, Or.inr hxtarget⟩
      · rw [← hsource]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_sdiff]
        constructor
        · rintro ⟨hxs, hxsour⟩
          exact ⟨hxs, hxsour,
            fun hxA₀ => Set.disjoint_left.1 hpDisjointA₀source hxs
              ⟨hxA₀, hxsour⟩⟩
        · rintro ⟨hxs, hxsour, -⟩
          exact ⟨hxs, hxsour⟩

/-- General carrier form of the closed-set assembly.  A path of `P` need
not itself belong to the competitor family `W`; it is enough that it be a
prefix (more generally, have support contained in a path) of `W` with the
same initial vertex. -/
theorem linkageBetween_union_outside_of_carrierCompetitorClosedSources
    (Γ : DWeb V) (A₀ Z : Set V) (P F W : Set Γ.DPath)
    (hA₀ : A₀ ⊆ Z)
    (hP : IsLinkageBetween Γ (Γ.source ∩ Z) Γ.target P)
    (hPZ : Γ.vertexSet P ⊆ Z)
    (hF : IsLinkageBetween Γ (Γ.source \ A₀) Γ.target F)
    (hFsub : F ⊆ W)
    (hcarrier : ∀ p ∈ P, ∃ q ∈ W,
      q.initial = p.initial ∧ p.support ⊆ q.support)
    (hclosed : Γ.competitorClosure W (Γ.source ∩ Z) ⊆ Z) :
    IsLinkageBetween Γ Γ.source Γ.target
      (P ∪ outsidePaths Γ F Z) := by
  apply linkageBetween_union_outside_of_disjoint Γ A₀ Z P F
    hA₀ hP hPZ hF
  exact outsidePaths_disjoint_vertexSet_of_carrier Γ Z P F W hP
    hFsub hcarrier hclosed

/-- Specialization of the carrier theorem to the literal family `P ∪ F`. -/
theorem linkageBetween_union_outside_of_competitorClosedSources
    (Γ : DWeb V) (A₀ Z : Set V) (P F : Set Γ.DPath)
    (hA₀ : A₀ ⊆ Z)
    (hP : IsLinkageBetween Γ (Γ.source ∩ Z) Γ.target P)
    (hPZ : Γ.vertexSet P ⊆ Z)
    (hF : IsLinkageBetween Γ (Γ.source \ A₀) Γ.target F)
    (hclosed :
      Γ.competitorClosure (P ∪ F) (Γ.source ∩ Z) ⊆ Z) :
    IsLinkageBetween Γ Γ.source Γ.target
      (P ∪ outsidePaths Γ F Z) := by
  apply linkageBetween_union_outside_of_carrierCompetitorClosedSources
    Γ A₀ Z P F (P ∪ F) hA₀ hP hPZ hF (fun _ hp => Or.inr hp)
  · intro p hp
    exact ⟨p, Or.inl hp, rfl, Set.Subset.rfl⟩
  · exact hclosed

/-- Direct linkability from a source-seeded competitor-closed ambient
family.  This is the most general assembly theorem in this file. -/
theorem isLinkable_of_carrierCompetitorClosedSources
    (Γ : DWeb V) (A₀ Z : Set V) (P F W : Set Γ.DPath)
    (hA₀ : A₀ ⊆ Z)
    (hP : IsLinkageBetween Γ (Γ.source ∩ Z) Γ.target P)
    (hPZ : Γ.vertexSet P ⊆ Z)
    (hF : IsLinkageBetween Γ (Γ.source \ A₀) Γ.target F)
    (hFsub : F ⊆ W)
    (hcarrier : ∀ p ∈ P, ∃ q ∈ W,
      q.initial = p.initial ∧ p.support ⊆ q.support)
    (hclosed : Γ.competitorClosure W (Γ.source ∩ Z) ⊆ Z) :
    IsLinkable Γ := by
  refine ⟨P ∪ outsidePaths Γ F Z, ?_⟩
  exact linkageBetween_union_outside_of_carrierCompetitorClosedSources
    Γ A₀ Z P F W hA₀ hP hPZ hF hFsub hcarrier hclosed

/-- All-of-`Z` closure form of the general carrier assembly. -/
theorem isLinkable_of_carrierCompetitorClosed
    (Γ : DWeb V) (A₀ Z : Set V) (P F W : Set Γ.DPath)
    (hA₀ : A₀ ⊆ Z)
    (hP : IsLinkageBetween Γ (Γ.source ∩ Z) Γ.target P)
    (hPZ : Γ.vertexSet P ⊆ Z)
    (hF : IsLinkageBetween Γ (Γ.source \ A₀) Γ.target F)
    (hFsub : F ⊆ W)
    (hcarrier : ∀ p ∈ P, ∃ q ∈ W,
      q.initial = p.initial ∧ p.support ⊆ q.support)
    (hclosed : Γ.competitorClosure W Z ⊆ Z) :
    IsLinkable Γ := by
  apply isLinkable_of_carrierCompetitorClosedSources Γ A₀ Z P F W
    hA₀ hP hPZ hF hFsub hcarrier
  exact (Γ.competitorClosure_mono_sources Set.inter_subset_right).trans hclosed

/-- Literal `P ∪ F` specialization in which competitor closure need only be
checked from the initial set of the newly constructed linkage. -/
theorem isLinkable_of_competitorClosedSources
    (Γ : DWeb V) (A₀ Z : Set V) (P F : Set Γ.DPath)
    (hA₀ : A₀ ⊆ Z)
    (hP : IsLinkageBetween Γ (Γ.source ∩ Z) Γ.target P)
    (hPZ : Γ.vertexSet P ⊆ Z)
    (hF : IsLinkageBetween Γ (Γ.source \ A₀) Γ.target F)
    (hclosed :
      Γ.competitorClosure (P ∪ F) (Γ.source ∩ Z) ⊆ Z) :
    IsLinkable Γ := by
  refine ⟨P ∪ outsidePaths Γ F Z, ?_⟩
  exact linkageBetween_union_outside_of_competitorClosedSources Γ A₀ Z P F
    hA₀ hP hPZ hF hclosed

/-- User-facing closed-set form.  Closure under competitors starting from
all of `Z` implies the smaller source-seeded closure needed by the assembly.
-/
theorem isLinkable_of_competitorClosed
    (Γ : DWeb V) (A₀ Z : Set V) (P F : Set Γ.DPath)
    (hA₀ : A₀ ⊆ Z)
    (hP : IsLinkageBetween Γ (Γ.source ∩ Z) Γ.target P)
    (hPZ : Γ.vertexSet P ⊆ Z)
    (hF : IsLinkageBetween Γ (Γ.source \ A₀) Γ.target F)
    (hclosed : Γ.competitorClosure (P ∪ F) Z ⊆ Z) :
    IsLinkable Γ := by
  apply isLinkable_of_competitorClosedSources Γ A₀ Z P F
    hA₀ hP hPZ hF
  exact (Γ.competitorClosure_mono_sources Set.inter_subset_right).trans hclosed

end RegularClosureAssembly
end CardinalInduction
end Erdos599
