/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LinkInnerEdgeSampling
import ErdosProblems.Erdos207.RawSampledLinkJointLaw

/-! # The full available link family used by future-degree tests -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def availableLinkFamily
    {O V : Type*} [DecidableEq V] (K : O → BipartiteLink V) (A : TripleSystemOn V) : TripleSystemOn V :=
  A.filter fun T ↦ ∃ x : SimultaneousLinkPair O V K, T = simultaneousLinkPairTriple K x

theorem mem_availableLinkFamily_iff
    {O V : Type*} [DecidableEq V] {K : O → BipartiteLink V} {A : TripleSystemOn V}
    {T : TripleOn V} :
    T ∈ availableLinkFamily K A ↔ T ∈ A ∧
      ∃ x : SimultaneousLinkPair O V K, T = simultaneousLinkPairTriple K x := by
  simp only [availableLinkFamily, mem_filter]

theorem availableLinkFamily_isFamily
    {O V : Type*} [DecidableEq V] (K : O → BipartiteLink V) (A : TripleSystemOn V) :
    IsSimultaneousLinkFamily K (availableLinkFamily K A) :=
  fun _ hT ↦ (mem_availableLinkFamily_iff.mp hT).2

theorem IsSampledLinkJointOutcome.selected_subset_availableLinkFamily
    {O V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V} {K : O → BipartiteLink V}
    {z : TripleSystemOn V × TripleSystemOn V} (h : IsSampledLinkJointOutcome F A P K z) :
    z.2 ⊆ availableLinkFamily K A := fun T hT ↦
  mem_availableLinkFamily_iff.mpr ⟨h.selected_safe.1 hT, h.selected_family T hT⟩

theorem availableLinkFamily_innerFan_le_overlap_add_one
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V) (A : TripleSystemOn V) (U : Finset V)
    (hout : ∀ o, (K o).center ∉ U) (M : ℕ)
    (hoverlap : ∀ x : SimultaneousLinkPair O V K,
      (otherLinkCoordinates K (fun o ↦ linkAvailableRelation (K o) A) x).card ≤ M)
    (e : Sym2 V) (he : e.toFinset ⊆ U) :
    (linkInnerEdgeFan (availableLinkFamily K A) e).card ≤ M + 1 := by
  apply card_linkInnerEdgeFan_le_other_overlap K U hout
    (fun o ↦ linkAvailableRelation (K o) A) (availableLinkFamily K A) _ e he M hoverlap
  intro T hT
  obtain ⟨hTA, x, hx⟩ := mem_availableLinkFamily_iff.mp hT
  refine ⟨x, ?_, hx⟩
  change simultaneousLinkPairTriple K x ∈ A
  exact hx ▸ hTA

end

end Erdos207
