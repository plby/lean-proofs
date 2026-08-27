/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialRootTypicality
import ErdosProblems.Erdos207.FiniteSpanCounting
import ErdosProblems.Erdos207.ExclusiveAbsorbers

/-! # A linear-in-ambient-size bound for initially unavailable triangles -/

namespace Erdos207

open Finset
open scoped Classical

noncomputable section

theorem singleton_absorber_forbidden_vertices_subset_bank
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} {bank : TripleSystemOn V} {T : TripleOn V}
    (hT : ({T} : TripleSystemOn V) ∈ absorberErdosForbiddenConfigurationsOn q bank) :
    T.1 ⊆ verticesOn bank := by
  obtain ⟨_, r, hr4, _, E, hE, hpack, hEout⟩ := mem_absorberErdosForbiddenConfigurationsOn_iff.mp hT
  have hr5 : 5 ≤ r := by
    by_contra h
    have hr : r = 4 := by omega
    subst r
    exact hpack.no_four_config ⟨E, Subset.rfl, hE.1⟩
  have hTE : T ∈ E := (mem_sdiff.mp (show T ∈ E \ bank by rw [hEout]; simp)).1
  intro v hv
  have hve : v ∈ verticesOn E := mem_biUnion.mpr ⟨T, hTE, hv⟩
  have hthrough := IsErdosConfig.two_le_card_triplesThrough hE hr5 hve
  obtain ⟨U, hU, hUT⟩ := Finset.exists_mem_ne (s := triplesThrough E v) (by omega) T
  have hUE := (mem_filter.mp hU).1
  have hUB : U ∈ bank := by
    by_contra hnot
    have hUout : U ∈ E \ bank := mem_sdiff.mpr ⟨hUE, hnot⟩
    rw [hEout, mem_singleton] at hUout
    exact hUT hUout
  exact mem_biUnion.mpr ⟨U, hUB, (mem_filter.mp hU).2⟩

theorem isLegalExtension_empty_of_not_bank_supported
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (bank : TripleSystemOn V) (T : TripleOn V)
    (hnot : ¬ T.1 ⊆ verticesOn bank) :
    IsLegalExtension (absorberErdosForbiddenConfigurationsOn q bank) ∅ T := by
  refine ⟨by simp, by simpa using isPackingOn_singleton T, ?_⟩
  intro D hD hDT
  have hsub : D ⊆ ({T} : TripleSystemOn V) := by simpa using hDT
  obtain ⟨U, hU⟩ := (mem_absorberErdosForbiddenConfigurationsOn_iff.mp hD).1
  have hUT : U = T := mem_singleton.mp (hsub hU)
  have hTD : T ∈ D := hUT ▸ hU
  have heq : D = {T} := Subset.antisymm hsub (singleton_subset_iff.mpr hTD)
  rw [heq] at hD
  exact hnot (singleton_absorber_forbidden_vertices_subset_bank hD)

theorem card_graph_blocked_triangles_le
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] :
    ((univ : TripleSystemOn V).filter (fun T ↦ ¬ TriangleAvoidsGraph H T)).card ≤
      (graphSupportFinset H).card ^ 2 * Fintype.card V := by
  classical
  let W := graphSupportFinset H
  let rootFamily := fun u v : V ↦ if u = v then ∅ else universeTriplesThroughPair u v
  have hsub : (univ : TripleSystemOn V).filter (fun T ↦ ¬ TriangleAvoidsGraph H T) ⊆
      W.biUnion (fun u ↦ W.biUnion (fun v ↦ rootFamily u v)) := by
    intro T hT
    have hnot := (mem_filter.mp hT).2
    unfold TriangleAvoidsGraph at hnot
    push Not at hnot
    obtain ⟨u, hu, v, hv, huv, hH⟩ := hnot
    apply mem_biUnion.mpr
    refine ⟨u, mem_graphSupportFinset_iff.mpr ⟨v, hH⟩, mem_biUnion.mpr
      ⟨v, mem_graphSupportFinset_iff.mpr ⟨u, hH.symm⟩, ?_⟩⟩
    dsimp only [rootFamily]
    rw [if_neg huv]
    exact mem_universeTriplesThroughPair_iff.mpr ⟨hu, hv⟩
  have hroot (u v : V) : (rootFamily u v).card ≤ Fintype.card V := by
    dsimp only [rootFamily]
    split_ifs with h
    · simp
    · exact card_universeTriplesThroughPair_le V h
  calc
    _ ≤ (W.biUnion (fun u ↦ W.biUnion (fun v ↦ rootFamily u v))).card := card_le_card hsub
    _ ≤ ∑ u ∈ W, ∑ v ∈ W, (rootFamily u v).card :=
      card_biUnion_le.trans (sum_le_sum fun _ _ ↦ card_biUnion_le)
    _ ≤ ∑ _u ∈ W, ∑ _v ∈ W, Fintype.card V :=
      sum_le_sum fun u _ ↦ sum_le_sum fun v _ ↦ hroot u v
    _ = _ := by simp [W, pow_two, Nat.mul_assoc]

theorem card_initial_unavailable_triangles_le
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (H : SimpleGraph V) [DecidableRel H.Adj]
    (bank : TripleSystemOn V) :
    ((univ : TripleSystemOn V) \ (absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q bank)
      (outsideAvailableTriangles H bank)).available).card ≤
        (graphSupportFinset H).card ^ 2 * Fintype.card V + (verticesOn bank).card ^ 3 := by
  classical
  have hsub : (univ : TripleSystemOn V) \ (absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q bank) (outsideAvailableTriangles H bank)).available ⊆
      ((univ : TripleSystemOn V).filter (fun T ↦ ¬ TriangleAvoidsGraph H T)) ∪ triplesSupportedOn (verticesOn bank) := by
    intro T hT
    by_cases havoid : TriangleAvoidsGraph H T
    · apply mem_union_right
      apply mem_triplesSupportedOn_iff.mpr
      by_contra hnot
      have hTnotB : T ∉ bank := fun hTB ↦ hnot (fun v hv ↦ mem_biUnion.mpr ⟨T, hTB, hv⟩)
      have hmem : T ∈ (absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q bank)
          (outsideAvailableTriangles H bank)).available := by
        apply mem_legalAvailable_iff.mpr
        exact ⟨mem_outsideAvailableTriangles_iff.mpr ⟨hTnotB, havoid⟩,
          isLegalExtension_empty_of_not_bank_supported q bank T hnot⟩
      exact (mem_sdiff.mp hT).2 hmem
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, havoid⟩)
  exact ((card_le_card hsub).trans (card_union_le _ _)).trans
    (Nat.add_le_add (card_graph_blocked_triangles_le H) (card_triplesSupportedOn_le_cube (verticesOn bank)))

end

end Erdos207
