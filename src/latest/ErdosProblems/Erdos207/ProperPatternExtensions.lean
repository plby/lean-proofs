/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PatternSurvival
import ErdosProblems.Erdos207.SeparatedLocalizedRootedThreat

/-! # Proper extensions and their uniquely determined triangles -/

namespace Erdos207

open Finset

noncomputable section

def properPatternExtensions
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (Q : SimpleGraph V) (U : Finset V) : Finset V :=
  iterationExtensionVertices A Q U \ graphSupportFinset Q

theorem mem_properPatternExtensions_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : TripleSystemOn V} {Q : SimpleGraph V} {U : Finset V} {u : V} :
    u ∈ properPatternExtensions A Q U ↔
      u ∈ iterationExtensionVertices A Q U ∧ u ∉ graphSupportFinset Q := by
  exact mem_sdiff

theorem properPatternExtensions_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (Q : SimpleGraph V) (U : Finset V) :
    properPatternExtensions A Q U ⊆ U := by
  exact sdiff_subset.trans (iterationExtensionVertices_subset A Q U)

theorem properPatternExtensions_mono_available
    {V : Type*} [Fintype V] [DecidableEq V]
    {A A' : TripleSystemOn V} (hA : A ⊆ A') (Q : SimpleGraph V) (U : Finset V) :
    properPatternExtensions A Q U ⊆ properPatternExtensions A' Q U := by
  intro u hu
  exact mem_sdiff.mpr
    ⟨iterationExtensionVertices_mono_available hA Q U (mem_sdiff.mp hu).1,
      (mem_sdiff.mp hu).2⟩

theorem properPatternExtensions_card_comparison
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (Q : SimpleGraph V) (U : Finset V) :
    (properPatternExtensions A Q U).card ≤ (iterationExtensionVertices A Q U).card ∧
      (iterationExtensionVertices A Q U).card ≤
        (properPatternExtensions A Q U).card + (graphSupportFinset Q).card := by
  exact ⟨card_le_card sdiff_subset, card_le_card_sdiff_add_card⟩

/-- A base edge together with a vertex outside the base support. -/
def patternExtensionTriangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) (e : graphEdges Q) (u : V) (hu : u ∉ graphSupportFinset Q) :
    TripleOn V :=
  thirdVertexTriple (out_fst_ne_snd_of_mem_graphEdges e.2)
    ⟨u, fun h ↦ hu (h ▸ (endpoint_mem_graphSupportFinset e.2).1),
      fun h ↦ hu (h ▸ (endpoint_mem_graphSupportFinset e.2).2)⟩

theorem patternExtensionTriangle_vertex_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) (e : graphEdges Q) (u : V) (hu : u ∉ graphSupportFinset Q) :
    u ∈ (patternExtensionTriangle Q e u hu).1 := by
  simp [patternExtensionTriangle, thirdVertexTriple, tripleOfThree]

theorem patternExtensionTriangle_base_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) (e : graphEdges Q) (u : V) (hu : u ∉ graphSupportFinset Q) :
    e.1 ∈ tripleEdgeFinset (patternExtensionTriangle Q e u hu) := by
  nth_rw 1 [← e.1.out_eq]
  rw [mk_mem_tripleEdgeFinset_iff]
  exact ⟨left_mem_thirdVertexTriple _ _, right_mem_thirdVertexTriple _ _,
    out_fst_ne_snd_of_mem_graphEdges e.2⟩

theorem patternExtensionTriangle_eq_of_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) (e : graphEdges Q) (u : V) (hu : u ∉ graphSupportFinset Q)
    (T : TripleOn V) (huT : u ∈ T.1) (heT : e.1 ∈ tripleEdgeFinset T) :
    patternExtensionTriangle Q e u hu = T := by
  have heT' := heT
  rw [← e.1.out_eq, mk_mem_tripleEdgeFinset_iff] at heT'
  exact thirdVertexTriple_eq_of_mem _ T heT'.1 heT'.2.1 huT
    (fun h ↦ hu (h ▸ (endpoint_mem_graphSupportFinset e.2).1))
    (fun h ↦ hu (h ▸ (endpoint_mem_graphSupportFinset e.2).2))

theorem mem_properPatternExtensions_iff_triangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (Q : SimpleGraph V) (U : Finset V)
    (u : V) (hu : u ∉ graphSupportFinset Q) :
    u ∈ properPatternExtensions A Q U ↔
      u ∈ U ∧ ∀ e : graphEdges Q, patternExtensionTriangle Q e u hu ∈ A := by
  rw [mem_properPatternExtensions_iff, mem_iterationExtensionVertices_iff]
  constructor
  · rintro ⟨⟨huU, hext⟩, _⟩
    refine ⟨huU, fun e ↦ ?_⟩
    obtain ⟨T, hT, huT, heT⟩ := hext e.1 e.2
    rwa [patternExtensionTriangle_eq_of_mem Q e u hu T huT heT]
  · rintro ⟨huU, hext⟩
    refine ⟨⟨huU, fun e he ↦ ?_⟩, hu⟩
    exact ⟨patternExtensionTriangle Q ⟨e, he⟩ u hu, hext ⟨e, he⟩,
      patternExtensionTriangle_vertex_mem Q ⟨e, he⟩ u hu,
      patternExtensionTriangle_base_mem Q ⟨e, he⟩ u hu⟩

end

end Erdos207
