/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.Core

/-! # The vertex-touching form of minimality -/

namespace Erdos207

open Finset

/-- Triangles of `C` meeting a prescribed vertex set. -/
def trianglesTouching
    {V : Type*} [DecidableEq V]
    (C : TripleSystemOn V) (W : Finset V) : TripleSystemOn V :=
  C.filter fun T ↦ ∃ v ∈ W, v ∈ T.1

@[simp]
lemma mem_trianglesTouching_iff
    {V : Type*} [DecidableEq V]
    {C : TripleSystemOn V} {W : Finset V} {T : TripleOn V} :
    T ∈ trianglesTouching C W ↔
      T ∈ C ∧ ∃ v ∈ W, v ∈ T.1 := by
  simp [trianglesTouching]

lemma verticesOn_sdiff_trianglesTouching_subset
    {V : Type*} [DecidableEq V]
    (C : TripleSystemOn V) (W : Finset V) :
    verticesOn (C \ trianglesTouching C W) ⊆ verticesOn C \ W := by
  intro v hv
  obtain ⟨T, hTD, hvT⟩ := mem_biUnion.mp hv
  have hTC : T ∈ C := (mem_sdiff.mp hTD).1
  apply mem_sdiff.mpr
  refine ⟨mem_biUnion.mpr ⟨T, hTC, hvT⟩, ?_⟩
  intro hvW
  exact (mem_sdiff.mp hTD).2
    (mem_trianglesTouching_iff.mpr ⟨hTC, v, hvW, hvT⟩)

lemma card_sdiff_trianglesTouching
    {V : Type*} [DecidableEq V]
    (C : TripleSystemOn V) (W : Finset V) :
    (C \ trianglesTouching C W).card =
      C.card - (trianglesTouching C W).card := by
  rw [card_sdiff_of_subset]
  exact filter_subset _ _

/-- Lemma 3.2(2), dual form: at most `r-2` vertices of an Erdős
configuration touch at least that many triangles. -/
theorem IsErdosConfig.card_le_trianglesTouching
    {V : Type*} [DecidableEq V] {r : ℕ}
    {C : TripleSystemOn V} (hC : IsErdosConfigOn r C) (hr : 5 ≤ r)
    (W : Finset V) (hWC : W ⊆ verticesOn C) (hWcard : W.card ≤ r - 2) :
    W.card ≤ (trianglesTouching C W).card := by
  by_contra hnot
  have htouch : (trianglesTouching C W).card < W.card := by omega
  let D := C \ trianglesTouching C W
  have hDC : D ⊆ C := sdiff_subset
  have hDcard : D.card = r - 2 - (trianglesTouching C W).card := by
    dsimp only [D]
    rw [card_sdiff_trianglesTouching, hC.1.1]
  have hDpos : 1 ≤ D.card := by omega
  have hDsmall : D.card ≤ r - 2 := by omega
  have hspan := IsErdosConfig.subset_span_weak
    hC hr hDC hDpos hDsmall
  have hverticesSub : verticesOn D ⊆ verticesOn C \ W := by
    exact verticesOn_sdiff_trianglesTouching_subset C W
  have hspanUpper : (verticesOn D).card ≤ r - W.card := by
    calc
      (verticesOn D).card ≤ (verticesOn C \ W).card :=
        card_le_card hverticesSub
      _ = (verticesOn C).card - W.card := card_sdiff_of_subset hWC
      _ = r - W.card := by rw [IsErdosConfig.vertices_card_eq hC hr]
  omega

/-- Lemma 3.2(1), dual form: a nonempty set of at most `r-4` vertices
touches at least one more triangle than its size. -/
theorem IsErdosConfig.card_add_one_le_trianglesTouching
    {V : Type*} [DecidableEq V] {r : ℕ}
    {C : TripleSystemOn V} (hC : IsErdosConfigOn r C) (hr : 5 ≤ r)
    (W : Finset V) (hWC : W ⊆ verticesOn C)
    (hWpos : 1 ≤ W.card) (hWcard : W.card ≤ r - 4) :
    W.card + 1 ≤ (trianglesTouching C W).card := by
  by_contra hnot
  have htouchUpper : (trianglesTouching C W).card ≤ W.card := by omega
  have htouchPos : 1 ≤ (trianglesTouching C W).card := by
    obtain ⟨v, hvW⟩ := card_pos.mp (by omega : 0 < W.card)
    have hvC := hWC hvW
    obtain ⟨T, hTC, hvT⟩ := mem_biUnion.mp hvC
    exact card_pos.mpr ⟨T,
      mem_trianglesTouching_iff.mpr ⟨hTC, v, hvW, hvT⟩⟩
  let D := C \ trianglesTouching C W
  have hDC : D ⊆ C := sdiff_subset
  have hDcard : D.card = r - 2 - (trianglesTouching C W).card := by
    dsimp only [D]
    rw [card_sdiff_trianglesTouching, hC.1.1]
  have hDtwo : 2 ≤ D.card := by omega
  have hDsmall : D.card ≤ r - 3 := by omega
  have hspan := IsErdosConfig.subset_span hC hDC hDtwo hDsmall
  have hverticesSub : verticesOn D ⊆ verticesOn C \ W := by
    exact verticesOn_sdiff_trianglesTouching_subset C W
  have hspanUpper : (verticesOn D).card ≤ r - W.card := by
    calc
      (verticesOn D).card ≤ (verticesOn C \ W).card :=
        card_le_card hverticesSub
      _ = (verticesOn C).card - W.card := card_sdiff_of_subset hWC
      _ = r - W.card := by rw [IsErdosConfig.vertices_card_eq hC hr]
  omega

end Erdos207
