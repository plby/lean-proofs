/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteSpanCounting

/-! # Bounded-span counting with a fixed vertex root -/

namespace Erdos207

open Finset

noncomputable section

theorem card_boundedSpan_family_with_vertex_root
    {V : Type*} [Fintype V] [DecidableEq V]
    (family : Finset (TripleSystemOn V)) (W : Finset V) (j : ℕ)
    (hroot : ∀ C ∈ family, W ⊆ verticesOn C)
    (hspan : ∀ C ∈ family, (verticesOn C).card ≤ j) :
    family.card ≤ (2 ^ (j ^ 3) * (j + 1)) * (Fintype.card V + 1) ^ (j - W.card) := by
  classical
  let code := fun C : TripleSystemOn V ↦ verticesOn C \ W
  have hfiber : ∀ X ∈ family.image code,
      (family.filter fun C ↦ code C = X).card ≤ 2 ^ (j ^ 3) := by
    intro X hX
    obtain ⟨C, hC, hCX⟩ := mem_image.mp hX
    have hspanUnion : (W ∪ X).card ≤ j := by
      rw [← hCX, show W ∪ code C = verticesOn C from union_sdiff_of_subset (hroot C hC)]
      exact hspan C hC
    have hsub : (family.filter fun D ↦ code D = X) ⊆ tripleSystemsSupportedOn (W ∪ X) := by
      intro D hD
      obtain ⟨hDf, hDX⟩ := mem_filter.mp hD
      apply mem_tripleSystemsSupportedOn_iff.mpr
      have hid : W ∪ code D = verticesOn D := union_sdiff_of_subset (hroot D hDf)
      rw [← hid, hDX]
    exact (card_le_card hsub).trans ((card_tripleSystemsSupportedOn_le (W ∪ X)).trans
      (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_left hspanUnion 3)))
  have himage : family.image code ⊆ subsetsUpToCard (univ : Finset V) (j - W.card) := by
    intro X hX
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hX
    apply mem_subsetsUpToCard_iff.mpr
    refine ⟨subset_univ _, ?_⟩
    dsimp only [code]
    rw [card_sdiff_of_subset (hroot C hC)]
    exact Nat.sub_le_sub_right (hspan C hC) W.card
  have hcode := (card_le_card himage).trans (card_subsetsUpToCard_le (univ : Finset V) (j - W.card))
  simp only [card_univ] at hcode
  calc
    _ ≤ 2 ^ (j ^ 3) * (family.image code).card := card_le_mul_card_image family (2 ^ (j ^ 3)) hfiber
    _ ≤ 2 ^ (j ^ 3) * ((j - W.card + 1) * (Fintype.card V + 1) ^ (j - W.card)) :=
      Nat.mul_le_mul_left _ hcode
    _ ≤ 2 ^ (j ^ 3) * ((j + 1) * (Fintype.card V + 1) ^ (j - W.card)) := by
      gcongr
      omega
    _ = _ := by ring

end

end Erdos207
