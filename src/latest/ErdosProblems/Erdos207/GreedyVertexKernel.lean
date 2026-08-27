/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyVertexEmbedding
import ErdosProblems.Erdos207.FiniteLawPushforward

/-! # Exact sampling-law transport under a vertex embedding -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem FiniteLaw.map_pure
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (f : A → B) (a : A) : FiniteLaw.map f (FiniteLaw.pure a) = FiniteLaw.pure (f a) := by
  classical
  apply FiniteLaw.ext_probability
  intro P
  simp only [FiniteLaw.probability_map, FiniteLaw.probability_pure]

theorem FiniteLaw.map_uniform_equiv
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B] [Nonempty A] [Nonempty B]
    (e : A ≃ B) : FiniteLaw.map e (FiniteLaw.uniform : FiniteLaw A) = FiniteLaw.uniform := by
  classical
  apply FiniteLaw.ext_probability
  intro P
  rw [FiniteLaw.probability_map]
  unfold FiniteLaw.probability
  dsimp only [FiniteLaw.uniform]
  rw [Fintype.card_congr e]
  exact e.sum_comp (fun b ↦ if P b then (Fintype.card B : ℝ≥0)⁻¹ else 0)

theorem greedyKernel_map
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) :
    FiniteLaw.map (mapGreedyState f) (greedyKernel F S) =
      greedyKernel (mapForbiddenFamily f F) (mapGreedyState f S) := by
  classical
  by_cases hA : S.available.Nonempty
  · have hA' : (mapGreedyState f S).available.Nonempty := hA.map
    letI : Nonempty S.available := ⟨⟨hA.choose, hA.choose_spec⟩⟩
    letI : Nonempty (mapGreedyState f S).available := ⟨⟨hA'.choose, hA'.choose_spec⟩⟩
    let e : S.available ≃ (mapGreedyState f S).available :=
      Finset.equivMap (mapTripleEmbedding f) S.available
    have hsrc : greedyKernel F S = FiniteLaw.map (fun T : S.available ↦ greedyStep F S T.1) FiniteLaw.uniform := by
      simp only [greedyKernel, dif_pos hA]
    have htgt : greedyKernel (mapForbiddenFamily f F) (mapGreedyState f S) =
        FiniteLaw.map (fun T : (mapGreedyState f S).available ↦
          greedyStep (mapForbiddenFamily f F) (mapGreedyState f S) T.1) FiniteLaw.uniform := by
      simp only [greedyKernel, dif_pos hA']
    rw [hsrc, htgt, FiniteLaw.map_comp, ← FiniteLaw.map_uniform_equiv e, FiniteLaw.map_comp]
    congr 1
    funext T
    exact greedyStep_map f F S T.1
  · have hA' : ¬ (mapGreedyState f S).available.Nonempty := by
      simpa only [mapGreedyState, mapTripleSystem, Finset.map_nonempty] using hA
    simp only [greedyKernel, dif_neg hA, dif_neg hA', FiniteLaw.map_pure]

end

end Erdos207
