/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PathCoverAugmentation

/-!
# Root semantics and grouping for the KSSS path cover

This file identifies the abstract roots in `FullCycleCoverCopy` with their
concrete realized graphs on the shared base vertices.  The equalities are the
interface between the short-cycle construction and the universal absorber
bank.
-/

namespace Erdos207

open Finset

noncomputable section

lemma fullCycleCoverRoot_c4c5_eq
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : C4C5QuotientMap Y) :
    fullCycleCoverRoot (FullCycleCoverCopy.c4c5 f) =
      c4c5TemplateGraph.map
        (fun x => fullCycleCoverBaseEmbedding Y (f.1 x)) := by
  change (c4c5LocalTargetRoot f).map
      (c4c5FullAttachmentEmbedding f) = _
  unfold c4c5LocalTargetRoot transformerTargetRoot
  rw [SimpleGraph.map_map, SimpleGraph.map_map, SimpleGraph.map_map]
  congr 1

lemma fullCycleCoverRoot_threeC4_eq
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : ThreeC4QuotientMap Y) :
    fullCycleCoverRoot (FullCycleCoverCopy.threeC4 f) =
      threeC4TemplateGraph.map
        (fun x => fullCycleCoverBaseEmbedding Y (f.1 x)) := by
  change (threeC4LocalTargetRoot f).map
      (threeC4FullAttachmentEmbedding f) = _
  unfold threeC4LocalTargetRoot transformerTargetRoot
  rw [SimpleGraph.map_map, SimpleGraph.map_map, SimpleGraph.map_map]
  congr 1

lemma fullCycleCoverRoot_c4c5OfEmbedded_eq
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f₄ : Fin 4 → Y) (f₅ : Fin 5 → Y)
    (hf₄ : EdgeFaithfulMap (SimpleGraph.cycleGraph 4) f₄)
    (hf₅ : EdgeFaithfulMap (SimpleGraph.cycleGraph 5) f₅)
    (hdisjoint : Disjoint ((SimpleGraph.cycleGraph 4).map f₄)
      ((SimpleGraph.cycleGraph 5).map f₅)) :
    fullCycleCoverRoot (.c4c5
      (c4c5QuotientMapOfEmbedded f₄ f₅ hf₄ hf₅ hdisjoint)) =
      ((SimpleGraph.cycleGraph 4).map f₄ ⊔
        (SimpleGraph.cycleGraph 5).map f₅).map
          (fullCycleCoverBaseEmbedding Y) := by
  rw [fullCycleCoverRoot_c4c5_eq]
  change c4c5TemplateGraph.map
      (fun x => fullCycleCoverBaseEmbedding Y
        (combineC4C5Maps f₄ f₅ x)) = _
  rw [c4c5TemplateGraph_eq_components,
    SimpleGraph.map_sup_function, SimpleGraph.map_sup_function]
  congr 1
  · calc
      c4C5FirstComponent.map
          (fun x => fullCycleCoverBaseEmbedding Y
            (combineC4C5Maps f₄ f₅ x)) =
          (c4C5FirstComponent.map (combineC4C5Maps f₄ f₅)).map
            (fullCycleCoverBaseEmbedding Y) := by
              rw [SimpleGraph.map_map]
              rfl
      _ = ((SimpleGraph.cycleGraph 4).map f₄).map
            (fullCycleCoverBaseEmbedding Y) := by
              rw [map_c4C5FirstComponent_combine]
  · calc
      c4C5SecondComponent.map
          (fun x => fullCycleCoverBaseEmbedding Y
            (combineC4C5Maps f₄ f₅ x)) =
          (c4C5SecondComponent.map (combineC4C5Maps f₄ f₅)).map
            (fullCycleCoverBaseEmbedding Y) := by
              rw [SimpleGraph.map_map]
              rfl
      _ = ((SimpleGraph.cycleGraph 5).map f₅).map
            (fullCycleCoverBaseEmbedding Y) := by
              rw [map_c4C5SecondComponent_combine]

lemma fullCycleCoverRoot_threeC4OfEmbedded_eq
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f₀ f₁ f₂ : Fin 4 → Y)
    (hf₀ : EdgeFaithfulMap (SimpleGraph.cycleGraph 4) f₀)
    (hf₁ : EdgeFaithfulMap (SimpleGraph.cycleGraph 4) f₁)
    (hf₂ : EdgeFaithfulMap (SimpleGraph.cycleGraph 4) f₂)
    (hd₀₁ : Disjoint ((SimpleGraph.cycleGraph 4).map f₀)
      ((SimpleGraph.cycleGraph 4).map f₁))
    (hd₀₂ : Disjoint ((SimpleGraph.cycleGraph 4).map f₀)
      ((SimpleGraph.cycleGraph 4).map f₂))
    (hd₁₂ : Disjoint ((SimpleGraph.cycleGraph 4).map f₁)
      ((SimpleGraph.cycleGraph 4).map f₂)) :
    fullCycleCoverRoot (.threeC4
      (threeC4QuotientMapOfEmbedded f₀ f₁ f₂ hf₀ hf₁ hf₂
        hd₀₁ hd₀₂ hd₁₂)) =
      (((SimpleGraph.cycleGraph 4).map f₀ ⊔
        (SimpleGraph.cycleGraph 4).map f₁) ⊔
        (SimpleGraph.cycleGraph 4).map f₂).map
          (fullCycleCoverBaseEmbedding Y) := by
  rw [fullCycleCoverRoot_threeC4_eq]
  change threeC4TemplateGraph.map
      (fun x => fullCycleCoverBaseEmbedding Y
        (combineThreeC4Maps f₀ f₁ f₂ x)) = _
  rw [threeC4TemplateGraph_eq_components,
    SimpleGraph.map_sup_function, SimpleGraph.map_sup_function,
    SimpleGraph.map_sup_function, SimpleGraph.map_sup_function]
  congr 1
  · congr 1
    · calc
        firstThreeC4Component.map
            (fun x => fullCycleCoverBaseEmbedding Y
              (combineThreeC4Maps f₀ f₁ f₂ x)) =
            (firstThreeC4Component.map
              (combineThreeC4Maps f₀ f₁ f₂)).map
              (fullCycleCoverBaseEmbedding Y) := by
                rw [SimpleGraph.map_map]
                rfl
        _ = ((SimpleGraph.cycleGraph 4).map f₀).map
              (fullCycleCoverBaseEmbedding Y) := by
                rw [map_firstThreeC4Component_combine]
    · calc
        secondThreeC4Component.map
            (fun x => fullCycleCoverBaseEmbedding Y
              (combineThreeC4Maps f₀ f₁ f₂ x)) =
            (secondThreeC4Component.map
              (combineThreeC4Maps f₀ f₁ f₂)).map
              (fullCycleCoverBaseEmbedding Y) := by
                rw [SimpleGraph.map_map]
                rfl
        _ = ((SimpleGraph.cycleGraph 4).map f₁).map
              (fullCycleCoverBaseEmbedding Y) := by
                rw [map_secondThreeC4Component_combine]
  · calc
      thirdThreeC4Component.map
          (fun x => fullCycleCoverBaseEmbedding Y
            (combineThreeC4Maps f₀ f₁ f₂ x)) =
          (thirdThreeC4Component.map
            (combineThreeC4Maps f₀ f₁ f₂)).map
            (fullCycleCoverBaseEmbedding Y) := by
              rw [SimpleGraph.map_map]
              rfl
      _ = ((SimpleGraph.cycleGraph 4).map f₂).map
            (fullCycleCoverBaseEmbedding Y) := by
              rw [map_thirdThreeC4Component_combine]

end

end Erdos207
