import Wikipedia.NoExoticSixSphere.EndingPathRestriction

/-!
# The path projection over the image of an actual embedding

Discarding the source coordinate identifies the homotopy fiber of an
embedding with the actual inverse image of its range under path evaluation.
The inverse recovers that coordinate using the embedding homeomorphism.
-/

noncomputable section

open Topology
open scoped unitInterval ContinuousMap
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.EndingPath

variable {A Y : Type*} [TopologicalSpace A] [TopologicalSpace Y]

def embeddingFiberHomeomorph (f : C(A, Y)) (hf : IsEmbedding f) (b : Y) :
    HomotopyFiber.Space f b ≃ₜ restriction b (Set.range f) where
  toFun p := ⟨⟨p.val.2, p.property.2⟩,
    show p.val.2 0 ∈ Set.range f from ⟨p.val.1, p.property.1.symm⟩⟩
  invFun p := ⟨(hf.toHomeomorph.symm ⟨source b p.val, p.property⟩, p.val.val),
    (congrArg Subtype.val
      (hf.toHomeomorph.apply_symm_apply ⟨source b p.val, p.property⟩)).symm,
    p.val.property⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply hf.injective
      exact (congrArg Subtype.val (hf.toHomeomorph.apply_symm_apply
        ⟨p.val.2 0, ⟨p.val.1, p.property.1.symm⟩⟩)).trans p.property.1
    · rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun :=
    ((hf.toHomeomorph.symm.continuous.comp
      (((source b).continuous.comp continuous_subtype_val).subtype_mk _)).prodMk
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

theorem embeddingFiberHomeomorph_val (f : C(A, Y)) (hf : IsEmbedding f) (b : Y)
    (p : HomotopyFiber.Space f b) :
    (embeddingFiberHomeomorph f hf b p).val.val = p.val.2 := rfl

end NoExoticSixSphere.EndingPath
