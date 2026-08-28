import Wikipedia.NoExoticSixSphere.TimeCollarClopenRestriction
import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenComponent

/-!
# Native framed clopen restrictions with the actual restricted boundary

Restrict the original atlas, closed embedding, full normal frame, time,
and collar to any clopen ambient subset. The boundary is restricted by
its actual zero points; it need not be connected. The restricted native
zero atlas is diffeomorphic to the inherited clopen original zero atlas.
-/

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState

open NoExoticSixSphere GLOrthonormalization

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)
  (U : Opens S.Space) (hU : IsClosed (U : Set S.Space))

def restrictClopen : LowCollaredSevenState (S.collar.clopenBoundary U) where
  Space := U
  topology := inferInstance
  atlas := inferInstance
  smooth := inferInstance
  compact := isCompact_iff_compactSpace.mp hU.isCompact
  separated := inferInstance
  embedding := ClopenEmbedding.restrict S.embedding U hU
  normalFrame := ClopenEmbedding.restrictNormalFrame S.embedding U hU S.normalFrame
  time := S.time ∘ Subtype.val
  time_smooth := S.time_smooth.comp contMDiff_subtype_val
  time_regular p hp := by
    rw [mfderiv_comp p (S.time_smooth.mdifferentiableAt (by simp))
      ((contMDiff_subtype_val (I := 𝓡 7) (U := U) (n := ∞)).mdifferentiableAt (by simp))]
    exact (S.time_regular p.val hp).comp
      (mfderiv_openSubset_val_bijective (I := 𝓡 7) U p).surjective
  collar := S.collar.restrictClopen U hU

def zeroOpen : Opens S.Zero := ⟨{p | p.val ∈ U}, U.isOpen.preimage continuous_subtype_val⟩

include hU in
theorem zeroOpen_closed : IsClosed (S.zeroOpen U : Set S.Zero) :=
  hU.preimage continuous_subtype_val

def restrictClopenZeroHomeomorph : (S.restrictClopen U hU).Zero ≃ₜ S.zeroOpen U where
  toFun p := ⟨⟨p.val.val, p.property⟩, p.val.property⟩
  invFun p := ⟨⟨p.val.val, p.property⟩, p.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    have h₁ : Continuous (Subtype.val : (S.restrictClopen U hU).Zero → U) := continuous_subtype_val
    have h₂ : Continuous (Subtype.val : U → S.Space) := continuous_subtype_val
    exact ((h₂.comp h₁).subtype_mk _).subtype_mk _
  continuous_invFun := by
    have h₁ : Continuous (Subtype.val : S.zeroOpen U → S.Zero) := continuous_subtype_val
    have h₂ : Continuous (Subtype.val : S.Zero → S.Space) := continuous_subtype_val
    exact ((h₂.comp h₁).subtype_mk _).subtype_mk _

def restrictClopenZeroDiffeomorph :
    letI := S.zeroAtlas;
    letI := (S.restrictClopen U hU).zeroAtlas;
    (S.restrictClopen U hU).Zero ≃ₘ⟮𝓡 6, 𝓡 6⟯ S.zeroOpen U := by
  let := S.zeroAtlas
  let := (S.restrictClopen U hU).zeroAtlas
  let e := S.restrictClopenZeroHomeomorph U hU
  refine { toEquiv := e.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · apply (ContMDiff.subtypeVal_comp_iff (S.zeroOpen U) e).mp
    apply (regularFiber_contMDiff_iff_ambient S.zeroTimeMap S.time_smooth
      0 S.time_regular 6 (by simp) (fun p ↦ (e p).val)).mpr
    exact (contMDiff_subtype_val (I := 𝓡 7) (U := U)).comp
      (regularFiber_contMDiff_subtype_val (S.restrictClopen U hU).zeroTimeMap
        (S.restrictClopen U hU).time_smooth 0 (S.restrictClopen U hU).time_regular 6 (by simp))
  · apply (regularFiber_contMDiff_iff_ambient (S.restrictClopen U hU).zeroTimeMap
      (S.restrictClopen U hU).time_smooth 0 (S.restrictClopen U hU).time_regular
        6 (by simp) e.symm).mpr
    apply (ContMDiff.subtypeVal_comp_iff (I := 𝓡 6) (I' := 𝓡 7)
      U (fun p : S.zeroOpen U ↦ (e.symm p).val)).mp
    have hv : ContMDiff (𝓡 6) (𝓡 7) ∞ (Subtype.val : S.Zero → S.Space) :=
      regularFiber_contMDiff_subtype_val S.zeroTimeMap S.time_smooth
        0 S.time_regular 6 (by simp)
    exact hv.comp contMDiff_subtype_val

theorem restrictClopenZeroDiffeomorph_point (p : (S.restrictClopen U hU).Zero) :
    letI := S.zeroAtlas;
    letI := (S.restrictClopen U hU).zeroAtlas;
    (S.restrictClopenZeroDiffeomorph U hU p).val.val = p.val.val := rfl

end Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState
