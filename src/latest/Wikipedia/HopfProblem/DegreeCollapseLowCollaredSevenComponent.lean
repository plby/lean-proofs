import Wikipedia.HopfProblem.DegreeCollapseTimeCollarComponent
import Wikipedia.HopfProblem.DegreeCollapseClopenEmbedding
import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenBoundary

/-!

# Select the actual component while retaining the native zero atlas

Restrict the original manifold to the clopen component containing its
connected collar boundary. The atlas is the inherited open-subset atlas,
the embedding and normal frame are the actual restrictions, and the time
and collar keep their original values. The identity on zero points is
smooth in both independently constructed regular-fiber atlases.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState

open NoExoticSixSphere GLOrthonormalization

variable {B : Type} [TopologicalSpace B] [PathConnectedSpace B]
  (S : LowCollaredSevenState B)

local instance : LocallyPathConnectedSpace S.Space :=
  ChartedSpace.locallyPathConnectedSpace (Vector 7) S.Space

def component (b : B) : LowCollaredSevenState B where
  Space := S.collar.boundaryComponent b
  topology := inferInstance
  atlas := inferInstance
  smooth := inferInstance
  compact := S.collar.boundaryComponent_compact b
  separated := inferInstance
  embedding := ClopenEmbedding.restrict S.embedding (S.collar.boundaryComponent b)
    (S.collar.boundaryComponent_isClosed b)
  normalFrame := ClopenEmbedding.restrictNormalFrame S.embedding (S.collar.boundaryComponent b)
    (S.collar.boundaryComponent_isClosed b) S.normalFrame
  time := S.time ∘ Subtype.val
  time_smooth := S.time_smooth.comp contMDiff_subtype_val
  time_regular p hp := by
    rw [mfderiv_comp p (S.time_smooth.mdifferentiableAt (by simp))
      ((contMDiff_subtype_val (I := 𝓡 7)
        (U := S.collar.boundaryComponent b) (n := ∞)).mdifferentiableAt (by simp))]
    exact (S.time_regular p.val hp).comp
      (mfderiv_openSubset_val_bijective (I := 𝓡 7) (S.collar.boundaryComponent b) p).surjective
  collar := S.collar.restrictToBoundaryComponent b

theorem component_pathConnected (b : B) : PathConnectedSpace (S.component b).Space :=
  S.collar.boundaryComponent_pathConnected b

def componentZeroDiffeomorph (b : B) :
    letI := S.zeroAtlas
    letI := (S.component b).zeroAtlas
    (S.component b).Zero ≃ₘ⟮𝓡 6, 𝓡 6⟯ S.Zero := by
  let := S.zeroAtlas
  let := (S.component b).zeroAtlas
  let e : (S.component b).Zero ≃ₜ S.Zero := S.collar.componentZeroHomeomorph b
  refine { toEquiv := e.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · apply (regularFiber_contMDiff_iff_ambient S.zeroTimeMap S.time_smooth
      0 S.time_regular 6 (by simp) e).mpr
    exact (contMDiff_subtype_val (I := 𝓡 7) (U := S.collar.boundaryComponent b)).comp
      (regularFiber_contMDiff_subtype_val (S.component b).zeroTimeMap
        (S.component b).time_smooth 0 (S.component b).time_regular 6 (by simp))
  · apply (regularFiber_contMDiff_iff_ambient (S.component b).zeroTimeMap
      (S.component b).time_smooth 0 (S.component b).time_regular 6 (by simp) e.symm).mpr
    apply (ContMDiff.subtypeVal_comp_iff (I := 𝓡 6) (I' := 𝓡 7)
      (S.collar.boundaryComponent b) (fun p : S.Zero ↦ (e.symm p).val)).mp
    exact regularFiber_contMDiff_subtype_val S.zeroTimeMap S.time_smooth
      0 S.time_regular 6 (by simp)

theorem componentZeroDiffeomorph_point (b : B) (p : (S.component b).Zero) :
    letI := S.zeroAtlas
    letI := (S.component b).zeroAtlas
    (S.componentZeroDiffeomorph b p).val = p.val.val := rfl

end Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState
