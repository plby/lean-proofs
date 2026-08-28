import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedCollarLevel
import Wikipedia.HopfProblem.DegreeCollapseSevenAttachingCollarSheet
import Wikipedia.NoExoticSixSphere.ManifoldParameterFDeriv

/-!
# Smooth differentiation in the actual transverse and height directions

The sphere parameter is held fixed. Thus the derivative is a map between
fixed Euclidean spaces and varies smoothly in the native sphere parameter,
without treating a raw manifold-coordinate differential as globally smooth.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct

open NoExoticSixSphere GLOrthonormalization Stiefel SevenRoundedHandleCorner

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def collarTransverseSheet (p : Collar) (z : Vector 4 × ℝ) : Vector (e.ambientDimension + 6) :=
  A.collarSheet ((p.1.1, z.1), z.2)

def collarTransverseDerivative (p : Collar) :
    (Vector 4 × ℝ) →L[ℝ] Vector (e.ambientDimension + 6) :=
  fderiv ℝ (A.collarTransverseSheet p) (collarProjection p)

theorem contMDiffAt_collarTransverseDerivative {p : Collar}
    (hp : p ∈ A.tubeHeightCoordinates.source) :
    ContMDiffAt collarModel
      𝓘(ℝ, (Vector 4 × ℝ) →L[ℝ] Vector (e.ambientDimension + 6)) ∞
      A.collarTransverseDerivative p := by
  have hm : ContMDiff (collarModel.prod 𝓘(ℝ, Vector 4 × ℝ)) collarModel ∞
      (fun q : Collar × (Vector 4 × ℝ) ↦ ((q.1.1.1, q.2.1), q.2.2)) :=
    ((contMDiff_fst.comp (contMDiff_fst.comp contMDiff_fst)).prodMk
      ((ContinuousLinearMap.fst ℝ (Vector 4) ℝ).contDiff.contMDiff.comp contMDiff_snd)).prodMk
        ((ContinuousLinearMap.snd ℝ (Vector 4) ℝ).contDiff.contMDiff.comp contMDiff_snd)
  have hs := A.contMDiffOn_collarSheet.contMDiffAt
    (A.tubeHeightCoordinates.open_source.mem_nhds hp)
  have hF : ContMDiffAt (collarModel.prod 𝓘(ℝ, Vector 4 × ℝ)) (𝓡 (e.ambientDimension + 6)) ∞
      (Function.uncurry A.collarTransverseSheet) (p, collarProjection p) :=
    hs.comp (p, collarProjection p) (hm (p, collarProjection p))
  exact ContMDiffAt.fderiv_parameter hF (contMDiff_collarProjection p)

theorem collarTransverseDerivative_apply {p : Collar} (hp : p ∈ A.tubeHeightCoordinates.source)
    (v : Vector 4 × ℝ) :
    A.collarTransverseDerivative p v = A.collarSheetDerivative p ((0, v.1), v.2) := by
  let j : (Vector 4 × ℝ) →L[ℝ] ((Vector 3 × Vector 4) × ℝ) :=
    ((0 : (Vector 4 × ℝ) →L[ℝ] Vector 3).prod (ContinuousLinearMap.fst ℝ (Vector 4) ℝ)).prod
      (ContinuousLinearMap.snd ℝ (Vector 4) ℝ)
  have hg : HasMFDerivAt 𝓘(ℝ, Vector 4 × ℝ) collarModel
      (fun z : Vector 4 × ℝ ↦ ((p.1.1, z.1), z.2)) (collarProjection p) j :=
    ((hasMFDerivAt_const p.1.1 (collarProjection p)).prodMk
      (ContinuousLinearMap.fst ℝ (Vector 4) ℝ).hasFDerivAt.hasMFDerivAt).prodMk
        (ContinuousLinearMap.snd ℝ (Vector 4) ℝ).hasFDerivAt.hasMFDerivAt
  have hs := A.contMDiffOn_collarSheet.contMDiffAt
    (A.tubeHeightCoordinates.open_source.mem_nhds hp)
  have hd : fderiv ℝ (A.collarTransverseSheet p) (collarProjection p) =
      (A.collarSheetDerivative p).comp j := by
    have he := ((hs.mdifferentiableAt (by simp)).hasMFDerivAt.comp (collarProjection p) hg).mfderiv
    rw [mfderiv_eq_fderiv] at he
    exact he
  exact congrArg (fun L : (Vector 4 × ℝ) →L[ℝ] Vector (e.ambientDimension + 6) ↦ L v) hd

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct
