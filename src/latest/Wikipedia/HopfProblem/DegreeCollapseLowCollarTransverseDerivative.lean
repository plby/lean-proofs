import Wikipedia.HopfProblem.DegreeCollapseLowRoundedCollarLevel
import Wikipedia.HopfProblem.DegreeCollapseLowAttachingCollarSheet
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

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct

open NoExoticSixSphere GLOrthonormalization Stiefel LowRoundedHandleCorner

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

def collarTransverseSheet (p : Collar d (7 - d)) (z : Vector (7 - d) × ℝ) :
    Vector (e.ambientDimension + (1 + (1 + (d + 1)))) :=
  A.collarSheet ((p.1.1, z.1), z.2)

def collarTransverseDerivative (p : (Collar d (7 - d))) :
    (Vector (7 - d) × ℝ) →L[ℝ] Vector (e.ambientDimension + (1 + (1 + (d + 1)))) :=
  fderiv ℝ (A.collarTransverseSheet p) (collarProjection p)

theorem contMDiffAt_collarTransverseDerivative {p : (Collar d (7 - d))}
    (hp : p ∈ A.tubeHeightCoordinates.source) :
    ContMDiffAt (collarModel d (7 - d))
      𝓘(ℝ, (Vector (7 - d) × ℝ) →L[ℝ] Vector (e.ambientDimension + (1 + (1 + (d + 1))))) ∞
      A.collarTransverseDerivative p := by
  have hm : ContMDiff ((collarModel d (7 - d)).prod 𝓘(ℝ, Vector (7 - d) × ℝ))
      (collarModel d (7 - d)) ∞
      (fun q : (Collar d (7 - d)) × (Vector (7 - d) × ℝ) ↦ ((q.1.1.1, q.2.1), q.2.2)) :=
    ((contMDiff_fst.comp (contMDiff_fst.comp contMDiff_fst)).prodMk
      ((ContinuousLinearMap.fst ℝ (Vector (7 - d)) ℝ).contDiff.contMDiff.comp contMDiff_snd)).prodMk
        ((ContinuousLinearMap.snd ℝ (Vector (7 - d)) ℝ).contDiff.contMDiff.comp contMDiff_snd)
  have hs := A.contMDiffOn_collarSheet.contMDiffAt
    (A.tubeHeightCoordinates.open_source.mem_nhds hp)
  have hF : ContMDiffAt ((collarModel d (7 - d)).prod 𝓘(ℝ, Vector (7 - d) × ℝ))
      (𝓡 (e.ambientDimension + (1 + (1 + (d + 1))))) ∞
      (Function.uncurry A.collarTransverseSheet) (p, collarProjection p) :=
    hs.comp (p, collarProjection p) (hm (p, collarProjection p))
  exact ContMDiffAt.fderiv_parameter hF ((contMDiff_collarProjection (d := d) (q := 7 - d)) p)

theorem collarTransverseDerivative_apply {p : Collar d (7 - d)}
    (hp : p ∈ A.tubeHeightCoordinates.source)
    (v : Vector (7 - d) × ℝ) :
    A.collarTransverseDerivative p v = A.collarSheetDerivative p ((0, v.1), v.2) := by
  let j : (Vector (7 - d) × ℝ) →L[ℝ] ((Vector d × Vector (7 - d)) × ℝ) :=
    ((0 : (Vector (7 - d) × ℝ) →L[ℝ] Vector d).prod
      (ContinuousLinearMap.fst ℝ (Vector (7 - d)) ℝ)).prod
      (ContinuousLinearMap.snd ℝ (Vector (7 - d)) ℝ)
  have hg : HasMFDerivAt 𝓘(ℝ, Vector (7 - d) × ℝ) (collarModel d (7 - d))
      (fun z : Vector (7 - d) × ℝ ↦ ((p.1.1, z.1), z.2)) (collarProjection p) j :=
    ((hasMFDerivAt_const p.1.1 (collarProjection p)).prodMk
      (ContinuousLinearMap.fst ℝ (Vector (7 - d)) ℝ).hasFDerivAt.hasMFDerivAt).prodMk
        (ContinuousLinearMap.snd ℝ (Vector (7 - d)) ℝ).hasFDerivAt.hasMFDerivAt
  have hs := A.contMDiffOn_collarSheet.contMDiffAt
    (A.tubeHeightCoordinates.open_source.mem_nhds hp)
  have hd : fderiv ℝ (A.collarTransverseSheet p) (collarProjection p) =
      (A.collarSheetDerivative p).comp j := by
    have he := ((hs.mdifferentiableAt (by simp)).hasMFDerivAt.comp (collarProjection p) hg).mfderiv
    rw [mfderiv_eq_fderiv] at he
    exact he
  exact congrArg (fun L : (Vector (7 - d) × ℝ) →L[ℝ]
    Vector (e.ambientDimension + (1 + (1 + (d + 1)))) ↦ L v) hd

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct
