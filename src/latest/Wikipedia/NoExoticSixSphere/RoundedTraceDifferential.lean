import Wikipedia.NoExoticSixSphere.RoundedTracePieceFrames
import Wikipedia.NoExoticSixSphere.SmoothOpenCoverImmersion

/-!
# Actual tangent images of the globally rounded trace

The parameter differentials on the two unchanged pieces are bijective.
Their actual ambient derivatives therefore have the cylinder and handle
tangent images. Local diffeomorphisms into the glued atlas then identify
these images with the global inclusion differential.
-/

noncomputable section

open Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  [IsManifold (𝓡 n) ∞ M] {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def pieceAmbientDerivative (i : Piece) (p : pieceDomain A i) :
    (ℝ × Vector n) →L[ℝ] Vector (e.ambientDimension + 6) := by
  let := pieceAtlas A i
  exact mfderiv (ProductHalfSpace.model (Vector n)) (𝓡 (e.ambientDimension + 6))
    (fun q : pieceDomain A i ↦ q.val.val) p

theorem cylinder_pieceDerivative_eq (p : cylinderOnlyPart A) :
    letI := unchangedCylinderChartedSpace A;
    pieceAmbientDerivative A .cylinder p =
      (e.heightCylinderDerivative (unchangedCylinderHomeomorph A p).val.val).comp
        (mfderiv (ProductHalfSpace.model (Vector n)) ((𝓡 n).prod 𝓘(ℝ, ℝ))
          (fun q : cylinderOnlyPart A ↦ (unchangedCylinderHomeomorph A q).val.val) p) := by
  let := unchangedCylinderChartedSpace A
  have he : (fun q : cylinderOnlyPart A ↦ q.val.val) = e.heightCylinder ∘
      (fun q : cylinderOnlyPart A ↦ (unchangedCylinderHomeomorph A q).val.val) :=
    funext (fun q ↦ (unchangedCylinderHomeomorph_ambient A q).symm)
  change mfderiv (ProductHalfSpace.model (Vector n)) (𝓡 (e.ambientDimension + 6))
    (fun q : cylinderOnlyPart A ↦ q.val.val) p = _
  rw [he]
  exact mfderiv_comp p (e.contMDiff_heightCylinder.mdifferentiableAt (by simp))
    ((contMDiff_unchangedCylinder_parameters A).mdifferentiableAt (by simp))

theorem handle_pieceDerivative_eq (p : handleOnlyPart A) :
    letI := unchangedHandleChartedSpace A;
    pieceAmbientDerivative A .handle p =
      (fderiv ℝ A.map (unchangedHandleHomeomorph A p).val.val).comp
        (mfderiv (ProductHalfSpace.model (Vector n)) 𝓘(ℝ, Vector 4 × Vector (n - 3))
          (fun q : handleOnlyPart A ↦ (unchangedHandleHomeomorph A q).val.val) p) := by
  let := unchangedHandleChartedSpace A
  let q := unchangedHandleHomeomorph A p
  have hs : ContDiffAt ℝ ∞ A.map q.val.val := A.smooth q.val.val.1
    (ball_subset_closedBall q.property.1) q.val.val.2 (handleSuperlevel_vector_mem A q.val)
  have he : (fun z : handleOnlyPart A ↦ z.val.val) = A.map ∘
      (fun z : handleOnlyPart A ↦ (unchangedHandleHomeomorph A z).val.val) :=
    funext (fun z ↦ (unchangedHandleHomeomorph_ambient A z).symm)
  change mfderiv (ProductHalfSpace.model (Vector n)) (𝓡 (e.ambientDimension + 6))
    (fun z : handleOnlyPart A ↦ z.val.val) p = _
  rw [he, mfderiv_comp p (hs.contMDiffAt.mdifferentiableAt (by simp))
    ((contMDiff_unchangedHandle_parameters A).mdifferentiableAt (by simp)), mfderiv_eq_fderiv]
  rfl

theorem injective_pieceAmbientDerivative (i : Piece) (p : pieceDomain A i) :
    Injective (pieceAmbientDerivative A i p) := by
  cases i with
  | cylinder =>
      change cylinderOnlyPart A at p
      let := unchangedCylinderChartedSpace A
      rw [cylinder_pieceDerivative_eq A p]
      exact (e.injective_heightCylinderDerivative _).comp
        (bijective_mfderiv_unchangedCylinder_parameters A p).1
  | handle =>
      change handleOnlyPart A at p
      let := unchangedHandleChartedSpace A
      rw [handle_pieceDerivative_eq A p]
      let q := unchangedHandleHomeomorph A p
      exact (A.immersive q.val.val.1 (ball_subset_closedBall q.property.1) q.val.val.2
        (handleSuperlevel_vector_mem A q.val)).comp
          (bijective_mfderiv_unchangedHandle_parameters A p).1
  | collar => exact injective_collarAmbientDerivative A p

theorem pieceNormalFrame_range (i : Piece) (p : pieceDomain A i) :
    (pieceNormalFrame A i p).range = (pieceAmbientDerivative A i p).rangeᗮ := by
  cases i with
  | cylinder =>
      change cylinderOnlyPart A at p
      let := unchangedCylinderChartedSpace A
      rw [cylinder_pieceDerivative_eq A p]
      have hr := LinearMap.range_comp_of_range_eq_top
        (e.heightCylinderDerivative (unchangedCylinderHomeomorph A p).val.val).toLinearMap
        (LinearMap.range_eq_top.mpr (bijective_mfderiv_unchangedCylinder_parameters A p).2)
      exact (e.heightCylinder_frame_range a _).trans
        (congrArg (fun S : Submodule ℝ (Vector (e.ambientDimension + 6)) ↦ Sᗮ) hr).symm
  | handle =>
      change handleOnlyPart A at p
      let := unchangedHandleChartedSpace A
      rw [handle_pieceDerivative_eq A p]
      have hr := LinearMap.range_comp_of_range_eq_top
        (fderiv ℝ A.map (unchangedHandleHomeomorph A p).val.val).toLinearMap
        (LinearMap.range_eq_top.mpr (bijective_mfderiv_unchangedHandle_parameters A p).2)
      let q := unchangedHandleHomeomorph A p
      exact (A.normalFrame_range q.val.val.1 (ball_subset_closedBall q.property.1) q.val.val.2
        (handleSuperlevel_vector_mem A q.val)).trans
          (congrArg (fun S : Submodule ℝ (Vector (e.ambientDimension + 6)) ↦ Sᗮ) hr).symm
  | collar => exact collarNormalFrame_range A p

def traceAmbientDerivative (p : ambientSet A) :
    (ℝ × Vector n) →L[ℝ] Vector (e.ambientDimension + 6) := by
  let := traceChartedSpace A
  exact mfderiv (ProductHalfSpace.model (Vector n)) (𝓡 (e.ambientDimension + 6))
    ((↑) : ambientSet A → Vector (e.ambientDimension + 6)) p

theorem injective_traceAmbientDerivative (p : ambientSet A) :
    Injective (traceAmbientDerivative A p) := by
  let := traceChartedSpace A
  exact (openCover A).injective_mfderiv_of_onPieces _ (trace_contMDiff_ambient A)
    (fun i ↦ injective_pieceAmbientDerivative A i) p

theorem range_pieceAmbientDerivative (i : Piece) (p : pieceDomain A i) :
    (pieceAmbientDerivative A i p).range = (traceAmbientDerivative A p.val).range := by
  let := traceChartedSpace A
  let := pieceAtlas A i
  have hi := (openCover A).isLocalDiffeomorphAt_inclusion i p
  have hd : pieceAmbientDerivative A i p = (traceAmbientDerivative A p.val).comp
      (mfderiv (ProductHalfSpace.model (Vector n)) (ProductHalfSpace.model (Vector n))
        (Subtype.val : pieceDomain A i → ambientSet A) p) :=
    mfderiv_comp p ((trace_contMDiff_ambient A).mdifferentiableAt (by simp))
      (hi.mdifferentiableAt (by simp))
  rw [hd]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (hi.mfderivToContinuousLinearEquiv (by simp)).surjective)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
