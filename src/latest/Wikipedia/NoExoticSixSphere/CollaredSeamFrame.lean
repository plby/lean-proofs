import Wikipedia.NoExoticSixSphere.LowSurgerySeamFrame
import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenComponent
import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenReversal

/-!
# Exact seam framing formulas for the native connectivity-surgery operations

These formulas concern the actual embedding and normal-frame fields of
the constructed collared states. A surgery adds the prescribed coordinate
axes and the fixed signed column change. Reversal leaves the seven-frame
unchanged; component restriction keeps the original ambient columns.
All point identifications use the native zero-atlas diffeomorphisms.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CollaredSeam

open GLOrthonormalization Stiefel Wikipedia.HopfProblem.DegreeCollapse
open LowSurgery FramedAttachingProduct RoundedTrace NativeSurgery

theorem regularZeroCongr_point {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
    [IsManifold (𝓡 7) ∞ M] (t u : C(M, ℝ))
    (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t) (hu : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ u)
    (hrt : ∀ p, t p = 0 → Function.Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t p))
    (hru : ∀ p, u p = 0 → Function.Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) u p))
    (h : t = u) (p : {p : M // t p = 0}) :
    letI := regularFiberAtlas t ht 0 hrt 6 (by simp);
    letI := regularFiberAtlas u hu 0 hru 6 (by simp);
    (CollaredSevenState.regularZeroCongr t u ht hu hrt hru h p).val = p.val := by
  subst u
  rfl

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)

section Surgery

variable {d : ℕ} {f : Sphere d → S.Space}
  (A : FramedAttachingProduct S.embedding S.normalFrame f) (hA : A.radius = 2)
  (T : TimeData A) (hT : T.time = S.time)

theorem perform_embedding (p : S.Zero) :
    letI := S.zeroAtlas; letI := (S.perform A hA T hT).zeroAtlas;
    (S.perform A hA T hT).embedding.toFun (S.performZeroDiffeomorph A hA T hT p).val =
      appendZeroMap S.embedding.ambientDimension (1 + (1 + (d + 1)))
        (S.embedding.toFun p.val) := by
  let := S.zeroAtlas
  let := boundaryChartedSpace A
  let := originalZeroAtlas A T
  let := (S.perform A hA T hT).zeroAtlas
  let E := CollaredSevenState.regularZeroCongr S.zeroTimeMap (originalTimeMap A T)
    S.time_smooth T.smooth S.time_regular T.regular
    (ContinuousMap.ext (fun p ↦ (congrFun hT p).symm))
  have he : (E p).val = p.val := regularZeroCongr_point S.zeroTimeMap (originalTimeMap A T)
    S.time_smooth T.smooth S.time_regular T.regular
    (ContinuousMap.ext (fun p ↦ (congrFun hT p).symm)) p
  have hp := LowSurgerySeam.embedding_retainedBand A T (originalZeroToBand A T (E p))
  change (S.perform A hA T hT).embedding.toFun
    (S.performZeroDiffeomorph A hA T hT p).val =
      appendZeroMap S.embedding.ambientDimension (1 + (1 + (d + 1)))
        (S.embedding.toFun (E p).val) at hp
  rw [he] at hp
  exact hp

theorem perform_frame (p : S.Zero) :
    letI := S.zeroAtlas; letI := (S.perform A hA T hT).zeroAtlas;
    ∀ v, (S.perform A hA T hT).normalFrame.ambient
        (S.performZeroDiffeomorph A hA T hT p).val v =
      BlockSum.operator (1 + (1 + (d + 1))) (S.normalFrame.orthonormal p.val).val
        (LowSurgerySeam.columnChange A v) := by
  let := S.zeroAtlas
  let := boundaryChartedSpace A
  let := originalZeroAtlas A T
  let := (S.perform A hA T hT).zeroAtlas
  let E := CollaredSevenState.regularZeroCongr S.zeroTimeMap (originalTimeMap A T)
    S.time_smooth T.smooth S.time_regular T.regular
    (ContinuousMap.ext (fun p ↦ (congrFun hT p).symm))
  have he : (E p).val = p.val := regularZeroCongr_point S.zeroTimeMap (originalTimeMap A T)
    S.time_smooth T.smooth S.time_regular T.regular
    (ContinuousMap.ext (fun p ↦ (congrFun hT p).symm)) p
  intro v
  have hp := LowSurgerySeam.framing_zero A hA T (E p) v
  change (S.perform A hA T hT).normalFrame.ambient
    (S.performZeroDiffeomorph A hA T hT p).val v =
      BlockSum.operator (1 + (1 + (d + 1))) (S.normalFrame.orthonormal (E p).val).val
        (LowSurgerySeam.columnChange A v) at hp
  rw [he] at hp
  exact hp

theorem perform_frame_norm (p : (S.perform A hA T hT).Space)
    (v : (S.perform A hA T hT).embedding.NormalModel) :
    ‖(S.perform A hA T hT).normalFrame.ambient p v‖ = ‖v‖ := by
  let := boundaryChartedSpace A
  exact inducedOtherEndNormalFraming_norm A p v

end Surgery

theorem reverse_frame (p : S.Zero) :
    letI := S.zeroAtlas; letI := S.reverse.zeroAtlas;
    S.reverse.normalFrame.ambient (S.reverseZeroDiffeomorph p).val =
      S.normalFrame.ambient p.val := by
  let := S.zeroAtlas
  let := S.reverse.zeroAtlas
  rw [S.reverseZeroDiffeomorph_point]
  rfl

theorem component_frame [PathConnectedSpace B] (b : B) (p : (S.component b).Zero) :
    letI := S.zeroAtlas; letI := (S.component b).zeroAtlas;
    (S.component b).normalFrame.ambient p.val =
      S.normalFrame.ambient (S.componentZeroDiffeomorph b p).val := by
  let := S.zeroAtlas
  let := (S.component b).zeroAtlas
  let : LocallyPathConnectedSpace S.Space :=
    ChartedSpace.locallyPathConnectedSpace (Vector 7) S.Space
  rw [S.componentZeroDiffeomorph_point]
  apply ContinuousLinearMap.ext
  intro v
  exact ClopenEmbedding.restrictNormalFrame_ambient S.embedding
    (S.collar.boundaryComponent b) (S.collar.boundaryComponent_isClosed b) S.normalFrame p.val v

end NoExoticSixSphere.CollaredSeam
