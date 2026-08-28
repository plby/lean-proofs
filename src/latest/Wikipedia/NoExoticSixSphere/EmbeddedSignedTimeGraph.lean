import Wikipedia.NoExoticSixSphere.EmbeddedNegativeTimeGraph

/-!
# Both time-graph signs retain the actual outward boundary frame

Use positive time and the outward normal at an inner annulus end, and
negative time and the inward normal at an outer end. The latter retains
the actual outward boundary frame through the explicit normal-coordinate
reflection. Both graph differentials are the native time differentials.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector (n + 1)) M]
  [IsManifold (𝓡 (n + 1)) ∞ M] (e : EuclideanEmbedding (n + 1) M)
  (r : e.TubularRetraction) (t : C(M, ℝ))
  (ht : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) t x))

def signedTimeGraph (positive : Bool) (g : Vector 4 → M) (x : Vector 4) :
    Vector e.ambientDimension × ℝ :=
  (e.toFun (g x), if positive then t (g x) else -t (g x))

def signedTimeCovector (positive : Bool) (x : M) : Vector e.ambientDimension →L[ℝ] ℝ :=
  if positive then timeCovector e r t x else -timeCovector e r t x

def signedTransverse (positive : Bool) (p : {x : M // t x = 0}) : Vector e.ambientDimension :=
  if positive then outwardNormal e r t p else inwardNormal e r t p

def signedNormalCoordinates (positive : Bool) (m : M) :
    Vector (e.ambientDimension - n) ≃L[ℝ] Vector ((e.ambientDimension - (n + 1)) + 1) :=
  if positive then (normalCoordinates (n := n) e m).toContinuousLinearEquiv
  else inwardNormalCoordinates (n := n) e m

include ht in
theorem contDiffAt_signedTimeGraph (positive : Bool) (g : Vector 4 → M) (x : Vector 4)
    (hg : ContMDiffAt (𝓡 4) (𝓡 (n + 1)) ∞ g x) :
    ContDiffAt ℝ ∞ (signedTimeGraph e t positive g) x := by
  cases positive
  · exact contDiffAt_negativeTimeGraph e t ht g x hg
  · exact (e.smooth.contMDiffAt.comp x hg).contDiffAt.prodMk
      (ht.contMDiffAt.comp x hg).contDiffAt

include ht in
theorem signedTimeGraph_derivative (positive : Bool) (g : Vector 4 → M) (x : Vector 4)
    (hg : ContMDiffAt (𝓡 4) (𝓡 (n + 1)) ∞ g x) :
    fderiv ℝ (signedTimeGraph e t positive g) x = OutwardGraphFrame.graph
      (fderiv ℝ (e.toFun ∘ g) x) (signedTimeCovector e r t positive (g x)) := by
  cases positive
  · exact negativeTimeGraph_derivative e r t ht g x hg
  · have hE : DifferentiableAt ℝ (e.toFun ∘ g) x :=
      (e.smooth.contMDiffAt.comp x hg).contDiffAt.differentiableAt (by simp)
    have hT : DifferentiableAt ℝ (t ∘ g) x :=
      (ht.contMDiffAt.comp x hg).contDiffAt.differentiableAt (by simp)
    have hd := (hE.hasFDerivAt.prodMk hT.hasFDerivAt).fderiv
    apply ContinuousLinearMap.ext
    intro v
    have hv := congrArg (fun L : Vector 4 →L[ℝ] (Vector e.ambientDimension × ℝ) ↦ L v) hd
    change fderiv ℝ (signedTimeGraph e t true g) x v =
      (fderiv ℝ (e.toFun ∘ g) x v, fderiv ℝ (t ∘ g) x v) at hv
    rw [OutwardGraphFrame.graph_apply]
    change fderiv ℝ (signedTimeGraph e t true g) x v =
      (fderiv ℝ (e.toFun ∘ g) x v, timeCovector e r t (g x) (fderiv ℝ (e.toFun ∘ g) x v))
    rw [timeCovector_composedDerivative e r t ht g x hg]
    exact hv

include r ht in
theorem signedTimeGraph_heightDerivative (positive : Bool) (g : Vector 4 → M)
    (x v : Vector 4) (hg : ContMDiffAt (𝓡 4) (𝓡 (n + 1)) ∞ g x) :
    (fderiv ℝ (signedTimeGraph e t positive g) x v).2 =
      if positive then fderiv ℝ (t ∘ g) x v else -fderiv ℝ (t ∘ g) x v := by
  rw [signedTimeGraph_derivative e r t ht positive g x hg, OutwardGraphFrame.graph_apply]
  cases positive
  · change -timeCovector e r t (g x) (fderiv ℝ (e.toFun ∘ g) x v) = -fderiv ℝ (t ∘ g) x v
    rw [timeCovector_composedDerivative e r t ht g x hg]
  · exact timeCovector_composedDerivative e r t ht g x hg v

include ht in
theorem contMDiff_signedTimeCovector (positive : Bool) :
    ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, Vector e.ambientDimension →L[ℝ] ℝ) ∞
      (signedTimeCovector e r t positive) := by
  cases positive
  · exact (contMDiff_timeCovector e r t ht).neg
  · exact contMDiff_timeCovector e r t ht

theorem contMDiff_signedTransverse (positive : Bool) : letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 n) (𝓡 e.ambientDimension) ∞ (signedTransverse e r t positive) := by
  let := zeroAtlas t ht hreg
  cases positive
  · exact contMDiff_inwardNormal e r t ht hreg
  · exact contMDiff_outwardNormal e r t ht hreg

theorem signedTimeCovector_frame (positive : Bool)
    (a : SmoothRangeFrame (𝓡 (n + 1)) e.normalProjection e.NormalModel)
    (x : M) (v : e.NormalModel) : signedTimeCovector e r t positive x (a.ambient x v) = 0 := by
  cases positive
  · change -timeCovector e r t x (a.ambient x v) = 0
    rw [timeCovector_frame, neg_zero]
  · exact timeCovector_frame e r t a x v

include ht hreg in
theorem signedTimeCovector_transverse_neg (positive : Bool) (p : {x : M // t x = 0}) :
    signedTimeCovector e r t positive p.val (signedTransverse e r t positive p) < 0 := by
  cases positive
  · exact inwardTimeCovector_inward_neg e r t ht hreg p
  · exact timeCovector_outward_neg e r t ht hreg p

theorem zeroNormalFrame_signed_columns (positive : Bool)
    (a : SmoothRangeFrame (𝓡 (n + 1)) e.normalProjection e.NormalModel)
    (m : M) (p : {x : M // t x = 0}) : letI := zeroAtlas t ht hreg;
    (zeroNormalFrame e r t ht hreg a m).ambient p =
      (OrthogonalFrameAppend.operator (a.orthonormal p.val).val
        (signedTransverse e r t positive p)).comp
          (signedNormalCoordinates e positive m).toContinuousLinearMap := by
  let := zeroAtlas t ht hreg
  cases positive
  · exact zeroNormalFrame_inward_columns e r t ht hreg a m p
  · apply ContinuousLinearMap.ext
    intro v
    exact zeroNormalFrame_ambient e r t ht hreg a m p v

end NoExoticSixSphere.EmbeddedTime
