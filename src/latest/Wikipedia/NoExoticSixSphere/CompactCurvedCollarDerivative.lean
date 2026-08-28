import Wikipedia.NoExoticSixSphere.CompactCurvedDiskProduct
import Wikipedia.NoExoticSixSphere.ClosedDiskCollarDerivative
import Wikipedia.NoExoticSixSphere.PrescribedCompactCollarFrame

/-!
# The original collar frame is normal to the actual compact-tube curved product

The exact closed-disk collar formula gives equality of ordinary derivatives
by unique within-differentiability, including at the sphere boundary. Thus
the original manifold normal frame and five graph axes lie in the actual
corrected product's normal space. No ambient-open collar identity is assumed.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {n d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M)
  (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 n) ∞ f)
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))
  {T : Vector 4 → Vector ((e.ambientDimension - n) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)}
  (A : DiskThickening.FramedProduct D.toFun T d) (R : e.RetractionNear (range f))
  (χ : ContDiffBump (0 : Vector 4))
  (hCb : ∀ s v, appendZeroMap e.ambientDimension 6
    (boundaryComplementOperator A.transverse s v) = A.transverse s.val v)
  (hχ : (1 / 2 : ℝ) < χ.rOut)
  (hc : ∀ y ∈ closedBall (0 : Vector 4) 1, χ.rOut ≤ ‖y‖ →
    D.toFun y = collar b (e.toFun ∘ f) y ∧
      A.transverse y = A.transverse (SphereRadialRetraction.retract b y).val)

include hf hCb hχ hc in
theorem fderiv_compactCurvedDiskProduct_eq_collarModel {x : Vector 4}
    (hx : x ∈ closedBall (0 : Vector 4) 1) (hxr : χ.rOut < ‖x‖) (v : Vector d)
    (hp : (SphereRadialRetraction.retract b x, v) ∈
      e.compactSphereTubeDomain f (boundaryComplementOperator A.transverse) R) :
    fderiv ℝ (e.compactCurvedDiskProduct f D A R χ) (x, v) =
      fderiv ℝ (e.compactCurvedCollarModel f (boundaryComplementOperator A.transverse) R b)
        (x, v) := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith)
  have heq (y : Vector 4) (hy : y ∈ closedBall (0 : Vector 4) 1)
      (hyr : χ.rOut ≤ ‖y‖) (w : Vector d) :
      e.compactCurvedDiskProduct f D A R χ (y, w) =
        e.compactCurvedCollarModel f (boundaryComplementOperator A.transverse) R b (y, w) :=
    e.compactCurvedDiskProduct_collar f D A R χ hCb (hχ.trans_le hyr)
      (hc y hy hyr).1 (hc y hy hyr).2 hyr w
  exact fderiv_eq_of_closedDisk_collar _ _ χ.rOut heq hx hxr v
    ((e.contDiffAt_compactCurvedDiskProduct f D A R χ hf hx v hp).differentiableAt (by simp))
    ((e.contDiffAt_compactCurvedCollarModel f (boundaryComplementOperator A.transverse) R b hf
      (contMDiff_boundaryComplementOperator A.transverse A.smooth_transverse)
      hx0 v hp).differentiableAt (by simp))

include hf hCb hχ hc in
theorem compactCollarNormalFrame_normal_product {x : Vector 4}
    (hx : x ∈ closedBall (0 : Vector 4) 1) (hxr : χ.rOut < ‖x‖) (v : Vector d)
    (hp : (SphereRadialRetraction.retract b x, v) ∈
      e.compactSphereTubeDomain f (boundaryComplementOperator A.transverse) R) :
    (e.compactCollarNormalFrame a f (boundaryComplementOperator A.transverse) R b (x, v)).range ≤
      (fderiv ℝ (e.compactCurvedDiskProduct f D A R χ) (x, v)).rangeᗮ := by
  rw [e.fderiv_compactCurvedDiskProduct_eq_collarModel f hf D A R χ hCb hχ hc hx hxr v hp]
  have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith)
  exact e.compactCollarNormalFrame_normal_model a f (boundaryComplementOperator A.transverse)
    R b hf (contMDiff_boundaryComplementOperator A.transverse A.smooth_transverse) hx0 v hp

end NoExoticSixSphere.EuclideanEmbedding
