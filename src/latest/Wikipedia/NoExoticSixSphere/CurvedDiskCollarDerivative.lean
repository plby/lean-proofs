import Wikipedia.NoExoticSixSphere.CurvedDiskCollar
import Wikipedia.NoExoticSixSphere.ClosedDiskCollarDerivative
import Wikipedia.NoExoticSixSphere.PrescribedCollarNormalFrame

/-!
# The prescribed collar frame is normal to the actual corrected disk product

The exact closed-disk collar formula identifies ordinary derivatives by
unique within-differentiability, including at the boundary. The original
manifold normal frame plus graph axes therefore lies in the actual corrected
normal space. When the corrected derivative is injective, dimensions give
equality with the full normal space.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))
  {T : Vector 4 → Vector ((e.ambientDimension - 6) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)}
  (A : DiskThickening.FramedProduct D.toFun T) (R : TubularRetraction e)
  (χ : ContDiffBump (0 : Vector 4))
  (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (e.normalFrameOnSphere a f s).val)
  (hχ : (1 / 2 : ℝ) < χ.rOut)
  (hc : ∀ y ∈ closedBall (0 : Vector 4) 1, χ.rOut ≤ ‖y‖ →
    D.toFun y = collar b (e.toFun ∘ f) y ∧
      A.transverse y = A.transverse (SphereRadialRetraction.retract b y).val)

include a hf hd hTb hχ hc in
theorem fderiv_curvedDiskProduct_eq_collarModel {x : Vector 4}
    (hx : x ∈ closedBall (0 : Vector 4) 1) (hxr : χ.rOut < ‖x‖) (v : Vector 3)
    (hp : (SphereRadialRetraction.retract b x, v) ∈ e.sphereTubeDomain f A.boundaryTransverse R) :
    fderiv ℝ (e.curvedDiskProduct f D A R χ) (x, v) =
      fderiv ℝ (e.curvedCollarModel f A.boundaryTransverse R b) (x, v) := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith)
  have heq (y : Vector 4) (hy : y ∈ closedBall (0 : Vector 4) 1)
      (hyr : χ.rOut ≤ ‖y‖) (w : Vector 3) :
      e.curvedDiskProduct f D A R χ (y, w) =
        e.curvedCollarModel f A.boundaryTransverse R b (y, w) :=
    e.curvedDiskProduct_collar a f hf hd D A R χ hTb (hχ.trans_le hyr) hyr
      (hc y hy hyr).1 (hc y hy hyr).2 w
  exact fderiv_eq_of_closedDisk_collar _ _ χ.rOut heq hx hxr v
    ((e.contDiffAt_curvedDiskProduct f D A R χ hf hx v hp).differentiableAt (by simp))
    ((e.contDiffAt_curvedCollarModel f A.boundaryTransverse R b hf
      A.contMDiff_boundaryTransverse hx0 v hp).differentiableAt (by simp))

include hf hd hTb hχ hc in
theorem collarNormalFrame_normal_curvedDiskProduct {x : Vector 4}
    (hx : x ∈ closedBall (0 : Vector 4) 1) (hxr : χ.rOut < ‖x‖) (v : Vector 3)
    (hp : (SphereRadialRetraction.retract b x, v) ∈ e.sphereTubeDomain f A.boundaryTransverse R) :
    (e.collarNormalFrame a f A.boundaryTransverse R b (x, v)).range ≤
      (fderiv ℝ (e.curvedDiskProduct f D A R χ) (x, v)).rangeᗮ := by
  rw [e.fderiv_curvedDiskProduct_eq_collarModel a f hf hd D A R χ hTb hχ hc hx hxr v hp]
  have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith)
  exact e.collarNormalFrame_normal_model a f A.boundaryTransverse R b hf
    A.contMDiff_boundaryTransverse hx0 v hp

include hf hd hTb hχ hc in
theorem range_collarNormalFrame_curvedDiskProduct {x : Vector 4}
    (hx : x ∈ closedBall (0 : Vector 4) 1) (hxr : χ.rOut < ‖x‖) (v : Vector 3)
    (hp : (SphereRadialRetraction.retract b x, v) ∈ e.sphereTubeDomain f A.boundaryTransverse R)
    (hi : Injective (fderiv ℝ (e.curvedDiskProduct f D A R χ) (x, v))) :
    (e.collarNormalFrame a f A.boundaryTransverse R b (x, v)).range =
      (fderiv ℝ (e.curvedDiskProduct f D A R χ) (x, v)).rangeᗮ := by
  apply Submodule.eq_of_le_of_finrank_eq
    (e.collarNormalFrame_normal_curvedDiskProduct a f hf hd D A R χ hTb hχ hc hx hxr v hp)
  rw [LinearMap.finrank_range_of_inj (Stiefel.injective
    ⟨e.collarNormalFrame a f A.boundaryTransverse R b (x, v),
      e.norm_collarNormalFrame a f A.boundaryTransverse R b (x, v)⟩),
    finrank_euclideanSpace_fin]
  have h := (fderiv ℝ (e.curvedDiskProduct f D A R χ) (x, v)).range.finrank_add_finrank_orthogonal
  simp only [LinearMap.finrank_range_of_inj hi, Module.finrank_prod,
    finrank_euclideanSpace_fin] at h
  have hN := e.dimension_le_ambient (f b)
  omega

end NoExoticSixSphere.EuclideanEmbedding
