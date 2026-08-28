import Wikipedia.HopfProblem.DegreeCollapseLowPrescribedCollarFrame
import Wikipedia.HopfProblem.DegreeCollapseLowClosedDiskDerivative

/-!

# Original collar columns lie in the actual corrected product's normal spaces

The exact closed-disk collar identity determines the ordinary derivative,
including boundary points. The original prescribed frame is normal to that
actual derivative. Injectivity and the native dimension count identify its
entire range, without replacing the underlying normal planes.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (f : NoExoticSixSphere.Sphere d → M) (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s))
  {b : NoExoticSixSphere.Sphere d}
  (D : FramedDisk b (e.toFun ∘ f) (fun s => a.orthonormal (f s)))
  (A : LowFramedProduct.FramedProduct (q := 7 - d) D.map D.frame)
  (R : EuclideanEmbedding.TubularRetraction e) (χ : ContDiffBump (0 : Vector (d + 1)))
  (hχ : (1 / 2 : ℝ) < χ.rOut)
  (hc : ∀ y ∈ closedBall (0 : Vector (d + 1)) 1, χ.rOut ≤ ‖y‖ →
    D.map y = collar b (e.toFun ∘ f) y ∧
      A.transverse y = A.transverse (SphereRadialRetraction.retract b y).val)

include a hf hd hχ hc in
theorem fderiv_curvedDiskProduct_eq_collarModel {x : Vector (d + 1)}
    (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) (hxr : χ.rOut < ‖x‖) (v : Vector (7 - d))
    (hp : (SphereRadialRetraction.retract b x, v) ∈ sphereTubeDomain e f A.boundaryTransverse R) :
    fderiv ℝ (curvedDiskProduct e f D A R χ) (x, v) =
      fderiv ℝ (curvedCollarModel e f A.boundaryTransverse R b) (x, v) := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith)
  have heq (y : Vector (d + 1)) (hy : y ∈ closedBall (0 : Vector (d + 1)) 1)
      (hyr : χ.rOut ≤ ‖y‖) (w : Vector (7 - d)) :
      curvedDiskProduct e f D A R χ (y, w) =
        curvedCollarModel e f A.boundaryTransverse R b (y, w) :=
    curvedDiskProduct_collar e a f hf hd D A R χ (hχ.trans_le hyr) hyr
      (hc y hy hyr).1 (hc y hy hyr).2 w
  exact LowDiskDerivative.fderiv_eq_of_closedDisk_collar _ _ χ.rOut heq hx hxr v
    ((contDiffAt_curvedDiskProduct e f D A R χ hf hx v hp).differentiableAt (by simp))
    ((contDiffAt_curvedCollarModel e f A.boundaryTransverse R b hf
      A.contMDiff_boundaryTransverse hx0 v hp).differentiableAt (by simp))

include hf hd hχ hc in
theorem collarNormalFrame_normal_curvedDiskProduct {x : Vector (d + 1)}
    (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) (hxr : χ.rOut < ‖x‖) (v : Vector (7 - d))
    (hp : (SphereRadialRetraction.retract b x, v) ∈ sphereTubeDomain e f A.boundaryTransverse R) :
    (collarNormalFrame e a f A.boundaryTransverse R b (x, v)).range ≤
      (fderiv ℝ (curvedDiskProduct e f D A R χ) (x, v)).rangeᗮ := by
  rw [fderiv_curvedDiskProduct_eq_collarModel e a f hf hd D A R χ hχ hc hx hxr v hp]
  have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith)
  exact collarNormalFrame_normal_model e a f A.boundaryTransverse R b hf
    A.contMDiff_boundaryTransverse hx0 v hp

include hf hd hχ hc in
theorem range_collarNormalFrame_curvedDiskProduct {x : Vector (d + 1)}
    (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) (hxr : χ.rOut < ‖x‖) (v : Vector (7 - d))
    (hp : (SphereRadialRetraction.retract b x, v) ∈ sphereTubeDomain e f A.boundaryTransverse R)
    (hi : Injective (fderiv ℝ (curvedDiskProduct e f D A R χ) (x, v))) :
    (collarNormalFrame e a f A.boundaryTransverse R b (x, v)).range =
      (fderiv ℝ (curvedDiskProduct e f D A R χ) (x, v)).rangeᗮ := by
  apply Submodule.eq_of_le_of_finrank_eq
    (collarNormalFrame_normal_curvedDiskProduct e a f hf hd D A R χ hχ hc hx hxr v hp)
  rw [LinearMap.finrank_range_of_inj (Stiefel.injective
    ⟨collarNormalFrame e a f A.boundaryTransverse R b (x, v),
      norm_collarNormalFrame e a f A.boundaryTransverse R b (x, v)⟩),
    finrank_euclideanSpace_fin]
  have h := (fderiv ℝ (curvedDiskProduct e f D A R χ) (x, v)).range.finrank_add_finrank_orthogonal
  simp only [LinearMap.finrank_range_of_inj hi, Module.finrank_prod,
    finrank_euclideanSpace_fin] at h
  have hN := e.dimension_le_ambient (f b)
  have hd7 := sphere_dimension_le_seven f hd b
  omega

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

