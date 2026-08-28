import Wikipedia.HopfProblem.DegreeCollapseSevenPrescribedCollarFrame
import Wikipedia.HopfProblem.DegreeCollapseGeneralClosedDiskDerivative

/-!
# SevenCollarNormalComparison

The exact closed-disk collar identity determines the ordinary derivative even at the boundary. The prescribed original frame consequently lies in the actual corrected normal space; injectivity and dimensions give its full range.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))
  {T : Vector 4 → Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)}
  (A : EightDimensionalFramedProduct.FramedProduct D.toFun T) (R : EuclideanEmbedding.TubularRetraction e)
  (χ : ContDiffBump (0 : Vector 4))
  (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (SevenSurgery.normalFrameOnSphere e a f s).val)
  (hχ : (1 / 2 : ℝ) < χ.rOut)
  (hc : ∀ y ∈ closedBall (0 : Vector 4) 1, χ.rOut ≤ ‖y‖ →
    D.toFun y = collar b (e.toFun ∘ f) y ∧
      A.transverse y = A.transverse (SphereRadialRetraction.retract b y).val)

include a hf hd hTb hχ hc in
theorem fderiv_curvedDiskProduct_eq_collarModel {x : Vector 4}
    (hx : x ∈ closedBall (0 : Vector 4) 1) (hxr : χ.rOut < ‖x‖) (v : Vector 4)
    (hp : (SphereRadialRetraction.retract b x, v) ∈ SevenSurgery.sphereTubeDomain e f A.boundaryTransverse R) :
    fderiv ℝ (SevenSurgery.curvedDiskProduct e f D A R χ) (x, v) =
      fderiv ℝ (SevenSurgery.curvedCollarModel e f A.boundaryTransverse R b) (x, v) := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith)
  have heq (y : Vector 4) (hy : y ∈ closedBall (0 : Vector 4) 1)
      (hyr : χ.rOut ≤ ‖y‖) (w : Vector 4) :
      SevenSurgery.curvedDiskProduct e f D A R χ (y, w) =
        SevenSurgery.curvedCollarModel e f A.boundaryTransverse R b (y, w) :=
    SevenSurgery.curvedDiskProduct_collar e a f hf hd D A R χ hTb (hχ.trans_le hyr) hyr
      (hc y hy hyr).1 (hc y hy hyr).2 w
  exact GeneralDiskDerivative.fderiv_eq_of_closedDisk_collar _ _ χ.rOut heq hx hxr v
    ((SevenSurgery.contDiffAt_curvedDiskProduct e f D A R χ hf hx v hp).differentiableAt (by simp))
    ((SevenSurgery.contDiffAt_curvedCollarModel e f A.boundaryTransverse R b hf
      A.contMDiff_boundaryTransverse hx0 v hp).differentiableAt (by simp))

include hf hd hTb hχ hc in
theorem collarNormalFrame_normal_curvedDiskProduct {x : Vector 4}
    (hx : x ∈ closedBall (0 : Vector 4) 1) (hxr : χ.rOut < ‖x‖) (v : Vector 4)
    (hp : (SphereRadialRetraction.retract b x, v) ∈ SevenSurgery.sphereTubeDomain e f A.boundaryTransverse R) :
    (SevenSurgery.collarNormalFrame e a f A.boundaryTransverse R b (x, v)).range ≤
      (fderiv ℝ (SevenSurgery.curvedDiskProduct e f D A R χ) (x, v)).rangeᗮ := by
  rw [SevenSurgery.fderiv_curvedDiskProduct_eq_collarModel e a f hf hd D A R χ hTb hχ hc hx hxr v hp]
  have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith)
  exact SevenSurgery.collarNormalFrame_normal_model e a f A.boundaryTransverse R b hf
    A.contMDiff_boundaryTransverse hx0 v hp

include hf hd hTb hχ hc in
theorem range_collarNormalFrame_curvedDiskProduct {x : Vector 4}
    (hx : x ∈ closedBall (0 : Vector 4) 1) (hxr : χ.rOut < ‖x‖) (v : Vector 4)
    (hp : (SphereRadialRetraction.retract b x, v) ∈ SevenSurgery.sphereTubeDomain e f A.boundaryTransverse R)
    (hi : Injective (fderiv ℝ (SevenSurgery.curvedDiskProduct e f D A R χ) (x, v))) :
    (SevenSurgery.collarNormalFrame e a f A.boundaryTransverse R b (x, v)).range =
      (fderiv ℝ (SevenSurgery.curvedDiskProduct e f D A R χ) (x, v)).rangeᗮ := by
  apply Submodule.eq_of_le_of_finrank_eq
    (SevenSurgery.collarNormalFrame_normal_curvedDiskProduct e a f hf hd D A R χ hTb hχ hc hx hxr v hp)
  rw [LinearMap.finrank_range_of_inj (Stiefel.injective
    ⟨SevenSurgery.collarNormalFrame e a f A.boundaryTransverse R b (x, v),
      SevenSurgery.norm_collarNormalFrame e a f A.boundaryTransverse R b (x, v)⟩),
    finrank_euclideanSpace_fin]
  have h := (fderiv ℝ (SevenSurgery.curvedDiskProduct e f D A R χ) (x, v)).range.finrank_add_finrank_orthogonal
  simp only [LinearMap.finrank_range_of_inj hi, Module.finrank_prod,
    finrank_euclideanSpace_fin] at h
  have hN := e.dimension_le_ambient (f b)
  omega

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
