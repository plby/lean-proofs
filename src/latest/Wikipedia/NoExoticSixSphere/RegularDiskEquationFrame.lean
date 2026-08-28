import Wikipedia.NoExoticSixSphere.RelativeRightInverseExtension
import Wikipedia.NoExoticSixSphere.FramedDiskZeroEquations
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Constructing the extending frame from regular disk equations

The actual equation differential is a continuous surjective operator
family over the closed disk. Its right inverses extend any prescribed
calibrated boundary columns, with exact equality on the sphere. This
constructs the frame required by the immersed-disk quadratic-vanishing
theorem; the frame and its transversality are no longer hypotheses.

An actual immersed disk satisfying the equations is still required.
-/

noncomputable section

open Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CollaredDiskFrame

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

def diskEquationDifferential (F : Vector 4 → E) (P : E → K)
    (hF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x)
    (hP : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ P (F x)) :
    C(Disk (E := Vector 4), E →L[ℝ] K) where
  toFun x := fderiv ℝ P (F x.val)
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (((hP x.val x.property).continuousAt_fderiv (by simp)).comp
      (hF x.val x.property).continuousAt).comp continuous_subtype_val.continuousAt

theorem exists_disk_equation_frame {N k : ℕ}
    (F : Vector 4 → Vector N × ℝ) (P : Vector N × ℝ → Vector k)
    (hF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x)
    (hP : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ P (F x))
    (hs : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, Surjective (fderiv ℝ P (F x)))
    (a : C(Sphere 3, Vector k →L[ℝ] (Vector N × ℝ)))
    (ha : ∀ s u, fderiv ℝ P (F s.val) (a s u) = u) :
    ∃ A : C(Disk (E := Vector 4), Vector k →L[ℝ] (Vector N × ℝ)),
      (∀ x u, fderiv ℝ P (F x.val) (A x u) = u) ∧
      ∀ s, A (boundaryToDisk s) = a s := by
  have hi : IsClosedEmbedding (boundaryToDisk (E := Vector 4)) :=
    boundaryToDisk.continuous.isClosedEmbedding (fun s t h ↦
      Subtype.ext (congrArg (fun x : Disk (E := Vector 4) ↦ x.val) h))
  exact RelativeRightInverse.exists_extension
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Vector N) ℝ) boundaryToDisk hi
    (diskEquationDifferential F P hF hP) (fun x ↦ hs x.val x.property) a ha

end NoExoticSixSphere.CollaredDiskFrame

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization CollaredDiskFrame

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (r : TubularRetraction e) (m : M) [Subsingleton (π_ 2 M m)]

theorem quadraticValue_zero_of_regular_disk_equations
    (f : C(Sphere 3, M)) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (F : Vector 4 → Vector e.ambientDimension × ℝ)
    (hF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x)
    (hDF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, Injective (fderiv ℝ F x))
    (hb : ∀ s : Sphere 3, F s.val = (e.toFun (f s), 0))
    (P : Vector e.ambientDimension × ℝ → e.NormalModel)
    (hP : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ P (F x))
    (hzero : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, P (F x) = 0)
    (hs : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, Surjective (fderiv ℝ P (F x)))
    (hcal : ∀ s u, fderiv ℝ P (e.toFun (f s), 0) (a.ambient (f s) u, 0) = u)
    (hheight : (∀ s : Sphere 3, 0 < (fderiv ℝ F s.val s.val).2) ∨
      (∀ s : Sphere 3, (fderiv ℝ F s.val s.val).2 < 0)) :
    e.modTwoHomologyQuadraticForm a r m (SixSphereMiddleParity.sphereClass f) = 0 := by
  let aS : C(Sphere 3,
      e.NormalModel →L[ℝ] (Vector e.ambientDimension × ℝ)) :=
    ⟨fun s ↦ (ContinuousLinearMap.inl ℝ (Vector e.ambientDimension) ℝ).comp
      (a.ambient (f s)), continuous_const.clm_comp
        (a.contMDiff_ambient.continuous.comp hf.continuous)⟩
  have hcal' (s : Sphere 3) (u : e.NormalModel) :
      fderiv ℝ P (F s.val) (aS s u) = u := by
    change fderiv ℝ P (F s.val) (a.ambient (f s) u, 0) = u
    rw [hb]
    exact hcal s u
  obtain ⟨A, hA, hAb⟩ := exists_disk_equation_frame F P hF hP hs aS hcal'
  exact e.quadraticValue_zero_of_framed_disk_equations a r m f hf hi hd F hF hDF hb
    P hP hzero A hA hAb hheight

end NoExoticSixSphere.EuclideanEmbedding
