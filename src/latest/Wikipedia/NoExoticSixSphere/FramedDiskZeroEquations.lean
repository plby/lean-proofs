import Wikipedia.NoExoticSixSphere.FramedCollaredDiskQuadraticValue
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Defining equations supply the disk-frame transversality

An ambient disk lying in a zero set has derivative killed by the actual
equation differential, including at its boundary. This uses uniqueness
of the derivative within the closed ball, not a nonexistent smooth map
from an open neighborhood into a manifold boundary. An actual right
inverse frame of the equation differential is injective and transverse
to that disk derivative. The framed collar theorem then gives zero
for the original geometric quadratic value.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CollaredDiskFrame

open GLOrthonormalization

theorem uniqueDiffOn_unitDisk : UniqueDiffOn ℝ (Metric.closedBall (0 : Vector 4) 1) := by
  apply uniqueDiffOn_convex (convex_closedBall (0 : Vector 4) 1)
  have hball : Metric.ball (0 : Vector 4) 1 ⊆ interior (Metric.closedBall 0 1) :=
    interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball
  exact ⟨0, hball (Metric.mem_ball_self zero_lt_one)⟩

variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

theorem equation_derivative_comp_zero
    (F : Vector 4 → E) (P : E → K)
    (hF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x)
    (hP : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ P (F x))
    (hzero : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, P (F x) = 0)
    (x : Vector 4) (hx : x ∈ Metric.closedBall (0 : Vector 4) 1) :
    (fderiv ℝ P (F x)).comp (fderiv ℝ F x) = 0 := by
  have hc := ((hP x hx).differentiableAt (by simp)).hasFDerivAt.comp x
    ((hF x hx).differentiableAt (by simp)).hasFDerivAt
  have hz : HasFDerivWithinAt (P ∘ F) (0 : Vector 4 →L[ℝ] K)
      (Metric.closedBall 0 1) x :=
    (hasFDerivWithinAt_const (0 : K) x (Metric.closedBall 0 1)).congr hzero (hzero x hx)
  exact (uniqueDiffOn_unitDisk x hx).eq hc.hasFDerivWithinAt hz

theorem rightInverse_injective (B : E →L[ℝ] K) (A : K →L[ℝ] E)
    (hBA : ∀ u, B (A u) = u) : Injective A := by
  intro u v h
  exact (hBA u).symm.trans ((congrArg B h).trans (hBA v))

theorem rightInverse_disjoint_disk (B : E →L[ℝ] K) (A : K →L[ℝ] E)
    (D : Vector 4 →L[ℝ] E) (hBA : ∀ u, B (A u) = u) (hBD : B.comp D = 0) :
    Disjoint A.range D.range := by
  apply Submodule.disjoint_def.mpr
  rintro _ ⟨u, rfl⟩ ⟨v, hv⟩
  have hu : u = 0 := by
    calc
      u = B (A u) := (hBA u).symm
      _ = B (D v) := congrArg B hv.symm
      _ = 0 := congrArg (fun L : Vector 4 →L[ℝ] K ↦ L v) hBD
  rw [hu, map_zero]

end NoExoticSixSphere.CollaredDiskFrame

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization CollaredDiskFrame
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (r : TubularRetraction e) (m : M) [Subsingleton (π_ 2 M m)]

theorem quadraticValue_zero_of_framed_disk_equations
    (f : C(Sphere 3, M)) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (F : Vector 4 → Vector e.ambientDimension × ℝ)
    (hF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x)
    (hDF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, Injective (fderiv ℝ F x))
    (hb : ∀ s : Sphere 3, F s.val = (e.toFun (f s), 0))
    (P : Vector e.ambientDimension × ℝ → e.NormalModel)
    (hP : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ P (F x))
    (hzero : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, P (F x) = 0)
    (A : C(Disk (E := Vector 4), e.NormalModel →L[ℝ] (Vector e.ambientDimension × ℝ)))
    (hPA : ∀ x u, fderiv ℝ P (F x.val) (A x u) = u)
    (hAb : ∀ s, A (boundaryToDisk s) =
      (ContinuousLinearMap.inl ℝ (Vector e.ambientDimension) ℝ).comp (a.ambient (f s)))
    (hheight : (∀ s : Sphere 3, 0 < (fderiv ℝ F s.val s.val).2) ∨
      (∀ s : Sphere 3, (fderiv ℝ F s.val s.val).2 < 0)) :
    e.modTwoHomologyQuadraticForm a r m (SixSphereMiddleParity.sphereClass f) = 0 := by
  apply e.quadraticValue_zero_of_framed_collared_disk a r m f hf hi hd F hF hDF hb A
    (fun x ↦ rightInverse_injective (fderiv ℝ P (F x.val)) (A x) (hPA x)) ?_ hAb hheight
  intro x
  exact rightInverse_disjoint_disk (fderiv ℝ P (F x.val)) (A x) (fderiv ℝ F x.val)
    (hPA x) (equation_derivative_comp_zero F P hF hP hzero x.val x.property)

end NoExoticSixSphere.EuclideanEmbedding
