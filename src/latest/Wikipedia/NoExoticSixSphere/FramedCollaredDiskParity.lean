import Wikipedia.NoExoticSixSphere.CollaredDiskFrameExtension
import Wikipedia.NoExoticSixSphere.ManifoldRawSphereFrame
import Wikipedia.NoExoticSixSphere.SphereAffineFrameDerivative
import Wikipedia.NoExoticSixSphere.ModTwoHomologyQuadraticParity

/-!
# An actual framed immersed boundary disk forces zero geometric parity

The disk operator is the derivative of the supplied smooth map into the
original ambient space times a height line. The supplied frame is defined
over that disk, is transverse to its actual derivative, and restricts
exactly to the prescribed normal frame. Boundary equality gives the
tangential derivative identity by the native chain rule. Positive radial
height and the checked collar homotopy then extend the original twisted
sphere obstruction, proving zero sphere parity and quadratic value.

Existence of such a disk and frame is not asserted for arbitrary classes.
In particular this is not yet boundary-kernel vanishing or Arf detection.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CollaredDiskFrame

open GLOrthonormalization SphereThreeTangentFrame
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {N : ℕ} (F : Vector 4 → Vector N × ℝ)
  (hF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x)

def diskDifferential : C(Disk (E := Vector 4), Vector 4 →L[ℝ] (Vector N × ℝ)) where
  toFun x := fderiv ℝ F x.val
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((hF x.val x.property).continuousAt_fderiv (by simp)).comp
      continuous_subtype_val.continuousAt

def radialDerivativeMap : C(Sphere 3, Vector N × ℝ) where
  toFun s := fderiv ℝ F s.val s.val
  continuous_toFun := ((diskDifferential F hF).continuous.comp
    boundaryToDisk.continuous).clm_apply continuous_subtype_val

include hF in
theorem boundary_tangent_derivative (g : Sphere 3 → Vector N)
    (hg : ContMDiff (𝓡 3) (𝓡 N) ∞ g) (hb : ∀ s, F s.val = (g s, 0))
    (s : Sphere 3) (u : Vector 3) :
    fderiv ℝ F s.val (operator s.val u) = (framedDerivative g s u, 0) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hs : ContMDiff (𝓡 3) (𝓡 4) ∞ (Subtype.val : Sphere 3 → Vector 4) :=
    contMDiff_coe_sphere
  have h₀ := framedDerivative_outer_comp_at F (Subtype.val : Sphere 3 → Vector 4) s
    ((hF s.val (Metric.sphere_subset_closedBall s.property)).differentiableAt (by simp))
    (hs.mdifferentiableAt (by simp))
  rw [framedDerivative_coe] at h₀
  have he : F ∘ (Subtype.val : Sphere 3 → Vector 4) =
      (ContinuousLinearMap.inl ℝ (Vector N) ℝ) ∘ g := funext hb
  rw [he] at h₀
  have h₁ := framedDerivative_outer_comp_at (ContinuousLinearMap.inl ℝ (Vector N) ℝ)
    g s (ContinuousLinearMap.inl ℝ (Vector N) ℝ).differentiableAt
    (hg.mdifferentiableAt (by simp))
  rw [ContinuousLinearMap.fderiv] at h₁
  exact congrArg (fun L : Vector 3 →L[ℝ] (Vector N × ℝ) ↦ L u) (h₀.symm.trans h₁)

end NoExoticSixSphere.CollaredDiskFrame

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SphereThreeTangentFrame CollaredDiskFrame
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem sphereParity_zero_of_framed_collared_disk
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (F : Vector 4 → Vector e.ambientDimension × ℝ)
    (hF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x)
    (hDF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, Injective (fderiv ℝ F x))
    (hb : ∀ s : Sphere 3, F s.val = (e.toFun (f s), 0))
    (A : C(Disk (E := Vector 4), e.NormalModel →L[ℝ] (Vector e.ambientDimension × ℝ)))
    (hA : ∀ x, Injective (A x))
    (hAD : ∀ x, Disjoint (A x).range (fderiv ℝ F x.val).range)
    (hAb : ∀ s, A (boundaryToDisk s) =
      (ContinuousLinearMap.inl ℝ (Vector e.ambientDimension) ℝ).comp (a.ambient (f s)))
    (hheight : ∀ s : Sphere 3, 0 < (fderiv ℝ F s.val s.val).2) :
    e.sphereParity a f hf hi hd = 0 := by
  let aS : C(Sphere 3, e.NormalModel →L[ℝ] Vector e.ambientDimension) :=
    ⟨fun s ↦ a.ambient (f s), a.contMDiff_ambient.continuous.comp hf.continuous⟩
  let TS : C(Sphere 3, Vector 3 →L[ℝ] Vector e.ambientDimension) :=
    ⟨framedDerivative (e.toFun ∘ f), e.continuous_sphereTangentOperator f hf⟩
  let v := (ContinuousMap.fst : C(Vector e.ambientDimension × ℝ, _)).comp
    (radialDerivativeMap F hF)
  let c := (ContinuousMap.snd : C(Vector e.ambientDimension × ℝ, ℝ)).comp
    (radialDerivativeMap F hF)
  have haS : ∀ s, Injective (aS s) := fun s ↦ a.ambient_injective (f s)
  have hTS : ∀ s, Injective (TS s) := e.injective_sphereTangentOperator f hf hd
  have hrS : ∀ s, Disjoint (aS s).range (TS s).range :=
    e.rawSphereNormal_range_disjoint a f hf
  have he : sphereOperatorMap aS TS haS hTS hrS = e.rawSphereFrameOperatorMap a f hf hd := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    rfl
  apply (e.sphereParity_zero_iff_raw_twisted_extension a f hf hd hi).mpr
  rw [← he]
  exact extends_twisted_sphereOperatorMap aS TS v c haS hTS hrS hheight
    A (diskDifferential F hF) hA (fun x ↦ hDF x.val x.property) hAD hAb
    (boundary_tangent_derivative F hF (e.toFun ∘ f) (e.smooth.comp hf) hb)
    (fun _ ↦ rfl)

end NoExoticSixSphere.EuclideanEmbedding
