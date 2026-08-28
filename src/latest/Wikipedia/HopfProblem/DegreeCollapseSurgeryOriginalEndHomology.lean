import Wikipedia.HopfProblem.DegreeCollapseSurgeryCylinder
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The exact original-end middle-homology quotient of a framed surgery trace

Transport the verified cell sequence through the actual top-cylinder
homotopy equivalence. The attaching map is compared by the genuine height
homotopy, and the forward inclusion is exactly `RoundedTrace.topMap`.
Thus the original end surjects onto the trace in degree three, with kernel
the integral span of the original sphere class. This computes the trace,
not yet the homology of its other boundary component or a framed filling.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TraceCoreAttachment

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
open Wikipedia.SmoothSixDPoincare
open SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  (f : C(Sphere 3, M)) (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

def originalEndHomologyEquiv (n : ℕ) :
    SingularHomology M n ≃ₗ[ℤ] SingularHomology (range (UnroundedTrace.cylinderMap A)) n :=
  homotopyEquivHomologyEquiv (topCylinderHomotopyEquiv A) n

theorem boundary_homology_compare (n : ℕ) (u : SingularHomology (Sphere 3) n) :
    singularHomologyMap (coreBoundary A hR) n u =
      originalEndHomologyEquiv f A n (singularHomologyMap f n u) := by
  have h := homotopic_homologyMap (top_sphere_homotopic_boundary f A hR) n
  rw [singularHomologyMap_comp] at h
  exact (LinearMap.congr_fun h u).symm

theorem topMap_homology_compare (n : ℕ) (u : SingularHomology M n) :
    singularHomologyMap (topMap A) n u =
      singularHomologyMap (cylinderInclusion A) n (originalEndHomologyEquiv f A n u) := by
  rw [← cylinderInclusion_comp_top A, singularHomologyMap_comp]
  rfl

include hR in
theorem topMap_homology_exact (n : ℕ) (hn : n ≠ 0) :
    LinearMap.range (singularHomologyMap f n) =
      LinearMap.ker (singularHomologyMap (topMap A) n) := by
  refine HomologyTransport.exact_of_equivalences (LinearEquiv.refl ℤ _)
    (originalEndHomologyEquiv f A n).symm (LinearEquiv.refl ℤ _)
    (singularHomologyMap (coreBoundary A hR) n)
    (singularHomologyMap (cylinderInclusion A) n)
    (singularHomologyMap f n) (singularHomologyMap (topMap A) n) ?_ ?_
    (cylinder_inclusion_exact A hR n hn)
  · intro u
    change singularHomologyMap f n u =
      (originalEndHomologyEquiv f A n).symm (singularHomologyMap (coreBoundary A hR) n u)
    rw [boundary_homology_compare, LinearEquiv.symm_apply_apply]
  · intro u
    change singularHomologyMap (topMap A) n ((originalEndHomologyEquiv f A n).symm u) = _
    rw [topMap_homology_compare, LinearEquiv.apply_symm_apply]
    rfl

include hR in
theorem topMap_homology_surjective_three : Surjective (singularHomologyMap (topMap A) 3) := by
  intro u
  obtain ⟨v, hv⟩ := cylinder_inclusion_surjective_three A hR u
  refine ⟨(originalEndHomologyEquiv f A 3).symm v, ?_⟩
  rw [topMap_homology_compare, LinearEquiv.apply_symm_apply, hv]

def originalSphereClass : SingularHomology M 3 := singularHomologyMap f 3 (unitSphereTopClass 2)

theorem originalSphereHomology_range :
    LinearMap.range (singularHomologyMap f 3) = Submodule.span ℤ {originalSphereClass f} := by
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨k, rfl⟩ := unitSphereTopClass_generates 2 v
    rw [map_zsmul]
    exact Submodule.mem_span_singleton.mpr
      ⟨k, int_smul_eq_zsmul (SingularHomology M 3).isModule k (originalSphereClass f)⟩
  · intro hu
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hu
    refine ⟨k • unitSphereTopClass 2, ?_⟩
    rw [map_zsmul]
    exact (int_smul_eq_zsmul (SingularHomology M 3).isModule k
      (originalSphereClass f)).symm.trans hk

include hR in
theorem topMap_three_kernel :
    LinearMap.ker (singularHomologyMap (topMap A) 3) =
      Submodule.span ℤ {originalSphereClass f} := by
  rw [← topMap_homology_exact f A hR 3 (by decide), originalSphereHomology_range]

def traceMiddleHomologyEquiv :
    (SingularHomology M 3 ⧸ Submodule.span ℤ {originalSphereClass f}) ≃ₗ[ℤ]
      SingularHomology (ambientSet A) 3 := by
  let e₁ := Submodule.quotEquivOfEq _ _ (topMap_three_kernel f A hR).symm
  let e₂ := (singularHomologyMap (topMap A) 3).quotKerEquivOfSurjective
    (topMap_homology_surjective_three f A hR)
  let e₃ := e₁.trans e₂
  let ea : (SingularHomology M 3 ⧸ Submodule.span ℤ {originalSphereClass f}) ≃+
      SingularHomology (ambientSet A) 3 :=
    { toEquiv := e₃.toEquiv
      map_add' := fun x y ↦ e₃.map_add x y }
  exact ea.toIntLinearEquiv

theorem traceMiddleHomologyEquiv_mk (u : SingularHomology M 3) :
    traceMiddleHomologyEquiv f A hR (Submodule.Quotient.mk u) =
      singularHomologyMap (topMap A) 3 u := by
  change (singularHomologyMap (topMap A) 3).quotKerEquivOfSurjective
    (topMap_homology_surjective_three f A hR)
    (Submodule.quotEquivOfEq _ _ (topMap_three_kernel f A hR).symm
      (Submodule.Quotient.mk u)) = _
  rw [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

end Wikipedia.HopfProblem.DegreeCollapse.TraceCoreAttachment
