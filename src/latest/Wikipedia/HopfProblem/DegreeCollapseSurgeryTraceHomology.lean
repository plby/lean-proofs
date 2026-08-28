import Wikipedia.HopfProblem.DegreeCollapseSurgeryCoreCell
import Wikipedia.HopfProblem.SphereHomologyVanishing
import Wikipedia.SmoothSixDPoincare.CellAttachmentHomologySequence
import Wikipedia.SmoothSixDPoincare.LinearExactTransport

/-!
# Exact homology of the literal cylinder inclusion into the surgery trace

Present the verified core union as an embedded four-cell attachment. The
comparison with the rounded trace is the identity on ambient points, so
transporting the actual cell sequence computes the literal inclusion map.
In degree three this map is surjective and its kernel is exactly the image
of the original core boundary, with no additional homology classes killed.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TraceCoreAttachment

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
open Wikipedia.SmoothSixDPoincare
open SingularMayerVietoris PeriodTorusHigherHomology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

def corePresentation : EmbeddedCellAttachment (Vector 4)
    ↥(range (UnroundedTrace.cylinderMap A) ∪ range (coreCellMap A)) :=
  EmbeddedCellAttachment.ofUnion (range (UnroundedTrace.cylinderMap A)) (coreCellMap A)
    (isCompact_range (UnroundedTrace.cylinderMap A).continuous).isClosed
    A.disk.embedded (coreCellMap_in_cylinder_iff A hR)

def cylinderOldHomeomorph :
    range (UnroundedTrace.cylinderMap A) ≃ₜ (corePresentation A hR).old where
  toFun x := ⟨⟨x.val, Or.inl x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def coreBoundary : C(Sphere 3, range (UnroundedTrace.cylinderMap A)) :=
  ⟨fun s ↦ ⟨A.disk.toFun s.val,
    (coreCellMap_in_cylinder_iff A hR
      ⟨s.val, sphere_subset_closedBall s.property⟩).mpr
        (mem_sphere_zero_iff_norm.mp s.property)⟩,
    (A.disk.smooth.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem coreBoundary_ambient (s : Sphere 3) :
    (coreBoundary A hR s).val = e.heightCylinder (f s, 0) := by
  change A.disk.toFun s.val = _
  rw [A.disk.boundary, e.heightCylinder_zero]
  rfl

theorem presentation_attaching : (corePresentation A hR).attachingSphere =
    (cylinderOldHomeomorph A hR).toHomotopyEquiv.toFun.comp (coreBoundary A hR) := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  apply Subtype.ext
  rfl

def cylinderInclusion : C(range (UnroundedTrace.cylinderMap A), ambientSet A) :=
  ⟨fun x ↦ ⟨x.val, unrounded_subset A (Or.inl x.property)⟩,
    continuous_subtype_val.subtype_mk _⟩

def cylinderHomologyEquiv (n : ℕ) :
    SingularHomology (range (UnroundedTrace.cylinderMap A)) n ≃ₗ[ℤ]
      SingularHomology (corePresentation A hR).old n :=
  homotopyEquivHomologyEquiv (cylinderOldHomeomorph A hR).toHomotopyEquiv n

def coreHomologyEquiv (n : ℕ) :
    SingularHomology ↥(range (UnroundedTrace.cylinderMap A) ∪ range (coreCellMap A)) n ≃ₗ[ℤ]
      SingularHomology (ambientSet A) n :=
  homotopyEquivHomologyEquiv (coreUnionTraceHomotopyEquiv A hR) n

theorem attachingHomology_compare (n : ℕ) (u : SingularHomology (Sphere 3) n) :
    (corePresentation A hR).attachingHomologyMap n u =
      cylinderHomologyEquiv A hR n (singularHomologyMap (coreBoundary A hR) n u) := by
  change singularHomologyMap (corePresentation A hR).attachingSphere n u = _
  rw [presentation_attaching, singularHomologyMap_comp, LinearMap.comp_apply]
  rfl

theorem old_homology_compare (n : ℕ)
    (u : SingularHomology (range (UnroundedTrace.cylinderMap A)) n) :
    coreHomologyEquiv A hR n ((corePresentation A hR).oldHomologyMap n
      (cylinderHomologyEquiv A hR n u)) =
        singularHomologyMap (cylinderInclusion A) n u := by
  let B := coreUnionTraceHomotopyEquiv A hR
  let old := subtypeInclusion (corePresentation A hR).old
  have hmaps : (B.toFun.comp old).comp
      (cylinderOldHomeomorph A hR).toHomotopyEquiv.toFun = cylinderInclusion A := by
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (coreUnionTraceHomotopyEquiv_ambient A hR _)
  change singularHomologyMap B.toFun n
    (singularHomologyMap old n (singularHomologyMap
      (cylinderOldHomeomorph A hR).toHomotopyEquiv.toFun n u)) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    ← LinearMap.comp_apply, ← singularHomologyMap_comp, hmaps]

theorem cylinder_inclusion_exact (n : ℕ) (hn : n ≠ 0) :
    LinearMap.range (singularHomologyMap (coreBoundary A hR) n) =
      LinearMap.ker (singularHomologyMap (cylinderInclusion A) n) := by
  refine HomologyTransport.exact_of_equivalences (LinearEquiv.refl ℤ _)
    (cylinderHomologyEquiv A hR n).symm (coreHomologyEquiv A hR n)
    ((corePresentation A hR).attachingHomologyMap n)
    ((corePresentation A hR).oldHomologyMap n)
    (singularHomologyMap (coreBoundary A hR) n) _ ?_ ?_
    ((corePresentation A hR).cell_exact_at_old n hn)
  · intro u
    change singularHomologyMap (coreBoundary A hR) n u =
      (cylinderHomologyEquiv A hR n).symm
        ((corePresentation A hR).attachingHomologyMap n u)
    rw [attachingHomology_compare, LinearEquiv.symm_apply_apply]
  · intro u
    have h := old_homology_compare A hR n ((cylinderHomologyEquiv A hR n).symm u)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

include hR in
theorem cylinder_inclusion_surjective_three :
    Surjective (singularHomologyMap (cylinderInclusion A) 3) := by
  let : Subsingleton (SingularHomology (Sphere 3) 2) :=
    SphereHomology.unitSphere_homology_subsingleton 2 2 (by decide) (by decide)
  have hsurj : Surjective ((corePresentation A hR).oldHomologyMap 3) := by
    intro u
    have hu : u ∈ LinearMap.ker ((corePresentation A hR).cellConnectingMap 2) :=
      Subsingleton.elim _ _
    rw [← (corePresentation A hR).cell_exact_at_ambient 2] at hu
    exact hu
  intro u
  obtain ⟨x, hx⟩ := hsurj ((coreHomologyEquiv A hR 3).symm u)
  refine ⟨(cylinderHomologyEquiv A hR 3).symm x, ?_⟩
  have h := old_homology_compare A hR 3 ((cylinderHomologyEquiv A hR 3).symm x)
  rw [LinearEquiv.apply_symm_apply, hx, LinearEquiv.apply_symm_apply] at h
  exact h.symm

end Wikipedia.HopfProblem.DegreeCollapse.TraceCoreAttachment
