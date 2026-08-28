import Wikipedia.HopfProblem.MappingTorusHomologyCoveringMap
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCrossProductConnecting

/-!
# Extending a circle cross-product formula to actual homology

The actual circle-product exact sequence shows that subtracting the positive
circle cross product of a class's boundary leaves a section class. Consequently,
a linear map which vanishes on section classes is determined by its values on
positive circle cross products.

For the actual finite cyclic map, vanishing on sections is already proved. The
last two lemmas isolate the cross-product computation which remains necessary
to obtain a formula on all homology classes; they do not assume that computation
without displaying it as a hypothesis.
-/

noncomputable section

namespace Wikipedia.HopfProblem.MappingTorusHomology.Covering

open SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomology.CircleTopology

variable {X : Type} [TopologicalSpace X]
variable {A : Type*} [AddCommGroup A] [Module ℤ A]

/-- Removing the actual positive cross product leaves a class from the section. -/
theorem sub_cross_boundary_mem_range_circleSection (n : ℕ)
    (a : SingularHomology (Circle × X) (n + 1)) :
    a - positiveCircleCross X n (circleBoundary X n a) ∈
      LinearMap.range (circleSectionHomology X (n + 1)) := by
  rw [circleBoundary_exact]
  change circleBoundary X n (a - positiveCircleCross X n (circleBoundary X n a)) = 0
  rw [map_sub, circleBoundary_positiveCircleCross, sub_self]

/-- A section-zero linear map is determined pointwise by its cross-product formula. -/
theorem eq_comp_circleBoundary_of_section_cross_apply (n : ℕ)
    (L : SingularHomology (Circle × X) (n + 1) →ₗ[ℤ] A)
    (N : SingularHomology X n →ₗ[ℤ] A)
    (hsec : ∀ b, L (circleSectionHomology X (n + 1) b) = 0)
    (hcross : ∀ b, L (positiveCircleCross X n b) = N b)
    (a : SingularHomology (Circle × X) (n + 1)) :
    L a = N (circleBoundary X n a) := by
  obtain ⟨b, hb⟩ := sub_cross_boundary_mem_range_circleSection n a
  have h := hsec b
  rw [hb, map_sub, hcross] at h
  exact sub_eq_zero.mp h

/-- The corresponding equality of actual integral linear maps. -/
theorem eq_comp_circleBoundary_of_section_cross (n : ℕ)
    (L : SingularHomology (Circle × X) (n + 1) →ₗ[ℤ] A)
    (N : SingularHomology X n →ₗ[ℤ] A)
    (hsec : ∀ b, L (circleSectionHomology X (n + 1) b) = 0)
    (hcross : ∀ b, L (positiveCircleCross X n b) = N b) :
    L = N.comp (circleBoundary X n) := by
  ext a
  exact eq_comp_circleBoundary_of_section_cross_apply n L N hsec hcross a

variable [CompactSpace X] [T2Space X]
  (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1)

/-- A proved cross-product formula suffices for the actual finite cyclic map.
Its section contribution vanishes by the actual Wang exact sequence. -/
theorem wangBoundary_productCover_eq_of_cross (n : ℕ)
    (N : SingularHomology X n →ₗ[ℤ] SingularHomology X n)
    (hcross : ∀ b, wangBoundary B.symm n
      (productCoverHomology m B hB (n + 1) (positiveCircleCross X n b)) = N b) :
    (wangBoundary B.symm n).comp (productCoverHomology m B hB (n + 1)) =
      N.comp (circleBoundary X n) := by
  apply eq_comp_circleBoundary_of_section_cross n
  · intro b
    exact wangBoundary_productCover_circleSection_apply m B hB n b
  · exact hcross

/-- The preceding actual-map extension, evaluated on an arbitrary homology class. -/
theorem wangBoundary_productCover_eq_of_cross_apply (n : ℕ)
    (N : SingularHomology X n →ₗ[ℤ] SingularHomology X n)
    (hcross : ∀ b, wangBoundary B.symm n
      (productCoverHomology m B hB (n + 1) (positiveCircleCross X n b)) = N b)
    (a : SingularHomology (Circle × X) (n + 1)) :
    wangBoundary B.symm n (productCoverHomology m B hB (n + 1) a) =
      N (circleBoundary X n a) :=
  LinearMap.congr_fun (wangBoundary_productCover_eq_of_cross m B hB n N hcross) a

end Wikipedia.HopfProblem.MappingTorusHomology.Covering
