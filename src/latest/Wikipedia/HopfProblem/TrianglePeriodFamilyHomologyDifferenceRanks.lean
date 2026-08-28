import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyDifferenceGroups

/-!
# Integral ranks of actual homology-difference kernels and cokernels

These are the literal submodules and quotients of actual singular homology.
The proved equivalences transfer finite generation, freeness, and the exact
integral ranks; no rationalization or rank assumption is used.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.HomologyDifference

open SpecialPeriods SingularMayerVietoris

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
  TrianglePeriodFamilyHomologyAlgebra.kernelModule

theorem kernelZero_free : Module.Free ℤ (LinearMap.ker (Homology.sourceDifference 0)) :=
  Module.Free.of_equiv kernelZeroEquiv.symm

theorem kernelZero_finite : Module.Finite ℤ (LinearMap.ker (Homology.sourceDifference 0)) :=
  Module.Finite.of_surjective kernelZeroEquiv.symm.toLinearMap kernelZeroEquiv.symm.surjective

theorem kernelZero_finrank : Module.finrank ℤ
    (LinearMap.ker (Homology.sourceDifference 0)) = 2 := by
  rw [kernelZeroEquiv.finrank_eq]
  simp

theorem cokernelZero_free : Module.Free ℤ
    (SingularHomology RealTorus₄ 0 ⧸ LinearMap.range (Homology.sourceDifference 0)) :=
  Module.Free.of_equiv cokernelZeroEquiv.symm

theorem cokernelZero_finite : Module.Finite ℤ
    (SingularHomology RealTorus₄ 0 ⧸ LinearMap.range (Homology.sourceDifference 0)) :=
  Module.Finite.of_surjective cokernelZeroEquiv.symm.toLinearMap
    cokernelZeroEquiv.symm.surjective

theorem cokernelZero_finrank : Module.finrank ℤ
    (SingularHomology RealTorus₄ 0 ⧸ LinearMap.range (Homology.sourceDifference 0)) = 1 := by
  rw [cokernelZeroEquiv.finrank_eq]
  exact Module.finrank_self ℤ

theorem kernelOne_free : Module.Free ℤ (LinearMap.ker (Homology.sourceDifference 1)) :=
  Module.Free.of_equiv kernelOneEquiv.symm

theorem kernelOne_finite : Module.Finite ℤ (LinearMap.ker (Homology.sourceDifference 1)) :=
  Module.Finite.of_surjective kernelOneEquiv.symm.toLinearMap kernelOneEquiv.symm.surjective

theorem kernelOne_finrank : Module.finrank ℤ
    (LinearMap.ker (Homology.sourceDifference 1)) = 5 := by
  rw [kernelOneEquiv.finrank_eq]
  simp

theorem cokernelOne_free : Module.Free ℤ
    (SingularHomology RealTorus₄ 1 ⧸ LinearMap.range (Homology.sourceDifference 1)) :=
  Module.Free.of_equiv cokernelOneEquiv.symm

theorem cokernelOne_finite : Module.Finite ℤ
    (SingularHomology RealTorus₄ 1 ⧸ LinearMap.range (Homology.sourceDifference 1)) :=
  Module.Finite.of_surjective cokernelOneEquiv.symm.toLinearMap
    cokernelOneEquiv.symm.surjective

theorem cokernelOne_finrank : Module.finrank ℤ
    (SingularHomology RealTorus₄ 1 ⧸ LinearMap.range (Homology.sourceDifference 1)) = 1 := by
  rw [cokernelOneEquiv.finrank_eq]
  exact Module.finrank_self ℤ

theorem kernelTwo_free : Module.Free ℤ (LinearMap.ker (Homology.sourceDifference 2)) :=
  Module.Free.of_equiv kernelTwoEquiv.symm

theorem kernelTwo_finite : Module.Finite ℤ (LinearMap.ker (Homology.sourceDifference 2)) :=
  Module.Finite.of_surjective kernelTwoEquiv.symm.toLinearMap kernelTwoEquiv.symm.surjective

theorem kernelTwo_finrank : Module.finrank ℤ
    (LinearMap.ker (Homology.sourceDifference 2)) = 7 := by
  rw [kernelTwoEquiv.finrank_eq]
  simp

theorem cokernelTwo_free : Module.Free ℤ
    (SingularHomology RealTorus₄ 2 ⧸ LinearMap.range (Homology.sourceDifference 2)) :=
  Module.Free.of_equiv cokernelTwoEquiv.symm

theorem cokernelTwo_finite : Module.Finite ℤ
    (SingularHomology RealTorus₄ 2 ⧸ LinearMap.range (Homology.sourceDifference 2)) :=
  Module.Finite.of_surjective cokernelTwoEquiv.symm.toLinearMap
    cokernelTwoEquiv.symm.surjective

theorem cokernelTwo_finrank : Module.finrank ℤ
    (SingularHomology RealTorus₄ 2 ⧸ LinearMap.range (Homology.sourceDifference 2)) = 1 := by
  rw [cokernelTwoEquiv.finrank_eq]
  exact Module.finrank_self ℤ

theorem kernelThree_free : Module.Free ℤ (LinearMap.ker (Homology.sourceDifference 3)) :=
  Module.Free.of_equiv kernelThreeEquiv.symm

theorem kernelThree_finite : Module.Finite ℤ (LinearMap.ker (Homology.sourceDifference 3)) :=
  Module.Finite.of_surjective kernelThreeEquiv.symm.toLinearMap kernelThreeEquiv.symm.surjective

theorem kernelThree_finrank : Module.finrank ℤ
    (LinearMap.ker (Homology.sourceDifference 3)) = 5 := by
  rw [kernelThreeEquiv.finrank_eq]
  simp

theorem cokernelThree_free : Module.Free ℤ
    (SingularHomology RealTorus₄ 3 ⧸ LinearMap.range (Homology.sourceDifference 3)) :=
  Module.Free.of_equiv cokernelThreeEquiv.symm

theorem cokernelThree_finite : Module.Finite ℤ
    (SingularHomology RealTorus₄ 3 ⧸ LinearMap.range (Homology.sourceDifference 3)) :=
  Module.Finite.of_surjective cokernelThreeEquiv.symm.toLinearMap
    cokernelThreeEquiv.symm.surjective

theorem cokernelThree_finrank : Module.finrank ℤ
    (SingularHomology RealTorus₄ 3 ⧸ LinearMap.range (Homology.sourceDifference 3)) = 1 := by
  rw [cokernelThreeEquiv.finrank_eq]
  exact Module.finrank_self ℤ

end Wikipedia.HopfProblem.TrianglePeriodFamily.HomologyDifference

