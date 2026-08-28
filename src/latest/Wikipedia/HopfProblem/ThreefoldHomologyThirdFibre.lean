import Wikipedia.HopfProblem.ThreefoldHomologyThirdClasses
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyDifferenceGroups

/-!
# The primitive actual third-fibre image in the regular family

The original source sequence identifies the entire third-fibre image
with its already computed infinite-cyclic coinvariant.  The positive
generator is the original ordered `γ ∧ u ∧ w` class.  These statements
concern the actual regular family, before imposing the remaining
third-degree cap-kernel relation.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.ThirdDegree

open SingularMayerVietoris PeriodTorusHigherHomology TrianglePeriodFamily
open TrianglePeriodFamily.Homology TrianglePeriodFamily.HomologyDifference

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The genuine primitive third-fibre coinvariant included in the actual regular family. -/
def thirdFibreCyclicMap : ℤ →ₗ[ℤ] SingularHomology SpecialRegularFamily 3 :=
  intLinearMapOfAddHom
    { toFun z := sourceCoinvariantInclusion Dsp 3 (cokernelThreeEquiv.symm z)
      map_zero' := by rw [map_zero, map_zero]
      map_add' a b := by rw [map_add, map_add] }

/-- No integer multiple is lost inside the actual regular family. -/
theorem thirdFibreCyclicMap_injective : Function.Injective thirdFibreCyclicMap := by
  intro a b h
  apply cokernelThreeEquiv.symm.injective
  exact sourceCoinvariantInclusion_injective Dsp 3 h

/-- Every original quotient representative retains its genuine fibre inclusion. -/
theorem thirdFibreCyclicMap_quotient (a : SingularHomology RealTorus₄ 3) :
    thirdFibreCyclicMap (cokernelThreeEquiv (Submodule.Quotient.mk a)) =
      singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) 3 a := by
  change sourceCoinvariantInclusion Dsp 3
    (cokernelThreeEquiv.symm (cokernelThreeEquiv (Submodule.Quotient.mk a))) = _
  rw [LinearEquiv.symm_apply_apply, sourceCoinvariantInclusion_mk]

/-- The primitive representative is the original positive ordered `γ ∧ u ∧ w` fibre class. -/
theorem thirdFibreCyclicMap_apply (z : ℤ) :
    thirdFibreCyclicMap z =
      singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) 3
        (FlatTorus.singularH3Coordinates.symm ![z, 0, 0, 0]) := by
  change sourceCoinvariantInclusion Dsp 3 (cokernelThreeEquiv.symm z) = _
  rw [cokernelThreeEquiv_symm_apply, sourceCoinvariantInclusion_mk]

/-- All original third-fibre classes use this exact primitive coordinate. -/
theorem thirdFibre_cyclic_coordinates (a : SingularHomology RealTorus₄ 3) :
    singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) 3 a =
      thirdFibreCyclicMap (FlatTorus.singularH3Coordinates a 0) := by
  rw [← cokernelThreeEquiv_mk]
  exact (thirdFibreCyclicMap_quotient a).symm

/-- The actual source-kernel projection kills precisely this fibre contribution. -/
theorem thirdFibreCyclicMap_source_eq_zero (z : ℤ) :
    sourceKernelProjection Dsp 2 (thirdFibreCyclicMap z) = 0 :=
  (sourceCoinvariantInclusion_kernelProjection_exact Dsp 2).apply_apply_eq_zero
    (cokernelThreeEquiv.symm z)

theorem thirdFibreCyclicMap_eq_zero_iff (z : ℤ) : thirdFibreCyclicMap z = 0 ↔ z = 0 := by
  constructor
  · intro h
    exact thirdFibreCyclicMap_injective (h.trans (map_zero _).symm)
  · rintro rfl
    exact map_zero _

/-- The third-fibre inclusion has exactly the range of this primitive integer map. -/
theorem thirdFibre_range_eq :
    LinearMap.range (singularHomologyMap
      (familyFibreInclusion Dsp normalizedSlitBaseLift) 3) =
        LinearMap.range thirdFibreCyclicMap := by
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    exact ⟨FlatTorus.singularH3Coordinates a 0, (thirdFibre_cyclic_coordinates a).symm⟩
  · rintro x ⟨z, rfl⟩
    exact ⟨FlatTorus.singularH3Coordinates.symm ![z, 0, 0, 0],
      (thirdFibreCyclicMap_apply z).symm⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.ThirdDegree
