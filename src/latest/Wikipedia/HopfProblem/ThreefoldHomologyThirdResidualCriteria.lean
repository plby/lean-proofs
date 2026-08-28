import Wikipedia.HopfProblem.ThreefoldHomologyThirdKernel

/-!
# Exact criteria for the actual middle-homology attachment

The original homology groups and the original signed attachment map
are characterized by the uniquely defined genuine residual integer.
These equivalences do not postulate its value: third homology vanishes
exactly when it is a unit, fourth homology vanishes exactly when it is
nonzero, and the original third attachment is bijective exactly when
it is a unit.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.ThirdDegree

open SingularMayerVietoris CapElimination

/-- Actual third homology vanishes exactly when the genuine residual relation is primitive. -/
theorem homologyThree_subsingleton_iff_referenceFibreCoefficient_isUnit :
    Subsingleton (SingularHomology Space 3) ↔ IsUnit referenceFibreCoefficient := by
  rw [homologyThree_subsingleton_iff_generator_eq_zero]
  change homologyThreeCyclicMap 1 = 0 ↔ IsUnit referenceFibreCoefficient
  rw [homologyThreeCyclicMap_eq_zero_iff, isUnit_iff_exists_inv']

/-- Actual fourth homology vanishes exactly when the genuine residual integer is nonzero. -/
theorem homologyFour_subsingleton_iff_referenceFibreCoefficient_ne_zero :
    Subsingleton (SingularHomology Space 4) ↔ referenceFibreCoefficient ≠ 0 := by
  constructor
  · intro hss hr
    let a : LinearMap.ker residualMultiplication := ⟨1, by
      change 1 * referenceFibreCoefficient = 0
      rw [hr, mul_zero]⟩
    have h := hss.elim (homologyFourResidualKernelEquiv.symm a)
      (homologyFourResidualKernelEquiv.symm 0)
    have ha : a = 0 := homologyFourResidualKernelEquiv.symm.injective h
    have hone : (1 : ℤ) = 0 := congrArg Subtype.val ha
    exact one_ne_zero hone
  · intro hr
    have hz (a : SingularHomology Space 4) : a = 0 := by
      apply homologyFourCoefficientMap_injective
      rw [map_zero]
      exact (mul_eq_zero.mp (homologyFourCoefficientMap_mul a)).resolve_right hr
    exact ⟨fun a b => (hz a).trans (hz b).symm⟩

/-- The genuine third native relation has no kernel precisely for a nonzero residual integer. -/
theorem nativeCapKernelRegularMap_three_injective_iff :
    Function.Injective (nativeCapKernelRegularMap 3) ↔ referenceFibreCoefficient ≠ 0 := by
  calc
    Function.Injective (nativeCapKernelRegularMap 3) ↔
        Subsingleton (LinearMap.ker (nativeCapKernelRegularMap 3)) :=
      (Submodule.subsingleton_iff_eq_bot.trans LinearMap.ker_eq_bot).symm
    _ ↔ Subsingleton (LinearMap.ker (starLeftHomologyMap 3)) :=
      (starKernelNativeEquiv 3).toEquiv.subsingleton_congr.symm
    _ ↔ Subsingleton (SingularHomology Space 4) :=
      FourthDegree.homologyFourKernelEquiv.toEquiv.subsingleton_congr.symm
    _ ↔ referenceFibreCoefficient ≠ 0 :=
      homologyFour_subsingleton_iff_referenceFibreCoefficient_ne_zero

/-- Surjectivity of the full native regular relation is equivalent to actual third vanishing. -/
theorem nativeCapKernelRegularMap_three_surjective_iff_homologyThree_subsingleton :
    Function.Surjective (nativeCapKernelRegularMap 3) ↔
      Subsingleton (SingularHomology Space 3) := by
  constructor
  · intro h
    apply homologyThree_subsingleton_iff_generator_eq_zero.mpr
    obtain ⟨a, ha⟩ := h (thirdFibreCyclicMap 1)
    exact (regularInclusion_eq_zero_iff_native 3 _).mpr ⟨a, ha⟩
  · intro h r
    exact (regularInclusion_eq_zero_iff_native 3 r).mp (h.elim _ _)

/-- The full native regular relation is onto exactly for a unit genuine residual coefficient. -/
theorem nativeCapKernelRegularMap_three_surjective_iff :
    Function.Surjective (nativeCapKernelRegularMap 3) ↔ IsUnit referenceFibreCoefficient :=
  nativeCapKernelRegularMap_three_surjective_iff_homologyThree_subsingleton.trans
    homologyThree_subsingleton_iff_referenceFibreCoefficient_isUnit

/-- Bijectivity refers to the original native relation map without a substituted matrix. -/
theorem nativeCapKernelRegularMap_three_bijective_iff :
    Function.Bijective (nativeCapKernelRegularMap 3) ↔ IsUnit referenceFibreCoefficient := by
  constructor
  · intro h
    exact nativeCapKernelRegularMap_three_surjective_iff.mp h.surjective
  · intro h
    exact ⟨nativeCapKernelRegularMap_three_injective_iff.mpr h.ne_zero,
      nativeCapKernelRegularMap_three_surjective_iff.mpr h⟩

/-- The literal original signed third attachment is injective exactly for a nonzero residual. -/
theorem starLeft_three_injective_iff :
    Function.Injective (starLeftHomologyMap 3) ↔ referenceFibreCoefficient ≠ 0 := by
  calc
    Function.Injective (starLeftHomologyMap 3) ↔
        Subsingleton (LinearMap.ker (starLeftHomologyMap 3)) :=
      (Submodule.subsingleton_iff_eq_bot.trans LinearMap.ker_eq_bot).symm
    _ ↔ Subsingleton (SingularHomology Space 4) :=
      FourthDegree.homologyFourKernelEquiv.toEquiv.subsingleton_congr.symm
    _ ↔ referenceFibreCoefficient ≠ 0 :=
      homologyFour_subsingleton_iff_referenceFibreCoefficient_ne_zero

/-- The literal original signed third attachment is onto exactly for a unit residual. -/
theorem starLeft_three_surjective_iff :
    Function.Surjective (starLeftHomologyMap 3) ↔ IsUnit referenceFibreCoefficient := by
  calc
    Function.Surjective (starLeftHomologyMap 3) ↔
        LinearMap.range (starLeftHomologyMap 3) = ⊤ := LinearMap.range_eq_top.symm
    _ ↔ Subsingleton (StarPairHomology 3 ⧸ LinearMap.range (starLeftHomologyMap 3)) :=
      Submodule.Quotient.subsingleton_iff.symm
    _ ↔ Subsingleton (SingularHomology Space 3) :=
      attachmentCokernelEquiv.toEquiv.subsingleton_congr
    _ ↔ IsUnit referenceFibreCoefficient :=
      homologyThree_subsingleton_iff_referenceFibreCoefficient_isUnit

/-- The genuine original third attachment is an isomorphism exactly for a primitive residual. -/
theorem starLeft_three_bijective_iff :
    Function.Bijective (starLeftHomologyMap 3) ↔ IsUnit referenceFibreCoefficient := by
  constructor
  · intro h
    exact starLeft_three_surjective_iff.mp h.surjective
  · intro h
    exact ⟨starLeft_three_injective_iff.mpr h.ne_zero, starLeft_three_surjective_iff.mpr h⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.ThirdDegree
