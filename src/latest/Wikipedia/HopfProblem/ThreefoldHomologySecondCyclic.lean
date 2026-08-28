import Wikipedia.HopfProblem.ThreefoldHomologySecondSource
import Wikipedia.HopfProblem.ThreefoldHomologyCapEliminationFibre
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyDifferenceGroups

/-!
# A genuine integral generator for global second homology

The source-kernel calculation and the literal star exact sequence show
that the original regular fibre surjects onto second homology.  Its
already computed joint monodromy coinvariant is infinite cyclic, with
primitive coordinate `6 (γ ∧ δ) + (u ∧ w)`.  Composing the actual fibre
map gives a surjection from the integers onto global second homology.
This does not yet assert that the resulting generator vanishes.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.SecondDegree

open SingularMayerVietoris PeriodTorusHigherHomology TrianglePeriodFamily
open TrianglePeriodFamily.Homology TrianglePeriodFamily.HomologyDifference
open CapElimination

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The literal normalized regular fibre surjects onto actual global second homology. -/
theorem regularFibre_homologyTwo_surjective :
    Function.Surjective (singularHomologyMap regularFibreIntoSpace 2) :=
  regularFibreIntoSpace_homology_surjective 1
    SecondSource.nativeCapKernelSourceMap_one_surjective regularInclusion_two_surjective

/-- The genuine map from the primitive source coinvariant to global second homology. -/
def homologyTwoCyclicMap : ℤ →ₗ[ℤ] SingularHomology Space 2 :=
  intLinearMapOfAddHom
    { toFun z := singularHomologyMap originalRegularInclusion 2
        (sourceCoinvariantInclusion Dsp 2 (cokernelTwoEquiv.symm z))
      map_zero' := by rw [map_zero, map_zero, map_zero]
      map_add' a b := by rw [map_add, map_add, map_add] }

/-- On every original quotient representative this is exactly the original fibre map. -/
theorem homologyTwoCyclicMap_quotient (a : SingularHomology RealTorus₄ 2) :
    homologyTwoCyclicMap (cokernelTwoEquiv (Submodule.Quotient.mk a)) =
      singularHomologyMap regularFibreIntoSpace 2 a := by
  change singularHomologyMap originalRegularInclusion 2
    (sourceCoinvariantInclusion Dsp 2
      (cokernelTwoEquiv.symm (cokernelTwoEquiv (Submodule.Quotient.mk a)))) = _
  rw [LinearEquiv.symm_apply_apply, sourceCoinvariantInclusion_mk,
    regularFibreIntoSpace_homology, LinearMap.comp_apply]

/-- The cyclic map is represented by the original marked `u ∧ w` fibre class. -/
theorem homologyTwoCyclicMap_apply (z : ℤ) :
    homologyTwoCyclicMap z = singularHomologyMap regularFibreIntoSpace 2
      (FlatTorus.singularH2Coordinates.symm ![0, 0, 0, z, 0, 0]) := by
  change singularHomologyMap originalRegularInclusion 2
    (sourceCoinvariantInclusion Dsp 2 (cokernelTwoEquiv.symm z)) = _
  rw [cokernelTwoEquiv_symm_apply, sourceCoinvariantInclusion_mk,
    regularFibreIntoSpace_homology, LinearMap.comp_apply]

/-- Every native second-homology class is an actual integer multiple of this fibre image. -/
theorem homologyTwoCyclicMap_surjective : Function.Surjective homologyTwoCyclicMap := by
  intro x
  obtain ⟨a, ha⟩ := regularFibre_homologyTwo_surjective x
  exact ⟨cokernelTwoEquiv (Submodule.Quotient.mk a), (homologyTwoCyclicMap_quotient a).trans ha⟩

/-- The exact evaluation of every actual original fibre class in the primitive cyclic marking. -/
theorem regularFibre_homologyTwo_coordinates (a : SingularHomology RealTorus₄ 2) :
    singularHomologyMap regularFibreIntoSpace 2 a =
      homologyTwoCyclicMap
        (6 * FlatTorus.singularH2Coordinates a 2 + FlatTorus.singularH2Coordinates a 3) := by
  rw [← cokernelTwoEquiv_mk]
  exact (homologyTwoCyclicMap_quotient a).symm

/-- The actual image of the original positive `u ∧ w` class. -/
def homologyTwoGenerator : SingularHomology Space 2 := homologyTwoCyclicMap 1

theorem homologyTwoGenerator_eq_fibre :
    homologyTwoGenerator = singularHomologyMap regularFibreIntoSpace 2
      (FlatTorus.singularH2Coordinates.symm ![0, 0, 0, 1, 0, 0]) :=
  homologyTwoCyclicMap_apply 1

/-- The usual integer-multiple description of the actual homology classes. -/
theorem homologyTwoCyclicMap_eq_smul (z : ℤ) :
    homologyTwoCyclicMap z = z • homologyTwoGenerator := by
  simpa [homologyTwoGenerator] using map_zsmul homologyTwoCyclicMap z (1 : ℤ)

/-- Vanishing of this one actual marked class is exactly vanishing of global second homology. -/
theorem homologyTwo_subsingleton_iff_generator_eq_zero :
    Subsingleton (SingularHomology Space 2) ↔ homologyTwoGenerator = 0 := by
  constructor
  · intro h
    exact h.elim _ _
  · intro h
    have hz (x : SingularHomology Space 2) : x = 0 := by
      obtain ⟨z, rfl⟩ := homologyTwoCyclicMap_surjective x
      rw [homologyTwoCyclicMap_eq_smul, h]
      exact @zsmul_zero (SingularHomology Space 2) _ z
    exact ⟨fun x y => (hz x).trans (hz y).symm⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.SecondDegree
