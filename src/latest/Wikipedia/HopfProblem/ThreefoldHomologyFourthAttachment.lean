import Wikipedia.HopfProblem.ThreefoldHomologyFourthSource
import Wikipedia.HopfProblem.ThreefoldHomologyFourthFibre
import Wikipedia.HopfProblem.ThreefoldHomologyCapEliminationFibre
import Wikipedia.HopfProblem.ThreefoldHomologyFifthDegree

/-!
# The actual fourth attachment map is an integral isomorphism

The genuine cap kernels cover the source kernel, and their actual
regular images contain the primitive positive fourth-fibre class.
Exactness therefore gives surjectivity of the original signed star map.
The already proved vanishing of fifth homology gives its injectivity.
The next connecting homomorphism then identifies fourth homology with
the genuine third attachment kernel, without asserting that kernel zero.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FourthDegree

open SingularMayerVietoris CapElimination

/-- Every actual fourth regular class is a sum of original native cap-kernel images. -/
theorem nativeCapKernelRegularMap_four_surjective :
    Function.Surjective (nativeCapKernelRegularMap 4) :=
  nativeCapKernelRegularMap_surjective_of_fibre_range 3
    FourthSource.nativeCapKernelSourceMap_three_surjective FourthFibre.fibre_range_le

/-- The full original signed fourth attachment map is onto over the integers. -/
theorem starLeft_four_surjective : Function.Surjective (starLeftHomologyMap 4) :=
  starLeft_surjective_of_nativeCapKernel 4 nativeCapKernelRegularMap_four_surjective

/-- Its actual kernel is zero by the already proved native fifth-homology vanishing. -/
theorem starLeft_four_injective : Function.Injective (starLeftHomologyMap 4) := by
  intro a b hab
  have hz : starLeftHomologyMap 4 (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := (star_exact_at_intersection 4 (a - b)).mp hz
  rw [FifthDegree.homologyFive_eq_zero c, map_zero] at hc
  exact sub_eq_zero.mp hc.symm

/-- This is bijectivity of the literal original star map, not a substituted matrix. -/
theorem starLeft_four_bijective : Function.Bijective (starLeftHomologyMap 4) :=
  ⟨starLeft_four_injective, starLeft_four_surjective⟩

/-- The corresponding integral linear equivalence has the original attachment map as forward map. -/
def starLeftFourthEquiv : StarOverlapHomology 4 ≃ₗ[ℤ] StarPairHomology 4 :=
  LinearEquiv.ofBijective (starLeftHomologyMap 4) starLeft_four_bijective

@[simp] theorem starLeftFourthEquiv_toLinearMap :
    starLeftFourthEquiv.toLinearMap = starLeftHomologyMap 4 := rfl

/-- The actual sum of fourth-degree piece inclusions consequently vanishes. -/
theorem starRight_four_eq_zero : starRightHomologyMap 4 = 0 := by
  apply LinearMap.ext
  intro a
  obtain ⟨b, rfl⟩ := starLeft_four_surjective a
  exact (star_exact_at_pair 4).apply_apply_eq_zero b

/-- The original connecting homomorphism loses no global fourth-homology class. -/
theorem connecting_three_injective : Function.Injective (starConnectingHomomorphism 3) := by
  intro a b hab
  have hz : starConnectingHomomorphism 3 (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := (star_exact_at_ambient 3 (a - b)).mp hz
  rw [starRight_four_eq_zero, LinearMap.zero_apply] at hc
  exact sub_eq_zero.mp hc.symm

/-- The actual connecting map with its proved native kernel codomain. -/
def connectingIntoKernel :
    SingularHomology Space 4 →ₗ[ℤ] LinearMap.ker (starLeftHomologyMap 3) :=
  (starConnectingHomomorphism 3).codRestrict (LinearMap.ker (starLeftHomologyMap 3))
    (fun a => (star_exact_at_intersection 3).apply_apply_eq_zero a)

theorem connectingIntoKernel_bijective : Function.Bijective connectingIntoKernel := by
  constructor
  · intro a b hab
    exact connecting_three_injective (congrArg Subtype.val hab)
  · intro a
    obtain ⟨b, hb⟩ := (star_exact_at_intersection 3 a.val).mp a.property
    exact ⟨b, Subtype.ext hb⟩

/-- Actual fourth homology is exactly the actual third attachment kernel. -/
def homologyFourKernelEquiv :
    SingularHomology Space 4 ≃ₗ[ℤ] LinearMap.ker (starLeftHomologyMap 3) :=
  LinearEquiv.ofBijective connectingIntoKernel connectingIntoKernel_bijective

@[simp] theorem homologyFourKernelEquiv_val (a : SingularHomology Space 4) :
    (homologyFourKernelEquiv a : StarOverlapHomology 3) = starConnectingHomomorphism 3 a := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FourthDegree
