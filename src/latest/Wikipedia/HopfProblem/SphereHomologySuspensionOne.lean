import Wikipedia.HopfProblem.SphereHomologySuspensionOneTopology
import Wikipedia.HopfProblem.SphereHomologySuspensionOneZero
import Wikipedia.HopfProblem.CuspCentralHomologySuspensionMayerVietoris
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# First integral homology of the genuine suspension of a path-connected space

The actual open cones cover the original unreduced suspension and have
proved contractions. Singular Mayer--Vietoris therefore identifies `H₁`
with the kernel of the actual degree-zero overlap map. The middle band
is path connected, so its first inclusion induces an injective `H₀` map.
The kernel, and hence the original suspension's first homology, is zero.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.SphereHomology

open CuspCentralHomology SingularMayerVietoris PeriodTorusHigherHomology

variable (X : Type) [TopologicalSpace X]

local notation "U" => (Suspension.northOpen : Set (Suspension X))
local notation "V" => (Suspension.southOpen : Set (Suspension X))

section Nonempty

variable [Nonempty X]

/-- The actual two-cone connecting map identifies first homology with the actual overlap kernel. -/
def suspensionHomologyOneEquivKernel :
    SingularHomology (Suspension X) 1 ≃ₗ[ℤ] LinearMap.ker (leftHomologyMap U V 0) :=
  contractibleCoverHomologyOneEquivKernel U V Suspension.northOpen_isOpen
    Suspension.southOpen_isOpen Suspension.open_cover

/-- This equivalence retains the actual singular Mayer--Vietoris connecting homomorphism. -/
@[simp] theorem suspensionHomologyOneEquivKernel_coe
    (a : SingularHomology (Suspension X) 1) :
    (suspensionHomologyOneEquivKernel X a : SingularHomology (Suspension.middleBand X) 0) =
      connectingHomomorphism U V Suspension.northOpen_isOpen
        Suspension.southOpen_isOpen Suspension.open_cover 0 a := rfl

end Nonempty

section Connected

variable [PathConnectedSpace X]

/-- The actual first inclusion on degree-zero band homology makes the full overlap map injective. -/
theorem suspensionLeftHomologyMap_zero_injective :
    Function.Injective (leftHomologyMap U V 0) :=
  leftHomologyMap_zero_injective U V

/-- The two actual augmentation coordinates have the precise Mayer--Vietoris difference sign. -/
theorem suspensionLeftHomologyMap_zero_coordinates
    (a : SingularHomology (Suspension.middleBand X) 0) :
    (connectedHomologyZeroEquiv U (leftHomologyMap U V 0 a).1,
        connectedHomologyZeroEquiv V (leftHomologyMap U V 0 a).2) =
      (suspensionMiddleBandHomologyZeroEquiv X a,
        -suspensionMiddleBandHomologyZeroEquiv X a) := by
  simpa only [suspensionMiddleBandHomologyZeroEquiv_eq_connectedHomologyZeroEquiv] using
    leftHomologyMap_zero_coordinates U V a

theorem suspensionLeftHomologyMap_zero_ker :
    LinearMap.ker (leftHomologyMap U V 0) = ⊥ :=
  leftHomologyMap_zero_ker U V

/-- The genuine unreduced suspension of any path-connected space has zero
first integral homology. -/
theorem suspension_homology_one_subsingleton :
    Subsingleton (SingularHomology (Suspension X) 1) := by
  let : Subsingleton (LinearMap.ker (leftHomologyMap U V 0)) := by
    rw [suspensionLeftHomologyMap_zero_ker X]
    infer_instance
  exact (suspensionHomologyOneEquivKernel X).injective.subsingleton

theorem suspension_homology_one_isZero : IsZero (SingularHomology (Suspension X) 1) := by
  let := suspension_homology_one_subsingleton X
  exact ModuleCat.isZero_of_subsingleton _

/-- The actual first homology is explicitly equivalent to the zero free coefficient module. -/
def suspensionHomologyOneEquivZero :
    SingularHomology (Suspension X) 1 ≃ₗ[ℤ] (Fin 0 → ℤ) := by
  let := suspension_homology_one_subsingleton X
  exact LinearEquiv.ofSubsingleton _ _

theorem suspension_homology_one_free : Module.Free ℤ (SingularHomology (Suspension X) 1) :=
  Module.Free.of_equiv (suspensionHomologyOneEquivZero X).symm

theorem suspension_homology_one_finite : Module.Finite ℤ (SingularHomology (Suspension X) 1) :=
  Module.Finite.of_surjective (suspensionHomologyOneEquivZero X).symm.toLinearMap
    (suspensionHomologyOneEquivZero X).symm.surjective

end Connected

end Wikipedia.HopfProblem.SphereHomology
