import Wikipedia.HopfProblem.CuspCentralHomologyTopDegreesMayerVietoris
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCoordinateAlgebra

/-!
# The actual Mayer–Vietoris boundary onto its exact image

For every two-member open cover, the actual connecting homomorphism
surjects onto the kernel of the difference of the intersection inclusions.
Restricting its codomain to this kernel does not change its own kernel.
If the upper-degree homology of both open sets vanishes, this restricted
connecting map is an actual integral linear equivalence.

All exactness statements are derived from the proved singular
Mayer–Vietoris sequence.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology

open SingularMayerVietoris PeriodTorusHigherHomology

variable {X : Type} [TopologicalSpace X]
variable (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
  (hcover : U ∪ V = Set.univ)

/-- The actual connecting map with its codomain restricted to its exact
image, the kernel of the difference of the intersection inclusions. -/
def coverConnectingToKernel (n : ℕ) :
    SingularHomology X (n + 1) →ₗ[ℤ] LinearMap.ker (leftHomologyMap U V n) :=
  intLinearMapOfAddHom
    ((connectingHomomorphism U V hU hV hcover n).codRestrict
      (LinearMap.ker (leftHomologyMap U V n)) (by
        intro a
        rw [← exact_at_intersection U V hU hV hcover n]
        exact ⟨a, rfl⟩)).toAddMonoidHom

@[simp] theorem coverConnectingToKernel_coe (n : ℕ)
    (a : SingularHomology X (n + 1)) :
    (coverConnectingToKernel U V hU hV hcover n a :
      SingularHomology (U ∩ V : Set X) n) =
        connectingHomomorphism U V hU hV hcover n a := rfl

/-- Exactness gives surjectivity onto the actual inclusion-map kernel
without any homology-vanishing assumption. -/
theorem coverConnectingToKernel_surjective (n : ℕ) :
    Function.Surjective (coverConnectingToKernel U V hU hV hcover n) := by
  intro a
  have ha : (a : SingularHomology (U ∩ V : Set X) n) ∈
      LinearMap.range (connectingHomomorphism U V hU hV hcover n) :=
    (exact_at_intersection U V hU hV hcover n).symm.le a.property
  obtain ⟨b, hb⟩ := ha
  exact ⟨b, Subtype.ext hb⟩

@[simp] theorem coverConnectingToKernel_eq_zero_iff (n : ℕ)
    (a : SingularHomology X (n + 1)) :
    coverConnectingToKernel U V hU hV hcover n a = 0 ↔
      connectingHomomorphism U V hU hV hcover n a = 0 := by
  constructor
  · exact fun ha => congrArg Subtype.val ha
  · exact fun ha => Subtype.ext ha

/-- Restricting the actual connecting map to its image does not change
which ambient homology classes it kills. -/
theorem coverConnectingToKernel_ker (n : ℕ) :
    LinearMap.ker (coverConnectingToKernel U V hU hV hcover n) =
      LinearMap.ker (connectingHomomorphism U V hU hV hcover n) := by
  ext a
  exact coverConnectingToKernel_eq_zero_iff U V hU hV hcover n a

/-- The preceding actual Mayer–Vietoris map still has exactly the kernel
of the codomain-restricted connecting map as its image. -/
theorem coverConnectingToKernel_exact (n : ℕ) :
    LinearMap.range (rightHomologyMap U V (n + 1)) =
      LinearMap.ker (coverConnectingToKernel U V hU hV hcover n) := by
  rw [coverConnectingToKernel_ker]
  exact exact_at_ambient U V hU hV hcover n

theorem coverConnectingToKernel_injective_of_vanishing (n : ℕ)
    [Subsingleton (SingularHomology U (n + 1))]
    [Subsingleton (SingularHomology V (n + 1))] :
    Function.Injective (coverConnectingToKernel U V hU hV hcover n) := by
  intro a b hab
  apply coverConnecting_injective_of_vanishing U V hU hV hcover n
  exact congrArg Subtype.val hab

/-- Upper-degree vanishing alone identifies actual ambient homology
with the exact kernel in the preceding intersection degree. -/
def coverConnectingKernelEquivOfVanishing (n : ℕ)
    [Subsingleton (SingularHomology U (n + 1))]
    [Subsingleton (SingularHomology V (n + 1))] :
    SingularHomology X (n + 1) ≃ₗ[ℤ] LinearMap.ker (leftHomologyMap U V n) :=
  LinearEquiv.ofBijective (coverConnectingToKernel U V hU hV hcover n)
    ⟨coverConnectingToKernel_injective_of_vanishing U V hU hV hcover n,
      coverConnectingToKernel_surjective U V hU hV hcover n⟩

@[simp] theorem coverConnectingKernelEquivOfVanishing_apply (n : ℕ)
    [Subsingleton (SingularHomology U (n + 1))]
    [Subsingleton (SingularHomology V (n + 1))]
    (a : SingularHomology X (n + 1)) :
    coverConnectingKernelEquivOfVanishing U V hU hV hcover n a =
      coverConnectingToKernel U V hU hV hcover n a := rfl

@[simp] theorem coverConnectingKernelEquivOfVanishing_coe (n : ℕ)
    [Subsingleton (SingularHomology U (n + 1))]
    [Subsingleton (SingularHomology V (n + 1))]
    (a : SingularHomology X (n + 1)) :
    (coverConnectingKernelEquivOfVanishing U V hU hV hcover n a :
      SingularHomology (U ∩ V : Set X) n) =
        connectingHomomorphism U V hU hV hcover n a := rfl

end Wikipedia.HopfProblem.CuspCentralHomology
