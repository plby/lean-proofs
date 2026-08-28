import Wikipedia.HopfProblem.SingularMayerVietoris
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePoint
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCoordinateAlgebra

/-!
# Singular Mayer–Vietoris for two contractible open sets

For an actual open cover `X = U ∪ V` whose two members are contractible,
the actual Mayer–Vietoris connecting homomorphism is injective in every
positive degree. Above degree one it is an isomorphism onto the homology
of the intersection in the preceding degree. In degree one its image is
exactly the kernel of the difference of the two intersection inclusions.

The exactness used here is the singular Mayer–Vietoris sequence proved
by subdivision in `SingularMayerVietoris`, and the vanishing of the open
sets' homology follows from their genuine contractions.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology

open SingularMayerVietoris PeriodTorusHigherHomology

variable {X : Type} [TopologicalSpace X]
variable (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
  (hcover : U ∪ V = Set.univ)
variable [ContractibleSpace U] [ContractibleSpace V]

/-- The connecting homomorphism of a cover by two contractible open sets
is injective in every positive ambient degree. -/
theorem contractibleCoverConnecting_injective (n : ℕ) :
    Function.Injective (connectingHomomorphism U V hU hV hcover n) := by
  let := contractible_homology_subsingleton U (n + 1) (Nat.succ_ne_zero _)
  let := contractible_homology_subsingleton V (n + 1) (Nat.succ_ne_zero _)
  apply LinearMap.ker_eq_bot.mp
  rw [← exact_at_ambient U V hU hV hcover n]
  apply LinearMap.range_eq_bot.mpr
  apply LinearMap.ext
  intro a
  have ha : a = 0 := Subsingleton.elim _ _
  rw [ha, map_zero, LinearMap.zero_apply]

/-- In positive intersection degree the actual connecting homomorphism
is also surjective. -/
theorem contractibleCoverConnecting_surjective (n : ℕ) :
    Function.Surjective (connectingHomomorphism U V hU hV hcover (n + 1)) := by
  let := contractible_homology_subsingleton U (n + 1) (Nat.succ_ne_zero _)
  let := contractible_homology_subsingleton V (n + 1) (Nat.succ_ne_zero _)
  intro a
  have ha : a ∈ LinearMap.ker (leftHomologyMap U V (n + 1)) := by
    exact Subsingleton.elim _ _
  rw [← exact_at_intersection U V hU hV hcover (n + 1)] at ha
  exact ha

/-- The actual connecting homomorphism computes all ambient homology
groups of degree at least two from the intersection. -/
def contractibleCoverHomologyHigherEquiv (n : ℕ) :
    SingularHomology X (n + 2) ≃ₗ[ℤ]
      SingularHomology (U ∩ V : Set X) (n + 1) :=
  LinearEquiv.ofBijective (connectingHomomorphism U V hU hV hcover (n + 1))
    ⟨contractibleCoverConnecting_injective U V hU hV hcover (n + 1),
      contractibleCoverConnecting_surjective U V hU hV hcover n⟩

@[simp] theorem contractibleCoverHomologyHigherEquiv_apply (n : ℕ)
    (a : SingularHomology X (n + 2)) :
    contractibleCoverHomologyHigherEquiv U V hU hV hcover n a =
      connectingHomomorphism U V hU hV hcover (n + 1) a := rfl

/-- The degree-one actual connecting map, with its codomain restricted
to the exact kernel of the two degree-zero intersection inclusions. -/
def contractibleCoverConnectingToKernel :
    SingularHomology X 1 →ₗ[ℤ] LinearMap.ker (leftHomologyMap U V 0) :=
  intLinearMapOfAddHom
    ((connectingHomomorphism U V hU hV hcover 0).codRestrict
      (LinearMap.ker (leftHomologyMap U V 0)) (by
        intro a
        rw [← exact_at_intersection U V hU hV hcover 0]
        exact ⟨a, rfl⟩)).toAddMonoidHom

omit [ContractibleSpace U] [ContractibleSpace V] in
@[simp] theorem contractibleCoverConnectingToKernel_coe
    (a : SingularHomology X 1) :
    (contractibleCoverConnectingToKernel U V hU hV hcover a :
      SingularHomology (U ∩ V : Set X) 0) =
        connectingHomomorphism U V hU hV hcover 0 a := rfl

theorem contractibleCoverConnectingToKernel_bijective :
    Function.Bijective (contractibleCoverConnectingToKernel U V hU hV hcover) := by
  constructor
  · intro a b hab
    apply contractibleCoverConnecting_injective U V hU hV hcover 0
    exact congrArg Subtype.val hab
  · intro a
    have ha : (a : SingularHomology (U ∩ V : Set X) 0) ∈
        LinearMap.range (connectingHomomorphism U V hU hV hcover 0) :=
      (exact_at_intersection U V hU hV hcover 0).symm.le a.property
    obtain ⟨b, hb⟩ := ha
    exact ⟨b, Subtype.ext hb⟩

/-- The actual first singular homology is the kernel of the difference
of the two actual degree-zero intersection-inclusion maps. -/
def contractibleCoverHomologyOneEquivKernel :
    SingularHomology X 1 ≃ₗ[ℤ] LinearMap.ker (leftHomologyMap U V 0) :=
  LinearEquiv.ofBijective (contractibleCoverConnectingToKernel U V hU hV hcover)
    (contractibleCoverConnectingToKernel_bijective U V hU hV hcover)

@[simp] theorem contractibleCoverHomologyOneEquivKernel_coe
    (a : SingularHomology X 1) :
    (contractibleCoverHomologyOneEquivKernel U V hU hV hcover a :
      SingularHomology (U ∩ V : Set X) 0) =
        connectingHomomorphism U V hU hV hcover 0 a := rfl

include hcover in
/-- A cover by two contractible sets with nonempty intersection is path
connected. This geometric fact does not require the sets to be open. -/
theorem contractibleCoverPathConnectedSpace (hne : (U ∩ V).Nonempty) :
    PathConnectedSpace X := by
  apply pathConnectedSpace_iff_univ.mpr
  rw [← hcover]
  exact (isPathConnected_iff_pathConnectedSpace.mpr
    (inferInstance : PathConnectedSpace U)).union
    (isPathConnected_iff_pathConnectedSpace.mpr
      (inferInstance : PathConnectedSpace V)) hne

/-- Degree zero is computed by the actual augmentation whenever the
intersection of the two contractible covering sets is nonempty. -/
def contractibleCoverHomologyZeroEquiv (hne : (U ∩ V).Nonempty) :
    SingularHomology X 0 ≃ₗ[ℤ] ℤ := by
  letI := contractibleCoverPathConnectedSpace U V hcover hne
  exact connectedHomologyZeroEquiv X

end Wikipedia.HopfProblem.CuspCentralHomology
