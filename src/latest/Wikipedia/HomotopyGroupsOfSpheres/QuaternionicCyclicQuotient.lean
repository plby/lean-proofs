import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPiSixVanishing
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicDegree
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# The sixth sphere group is the actual projected-degree quotient

Vanishing of `π₆(Sp(2))` makes the integer connecting homomorphism
surjective. Its kernel was already identified with the actual image of
the first-column degree map. The unresolved numerical input is now the
identification of that image with `12ℤ`.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

theorem connecting_six_surjective : Function.Surjective (connectingHom 6) := by
  let := QuaternionicColumns.piSixSpTwo_subsingleton
  intro a
  exact (connecting_range_eq_kernel a).mpr (Subsingleton.elim _ _)

theorem integerConnecting_surjective : Function.Surjective integerConnecting :=
  connecting_six_surjective.comp baseDegreeEquiv.symm.surjective

/-- Every class in the actual fiber group is a power of the connecting class. -/
theorem exists_boundaryClass_zpow (a : π_ 6 northSubgroup 1) :
    ∃ k : ℤ, boundaryClass ^ k = a := by
  obtain ⟨k, hk⟩ := integerConnecting_surjective a
  exact ⟨k.toAdd, (integerConnecting_eq_zpow k.toAdd).symm.trans hk⟩

theorem zpowers_boundaryClass_eq_top : Subgroup.zpowers boundaryClass = ⊤ := by
  apply le_antisymm le_top
  intro a _
  obtain ⟨k, rfl⟩ := exists_boundaryClass_zpow a
  exact Subgroup.zpow_mem_zpowers _ _

theorem piSix_fiber_isCyclic : IsCyclic (π_ 6 northSubgroup 1) :=
  isCyclic_iff_exists_zpowers_eq_top.mpr ⟨boundaryClass, zpowers_boundaryClass_eq_top⟩

/-- An unconditional quotient description, with the actual projection-degree image. -/
def degreeQuotientMulEquiv :
    (Multiplicative ℤ ⧸ projectionDegree.range) ≃* π_ 6 northSubgroup 1 :=
  (QuotientGroup.quotientMulEquivOfEq projectionDegree_range_eq_integerConnecting_ker).trans
    (QuotientGroup.quotientKerEquivOfSurjective integerConnecting integerConnecting_surjective)

theorem degreeQuotientMulEquiv_mk (k : Multiplicative ℤ) :
    degreeQuotientMulEquiv (QuotientGroup.mk k) = integerConnecting k := by
  change QuotientGroup.quotientKerEquivOfSurjective integerConnecting integerConnecting_surjective
    (QuotientGroup.quotientMulEquivOfEq projectionDegree_range_eq_integerConnecting_ker
      (QuotientGroup.mk k)) = integerConnecting k
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

def sphereDegreeQuotientMulEquiv :
    (Multiplicative ℤ ⧸ projectionDegree.range) ≃*
      π_ 6 (Sphere 3) (fiberSphereHomeomorph 1) :=
  degreeQuotientMulEquiv.trans (homeomorphMulEquiv (N := Fin 6) fiberSphereHomeomorph 1)

theorem piSix_sphere_isCyclic : IsCyclic (π_ 6 (Sphere 3) (fiberSphereHomeomorph 1)) :=
  (homeomorphMulEquiv (N := Fin 6) fiberSphereHomeomorph 1).isCyclic.mp piSix_fiber_isCyclic

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration
