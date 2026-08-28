import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicAnticommutingStructures
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureConjugation

/-! # Recover quaternionic complex structures from actual symplectic square roots of minus one -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.OrthogonalPaths

variable {n : ℕ}

theorem inverse_operator_of_square (a : symplecticSubgroup n)
    (ha : a.val.val.val.comp a.val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) :
    (a⁻¹).val.val.val = -a.val.val.val := by
  apply ContinuousLinearMap.ext
  intro x
  apply a.val.val.property.injective
  change a.val.val.val ((inverse a.val).val.val x) = a.val.val.val (-a.val.val.val x)
  rw [self_apply_inverse, map_neg]
  have hx : a.val.val.val (a.val.val.val x) = -x := DFunLike.congr_fun ha x
  rw [hx, neg_neg]

def ofSymplecticSquare (a : symplecticSubgroup n)
    (ha : a.val.val.val.comp a.val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) : Space n :=
  ⟨⟨a.val.val.val, ⟨by
      change a.val.val.val.adjoint = -a.val.val.val
      rw [← NoExoticSixSphere.OrthogonalVelocity.inverse_eq_adjoint a.val]
      exact inverse_operator_of_square a ha,
    (mem_symplecticSubgroup_iff n a.val).mp a.property⟩⟩, ha⟩

theorem toSymplectic_ofSymplecticSquare (a : symplecticSubgroup n)
    (ha : a.val.val.val.comp a.val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) :
    toSymplectic (ofSymplecticSquare a ha) = a := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rfl

theorem toSymplectic_mul_self (J : Space n) :
    toSymplectic J * toSymplectic J = antipode n := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [antipode_operator]
  exact J.property

theorem toSymplectic_inv (J : Space n) :
    (toSymplectic J)⁻¹ = toSymplectic (negative J) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact inverse_operator_of_square (toSymplectic J) J.property

theorem continuous_ofSymplecticSquare {X : Type*} [TopologicalSpace X]
    (a : X → symplecticSubgroup n) (hc : Continuous a)
    (ha : ∀ x, (a x).val.val.val.comp (a x).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) :
    Continuous (fun x ↦ ofSymplecticSquare (a x) (ha x)) := by
  have hop : Continuous (fun x ↦ (a x).val.val.val) :=
    continuous_subtype_val.comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp hc))
  exact (hop.subtype_mk _).subtype_mk _

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures
