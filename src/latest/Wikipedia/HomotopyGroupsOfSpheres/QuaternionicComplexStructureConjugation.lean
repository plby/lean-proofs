import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructures
import Wikipedia.NoExoticSixSphere.ComplexStructureConjugation

/-!
# The symplectic action on quaternionic complex structures

Conjugation preserves both skew adjointness and the quaternionic commutant.
It therefore acts continuously on the original complex-structure locus.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures

open NoExoticSixSphere.GLOrthonormalization

variable {n : ℕ}

def conjugateSkew (a : symplecticSubgroup n) (K : SkewSpace n) : SkewSpace n :=
  ⟨(NoExoticSixSphere.SkewConjugation.conjugate a.val (toOrthogonalSkew n K)).val,
    ⟨NoExoticSixSphere.SkewConjugation.conjugate_mem_skew a.val (toOrthogonalSkew n K), by
      change a.val.val.val * (K.val * (a⁻¹).val.val.val) ∈ commutant n
      exact (commutant n).mul_mem ((mem_symplecticSubgroup_iff n a.val).mp a.property)
        ((commutant n).mul_mem K.property.2
          ((mem_symplecticSubgroup_iff n (a⁻¹).val).mp (a⁻¹).property))⟩⟩

def conjugate (a : symplecticSubgroup n) (J : Space n) : Space n :=
  ⟨conjugateSkew a J.val,
    NoExoticSixSphere.OrthogonalComplexStructures.conjugate_square a.val (toOrthogonal J)⟩

theorem conjugate_operator (a : symplecticSubgroup n) (J : Space n) :
    (conjugate a J).val.val = a.val.val.val * (J.val.val * (a⁻¹).val.val.val) := rfl

theorem toSymplectic_injective : Function.Injective (toSymplectic (n := n)) := by
  intro J K h
  have he := congrArg (fun a : symplecticSubgroup n ↦ a.val.val.val) h
  exact Subtype.ext (Subtype.ext he)

theorem toSymplectic_conjugate (a : symplecticSubgroup n) (J : Space n) :
    toSymplectic (conjugate a J) = a * toSymplectic J * a⁻¹ := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rfl

theorem conjugate_one (J : Space n) : conjugate 1 J = J := by
  apply toSymplectic_injective
  rw [toSymplectic_conjugate, one_mul, inv_one, mul_one]

theorem conjugate_mul (a b : symplecticSubgroup n) (J : Space n) :
    conjugate (a * b) J = conjugate a (conjugate b J) := by
  apply toSymplectic_injective
  simp only [toSymplectic_conjugate, mul_inv_rev, mul_assoc]

theorem conjugate_inv_cancel (a : symplecticSubgroup n) (J : Space n) :
    conjugate a⁻¹ (conjugate a J) = J := by
  rw [← conjugate_mul, inv_mul_cancel, conjugate_one]

theorem conjugate_cancel_inv (a : symplecticSubgroup n) (J : Space n) :
    conjugate a (conjugate a⁻¹ J) = J := by
  rw [← conjugate_mul, mul_inv_cancel, conjugate_one]

theorem continuous_conjugate {X : Type*} [TopologicalSpace X]
    (a : X → symplecticSubgroup n) (J : X → Space n)
    (ha : Continuous a) (hJ : Continuous J) :
    Continuous (fun x ↦ conjugate (a x) (J x)) := by
  have hA : Continuous (fun x ↦ (a x).val.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp
      (continuous_subtype_val.comp ha))
  have hK : Continuous (fun x ↦ (J x).val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp hJ)
  have hI : Continuous (fun x ↦ ((a x)⁻¹).val.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp
      (continuous_subtype_val.comp ha.inv))
  exact ((hA.clm_comp (hK.clm_comp hI)).subtype_mk _).subtype_mk _

def conjugationHomeomorph (a : symplecticSubgroup n) : Space n ≃ₜ Space n where
  toFun := conjugate a
  invFun := conjugate a⁻¹
  left_inv := conjugate_inv_cancel a
  right_inv := conjugate_cancel_inv a
  continuous_toFun := continuous_conjugate _ _ continuous_const continuous_id
  continuous_invFun := continuous_conjugate _ _ continuous_const continuous_id

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures
