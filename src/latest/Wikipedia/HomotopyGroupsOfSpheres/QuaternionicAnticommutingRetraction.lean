import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureRetraction
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicAnticommutingStructures
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureDirections
import Wikipedia.HomotopyGroupsOfSpheres.ComplexStructureRotationAlgebra

/-!
# Polar normalization preserves anticommutation

The Gram operator of an anticommuting skew direction commutes with the base
complex structure. Its local square root and inverse do too, so polar
normalization gives a retraction onto the anticommuting complex structures.
-/

noncomputable section

open Set
open scoped Ring

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.SkewSpectralPlane

variable {n : ℕ}

private theorem negative_square_commute {A : Type*} [Ring A] (J K : A)
    (hJK : J * K = -(K * J)) : Commute (-(K * K)) J := by
  have hKJ := ComplexStructureRotationAlgebra.reverse_anticommute J K hJK
  change (-(K * K)) * J = J * (-(K * K))
  calc
    _ = -(K * (K * J)) := by noncomm_ring
    _ = -(K * (-(J * K))) := by rw [hKJ]
    _ = (K * J) * K := by noncomm_ring
    _ = (-(J * K)) * K := by rw [hKJ]
    _ = _ := by noncomm_ring

private theorem anticommute_mul_commuting {A : Type*} [Ring A] (J K B : A)
    (hJK : J * K = -(K * J)) (hBJ : Commute B J) : J * (K * B) = -((K * B) * J) := by
  rw [← mul_assoc, hJK, neg_mul]
  apply congrArg Neg.neg
  rw [mul_assoc K J B, ← hBJ.eq, ← mul_assoc]

theorem gram_commute_of_anticommute (J : Space n) (K : SkewSpace n)
    (hJK : J.val.val * K.val = -(K.val * J.val.val)) :
    Commute (gram (toOrthogonalSkew n K)) J.val.val := by
  rw [NoExoticSixSphere.OrthogonalComplexStructures.gram_eq_neg_comp]
  exact negative_square_commute J.val.val K.val hJK

theorem normalizationOperator_anticommute (J : Space n) (K : SkewSpace n)
    (hK : K ∈ normalizationDomain n) (hJK : J.val.val * K.val = -(K.val * J.val.val)) :
    J.val.val * normalizationOperator K = -(normalizationOperator K * J.val.val) := by
  let R := NoExoticSixSphere.OrthogonalComplexStructures.rootData (4 * n + 4)
  have hdom : gram (toOrthogonalSkew n K) ∈ R.domain := hK
  have hr : Commute (R.root (gram (toOrthogonalSkew n K))) J.val.val :=
    R.commute hdom (gram_commute_of_anticommute J K hJK)
  have hi : Commute (R.root (gram (toOrthogonalSkew n K)))⁻¹ʳ J.val.val :=
    NoExoticSixSphere.NearIdentitySquare.commute_ringInverse_of_isUnit (R.isUnit_root hdom) hr
  exact anticommute_mul_commuting J.val.val K.val _ hJK hi

end ComplexStructures

namespace AnticommutingStructures

open ComplexStructures

variable {n : ℕ}

def normalizationDomain (J : ComplexStructures.Space n) : Set (AntiSkewSpace J) :=
  (antiSkewToSkew J) ⁻¹' ComplexStructures.normalizationDomain n

theorem isOpen_normalizationDomain (J : ComplexStructures.Space n) :
    IsOpen (normalizationDomain J) :=
  (ComplexStructures.isOpen_normalizationDomain n).preimage (continuous_antiSkewToSkew J)

def asDirection {J : ComplexStructures.Space n} (Q : Space J) : AntiSkewSpace J :=
  ⟨Q.val.val.val, ⟨Q.val.val.property, Q.property⟩⟩

theorem asDirection_toSkew {J : ComplexStructures.Space n} (Q : Space J) :
    antiSkewToSkew J (asDirection Q) = Q.val.val := rfl

theorem mem_normalizationDomain {J : ComplexStructures.Space n} (Q : Space J) :
    asDirection Q ∈ normalizationDomain J := ComplexStructures.mem_normalizationDomain Q.val

def neighborhoodRetraction (J : ComplexStructures.Space n) : C(normalizationDomain J, Space J) where
  toFun K := ⟨ComplexStructures.neighborhoodRetraction n
    ⟨antiSkewToSkew J K.val, K.property⟩,
      normalizationOperator_anticommute J (antiSkewToSkew J K.val) K.property K.val.property.2⟩
  continuous_toFun := by
    let F : C(normalizationDomain J, ComplexStructures.normalizationDomain n) :=
      ⟨fun K ↦ ⟨antiSkewToSkew J K.val, K.property⟩,
        ((continuous_antiSkewToSkew J).comp continuous_subtype_val).subtype_mk _⟩
    exact ((ComplexStructures.neighborhoodRetraction n).continuous.comp F.continuous).subtype_mk _

theorem neighborhoodRetraction_eq_self {J : ComplexStructures.Space n} (Q : Space J) :
    neighborhoodRetraction J ⟨asDirection Q, mem_normalizationDomain Q⟩ = Q := by
  apply Subtype.ext
  exact ComplexStructures.neighborhoodRetraction_eq_self Q.val

end AnticommutingStructures
end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
