import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructures
import Wikipedia.NoExoticSixSphere.ComplexStructureRetraction

/-!
# A neighborhood retraction onto quaternionic complex structures

The local Gram square root commutes with every quaternionic right action.
Its inverse and the polar normalization therefore preserve quaternionic
linearity. Restriction of the actual orthogonal normalization gives a
continuous retraction with the original subspace topology.
-/

noncomputable section

open Set
open scoped ContDiff Ring

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.SkewSpectralPlane

variable {n : ℕ}

def normalizationDomain (n : ℕ) : Set (SkewSpace n) :=
  (toOrthogonalSkew n) ⁻¹'
    NoExoticSixSphere.OrthogonalComplexStructures.normalizationDomain (4 * n + 4)

theorem isOpen_normalizationDomain (n : ℕ) : IsOpen (normalizationDomain n) :=
  (NoExoticSixSphere.OrthogonalComplexStructures.isOpen_normalizationDomain (4 * n + 4)).preimage
    (continuous_toOrthogonalSkew n)

theorem mem_normalizationDomain (J : Space n) : J.val ∈ normalizationDomain n :=
  NoExoticSixSphere.OrthogonalComplexStructures.mem_normalizationDomain (toOrthogonal J)

def normalizationOperator (K : SkewSpace n) : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4) :=
  NoExoticSixSphere.OrthogonalComplexStructures.normalizationOperator (toOrthogonalSkew n K)

theorem gram_mem_commutant (K : SkewSpace n) : gram (toOrthogonalSkew n K) ∈ commutant n := by
  rw [NoExoticSixSphere.OrthogonalComplexStructures.gram_eq_neg_comp]
  exact (commutant n).neg_mem ((commutant n).mul_mem K.property.2 K.property.2)

theorem normalizationOperator_mem_commutant {K : SkewSpace n}
    (hK : K ∈ normalizationDomain n) : normalizationOperator K ∈ commutant n := by
  let R := NoExoticSixSphere.OrthogonalComplexStructures.rootData (4 * n + 4)
  have hdom : gram (toOrthogonalSkew n K) ∈ R.domain := hK
  have hroot : R.root (gram (toOrthogonalSkew n K)) ∈ commutant n := by
    apply (mem_commutant_iff n _).mpr
    intro q
    exact (R.commute hdom
      (show Commute (gram (toOrthogonalSkew n K)) (rightAction n q) from
        (mem_commutant_iff n _).mp (gram_mem_commutant K) q)).eq
  have hinv : (R.root (gram (toOrthogonalSkew n K)))⁻¹ʳ ∈ commutant n := by
    apply (mem_commutant_iff n _).mpr
    intro q
    exact (NoExoticSixSphere.NearIdentitySquare.commute_ringInverse_of_isUnit
      (R.isUnit_root hdom)
      (show Commute (R.root (gram (toOrthogonalSkew n K))) (rightAction n q) from
        (mem_commutant_iff n _).mp hroot q)).eq
  exact (commutant n).mul_mem K.property.2 hinv

theorem normalizationOperator_skew {K : SkewSpace n} (hK : K ∈ normalizationDomain n) :
    star (normalizationOperator K) = -normalizationOperator K :=
  NoExoticSixSphere.OrthogonalComplexStructures.normalizationOperator_skew hK

theorem normalizationOperator_square {K : SkewSpace n} (hK : K ∈ normalizationDomain n) :
    (normalizationOperator K).comp (normalizationOperator K) =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) :=
  NoExoticSixSphere.OrthogonalComplexStructures.normalizationOperator_square hK

theorem contDiffOn_normalizationOperator :
    ContDiffOn ℝ ∞ (normalizationOperator (n := n)) (normalizationDomain n) := by
  have hL : ContDiff ℝ ∞ (toOrthogonalSkew n) :=
    finiteLinearMap_contDiff (E := SkewSpace n)
      (F := NoExoticSixSphere.CayleyTransform.SkewOperators (4 * n + 4)) (toOrthogonalSkew n)
  exact NoExoticSixSphere.OrthogonalComplexStructures.contDiffOn_normalizationOperator.comp
    hL.contDiffOn (fun _ hK => hK)

def neighborhoodRetraction (n : ℕ) : C(normalizationDomain n, Space n) where
  toFun K := ⟨⟨normalizationOperator K.val,
    ⟨normalizationOperator_skew K.property, normalizationOperator_mem_commutant K.property⟩⟩,
      normalizationOperator_square K.property⟩
  continuous_toFun :=
    (contDiffOn_normalizationOperator.continuousOn.domRestrict.subtype_mk _).subtype_mk _

theorem normalizationOperator_of_complexStructure (J : Space n) :
    normalizationOperator J.val = J.val.val :=
  NoExoticSixSphere.OrthogonalComplexStructures.normalizationOperator_of_complexStructure
    (toOrthogonal J)

theorem neighborhoodRetraction_eq_self (J : Space n) :
    neighborhoodRetraction n ⟨J.val, mem_normalizationDomain J⟩ = J := by
  apply Subtype.ext
  apply Subtype.ext
  exact normalizationOperator_of_complexStructure J

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures
