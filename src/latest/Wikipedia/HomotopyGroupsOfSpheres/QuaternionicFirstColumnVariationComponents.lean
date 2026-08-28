import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFirstColumnDerivative

/-! # Complex components of the actual midpoint first-column variation -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicComplexPlane

theorem midpointColumnVariation_complexPart (w : ℂ) (u : unitary ℂ)
    (D : Matrix (Fin 3) (Fin 3) ℂ) (r : Fin 2) :
    complexPart (midpointColumnVariation w u D r) =
      D (remainingRow r) 0 * star u.val +
        u.val * targetComplexColumn r * star (D 1 1) := by
  fin_cases r <;>
    simp [midpointColumnVariation, normalizedSchurVariation, midpointRotationVariation,
      remainingRow, targetComplexColumn, sub_eq_add_neg, complexPart_add, complexPart_neg,
      complexPart_mul, complexPart_embed, complexPart_coeComplex, coordinate_add,
      coordinate_mul, coordinate_coeComplex]

theorem midpointColumnVariation_coordinate_zero (w : ℂ) (u : unitary ℂ)
    (D : Matrix (Fin 3) (Fin 3) ℂ) :
    coordinate (midpointColumnVariation w u D 0) =
      D 0 1 - u.val ^ 2 * targetAlpha * star (D 1 0) -
        u.val * (w + targetAlpha * star w) + (w + star w) * targetAlpha := by
  have hu := u.property.2
  simp only [Complex.star_def] at hu
  simp [midpointColumnVariation, normalizedSchurVariation, midpointRotationVariation,
    remainingRow, targetComplexColumn, sub_eq_add_neg, complexPart_add,
    complexPart_mul, complexPart_embed, complexPart_coeComplex, coordinate_add,
    coordinate_neg, coordinate_mul, coordinate_coeComplex]
  linear_combination targetAlpha * (w + (starRingEnd ℂ) w) * hu

theorem midpointColumnVariation_coordinate_one (w : ℂ) (u : unitary ℂ)
    (D : Matrix (Fin 3) (Fin 3) ℂ) :
    coordinate (midpointColumnVariation w u D 1) =
      D 2 1 - u.val ^ 2 * targetBeta * star (D 1 0) -
        u.val * targetBeta * star w + (w + star w) * targetBeta := by
  have hu := u.property.2
  simp only [Complex.star_def] at hu
  simp [midpointColumnVariation, normalizedSchurVariation, midpointRotationVariation,
    remainingRow, targetComplexColumn, sub_eq_add_neg, complexPart_add,
    complexPart_mul, complexPart_embed, complexPart_coeComplex, coordinate_add,
    coordinate_neg, coordinate_mul, coordinate_coeComplex]
  linear_combination targetBeta * (w + (starRingEnd ℂ) w) * hu

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
