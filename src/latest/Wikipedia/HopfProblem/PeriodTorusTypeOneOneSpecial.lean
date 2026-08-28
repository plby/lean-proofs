import Wikipedia.HopfProblem.PeriodTorusTypeOneOneEta
import Wikipedia.HopfProblem.SpecialPeriodsExceptionalRelations

/-!
# Type `(1,1)` for the actual constructed period functions

The tangent criterion is applied to the genuine special period map.
Outside the proved countable exceptional set, the integral alternating
coefficient forms of type `(1,1)` are exactly the integer multiples of
the distinguished form. This is a tangent-form statement, not an assumed
Néron–Severi or algebraic-dimension identification.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

open SpecialPeriods UpperHalfPlane

theorem periodPolynomial_special (E : Fin 6 → ℤ) (z : ℍ) :
    periodPolynomial (specialPeriodMap.point z).val E = specialPeriodRelation E z := rfl

/-- The exact criterion at every point of the genuinely constructed period map. -/
theorem special_tangentForm_isTypeOneOne_iff (z : ℍ) (E : Fin 6 → ℤ) :
    IsTypeOneOne (tangentForm (specialPeriodMap.point z) E) ↔
      specialPeriodRelation E z = 0 :=
  tangentForm_isTypeOneOne_iff (specialPeriodMap.point z) E

/-- Universally type `(1,1)` integral coefficient forms are exactly the multiples of `η`. -/
theorem universally_typeOneOne_iff (E : Fin 6 → ℤ) :
    (∀ z : ℍ, IsTypeOneOne (tangentForm (specialPeriodMap.point z) E)) ↔
      ∃ n : ℤ, E = n • periodRelationEta := by
  simp only [special_tangentForm_isTypeOneOne_iff]
  exact specialPeriodRelation_identically_zero_iff E

/-- The genuine tangent-form exceptional locus. -/
def exceptionalTypeOneOneSet : Set ℍ :=
  {z | ∃ E : Fin 6 → ℤ, (¬ ∃ n : ℤ, E = n • periodRelationEta) ∧
    IsTypeOneOne (tangentForm (specialPeriodMap.point z) E)}

theorem exceptionalTypeOneOneSet_eq : exceptionalTypeOneOneSet = exceptionalPeriodRelationSet := by
  ext z
  simp only [exceptionalTypeOneOneSet, exceptionalPeriodRelationSet, Set.mem_setOf_eq,
    special_tangentForm_isTypeOneOne_iff]

theorem exceptionalTypeOneOneSet_countable : exceptionalTypeOneOneSet.Countable := by
  rw [exceptionalTypeOneOneSet_eq]
  exact exceptionalPeriodRelationSet_countable

/-- Outside the actual countable exceptional locus, every integral type `(1,1)`
coefficient form is the actual distinguished multiple. -/
theorem typeOneOne_iff_of_not_exceptional (z : ℍ) (hz : z ∉ exceptionalTypeOneOneSet)
    (E : Fin 6 → ℤ) :
    IsTypeOneOne (tangentForm (specialPeriodMap.point z) E) ↔
      ∃ n : ℤ, E = n • periodRelationEta := by
  rw [special_tangentForm_isTypeOneOne_iff]
  apply specialPeriodRelation_iff_of_not_exceptional z
  simpa only [exceptionalTypeOneOneSet_eq] using hz

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
