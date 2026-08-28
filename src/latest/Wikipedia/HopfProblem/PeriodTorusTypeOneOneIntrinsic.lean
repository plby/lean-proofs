import Wikipedia.HopfProblem.PeriodTorusTypeOneOneIntegralCompleteness
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneSpecial

/-!
# Intrinsic classification of integral alternating forms away from the exceptional set

The coefficient completeness theorem transfers the proved classification
from integer six-tuples to arbitrary real alternating forms integral on
the actual period lattice.  Thus no presentation of the form by chosen
coefficients is an assumption.  The conclusion remains about genuine
tangent forms; no Néron--Severi identification is asserted.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

open SpecialPeriods UpperHalfPlane

/-- The coefficient `uw = 1` makes distinct integer multiples of the
distinguished actual tangent form distinct. -/
theorem etaIntegerMultiple_injective (p : PeriodDomain) :
    Function.Injective (fun n : ℤ => (n : ℝ) • etaTangent p) := by
  intro n m h
  have hcoeff : n • periodRelationEta = m • periodRelationEta := by
    apply tangentForm_injective p
    simpa only [tangentForm_zsmul, etaTangent] using h
  simpa [Pi.smul_apply, smul_eq_mul, periodRelationEta] using congrFun hcoeff (3 : Fin 6)

theorem etaIntegerMultiple_eq_zero_iff (p : PeriodDomain) (n : ℤ) :
    (n : ℝ) • etaTangent p = 0 ↔ n = 0 := by
  constructor
  · intro h
    apply etaIntegerMultiple_injective p
    simpa using h
  · rintro rfl
    simp

/-- Away from the actual countable exceptional locus, intrinsic integral
alternating forms of type `(1,1)` are exactly the integer multiples of `η`. -/
theorem typeOneOne_integral_iff_of_not_exceptional (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet) (B : RealForm)
    (hAlt : ∀ x, B x x = 0)
    (hInt : IntegralOnPeriodLattice (specialPeriodMap.point z) B) :
    IsTypeOneOne B ↔ ∃ n : ℤ, B = (n : ℝ) • etaTangent (specialPeriodMap.point z) := by
  obtain ⟨E, hE, _⟩ := existsUnique_tangentForm_of_integral
    (specialPeriodMap.point z) B hAlt hInt
  rw [← hE, typeOneOne_iff_of_not_exceptional z hz]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, tangentForm_zsmul (specialPeriodMap.point z) n periodRelationEta⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, tangentForm_injective (specialPeriodMap.point z) ?_⟩
    exact hn.trans (tangentForm_zsmul (specialPeriodMap.point z) n periodRelationEta).symm

/-- The integer multiple in the intrinsic classification is unique. -/
theorem existsUnique_etaMultiple_of_typeOneOne_integral (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet) (B : RealForm)
    (hAlt : ∀ x, B x x = 0)
    (hInt : IntegralOnPeriodLattice (specialPeriodMap.point z) B)
    (hType : IsTypeOneOne B) :
    ∃! n : ℤ, B = (n : ℝ) • etaTangent (specialPeriodMap.point z) := by
  obtain ⟨n, hn⟩ := (typeOneOne_integral_iff_of_not_exceptional z hz B hAlt hInt).mp hType
  refine ⟨n, hn, ?_⟩
  intro m hm
  exact etaIntegerMultiple_injective (specialPeriodMap.point z) (hm.symm.trans hn)

theorem typeOneOne_integral_iff_existsUnique_etaMultiple (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet) (B : RealForm)
    (hAlt : ∀ x, B x x = 0)
    (hInt : IntegralOnPeriodLattice (specialPeriodMap.point z) B) :
    IsTypeOneOne B ↔ ∃! n : ℤ, B = (n : ℝ) • etaTangent (specialPeriodMap.point z) := by
  constructor
  · exact existsUnique_etaMultiple_of_typeOneOne_integral z hz B hAlt hInt
  · intro h
    exact (typeOneOne_integral_iff_of_not_exceptional z hz B hAlt hInt).mpr h.exists

/-- A nonzero intrinsic form has a nonzero integer coefficient. -/
theorem exists_nonzero_etaMultiple_of_typeOneOne_integral (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet) (B : RealForm)
    (hAlt : ∀ x, B x x = 0)
    (hInt : IntegralOnPeriodLattice (specialPeriodMap.point z) B)
    (hType : IsTypeOneOne B) (hB : B ≠ 0) :
    ∃ n : ℤ, n ≠ 0 ∧ B = (n : ℝ) • etaTangent (specialPeriodMap.point z) := by
  obtain ⟨n, hn⟩ := (typeOneOne_integral_iff_of_not_exceptional z hz B hAlt hInt).mp hType
  refine ⟨n, ?_, hn⟩
  intro hn0
  apply hB
  simpa [hn0] using hn

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
