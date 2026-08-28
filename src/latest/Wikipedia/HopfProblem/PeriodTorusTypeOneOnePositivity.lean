import Wikipedia.HopfProblem.PeriodTorusTypeOneOneIntrinsic
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneEtaMultiples

/-!
# Intrinsic nondegeneracy and the absence of nonzero nonnegative integral forms

Away from the actual countable exceptional locus, the Hermitian form
associated with every nonzero alternating lattice-integral form of type
`(1,1)` has signature `(1,1)`. In particular the only such form whose
associated Hermitian form is nonnegative on every diagonal is zero.

These are statements about actual tangent forms on the actual period
lattice, with neither a Néron--Severi comparison nor an algebraic-dimension
assumption.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

open SpecialPeriods UpperHalfPlane

/-- Identification by the actual imaginary part handles the dependent type proof. -/
theorem associated_eq_etaMultipleHermitian (p : PeriodDomain) (n : ℤ)
    (B : RealForm) (hType : IsTypeOneOne B) (hB : B = (n : ℝ) • etaTangent p) :
    associatedSesquilinear B hType = etaMultipleHermitian p n := by
  symm
  apply eq_associatedSesquilinear_of_im B hType
  intro x y
  rw [etaMultipleHermitian_im, etaMultipleTangent_eq_smul, ← hB]

/-- The signature holds for every intrinsic form satisfying the actual lattice conditions. -/
theorem associated_signature_of_not_exceptional (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet) (B : RealForm)
    (hAlt : ∀ x, B x x = 0)
    (hInt : IntegralOnPeriodLattice (specialPeriodMap.point z) B)
    (hType : IsTypeOneOne B) (hB : B ≠ 0) :
    HasSignatureOneOne (associatedSesquilinear B hType) := by
  obtain ⟨n, hn, hBn⟩ :=
    exists_nonzero_etaMultiple_of_typeOneOne_integral z hz B hAlt hInt hType hB
  rw [associated_eq_etaMultipleHermitian (specialPeriodMap.point z) n B hType hBn]
  exact etaMultipleHermitian_signature_one_one (specialPeriodMap.point z) n hn

theorem associated_nondegenerate_of_not_exceptional (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet) (B : RealForm)
    (hAlt : ∀ x, B x x = 0)
    (hInt : IntegralOnPeriodLattice (specialPeriodMap.point z) B)
    (hType : IsTypeOneOne B) (hB : B ≠ 0) :
    (associatedSesquilinear B hType).Nondegenerate := by
  obtain ⟨n, hn, hBn⟩ :=
    exists_nonzero_etaMultiple_of_typeOneOne_integral z hz B hAlt hInt hType hB
  rw [associated_eq_etaMultipleHermitian (specialPeriodMap.point z) n B hType hBn]
  exact etaMultipleHermitian_nondegenerate (specialPeriodMap.point z) n hn

theorem realForm_nondegenerate_of_not_exceptional (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet) (B : RealForm)
    (hAlt : ∀ x, B x x = 0)
    (hInt : IntegralOnPeriodLattice (specialPeriodMap.point z) B)
    (hType : IsTypeOneOne B) (hB : B ≠ 0) : B.Nondegenerate :=
  (associatedSesquilinear_nondegenerate_iff B hType).mp
    (associated_nondegenerate_of_not_exceptional z hz B hAlt hInt hType hB)

theorem associated_indefinite_of_not_exceptional (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet) (B : RealForm)
    (hAlt : ∀ x, B x x = 0)
    (hInt : IntegralOnPeriodLattice (specialPeriodMap.point z) B)
    (hType : IsTypeOneOne B) (hB : B ≠ 0) :
    (∃ x, 0 < (associatedSesquilinear B hType x x).re) ∧
      (∃ y, (associatedSesquilinear B hType y y).re < 0) := by
  obtain ⟨b, hp, hn, _, _⟩ :=
    associated_signature_of_not_exceptional z hz B hAlt hInt hType hB
  exact ⟨⟨b 0, hp⟩, ⟨b 1, hn⟩⟩

/-- Nonnegativity is the literal condition on every diagonal value, not a matrix surrogate. -/
theorem associated_nonnegative_iff_zero (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet) (B : RealForm)
    (hAlt : ∀ x, B x x = 0)
    (hInt : IntegralOnPeriodLattice (specialPeriodMap.point z) B)
    (hType : IsTypeOneOne B) :
    (∀ x, 0 ≤ (associatedSesquilinear B hType x x).re) ↔ B = 0 := by
  constructor
  · intro hNonneg
    by_contra hB
    obtain ⟨_, ⟨y, hy⟩⟩ :=
      associated_indefinite_of_not_exceptional z hz B hAlt hInt hType hB
    exact (not_le_of_gt hy) (hNonneg y)
  · intro hB x
    rw [associatedSesquilinear_re, hB]
    simp

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
