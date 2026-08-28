import Wikipedia.HopfProblem.PeriodTorusTypeOneOneSignatureScaling
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneExterior

/-!
# Genuine nonzero integer multiples of the distinguished form

Both the actual tangent form and its associated Hermitian form scale by the
same integer. Every nonzero multiple is nondegenerate and has signature
`(1,1)`, including negative multiples. Its integral exterior square is
`12 n²` times the marked volume element.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

open SpecialPeriods

/-- The form of the actual integer multiple of the source coefficient vector. -/
def etaMultipleTangent (p : PeriodDomain) (n : ℤ) : RealForm :=
  tangentForm p (n • periodRelationEta)

theorem etaMultipleTangent_eq_smul (p : PeriodDomain) (n : ℤ) :
    etaMultipleTangent p n = (n : ℝ) • etaTangent p :=
  tangentForm_zsmul p n periodRelationEta

theorem etaMultipleTangent_isTypeOneOne (p : PeriodDomain) (n : ℤ) :
    IsTypeOneOne (etaMultipleTangent p n) := by
  rw [etaMultipleTangent_eq_smul]
  exact (etaTangent_isTypeOneOne p).smul (etaTangent p) (n : ℝ)

theorem etaMultipleTangent_integral (p : PeriodDomain) (n : ℤ) :
    IntegralOnPeriodLattice p (etaMultipleTangent p n) :=
  tangentForm_integral p (n • periodRelationEta)

/-- The actual associated Hermitian form, rather than a separately postulated matrix. -/
def etaMultipleHermitian (p : PeriodDomain) (n : ℤ) :
    ComplexPlane₂ →ₗ[ℂ] ComplexPlane₂ →ₗ⋆[ℂ] ℂ :=
  associatedSesquilinear (etaMultipleTangent p n) (etaMultipleTangent_isTypeOneOne p n)

theorem etaMultipleHermitian_eq_smul (p : PeriodDomain) (n : ℤ) :
    etaMultipleHermitian p n = (n : ℝ) • etaHermitian p := by
  unfold etaMultipleHermitian etaHermitian
  simp only [etaMultipleTangent_eq_smul]
  exact associatedSesquilinear_real_smul (etaTangent p) (etaTangent_isTypeOneOne p) (n : ℝ)

@[simp] theorem etaMultipleHermitian_im (p : PeriodDomain) (n : ℤ) (x y : ComplexPlane₂) :
    (etaMultipleHermitian p n x y).im = etaMultipleTangent p n x y :=
  associatedSesquilinear_im _ _ x y

theorem etaMultipleHermitian_conj_symm (p : PeriodDomain) (n : ℤ) (x y : ComplexPlane₂) :
    etaMultipleHermitian p n y x = star (etaMultipleHermitian p n x y) :=
  associatedSesquilinear_conj_symm _ _ (tangentForm_self p (n • periodRelationEta)) x y

theorem etaMultipleHermitian_nondegenerate (p : PeriodDomain) (n : ℤ) (hn : n ≠ 0) :
    (etaMultipleHermitian p n).Nondegenerate := by
  rw [etaMultipleHermitian_eq_smul]
  exact sesquilinear_real_smul_nondegenerate (etaHermitian p)
    (etaHermitian_nondegenerate p) (Int.cast_ne_zero.mpr hn)

theorem etaMultipleTangent_nondegenerate (p : PeriodDomain) (n : ℤ) (hn : n ≠ 0) :
    (etaMultipleTangent p n).Nondegenerate :=
  (associatedSesquilinear_nondegenerate_iff _ _).mp
    (etaMultipleHermitian_nondegenerate p n hn)

theorem etaMultipleHermitian_signature_one_one (p : PeriodDomain) (n : ℤ) (hn : n ≠ 0) :
    HasSignatureOneOne (etaMultipleHermitian p n) := by
  rw [etaMultipleHermitian_eq_smul]
  exact (etaHermitian_signature_one_one p).real_smul (Int.cast_ne_zero.mpr hn)

theorem etaMultipleHermitian_indefinite (p : PeriodDomain) (n : ℤ) (hn : n ≠ 0) :
    (∃ x, 0 < (etaMultipleHermitian p n x x).re) ∧
      (∃ y, (etaMultipleHermitian p n y y).re < 0) := by
  obtain ⟨b, hp, hn', _, _⟩ := etaMultipleHermitian_signature_one_one p n hn
  exact ⟨⟨b 0, hp⟩, ⟨b 1, hn'⟩⟩

/-- The tangent coefficient convention and the genuine exterior-power convention coincide. -/
theorem integralExteriorForm_etaMultiple (n : ℤ) :
    integralExteriorForm (n • periodRelationEta) = n • etaExteriorPower := by
  rw [map_smul]
  congr 1
  exact integralExteriorForm_eta

/-- The source's nonzero-square assertion is an equality in the actual exterior algebra. -/
theorem integralExteriorForm_etaMultiple_sq (n : ℤ) :
    (integralExteriorForm (n • periodRelationEta) : IntegralExterior) ^ 2 =
      (12 * n ^ 2) • volumeExterior := by
  rw [integralExteriorForm_etaMultiple, Submodule.coe_smul]
  exact zsmul_etaExterior_sq n

theorem integralExteriorForm_etaMultiple_sq_ne_zero (n : ℤ) (hn : n ≠ 0) :
    (integralExteriorForm (n • periodRelationEta) : IntegralExterior) ^ 2 ≠ 0 := by
  rw [integralExteriorForm_etaMultiple, Submodule.coe_smul]
  exact zsmul_etaExterior_sq_ne_zero n hn

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
