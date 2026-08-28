import Wikipedia.HopfProblem.PeriodTorusTypeOneOneCriterion
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneIntegral
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneHermitianProperties
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneEtaMatrixSignature
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneEtaMatrixPullback
import Wikipedia.HopfProblem.SpecialPeriodsIntegralRelations

/-!
# The actual Hermitian form associated with the distinguished integral form

The coefficient vector is the source's `u ∧ w + 6 γ ∧ δ`, not the earlier
dual invariant matrix. Its transported real form is of type `(1,1)`.
The unique associated first-linear Hermitian form is identified with the
explicit period matrix by equality of its genuine imaginary part. Its
nondegeneracy and signature are therefore assertions about that actual
associated form, not merely about a candidate matrix.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

open SpecialPeriods

theorem periodPolynomial_eta (p : PeriodPoint) : periodPolynomial p periodRelationEta = 0 := by
  simp [periodPolynomial, periodRelationEta]

/-- The distinguished genuine real alternating form on the period-torus tangent model. -/
def etaTangent (p : PeriodDomain) : RealForm := tangentForm p periodRelationEta

theorem etaTangent_isTypeOneOne (p : PeriodDomain) : IsTypeOneOne (etaTangent p) :=
  (tangentForm_isTypeOneOne_iff p periodRelationEta).mpr (periodPolynomial_eta p.val)

theorem etaTangent_integral (p : PeriodDomain) : IntegralOnPeriodLattice p (etaTangent p) :=
  tangentForm_integral p periodRelationEta

/-- The actual uniquely associated first-linear Hermitian form. -/
def etaHermitian (p : PeriodDomain) : ComplexPlane₂ →ₗ[ℂ] ComplexPlane₂ →ₗ⋆[ℂ] ℂ :=
  associatedSesquilinear (etaTangent p) (etaTangent_isTypeOneOne p)

@[simp] theorem etaHermitian_im (p : PeriodDomain) (x y : ComplexPlane₂) :
    (etaHermitian p x y).im = etaTangent p x y :=
  associatedSesquilinear_im _ _ x y

theorem etaHermitian_conj_symm (p : PeriodDomain) (x y : ComplexPlane₂) :
    etaHermitian p y x = star (etaHermitian p x y) :=
  associatedSesquilinear_conj_symm _ _ (tangentForm_self p periodRelationEta) x y

/-- The explicitly computed matrix has precisely the genuine transported imaginary part. -/
theorem etaMatrixSesquilinear_im_tangent (p : PeriodDomain) (x y : ComplexPlane₂) :
    (etaMatrixSesquilinear p x y).im = etaTangent p x y := by
  have hE : (fun k : Fin 6 => (periodRelationEta k : ℝ)) = ![0, 0, 6, 1, 0, 0] := by
    funext k
    fin_cases k <;> norm_num [periodRelationEta]
  obtain ⟨r, rfl⟩ := (periodEquiv p).surjective x
  obtain ⟨s, rfl⟩ := (periodEquiv p).surjective y
  rw [etaMatrixSesquilinear_apply]
  change (etaMatrixForm p ((p.realEquiv.trans complexCoordinates) r)
      ((p.realEquiv.trans complexCoordinates) s)).im =
    tangentForm p periodRelationEta (periodEquiv p r) (periodEquiv p s)
  rw [etaMatrixForm_im_realEquiv, tangentForm_periodEquiv, hE]
  change r 1 * s 2 - r 2 * s 1 + 6 * (r 0 * s 3 - r 3 * s 0) =
    0 * (r 0 * s 1 - r 1 * s 0) + 0 * (r 0 * s 2 - r 2 * s 0) +
      6 * (r 0 * s 3 - r 3 * s 0) + 1 * (r 1 * s 2 - r 2 * s 1) +
      0 * (r 1 * s 3 - r 3 * s 1) + 0 * (r 2 * s 3 - r 3 * s 2)
  ring

/-- Uniqueness identifies the independently constructed associated form with the actual matrix. -/
theorem etaHermitian_eq_matrix (p : PeriodDomain) : etaHermitian p = etaMatrixSesquilinear p :=
  (eq_associatedSesquilinear_of_im (etaTangent p) (etaTangent_isTypeOneOne p)
    (etaMatrixSesquilinear p) (etaMatrixSesquilinear_im_tangent p)).symm

theorem etaHermitian_apply (p : PeriodDomain) (x y : ComplexPlane₂) :
    etaHermitian p x y = etaMatrixForm p x y := by
  rw [etaHermitian_eq_matrix, etaMatrixSesquilinear_apply]

theorem etaHermitian_nondegenerate (p : PeriodDomain) : (etaHermitian p).Nondegenerate := by
  rw [etaHermitian_eq_matrix]
  exact etaMatrixSesquilinear_nondegenerate p

theorem etaTangent_nondegenerate (p : PeriodDomain) : (etaTangent p).Nondegenerate :=
  (associatedSesquilinear_nondegenerate_iff _ _).mp (etaHermitian_nondegenerate p)

/-- Signature `(1,1)` expressed by a complete orthogonal complex basis. -/
def HasSignatureOneOne (H : ComplexPlane₂ →ₗ[ℂ] ComplexPlane₂ →ₗ⋆[ℂ] ℂ) : Prop :=
  ∃ b : Module.Basis (Fin 2) ℂ ComplexPlane₂,
    0 < (H (b 0) (b 0)).re ∧ (H (b 1) (b 1)).re < 0 ∧
      H (b 0) (b 1) = 0 ∧ H (b 1) (b 0) = 0

/-- The signature assertion holds for the uniquely associated genuine Hermitian form. -/
theorem etaHermitian_signature_one_one (p : PeriodDomain) :
    HasSignatureOneOne (etaHermitian p) := by
  unfold HasSignatureOneOne
  simpa only [etaHermitian_apply] using etaMatrixForm_signature_one_one p

theorem etaHermitian_indefinite (p : PeriodDomain) :
    (∃ x, 0 < (etaHermitian p x x).re) ∧ (∃ y, (etaHermitian p y y).re < 0) := by
  obtain ⟨b, hp, hn, _, _⟩ := etaHermitian_signature_one_one p
  exact ⟨⟨b 0, hp⟩, ⟨b 1, hn⟩⟩

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
