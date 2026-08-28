import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniquenessIntegral
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneHermitianProperties
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneIntegral

/-!
# The actual integral type-(1,1) form of unitary data

The imaginary part is made into a real bilinear form using the original
sesquilinear maps.  Alternation, type `(1,1)`, and integrality on the original
period lattice are proved, and the Hermitian construction recovers the
original form.  No cohomological or Chern-class identification is asserted.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniqueness
namespace UnitaryDatum

open PeriodTorusTypeOneOne PeriodTorusTheta

variable {p : PeriodDomain} (D : UnitaryDatum p)

theorem form_real_smul_left (r : ℝ) (x y : ComplexPlane₂) :
    D.form (r • x) y = r • D.form x y := by
  have hx : r • x = (r : ℂ) • x := by ext i; rfl
  rw [hx, map_smul, LinearMap.smul_apply]
  rfl

theorem form_real_smul_right (r : ℝ) (x y : ComplexPlane₂) :
    D.form x (r • y) = r • D.form x y := by
  have hy : r • y = (r : ℂ) • y := by ext i; rfl
  rw [hy, map_smulₛₗ]
  change star (r : ℂ) * D.form x y = (r : ℂ) * D.form x y
  rw [Complex.star_def, Complex.conj_ofReal]

/-- The actual imaginary part of the original form, real-bilinearly. -/
def imaginaryForm : RealForm where
  toFun x :=
    { toFun := fun y => (D.form x y).im
      map_add' y z := by simp only [map_add, Complex.add_im]
      map_smul' r y := by
        change (D.form x (r • y)).im = r • (D.form x y).im
        rw [D.form_real_smul_right, Complex.smul_im] }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change (D.form (x + y) z).im = (D.form x z).im + (D.form y z).im
    simp only [map_add, LinearMap.add_apply, Complex.add_im]
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    change (D.form (r • x) y).im = r • (D.form x y).im
    rw [D.form_real_smul_left, Complex.smul_im]

@[simp] theorem imaginaryForm_apply (x y : ComplexPlane₂) :
    D.imaginaryForm x y = (D.form x y).im := rfl

theorem imaginaryForm_self (x : ComplexPlane₂) : D.imaginaryForm x x = 0 :=
  IsHermitian.diagonal_im D.form D.hermitian x

theorem imaginaryForm_isTypeOneOne : IsTypeOneOne D.imaginaryForm :=
  isTypeOneOne_of_sesquilinear_im D.imaginaryForm D.form (fun _ _ => rfl)

theorem imaginaryForm_integral : IntegralOnPeriodLattice p D.imaginaryForm := by
  intro x hx y hy
  exact D.imaginary_pairing_integral_of_mem x y hx hy

/-- The old tangent-form construction recovers the genuine input form. -/
theorem form_eq_associatedSesquilinear :
    D.form = associatedSesquilinear D.imaginaryForm D.imaginaryForm_isTypeOneOne :=
  eq_associatedSesquilinear_of_im D.imaginaryForm D.imaginaryForm_isTypeOneOne
    D.form (fun _ _ => rfl)

end UnitaryDatum
end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniqueness
