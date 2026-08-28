import Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveLatitude
import Wikipedia.HomotopyGroupsOfSpheres.SphereCoordinateIsometries

/-! # Explicit isometric real coordinates for the Clifford parameter five-sphere -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

local notation "RealAmbient" => EuclideanSpace ℝ (Fin 6)
local notation "ComplexAmbient" => EuclideanSpace ℂ (Fin 3)

def ofRealCoordinates (x : RealAmbient) : ComplexAmbient :=
  WithLp.toLp 2 ![(x 0 : ℂ) + (x 1 : ℂ) * Complex.I,
    (x 2 : ℂ) + (x 3 : ℂ) * Complex.I, (x 4 : ℂ) + (x 5 : ℂ) * Complex.I]

def toRealCoordinates (z : ComplexAmbient) : RealAmbient :=
  WithLp.toLp 2 ![(z 0).re, (z 0).im, (z 1).re, (z 1).im, (z 2).re, (z 2).im]

theorem sixVector_last {α : Type*} (a b c d e f : α) :
    ![a, b, c, d, e, f] (5 : Fin 6) = f := rfl

theorem toRealCoordinates_ofRealCoordinates (x : RealAmbient) :
    toRealCoordinates (ofRealCoordinates x) = x := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    norm_num [toRealCoordinates, ofRealCoordinates, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, sixVector_last,
      Complex.mul_re, Complex.mul_im] <;> rfl

theorem ofRealCoordinates_toRealCoordinates (z : ComplexAmbient) :
    ofRealCoordinates (toRealCoordinates z) = z := by
  apply PiLp.ext
  intro i
  fin_cases i <;> apply Complex.ext <;>
    norm_num [toRealCoordinates, ofRealCoordinates, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, sixVector_last,
      Complex.mul_re, Complex.mul_im] <;> rfl

def coordinatesLinearEquiv : RealAmbient ≃ₗ[ℝ] ComplexAmbient where
  toFun := ofRealCoordinates
  invFun := toRealCoordinates
  left_inv := toRealCoordinates_ofRealCoordinates
  right_inv := ofRealCoordinates_toRealCoordinates
  map_add' x y := by
    apply PiLp.ext
    intro i
    fin_cases i <;> apply Complex.ext <;>
      norm_num [ofRealCoordinates, Matrix.cons_val_two, Complex.mul_re, Complex.mul_im]
  map_smul' r x := by
    apply PiLp.ext
    intro i
    fin_cases i <;> apply Complex.ext <;>
      norm_num [ofRealCoordinates, Matrix.cons_val_two, Complex.mul_re, Complex.mul_im]

theorem ofRealCoordinates_norm_sq (x : RealAmbient) : ‖ofRealCoordinates x‖ ^ 2 = ‖x‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← ComplexCrossProductUnitary.normPolynomial_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
  apply Complex.ext <;>
    norm_num [ComplexCrossProductUnitary.normPolynomial, ofRealCoordinates,
      Fin.sum_univ_succ, Matrix.cons_val_two, pow_two,
      Complex.mul_re, Complex.mul_im]
  all_goals ring_nf
  rfl

def coordinatesIsometry : RealAmbient ≃ₗᵢ[ℝ] ComplexAmbient where
  toLinearEquiv := coordinatesLinearEquiv
  norm_map' x := by
    change ‖ofRealCoordinates x‖ = ‖x‖
    nlinarith [ofRealCoordinates_norm_sq x, norm_nonneg (ofRealCoordinates x), norm_nonneg x]

def coordinateSphereHomeomorph :
    Metric.sphere (0 : RealAmbient) 1 ≃ₜ ComplexCrossProductUnitary.UnitSphere :=
  SphereCenteredCoordinates.sphereIsometry coordinatesIsometry

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
