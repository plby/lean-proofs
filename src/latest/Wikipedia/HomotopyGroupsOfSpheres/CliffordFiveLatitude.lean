import Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveLinearization
import Wikipedia.HomotopyGroupsOfSpheres.CliffordSixBalanced
import Wikipedia.HomotopyGroupsOfSpheres.BalancedPhasePaddingMatrix
import Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductScalarAction

/-! # Actual latitude coordinates for the realified Clifford sphere -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open ComplexCrossProductUnitary

def latitudeVector (θ : ℝ) (v : Coordinates) : Vector :=
  ![(Real.cos θ : ℂ) + (Real.sin θ : ℂ) * (v 0 : ℂ) * Complex.I,
    (Real.sin θ : ℂ) * ((v 1 : ℂ) + (v 2 : ℂ) * Complex.I),
    (Real.sin θ : ℂ) * ((v 3 : ℂ) + (v 4 : ℂ) * Complex.I)]

theorem normPolynomial_latitudeVector (θ : ℝ) (v : Coordinates) :
    normPolynomial (latitudeVector θ v) =
      ((Real.cos θ ^ 2 + Real.sin θ ^ 2 * ∑ k, v k ^ 2 : ℝ) : ℂ) := by
  have h3 : (2 : Fin 4).succ = 3 := rfl
  have h4 : (2 : Fin 3).succ.succ = 4 := rfl
  apply Complex.ext <;>
    norm_num [normPolynomial, latitudeVector, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      pow_two, Complex.mul_re, Complex.mul_im, h3, h4] <;> ring

theorem normPolynomial_latitude_unit (θ : ℝ) (v : UnitSphere) :
    normPolynomial (latitudeVector θ v.val) = 1 := by
  have hv : ∑ k, v.val k ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, mem_sphere_zero_iff_norm.mp v.property]
    norm_num
  rw [normPolynomial_latitudeVector, hv, mul_one, Real.cos_sq_add_sin_sq]
  rfl

def latitudePoint (θ : ℝ) (v : UnitSphere) : ComplexCrossProductUnitary.UnitSphere :=
  sphereOfNormPolynomial (latitudeVector θ v.val) (normPolynomial_latitude_unit θ v)

theorem latitudePoint_val (θ : ℝ) (v : UnitSphere) :
    (fun i ↦ (latitudePoint θ v).val i) = latitudeVector θ v.val := rfl

theorem continuous_latitudeVector :
    Continuous (fun p : ℝ × Coordinates ↦ latitudeVector p.1 p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [latitudeVector] <;> fun_prop

attribute [local irreducible] latitudeVector

theorem continuous_latitudeVector_unit :
    Continuous (fun p : ℝ × UnitSphere ↦ latitudeVector p.1 p.2.val) := by
  have hv : Continuous (fun p : ℝ × UnitSphere ↦ ((fun i ↦ p.2.val i) : Coordinates)) :=
    (PiLp.continuous_ofLp 2 (fun _ : Fin 5 ↦ ℝ)).comp
      (continuous_subtype_val.comp continuous_snd)
  exact continuous_latitudeVector.comp
    (f := fun p : ℝ × UnitSphere ↦ (p.1, (fun i ↦ p.2.val i)))
    (continuous_fst.prodMk hv)

theorem continuous_latitudePoint :
    Continuous (fun p : ℝ × UnitSphere ↦ latitudePoint p.1 p.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : ℝ × UnitSphere ↦ WithLp.toLp 2 (latitudeVector p.1 p.2.val))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℂ)).comp
    continuous_latitudeVector_unit

theorem latitudePoint_zero (v : UnitSphere) : latitudePoint 0 v = axis := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  change latitudeVector 0 v.val i = axis.val i
  rw [show axis.val i = ![1, 0, 0] i from congrFun axis_val i]
  fin_cases i <;> norm_num [latitudeVector]

theorem latitudePoint_re (θ : ℝ) (v : UnitSphere) :
    ((latitudePoint θ v).val 0).re = Real.cos θ := by
  change (latitudeVector θ v.val 0).re = _
  simp [latitudeVector, Complex.mul_re, Complex.mul_im,
    -Complex.ofReal_sin, -Complex.ofReal_cos]

theorem realCoordinates_latitude (θ : ℝ) (v : UnitSphere) :
    ComplexCliffordFive.realCoordinates (latitudePoint θ v).val =
      Real.sin θ • (fun i ↦ v.val i) := by
  funext i
  fin_cases i <;>
    norm_num [ComplexCliffordFive.realCoordinates, latitudePoint, sphereOfNormPolynomial,
      latitudeVector, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Complex.mul_re, Complex.mul_im, -Complex.ofReal_sin, -Complex.ofReal_cos] <;>
      exact Or.inl rfl

theorem matrix_smul (r : ℝ) (v : Coordinates) : matrix (r • v) = (r : ℂ) • matrix v := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [matrix, Matrix.cons_val_two, Matrix.cons_val_three,
      Complex.mul_re, Complex.mul_im]

theorem linearized_latitude_val (θ : ℝ) (v : UnitSphere) :
    (ComplexCliffordFive.linearizedSymmetricMap (latitudePoint θ v)).val.val =
      BalancedRealInvolutions.rotationMatrix 4 θ
        (ComplexMatrixRealification.matrix (matrix v.val)) := by
  rw [ComplexCliffordFive.linearizedSymmetricMap_val, latitudePoint_re,
    realCoordinates_latitude, matrix_smul, ComplexMatrixRealification.matrix_smul, map_smul]
  change (Real.cos θ : ℂ) • 1 + Complex.I •
    (Real.sin θ • RealUnitaryMatrices.complexification
      (ComplexMatrixRealification.matrix (matrix v.val))) = _
  rw [smul_comm Complex.I (Real.sin θ), ← smul_assoc]
  rfl

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
