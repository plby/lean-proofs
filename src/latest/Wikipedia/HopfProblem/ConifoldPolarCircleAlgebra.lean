import Wikipedia.HopfProblem.ConifoldPolarDefs

/-!
# The original right-circle action in explicit polar coordinates

The three Hermitian coordinates are fixed.  The second column of the unitary
factor undergoes the two ordinary real rotation blocks, using the same signs
as the original complex normal coordinates.
-/

noncomputable section

open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.ConifoldPolar

open ConifoldStandardBoundary

/-- Two literal real rotation blocks of a complex scalar. -/
def normalRotation (u : ℂ) (z : Normal) : Normal :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm
    ![u.re * z 0 - u.im * z 1, u.im * z 0 + u.re * z 1,
      u.re * z 2 - u.im * z 3, u.im * z 2 + u.re * z 3]

theorem normalRotation_norm_sq (u : ℂ) (z : Normal) :
    ‖normalRotation u z‖ ^ 2 = Complex.normSq u * ‖z‖ ^ 2 := by
  simp [normalRotation, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ,
    Complex.normSq_apply]
  ring

theorem normalRotation_norm (u : ℂ) (hu : ‖u‖ = 1) (z : Normal) :
    ‖normalRotation u z‖ = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [normalRotation_norm_sq, Complex.normSq_eq_norm_sq, hu, one_pow, one_mul]

theorem normalCoordinates_rightCircle (u : ℂ) (M : MatrixSpace) :
    normalCoordinates (rightCircle u M) = normalRotation u (normalCoordinates M) := by
  ext i
  fin_cases i <;>
    simp [normalCoordinates, normalRotation, rightCircle_apply, mul_comm, add_comm]

theorem denominator_rightCircle (u : ℂ) (hu : ‖u‖ = 1) (M : MatrixSpace) :
    denominator (rightCircle u M) = denominator M := by
  rw [denominator, frobeniusSq_rightCircle u hu]
  rfl

theorem unitaryPart_rightCircle (u : ℂ) (hu : ‖u‖ = 1) (M : MatrixSpace) :
    unitaryPart (rightCircle u M) = rightCircle u (unitaryPart M) := by
  rw [unitaryPart, denominator_rightCircle u hu, deform_rightCircle _ u hu,
    ← Complex.ofReal_inv, smul_rightCircle]
  rw [Complex.ofReal_inv]
  rfl

theorem circleDiagonal_mul_conjTranspose (u : ℂ) (hu : ‖u‖ = 1) :
    circleDiagonal u * (circleDiagonal u).conjTranspose = 1 := by
  have hzero : u ≠ 0 := by
    intro h
    simp [h] at hu
  have hc : conj u = u⁻¹ := (Complex.inv_eq_conj hu).symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circleDiagonal_entries, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Fin.sum_univ_two, hc, hzero]

theorem positivePart_rightCircle (u : ℂ) (hu : ‖u‖ = 1) (M : MatrixSpace) :
    positivePart (rightCircle u M) = positivePart M := by
  rw [positivePart, unitaryPart_rightCircle u hu, rightCircle, rightCircle]
  calc
    (M * circleDiagonal u) * (unitaryPart M * circleDiagonal u).conjTranspose =
        (M * (circleDiagonal u * (circleDiagonal u).conjTranspose)) *
          (unitaryPart M).conjTranspose := by
      simp only [Matrix.conjTranspose_mul, mul_assoc]
    _ = positivePart M := by rw [circleDiagonal_mul_conjTranspose u hu, mul_one]; rfl

/-- The actual matrix-group circle map, without transporting an action through polar coordinates. -/
def circleAction (u : ℂ) (hu : ‖u‖ = 1) (M : SpecialLinear) : SpecialLinear :=
  ⟨rightCircle u M.val, (det_rightCircle u hu M.val).trans M.property⟩

/-- The literal standard circle action on the Euclidean unit three-sphere. -/
def sphereRotation (u : ℂ) (hu : ‖u‖ = 1) (z : NormalSphere) : NormalSphere :=
  ⟨normalRotation u z.val, by
    rw [Metric.mem_sphere, dist_zero_right, normalRotation_norm u hu]
    exact StandardSixSphereCircleModel.normalSphere_norm z⟩

@[simp] theorem circleAction_val (u : ℂ) (hu : ‖u‖ = 1) (M : SpecialLinear) :
    (circleAction u hu M).val = rightCircle u M.val := rfl

@[simp] theorem sphereRotation_val (u : ℂ) (hu : ‖u‖ = 1) (z : NormalSphere) :
    (sphereRotation u hu z).val = normalRotation u z.val := rfl

end Wikipedia.HopfProblem.ConifoldPolar
