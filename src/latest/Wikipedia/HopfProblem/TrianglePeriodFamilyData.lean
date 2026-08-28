import Wikipedia.HopfProblem.PeriodFamily
import Wikipedia.HopfProblem.PeriodMonodromy
import Wikipedia.HopfProblem.SpecialPeriodsTrianglePresentation

/-!
# Period data equivariant under the actual triangle group

Only the two generator transformation laws are required of the supplied
holomorphic period map.  They imply the period-matrix covariance for
every element of the constructed free product.  The complex matrices
are extracted from the actual period matrices and satisfy the cocycle
law; no global quotient or complex structure is an input field.
-/

noncomputable section

open Set Matrix
open scoped ContDiff MatrixGroups

namespace Wikipedia.HopfProblem.TrianglePeriodFamily

open SpecialPeriods

/-- The actual dual integral representation, with complex coefficients. -/
def dualComplexMatrix (g : TriangleGroup) : Matrix (Fin 4) (Fin 4) ℂ :=
  (triangleDualRepresentation g : LatticeMatrix).map (Int.castRingHom ℂ)

@[simp] theorem dualComplexMatrix_one : dualComplexMatrix 1 = 1 := by
  simp [dualComplexMatrix]

theorem dualComplexMatrix_mul (g h : TriangleGroup) :
    dualComplexMatrix (g * h) = dualComplexMatrix g * dualComplexMatrix h := by
  simp only [dualComplexMatrix, map_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact Matrix.map_mul

@[simp] theorem dualComplexMatrix_generator₁ :
    dualComplexMatrix triangleGenerator₁ = A₁.map (Int.castRingHom ℂ) := by
  rw [dualComplexMatrix, triangleDualRepresentation_generator₁_matrix]

@[simp] theorem dualComplexMatrix_generator₂ :
    dualComplexMatrix triangleGenerator₂ = A₂.map (Int.castRingHom ℂ) := by
  rw [dualComplexMatrix, triangleDualRepresentation_generator₂_matrix]

/-- The transposed source coordinate representation. -/
def coordinateComplexMatrix (g : TriangleGroup) : Matrix (Fin 4) (Fin 4) ℂ :=
  dualComplexMatrix g⁻¹

theorem coordinateComplexMatrix_eq (g : TriangleGroup) :
    coordinateComplexMatrix g = (triangleCoordinateMatrix g).map (Int.castRingHom ℂ) := by
  unfold coordinateComplexMatrix dualComplexMatrix
  rw [← triangleCoordinateMatrix_inv, inv_inv]

@[simp] theorem dual_mul_coordinate (g : TriangleGroup) :
    dualComplexMatrix g * coordinateComplexMatrix g = 1 := by
  rw [coordinateComplexMatrix, ← dualComplexMatrix_mul, mul_inv_cancel,
    dualComplexMatrix_one]

/-- Extracting the two right columns, in the source's normalized convention. -/
def matrixRight (M : Matrix (Fin 2) (Fin 4) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i k => M i (![2, 3] k)

theorem matrixRight_mul (R : Matrix (Fin 2) (Fin 2) ℂ)
    (M : Matrix (Fin 2) (Fin 4) ℂ) : matrixRight (R * M) = R * matrixRight M := rfl

/-- The normalized period matrix has the identity as its last two columns. -/
theorem periodMatrix_right (p : PeriodPoint) (R : Matrix (Fin 2) (Fin 2) ℂ) :
    (fun i k => (R * p.matrix) i (![2, 3] k)) = R := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [PeriodPoint.matrix, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem matrixRight_periodMatrix (p : PeriodPoint) : matrixRight p.matrix = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [matrixRight, PeriodPoint.matrix]

variable (V B : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]

/-- Actual admissible holomorphic periods with the two source generator
laws, over a base carrying an actual holomorphic triangle action. -/
structure Data where
  periods : HolomorphicPeriodMap V B
  base_holomorphic : ∀ g : TriangleGroup,
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ V) ω (fun b : B => g • b)
  covariance₁ : ∀ b, periods.point (triangleGenerator₁ • b) = (periods.point b).step₁
  covariance₂ : ∀ b, periods.point (triangleGenerator₂ • b) = (periods.point b).step₂

namespace Data

variable {V B} (D : Data V B)

/-- The complex monodromy matrix, extracted from the last two columns
of the target period matrix after dual lattice transport. -/
def rightBlock (g : TriangleGroup) (b : B) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i k => ((D.periods.point (g • b)).val.matrix * dualComplexMatrix g) i (![2, 3] k)

private def HasCovariance (g : TriangleGroup) : Prop :=
  ∀ b : B, ∃ R : Matrix (Fin 2) (Fin 2) ℂ,
    (D.periods.point (g • b)).val.matrix * dualComplexMatrix g =
      R * (D.periods.point b).val.matrix

private theorem hasCovariance_one : D.HasCovariance 1 := by
  intro b
  exact ⟨1, by simp⟩

private theorem hasCovariance_mul {g h : TriangleGroup}
    (hg : D.HasCovariance g) (hh : D.HasCovariance h) : D.HasCovariance (g * h) := by
  intro b
  obtain ⟨Rg, hg⟩ := hg (h • b)
  obtain ⟨Rh, hh⟩ := hh b
  refine ⟨Rg * Rh, ?_⟩
  rw [mul_smul, dualComplexMatrix_mul, ← Matrix.mul_assoc, hg, Matrix.mul_assoc,
    hh, Matrix.mul_assoc]

private theorem hasCovariance_generator₁ : D.HasCovariance triangleGenerator₁ := by
  intro b
  refine ⟨(D.periods.point b).val.R₁, ?_⟩
  rw [D.covariance₁, dualComplexMatrix_generator₁]
  change (D.periods.point b).val.step₁.matrix * A₁.map (Int.castRingHom ℂ) = _
  rw [PeriodPoint.step₁_matrix _ ((D.periods.point b).val.τ_ne_zero
    (D.periods.point b).property.1), Matrix.mul_assoc]
  have h : (T₁.map (Int.castRingHom ℂ)).transpose * A₁.map (Int.castRingHom ℂ) = 1 := by
    change T₁.transpose.map (Int.castRingHom ℂ) * A₁.map (Int.castRingHom ℂ) = 1
    rw [← Matrix.map_mul, show T₁.transpose * A₁ = 1 by decide]
    simp
  rw [h, Matrix.mul_one]

private theorem hasCovariance_generator₂ : D.HasCovariance triangleGenerator₂ := by
  intro b
  refine ⟨(D.periods.point b).val.R₂, ?_⟩
  rw [D.covariance₂, dualComplexMatrix_generator₂]
  change (D.periods.point b).val.step₂.matrix * A₂.map (Int.castRingHom ℂ) = _
  rw [PeriodPoint.step₂_matrix _ ((D.periods.point b).val.τ_ne_zero
    (D.periods.point b).property.1), Matrix.mul_assoc]
  have h : (T₂.map (Int.castRingHom ℂ)).transpose * A₂.map (Int.castRingHom ℂ) = 1 := by
    change T₂.transpose.map (Int.castRingHom ℂ) * A₂.map (Int.castRingHom ℂ) = 1
    rw [← Matrix.map_mul, show T₂.transpose * A₂ = 1 by decide]
    simp
  rw [h, Matrix.mul_one]

private theorem hasCovariance_pow {g : TriangleGroup} (hg : D.HasCovariance g) (n : ℕ) :
    D.HasCovariance (g ^ n) := by
  induction n with
  | zero => simpa using D.hasCovariance_one
  | succ n ih => simpa only [pow_succ] using D.hasCovariance_mul ih hg

private theorem cyclic_eq_generator_pow {n : ℕ} [NeZero n]
    (x : Multiplicative (ZMod n)) :
    x = Multiplicative.ofAdd (1 : ZMod n) ^ x.toAdd.val := by
  change x.toAdd = x.toAdd.val • (1 : ZMod n)
  simpa only [nsmul_eq_mul, mul_one] using (ZMod.natCast_zmod_val x.toAdd).symm

/-- The generator identities extend to every actual word in the free
product, not merely to assumed monodromy data for individual elements. -/
private theorem hasCovariance (g : TriangleGroup) : D.HasCovariance g := by
  induction g using Monoid.Coprod.induction_on with
  | inl x =>
      rw [cyclic_eq_generator_pow x, map_pow]
      exact D.hasCovariance_pow D.hasCovariance_generator₁ _
  | inr x =>
      rw [cyclic_eq_generator_pow x, map_pow]
      exact D.hasCovariance_pow D.hasCovariance_generator₂ _
  | mul g h hg hh => exact D.hasCovariance_mul hg hh

theorem rightBlock_eq_of_covariance (g : TriangleGroup) (b : B)
    (R : Matrix (Fin 2) (Fin 2) ℂ)
    (hR : (D.periods.point (g • b)).val.matrix * dualComplexMatrix g =
      R * (D.periods.point b).val.matrix) : D.rightBlock g b = R := by
  unfold rightBlock
  rw [hR, periodMatrix_right]

/-- Proposition 3.16 for every group element, deduced from the two
generator period laws and the actual integral representation. -/
theorem matrix_covariance (g : TriangleGroup) (b : B) :
    (D.periods.point (g • b)).val.matrix * dualComplexMatrix g =
      D.rightBlock g b * (D.periods.point b).val.matrix := by
  obtain ⟨R, hR⟩ := D.hasCovariance g b
  rw [D.rightBlock_eq_of_covariance g b R hR]
  exact hR

/-- The full source convention `Π(gb) = R_g(b) Π(b) ρ_Γ(g)`. -/
theorem matrix_transformation (g : TriangleGroup) (b : B) :
    (D.periods.point (g • b)).val.matrix =
      D.rightBlock g b * (D.periods.point b).val.matrix * coordinateComplexMatrix g := by
  calc
    _ = ((D.periods.point (g • b)).val.matrix * dualComplexMatrix g) *
        coordinateComplexMatrix g := by
      rw [Matrix.mul_assoc, dual_mul_coordinate, Matrix.mul_one]
    _ = _ := by rw [D.matrix_covariance]

/-- The right block before normalization, whose inverse gives the
source's matrix `R_g`. -/
def sourceRightBlock (g : TriangleGroup) (b : B) : Matrix (Fin 2) (Fin 2) ℂ :=
  matrixRight ((D.periods.point b).val.matrix * coordinateComplexMatrix g)

theorem rightBlock_mul_sourceRightBlock (g : TriangleGroup) (b : B) :
    D.rightBlock g b * D.sourceRightBlock g b = 1 := by
  rw [sourceRightBlock, ← matrixRight_mul, ← Matrix.mul_assoc,
    ← D.matrix_transformation, matrixRight_periodMatrix]

/-- The constructed cocycle is exactly the inverse right block used
in the normalized period-matrix formula of the source. -/
theorem rightBlock_eq_sourceRightBlock_inv (g : TriangleGroup) (b : B) :
    D.rightBlock g b = (D.sourceRightBlock g b)⁻¹ :=
  (Matrix.inv_eq_left_inv (D.rightBlock_mul_sourceRightBlock g b)).symm

@[simp] theorem rightBlock_one (b : B) : D.rightBlock 1 b = 1 := by
  exact D.rightBlock_eq_of_covariance 1 b 1 (by simp)

/-- The exact cocycle identity for the constructed complex monodromy. -/
theorem rightBlock_mul (g h : TriangleGroup) (b : B) :
    D.rightBlock (g * h) b = D.rightBlock g (h • b) * D.rightBlock h b := by
  apply D.rightBlock_eq_of_covariance
  rw [mul_smul, dualComplexMatrix_mul, ← Matrix.mul_assoc, D.matrix_covariance,
    Matrix.mul_assoc, D.matrix_covariance, Matrix.mul_assoc]

@[simp] theorem rightBlock_inv_mul (g : TriangleGroup) (b : B) :
    D.rightBlock g⁻¹ (g • b) * D.rightBlock g b = 1 := by
  rw [← D.rightBlock_mul, inv_mul_cancel, D.rightBlock_one]

@[simp] theorem rightBlock_mul_inv (g : TriangleGroup) (b : B) :
    D.rightBlock g (g⁻¹ • b) * D.rightBlock g⁻¹ b = 1 := by
  rw [← D.rightBlock_mul, mul_inv_cancel, D.rightBlock_one]

theorem rightBlock_det_ne_zero (g : TriangleGroup) (b : B) : (D.rightBlock g b).det ≠ 0 := by
  intro h
  have he := congrArg Matrix.det (D.rightBlock_inv_mul g b)
  rw [Matrix.det_mul, Matrix.det_one, h, mul_zero] at he
  exact zero_ne_one he

/-- The matrices give actual invertible complex-linear maps, not only
formal multiplication rules. -/
def rightEquiv (g : TriangleGroup) (b : B) : ComplexPlane₂ ≃L[ℂ] ComplexPlane₂ :=
  (Matrix.toLinearEquiv (Pi.basisFun ℂ (Fin 2)) (D.rightBlock g b)
    (isUnit_iff_ne_zero.mpr (D.rightBlock_det_ne_zero g b))).toContinuousLinearEquiv

@[simp] theorem rightEquiv_apply (g : TriangleGroup) (b : B) (w : ComplexPlane₂) :
    D.rightEquiv g b w = D.rightBlock g b *ᵥ w := by
  simp [rightEquiv, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]

end Data

end Wikipedia.HopfProblem.TrianglePeriodFamily
