import Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryLatitude
import Wikipedia.NoExoticSixSphere.RankSixUnitSpinor

/-! # The concrete two-sphere of rank-six orthogonal complex structures -/

noncomputable section

open scoped Matrix Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott

open NoExoticSixSphere NoExoticSixSphere.RankSixSkewMatrix

theorem vecCons_five {α : Type*} {n : ℕ} (a : α) (v : Fin (n + 5) → α) :
    Matrix.vecCons a v (5 : Fin (n + 6)) = v 4 := rfl

def realGenerator (v : Fin 3 → ℝ) : Matrix6 :=
  !![0, 0, 0, -1, 0, 0;
     0, 0, -v 1, 0, -v 0, -v 2;
     0, v 1, 0, 0, -v 2, v 0;
     1, 0, 0, 0, 0, 0;
     0, v 0, v 2, 0, 0, -v 1;
     0, v 2, -v 0, 0, v 1, 0]

theorem realGenerator_transpose (v : Fin 3 → ℝ) :
    (realGenerator v).transpose = -realGenerator v := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [realGenerator]

theorem sphereTwo_sum_sq (v : Sphere 2) : v.val 0 ^ 2 + v.val 1 ^ 2 + v.val 2 ^ 2 = 1 := by
  have h : ∑ i, v.val i ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, mem_sphere_zero_iff_norm.mp v.property]
    norm_num
  simpa [Fin.sum_univ_succ, add_assoc] using h

theorem realGenerator_square (v : Sphere 2) :
    realGenerator v.val * realGenerator v.val = -(1 : Matrix6) := by
  have hv := sphereTwo_sum_sq v
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realGenerator, Matrix.mul_apply, sum_six,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vecCons_five] <;>
      nlinarith [hv]

theorem realGenerator_realification (v : Fin 3 → ℝ) :
    Matrix.reindex (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6) finSumFinEquiv
      (ComplexMatrixRealification.matrix (MatrixBorder.border Complex.I (generatorMatrix v))) =
        realGenerator v := by
  have hb : MatrixBorder.border Complex.I (generatorMatrix v) =
      !![Complex.I, 0, 0;
         0, (v 0 : ℂ) * Complex.I, -(v 1 : ℂ) + (v 2 : ℂ) * Complex.I;
         0, (v 1 : ℂ) + (v 2 : ℂ) * Complex.I, -(v 0 : ℂ) * Complex.I] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hb]
  have hi (i : Fin 6) : (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm i =
      ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1, Sum.inr 2] i := by
    fin_cases i <;> rfl
  apply Matrix.ext
  intro i j
  simp only [Matrix.reindex, Matrix.submatrix, hi]
  fin_cases i <;> fin_cases j <;>
    norm_num [ComplexMatrixRealification.matrix, realGenerator,
      Complex.mul_re, Complex.mul_im,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vecCons_five]

theorem continuous_realGenerator : Continuous realGenerator := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [realGenerator, Matrix.of_apply] <;> fun_prop

def rawStructureMap : C(Sphere 2, OrthogonalComplexStructures.Space 6) where
  toFun v := RankSixComplexProjection.ofMatrix (realGenerator v.val)
    (realGenerator_transpose v.val) (realGenerator_square v)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (LinearMap.continuous_of_finiteDimensional
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 6)).toAlgEquiv.toLinearMap).comp
      (continuous_realGenerator.comp
        ((PiLp.continuous_ofLp _ _).comp continuous_subtype_val))

theorem exists_structureMap :
    ∃ f : C(Sphere 2, OrthogonalComplexStructures.Space 6), f = rawStructureMap :=
  ⟨rawStructureMap, rfl⟩

/-- Keep the matrix constructor out of native group types; the equality below fixes the map. -/
def structureMap : C(Sphere 2, OrthogonalComplexStructures.Space 6) :=
  Classical.choose exists_structureMap

theorem structureMap_eq : structureMap = rawStructureMap :=
  Classical.choose_spec exists_structureMap

theorem structureMap_apply (v : Sphere 2) : structureMap v = rawStructureMap v :=
  DFunLike.congr_fun structureMap_eq v

theorem structureMap_matrix (v : Sphere 2) :
    RankSixComplexProjection.matrix (structureMap v) = realGenerator v.val := by
  rw [structureMap_apply]
  exact RankSixComplexProjection.matrix_ofMatrix _
    (realGenerator_transpose v.val) (realGenerator_square v)

theorem structureMap_pfaffian (v : Sphere 2) :
    pfaffian (RankSixComplexProjection.matrix (structureMap v)) = -1 := by
  rw [structureMap_matrix]
  have hv := sphereTwo_sum_sq v
  norm_num [pfaffian, realGenerator, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vecCons_five]
  nlinarith [hv]

def structurePole : Sphere 2 :=
  ⟨EuclideanSpace.basisFun (Fin 3) ℝ 1, mem_sphere_zero_iff_norm.mpr
    ((EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.1 1)⟩

end Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott
