import Wikipedia.HopfProblem.UnitQuaternionSphere
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Instances.Matrix

/-!
# The quaternionic two-frame projection

`SpTwo` is the actual group of quaternionic unitary two-by-two matrices.
Its first-column projection takes values in the ordinary unit sphere of
the eight-dimensional real inner product space `ℍ × ℍ` with its Euclidean norm.
No homotopy-group computation is assumed in these definitions.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

open HopfProblem.UnitQuaternionSphere

local notation "ℍ" => Quaternion ℝ

/-- The compact quaternionic symplectic group, with its matrix subspace topology. -/
abbrev SpTwo := unitary (Matrix (Fin 2) (Fin 2) ℍ)

abbrev QuaternionPlane := WithLp 2 (ℍ × ℍ)

abbrev BaseSphere := Metric.sphere (0 : QuaternionPlane) 1

instance : IsTopologicalGroup SpTwo := inferInstance

theorem norm_sq_plane (v : QuaternionPlane) :
    ‖v‖ ^ 2 = Quaternion.normSq v.fst + Quaternion.normSq v.snd := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [Quaternion.normSq_eq_norm_mul_self, pow_two]

theorem mem_baseSphere_iff (v : QuaternionPlane) :
    v ∈ BaseSphere ↔ Quaternion.normSq v.fst + Quaternion.normSq v.snd = 1 := by
  rw [mem_sphere_zero_iff_norm, ← norm_sq_plane]
  constructor
  · intro h
    rw [h, one_pow]
  · intro h
    nlinarith [norm_nonneg v]

/-- Coordinates identifying the quaternionic plane isometrically with real eight-space. -/
def planeCoordinates : QuaternionPlane ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 8) :=
  (LinearIsometryEquiv.withLpProdCongr 2
    Quaternion.linearIsometryEquivTuple Quaternion.linearIsometryEquivTuple).trans
    ((PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin 4 ⊕ Fin 4 => ℝ)).symm.trans
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv))

/-- This is a homeomorphism to the literal standard seven-sphere. -/
def baseSphereHomeomorph : BaseSphere ≃ₜ HopfProblem.SphereHomology.UnitSphere 7 where
  toFun v := ⟨planeCoordinates v, by
    simpa only [mem_sphere_zero_iff_norm, planeCoordinates.norm_map] using v.property⟩
  invFun v := ⟨planeCoordinates.symm v, by
    simpa only [mem_sphere_zero_iff_norm, planeCoordinates.symm.norm_map] using v.property⟩
  left_inv v := by apply Subtype.ext; exact planeCoordinates.symm_apply_apply v
  right_inv v := by apply Subtype.ext; exact planeCoordinates.apply_symm_apply v
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem column_normSq (A : SpTwo) (j : Fin 2) :
    Quaternion.normSq (A.val 0 j) + Quaternion.normSq (A.val 1 j) = 1 := by
  have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℍ => B j j)
    (Unitary.coe_star_mul_self A)
  have hq : ((Quaternion.normSq (A.val 0 j) + Quaternion.normSq (A.val 1 j) : ℝ) : ℍ)
      = 1 := by
    simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Quaternion.star_mul_self, Matrix.one_apply_eq, Quaternion.coe_add] using h
  exact congrArg (fun q : ℍ => q.re) hq

/-- Forget the second column of a quaternionic orthonormal two-frame. -/
def projection : C(SpTwo, BaseSphere) where
  toFun A := ⟨WithLp.toLp 2 (A.val 0 0, A.val 1 0),
    (mem_baseSphere_iff _).mpr (column_normSq A 0)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (WithLp.prod_continuous_toLp 2 ℍ ℍ).comp
      ((continuous_subtype_val.matrix_elem 0 0).prodMk
        (continuous_subtype_val.matrix_elem 1 0))

/-- The first standard quaternionic basis vector. -/
def north : BaseSphere :=
  ⟨WithLp.toLp 2 (1, 0), (mem_baseSphere_iff _).mpr (by simp)⟩

@[simp] theorem projection_one : projection 1 = north := by
  apply Subtype.ext
  rfl

/-- The diagonal matrix fixing the first standard basis vector. -/
def fiberMatrix (q : ℍ) : Matrix (Fin 2) (Fin 2) ℍ := !![1, 0; 0, q]

theorem fiberMatrix_unitary (q : UnitQuaternions) :
    fiberMatrix q.val ∈ unitary (Matrix (Fin 2) (Fin 2) ℍ) := by
    constructor <;> apply Matrix.ext <;> intro i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Unitary.star_mul_self_of_mem q.property,
        Unitary.mul_star_self_of_mem q.property, fiberMatrix]

/-- Inclusion of the group preserving the first standard basis vector. -/
def fiberInclusion : UnitQuaternions →* SpTwo where
  toFun q := ⟨fiberMatrix q.val, fiberMatrix_unitary q⟩
  map_one' := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  map_mul' q r := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [fiberMatrix]

theorem continuous_fiberInclusion : Continuous fiberInclusion := by
  apply Continuous.subtype_mk
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> dsimp [fiberInclusion, fiberMatrix] <;> fun_prop

@[simp] theorem projection_fiberInclusion (q : UnitQuaternions) :
    projection (fiberInclusion q) = north := by
  apply Subtype.ext
  rfl

theorem projection_eq_north_iff (A : SpTwo) :
    projection A = north ↔ A.val 0 0 = 1 ∧ A.val 1 0 = 0 := by
  constructor
  · intro h
    exact ⟨congrArg (fun v : BaseSphere => v.val.fst) h,
      congrArg (fun v : BaseSphere => v.val.snd) h⟩
  · rintro ⟨h₀, h₁⟩
    apply Subtype.ext
    change WithLp.toLp 2 (A.val 0 0, A.val 1 0) = WithLp.toLp 2 (1, 0)
    rw [h₀, h₁]

theorem upperRight_eq_zero (A : SpTwo) (h : projection A = north) : A.val 0 1 = 0 := by
  obtain ⟨h₀, h₁⟩ := (projection_eq_north_iff A).mp h
  have hh := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℍ => B 0 1)
    (Unitary.coe_star_mul_self A)
  simpa [Matrix.mul_apply, Fin.sum_univ_two, h₀, h₁] using hh

theorem lowerRight_mem_unitary (A : SpTwo) (h : projection A = north) :
    A.val 1 1 ∈ unitary ℍ := by
  have hq : Quaternion.normSq (A.val 1 1) = 1 := by
    simpa only [upperRight_eq_zero A h, map_zero, zero_add] using column_normSq A 1
  exact ⟨by rw [Quaternion.star_mul_self, hq, Quaternion.coe_one],
    by rw [Quaternion.self_mul_star, hq, Quaternion.coe_one]⟩

/-- The actual fiber over the standard basis vector. -/
abbrev NorthFiber := { A : SpTwo // projection A = north }

/-- Recover the unique unit quaternion from a matrix in the fiber. -/
def fiberCoordinate (A : NorthFiber) : UnitQuaternions :=
  ⟨A.val.val 1 1, lowerRight_mem_unitary A.val A.property⟩

theorem fiberInclusion_coordinate (A : NorthFiber) : fiberInclusion (fiberCoordinate A) = A := by
  obtain ⟨h₀, h₁⟩ := (projection_eq_north_iff A.val).mp A.property
  have h₂ := upperRight_eq_zero A.val A.property
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [fiberInclusion, fiberMatrix, fiberCoordinate, h₀, h₁, h₂]

/-- The fiber is homeomorphic to the standard unit quaternion group, hence to `S³`. -/
def northFiberHomeomorph : UnitQuaternions ≃ₜ NorthFiber where
  toFun q := ⟨fiberInclusion q, projection_fiberInclusion q⟩
  invFun := fiberCoordinate
  left_inv q := by apply Subtype.ext; rfl
  right_inv A := by apply Subtype.ext; exact fiberInclusion_coordinate A
  continuous_toFun := continuous_fiberInclusion.subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_subtype_val).matrix_elem 1 1

theorem fiberInclusion_injective : Function.Injective fiberInclusion := by
  intro q r h
  apply Subtype.ext
  exact congrArg (fun A : SpTwo => A.val 1 1) h

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration
