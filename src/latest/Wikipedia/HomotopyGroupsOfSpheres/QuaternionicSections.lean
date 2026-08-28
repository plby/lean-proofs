import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

/-!
# Local sections of the quaternionic two-frame projection

Quaternionic rotations provide a continuous section wherever the first
quaternion coordinate is nonzero. A rotation also completes columns whose
first coordinate vanishes, proving surjectivity of the projection.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

open HopfProblem.UnitQuaternionSphere

local notation "ℍ" => Quaternion ℝ

/-- A quaternionic rotation with real diagonal entries. -/
def rotationMatrix (r : ℝ) (b : ℍ) : Matrix (Fin 2) (Fin 2) ℍ :=
  !![(r : ℍ), -star b; b, (r : ℍ)]

theorem rotationMatrix_unitary (r : ℝ) (b : ℍ)
    (h : r ^ 2 + Quaternion.normSq b = 1) :
    rotationMatrix r b ∈ unitary (Matrix (Fin 2) (Fin 2) ℍ) := by
  have hsum : ((r ^ 2 : ℝ) : ℍ) + ((Quaternion.normSq b : ℝ) : ℍ) = 1 := by
    rw [← Quaternion.coe_add, h, Quaternion.coe_one]
  have hsum' : ((Quaternion.normSq b : ℝ) : ℍ) + ((r ^ 2 : ℝ) : ℍ) = 1 :=
    (add_comm _ _).trans hsum
  simp only [Quaternion.coe_pow] at hsum hsum'
  constructor <;> apply Matrix.ext <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Quaternion.star_mul_self, Quaternion.self_mul_star, Quaternion.coe_commutes,
      Quaternion.normSq_coe, hsum, hsum']

def rotation (r : ℝ) (b : ℍ) (h : r ^ 2 + Quaternion.normSq b = 1) : SpTwo :=
  ⟨rotationMatrix r b, rotationMatrix_unitary r b h⟩

/-- The other diagonal inclusion. -/
def firstDiagonal (q : UnitQuaternions) : SpTwo := ⟨!![q.val, 0; 0, 1], by
  constructor <;> apply Matrix.ext <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Unitary.star_mul_self_of_mem q.property,
      Unitary.mul_star_self_of_mem q.property]⟩

theorem continuous_firstDiagonal : Continuous firstDiagonal := by
  apply Continuous.subtype_mk
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> dsimp [firstDiagonal] <;> fun_prop

/-- Normalize a nonzero quaternion to a unit quaternion. -/
def normalize (a : ℍ) (ha : a ≠ 0) : UnitQuaternions :=
  ⟨‖a‖⁻¹ • a, (mem_unitary_iff_norm_eq_one _).mpr (by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha)])⟩

theorem normalize_mul_norm (a : ℍ) (ha : a ≠ 0) :
    (normalize a ha).val * (‖a‖ : ℍ) = a := by
  rw [Quaternion.mul_coe_eq_smul]
  change ‖a‖ • (‖a‖⁻¹ • a) = a
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha), one_smul]

/-- The open chart where the first quaternionic coordinate is nonzero. -/
def firstChart : Set BaseSphere := {v | v.val.fst ≠ 0}

theorem isOpen_firstChart : IsOpen firstChart := by
  exact isOpen_ne.preimage ((WithLp.continuous_fst 2 ℍ ℍ).comp continuous_subtype_val)

theorem firstChart_norm (v : BaseSphere) :
    ‖v.val.fst‖ ^ 2 + Quaternion.normSq v.val.snd = 1 := by
  simpa only [Quaternion.normSq_eq_norm_mul_self, pow_two] using
    (mem_baseSphere_iff v.val).mp v.property

/-- A continuous completion of the first column on the first chart. -/
def firstSection (v : firstChart) : SpTwo :=
  firstDiagonal (normalize v.val.val.fst v.property) *
    rotation ‖v.val.val.fst‖ v.val.val.snd (firstChart_norm v.val)

theorem projection_firstSection (v : firstChart) : projection (firstSection v) = v.val := by
  apply Subtype.ext
  apply (WithLp.equiv 2 (ℍ × ℍ)).injective
  apply Prod.ext
  · change (firstSection v).val 0 0 = v.val.val.fst
    simpa [firstSection, firstDiagonal, rotation, rotationMatrix,
      Matrix.mul_apply, Fin.sum_univ_two] using normalize_mul_norm v.val.val.fst v.property
  · change (firstSection v).val 1 0 = v.val.val.snd
    simp [firstSection, firstDiagonal, rotation, rotationMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem continuous_firstSection : Continuous firstSection := by
  have hv : Continuous (fun v : firstChart => v.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  have ha := (WithLp.continuous_fst 2 ℍ ℍ).comp hv
  have hb := (WithLp.continuous_snd 2 ℍ ℍ).comp hv
  have hn : Continuous (fun v : firstChart => normalize v.val.val.fst v.property) := by
    apply Continuous.subtype_mk
    exact (ha.norm.inv₀ (fun v => norm_ne_zero_iff.mpr v.property)).smul ha
  have hr : Continuous (fun v : firstChart =>
      rotation ‖v.val.val.fst‖ v.val.val.snd (firstChart_norm v.val)) := by
    apply Continuous.subtype_mk
    apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j <;> dsimp [rotation, rotationMatrix]
    · exact Quaternion.continuous_coe.comp ha.norm
    · exact hb.star.neg
    · exact hb
    · exact Quaternion.continuous_coe.comp ha.norm
  exact (continuous_firstDiagonal.comp hn).mul hr

@[simp] theorem north_mem_firstChart : north ∈ firstChart := by
  change (1 : ℍ) ≠ 0
  exact one_ne_zero

@[simp] theorem firstSection_north : firstSection ⟨north, north_mem_firstChart⟩ = 1 := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [firstSection, firstDiagonal, normalize, rotation, rotationMatrix, north]

/-- Every unit column extends to a quaternionic orthonormal two-frame. -/
theorem projection_surjective : Function.Surjective projection := by
  intro v
  by_cases ha : v.val.fst = 0
  · have hr : (0 : ℝ) ^ 2 + Quaternion.normSq v.val.snd = 1 := by
      simpa only [ha, map_zero, zero_add, zero_pow (by decide : 2 ≠ 0)] using
        (mem_baseSphere_iff v.val).mp v.property
    refine ⟨rotation 0 v.val.snd hr, ?_⟩
    apply Subtype.ext
    apply (WithLp.equiv 2 (ℍ × ℍ)).injective
    apply Prod.ext
    · change ((0 : ℝ) : ℍ) = v.val.fst
      rw [ha, Quaternion.coe_zero]
    · rfl
  · exact ⟨firstSection ⟨v, ha⟩, projection_firstSection _⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration
