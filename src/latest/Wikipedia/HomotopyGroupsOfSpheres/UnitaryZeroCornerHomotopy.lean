import Wikipedia.HomotopyGroupsOfSpheres.UnitaryZeroCorner
import Mathlib.Topology.Homotopy.Basic

/-! # The continuous unitary zero-corner reduction, including both endpoints -/

noncomputable section

open scoped Matrix unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.UnitaryZeroCorner

variable {N M : Type*} [Fintype N] [DecidableEq N] [Fintype M] [DecidableEq M]

abbrev Domain (N M : Type*) [Fintype N] [DecidableEq N] [Fintype M] [DecidableEq M] :=
  {U : unitary (Matrix (N ⊕ M) (N ⊕ M) ℂ) // U.val.toBlocks₂₂ = 0}

theorem fromBlocks_mem (U : Domain N M) :
    Matrix.fromBlocks U.val.val.toBlocks₁₁ U.val.val.toBlocks₁₂ U.val.val.toBlocks₂₁ 0 ∈
      unitary (Matrix (N ⊕ M) (N ⊕ M) ℂ) := by
  have he : Matrix.fromBlocks U.val.val.toBlocks₁₁ U.val.val.toBlocks₁₂
      U.val.val.toBlocks₂₁ 0 = U.val.val := by
    simpa only [U.property] using Matrix.fromBlocks_toBlocks U.val.val
  rw [he]
  exact U.val.property

def atAngle (θ : ℝ) (U : Domain N M) : unitary (Matrix (N ⊕ M) (N ⊕ M) ℂ) :=
  ⟨deformation U.val.val.toBlocks₁₁ U.val.val.toBlocks₁₂ U.val.val.toBlocks₂₁
    (Real.sin θ) (Real.cos θ),
    deformation_unitary _ _ _ (fromBlocks_mem U) _ _ (Real.sin_sq_add_cos_sq θ)⟩

theorem atAngle_zero (U : Domain N M) : atAngle 0 U = U.val := by
  apply Subtype.ext
  change deformation _ _ _ (Real.sin 0) (Real.cos 0) = U.val.val
  simp only [deformation, Real.sin_zero, Real.cos_zero, zero_smul, sub_zero, one_smul]
  simpa only [U.property] using Matrix.fromBlocks_toBlocks U.val.val

theorem atAngle_half_pi (U : Domain N M) :
    (atAngle (Real.pi / 2) U).val =
      Matrix.fromBlocks (U.val.val.toBlocks₁₁ - U.val.val.toBlocks₁₂ * U.val.val.toBlocks₂₁)
        0 0 1 := by
  change deformation _ _ _ (Real.sin (Real.pi / 2)) (Real.cos (Real.pi / 2)) = _
  simp [deformation]

theorem continuous_upperLeft : Continuous (fun U : Domain N M ↦ U.val.val.toBlocks₁₁) :=
  (continuous_subtype_val.comp continuous_subtype_val).matrix_submatrix Sum.inl Sum.inl

theorem continuous_upperRight : Continuous (fun U : Domain N M ↦ U.val.val.toBlocks₁₂) :=
  (continuous_subtype_val.comp continuous_subtype_val).matrix_submatrix Sum.inl Sum.inr

theorem continuous_lowerLeft : Continuous (fun U : Domain N M ↦ U.val.val.toBlocks₂₁) :=
  (continuous_subtype_val.comp continuous_subtype_val).matrix_submatrix Sum.inr Sum.inl

theorem continuous_atAngle : Continuous (fun p : ℝ × Domain N M ↦ atAngle p.1 p.2) := by
  have hA := (continuous_upperLeft (N := N) (M := M)).comp (continuous_snd (X := ℝ))
  have hB := (continuous_upperRight (N := N) (M := M)).comp (continuous_snd (X := ℝ))
  have hC := (continuous_lowerLeft (N := N) (M := M)).comp (continuous_snd (X := ℝ))
  have hs := Real.continuous_sin.comp (continuous_fst (Y := Domain N M))
  have ht := Real.continuous_cos.comp (continuous_fst (Y := Domain N M))
  apply Continuous.subtype_mk
  apply continuous_matrix
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · exact (continuous_apply_apply i j).comp (hA.sub (hs.smul (hB.matrix_mul hC)))
  · exact (continuous_apply_apply i j).comp (ht.smul hB)
  · exact (continuous_apply_apply i j).comp (ht.smul hC)
  · exact (continuous_apply_apply i j).comp (hs.smul
      (show Continuous (fun _ : ℝ × Domain N M ↦ (1 : Matrix M M ℂ)) from continuous_const))

def reducedMatrix (U : Domain N M) : Matrix N N ℂ :=
  U.val.val.toBlocks₁₁ - U.val.val.toBlocks₁₂ * U.val.val.toBlocks₂₁

theorem reducedMatrix_unitary (U : Domain N M) : reducedMatrix U ∈ unitary (Matrix N N ℂ) := by
  have h := (atAngle (Real.pi / 2) U).property.2
  change (atAngle (Real.pi / 2) U).val * (atAngle (Real.pi / 2) U).valᴴ = 1 at h
  rw [atAngle_half_pi, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one] at h
  have hr := (Matrix.fromBlocks_inj.mp h).1
  simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, add_zero] at hr
  exact ⟨mul_eq_one_comm.mp hr, hr⟩

def reduction : C(Domain N M, unitary (Matrix N N ℂ)) where
  toFun U := ⟨reducedMatrix U, reducedMatrix_unitary U⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_upperLeft.sub (continuous_upperRight.matrix_mul continuous_lowerLeft)

def inclusion : C(Domain N M, unitary (Matrix (N ⊕ M) (N ⊕ M) ℂ)) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def reducedInclusion : C(Domain N M, unitary (Matrix (N ⊕ M) (N ⊕ M) ℂ)) :=
  ⟨atAngle (Real.pi / 2), continuous_atAngle.comp (continuous_const.prodMk continuous_id)⟩

theorem reducedInclusion_val (U : Domain N M) :
    (reducedInclusion U).val = Matrix.fromBlocks (reduction U).val 0 0 1 :=
  atAngle_half_pi U

def homotopy : (inclusion (N := N) (M := M)).Homotopy reducedInclusion where
  toFun p := atAngle ((p.1 : ℝ) * (Real.pi / 2)) p.2
  continuous_toFun := continuous_atAngle.comp
    (((continuous_subtype_val.comp continuous_fst).mul_const _).prodMk continuous_snd)
  map_zero_left U := by
    change atAngle ((0 : ℝ) * (Real.pi / 2)) U = U.val
    rw [zero_mul, atAngle_zero]
  map_one_left U := by
    change atAngle ((1 : ℝ) * (Real.pi / 2)) U = atAngle (Real.pi / 2) U
    rw [one_mul]

end Wikipedia.HomotopyGroupsOfSpheres.UnitaryZeroCorner
