import Wikipedia.HomotopyGroupsOfSpheres.BalancedDiagonalPaths

/-!
# Balanced involutions give paths in symmetric special-unitary matrices

The formula `cos θ · 1 + i sin θ · J` depends only on the real involution.
An orthogonal frame is used solely to prove its membership and determinant,
never as a continuous choice in the path construction.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

open RealUnitaryMatrices QuaternionicSymmetricMatrices

def rotationMatrix (n : ℕ) (θ : ℝ) (A : Matrix (Index n) (Index n) ℝ) :
    Matrix (Index n) (Index n) ℂ :=
  (Real.cos θ : ℂ) • 1 + ((Real.sin θ : ℂ) * Complex.I) • complexification A

theorem rotationMatrix_orbit (n : ℕ) (θ : ℝ)
    (U : unitary (Matrix (Index n) (Index n) ℝ)) :
    rotationMatrix n θ (orbitMatrix n U) =
      complexification U.val * diagonalPhase n θ * (complexification U.val).transpose := by
  have hU : complexification U.val * (complexification U.val).transpose = 1 :=
    toComplex_mul_transpose U
  rw [rotationMatrix, orbitMatrix, map_mul, map_mul, complexification_transpose,
    diagonalPhase_eq]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one]
  rw [hU]

theorem rotationMatrix_relations {n : ℕ} (J : Space n) (θ : ℝ) :
    rotationMatrix n θ J.val ∈ unitary (Matrix (Index n) (Index n) ℂ) ∧
      (rotationMatrix n θ J.val).transpose = rotationMatrix n θ J.val ∧
      (rotationMatrix n θ J.val).det = 1 := by
  obtain ⟨U, hU⟩ := J.property
  let B := congruenceSpecial (toComplex U) (toComplex_det_square U) (diagonalSpecial n θ)
  have he : B.val.val.val = rotationMatrix n θ J.val := by
    change complexification U.val * diagonalPhase n θ * (complexification U.val).transpose = _
    rw [← hU]
    exact (rotationMatrix_orbit n θ U).symm
  rw [← he]
  exact ⟨B.val.val.property, B.val.property, congrArg (fun z : Circle ↦ (z : ℂ)) B.property⟩

def rotation {n : ℕ} (J : Space n) (θ : ℝ) : SpecialSpace (Index n) :=
  ⟨⟨⟨rotationMatrix n θ J.val, (rotationMatrix_relations J θ).1⟩,
    (rotationMatrix_relations J θ).2.1⟩,
    Circle.ext (rotationMatrix_relations J θ).2.2⟩

theorem continuous_rotation (n : ℕ) :
    Continuous (fun z : ℝ × Space n ↦ rotation z.2 z.1) := by
  have hJ : Continuous (fun z : ℝ × Space n ↦ complexification z.2.val) :=
    continuous_complexification.comp (continuous_subtype_val.comp continuous_snd)
  have hc : Continuous (fun z : ℝ × Space n ↦
      (Real.cos z.1 : ℂ) • (1 : Matrix (Index n) (Index n) ℂ)) :=
    (Complex.continuous_ofReal.comp (Real.continuous_cos.comp continuous_fst)).smul
      continuous_const
  have hs : Continuous (fun z : ℝ × Space n ↦
      ((Real.sin z.1 : ℂ) * Complex.I) • complexification z.2.val) :=
    ((Complex.continuous_ofReal.comp (Real.continuous_sin.comp continuous_fst)).mul
      continuous_const).smul hJ
  exact (((hc.add hs).subtype_mk _).subtype_mk _).subtype_mk _

theorem rotation_standard (n : ℕ) (θ : ℝ) : rotation (standard n) θ = diagonalSpecial n θ := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact (diagonalPhase_eq n θ).symm

def antipode (n : ℕ) : SpecialSpace (Index n) := diagonalSpecial n Real.pi

theorem antipode_matrix (n : ℕ) : (antipode n).val.val.val = -1 := diagonalPhase_pi n

@[simp] theorem rotation_zero {n : ℕ} (J : Space n) : rotation J 0 = specialIdentity := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change rotationMatrix n 0 J.val = 1
  simp [rotationMatrix]

theorem rotation_pi {n : ℕ} (J : Space n) : rotation J Real.pi = antipode n := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change rotationMatrix n Real.pi J.val = diagonalPhase n Real.pi
  rw [diagonalPhase_pi]
  simp [rotationMatrix]

theorem rotation_half_pi {n : ℕ} (J : Space n) :
    (rotation J (Real.pi / 2)).val.val.val = Complex.I • complexification J.val := by
  change rotationMatrix n (Real.pi / 2) J.val = _
  simp [rotationMatrix]

theorem rotation_midpoint_recover {n : ℕ} (J : Space n) :
    (rotation J (Real.pi / 2)).val.val.val.map Complex.im = J.val := by
  rw [rotation_half_pi]
  apply Matrix.ext
  intro r s
  change (Complex.I * ((J.val r s : ℝ) : ℂ)).im = J.val r s
  simp

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
