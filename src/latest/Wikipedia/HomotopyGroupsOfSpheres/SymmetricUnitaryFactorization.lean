import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexCentralizer
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicJointSpectralTheorem
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryCongruence
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Unitary congruence factorization of symmetric unitary matrices

Apply the proved simultaneous quaternionic spectral theorem to the fixed
scalar i and the anticommuting structure encoded by the symmetric matrix.
The first operator has only unit speeds, so its diagonalizing frame
commutes with i and is complex unitary. The second diagonalization gives
the factorization B = U Uᵀ.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

open QuaternionicColumns QuaternionicScalars

local notation "ℍ" => Quaternion ℝ

theorem exists_unitary_factor_fin (n : ℕ) (B : Space (Fin n)) :
    ∃ U : unitary (Matrix (Fin n) (Fin n) ℂ), U.val * U.val.transpose = B.val.val := by
  let D : Matrix (Fin n) (Fin n) ℍ := Matrix.diagonal (fun _ ↦ i)
  let P := quaternionMatrix B.val.val
  have hD : star D = -D := by
    change (Matrix.diagonal (fun _ : Fin n ↦ i)).conjTranspose = -Matrix.diagonal (fun _ ↦ i)
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_neg]
    congr 1
    funext a
    exact star_i
  have hDsq : D * D = -1 := by
    change Matrix.diagonal (fun _ : Fin n ↦ i) * Matrix.diagonal (fun _ ↦ i) = -1
    rw [Matrix.diagonal_mul_diagonal]
    apply Matrix.ext
    intro a b
    by_cases hab : a = b
    · subst b
      simp only [Matrix.diagonal_apply_eq, i_mul_i, Matrix.neg_apply, Matrix.one_apply_eq]
    · simp only [Matrix.diagonal_apply_ne _ hab, Matrix.neg_apply,
        Matrix.one_apply_ne hab, neg_zero]
  have hP : star P = -P := (quaternionMatrix_skew_iff _).mpr B.property
  have hPsq : P * P = -1 := (quaternionMatrix_square_iff _ B.property).mpr B.val.property
  have hPD : P * D = -(D * P) := by
    have h := quaternionMatrix_anticommutes B.val.val
    exact neg_eq_iff_eq_neg.mp h.symm
  obtain ⟨U, α, hα, hUD, hUP⟩ := exists_joint_unitary_diagonalization n D P hD hP hPsq hPD
  have hαone (a : Fin n) : α a = 1 := by
    have hs := conjugateMatrix_square_neg_one U D hDsq
    rw [hUD, Matrix.diagonal_mul_diagonal] at hs
    have ha : (α a • i) * (α a • i) = -1 := by
      simpa only [Matrix.diagonal_apply_eq, Matrix.neg_apply, Matrix.one_apply_eq] using
        congrArg (fun A : Matrix (Fin n) (Fin n) ℍ ↦ A a a) hs
    have hn := norm_eq_one_of_square ha
    simpa only [norm_smul, Real.norm_of_nonneg (hα a), norm_i, mul_one] using hn
  have hUD' : conjugateMatrix U D = D := by
    simpa only [hαone, one_smul] using hUD
  have hcomm : D * U.val = U.val * D := by
    have hc := congrArg (fun A : Matrix (Fin n) (Fin n) ℍ ↦ U.val * A) hUD'
    simpa only [conjugateMatrix, ← mul_assoc, Unitary.mul_star_self_of_mem U.property,
      one_mul] using hc
  obtain ⟨V, hV⟩ := exists_complex_unitary_of_commute U hcomm
  refine ⟨V, quaternionMatrix_injective ?_⟩
  rw [quaternionMatrix_mul_self_transpose, hV, ← hUP]
  change U.val * (star U.val * P * U.val) * star U.val = P
  calc
    U.val * (star U.val * P * U.val) * star U.val =
        (U.val * star U.val) * P * (U.val * star U.val) := by simp only [mul_assoc]
    _ = P := by rw [Unitary.mul_star_self_of_mem U.property, one_mul, mul_one]

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem exists_unitary_factor (B : Space N) :
    ∃ U : unitary (Matrix N N ℂ), U.val * U.val.transpose = B.val.val := by
  let e := Fintype.equivFin N
  let R := Matrix.reindexRingEquiv ℂ e
  have hstar (A : Matrix N N ℂ) : R (star A) = star (R A) := rfl
  have htranspose (A : Matrix N N ℂ) : R A.transpose = (R A).transpose := rfl
  have hunit : R B.val.val ∈ unitary (Matrix (Fin (Fintype.card N)) (Fin (Fintype.card N)) ℂ) := by
    constructor
    · rw [← hstar, ← map_mul, Unitary.star_mul_self_of_mem B.val.property, map_one]
    · rw [← hstar, ← map_mul, Unitary.mul_star_self_of_mem B.val.property, map_one]
  let B' : Space (Fin (Fintype.card N)) :=
    ⟨⟨R B.val.val, hunit⟩, by rw [← htranspose, B.property]⟩
  obtain ⟨V, hV⟩ := exists_unitary_factor_fin (Fintype.card N) B'
  have hstar' (A : Matrix (Fin (Fintype.card N)) (Fin (Fintype.card N)) ℂ) :
      R.symm (star A) = star (R.symm A) := rfl
  have hunit' : R.symm V.val ∈ unitary (Matrix N N ℂ) := by
    constructor
    · rw [← hstar', ← map_mul, Unitary.star_mul_self_of_mem V.property, map_one]
    · rw [← hstar', ← map_mul, Unitary.mul_star_self_of_mem V.property, map_one]
  refine ⟨⟨R.symm V.val, hunit'⟩, ?_⟩
  apply R.injective
  rw [map_mul, htranspose, R.apply_symm_apply]
  exact hV

theorem exists_special_unitary_congruence (B : SpecialSpace N) :
    ∃ (U : unitary (Matrix N N ℂ)) (hU : U.val.det ^ 2 = 1),
      congruenceSpecial U hU specialIdentity = B := by
  obtain ⟨U, hU⟩ := exists_unitary_factor B.val
  have hdet : U.val.det ^ 2 = 1 := by
    have h := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_transpose, ← pow_two] at h
    exact h.trans (congrArg (fun z : Circle ↦ (z : ℂ)) B.property)
  refine ⟨U, hdet, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change U.val * 1 * U.val.transpose = B.val.val.val
  rwa [mul_one]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
