import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicJointSpectralTheorem
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicAntipodalDiagonalization

/-! # A simultaneous antipodal diagonalization with a fast first eigenline -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.SkewSpectralPlane
open ComplexStructures

local notation "ℍ" => Quaternion ℝ

variable {n : ℕ}

theorem coefficients_complexStructure_square (J : Space n) :
    coefficients n J.val.val * coefficients n J.val.val = -1 := by
  apply realAction_injective n
  rw [realAction_mul, realAction_coefficients n J.val.val J.val.property.2]
  change J.val.val * J.val.val = realRepresentation n (-1)
  rw [map_neg, map_one]
  exact J.property

theorem coefficients_anticommute (J : Space n) (K : SkewSpace n)
    (hJK : J.val.val * K.val = -(K.val * J.val.val)) :
    coefficients n J.val.val * coefficients n K.val =
      -(coefficients n K.val * coefficients n J.val.val) := by
  apply realAction_injective n
  change realRepresentation n (_ * _) = realRepresentation n (-(_ * _))
  have hJ : realRepresentation n (coefficients n J.val.val) = J.val.val :=
    realAction_coefficients n J.val.val J.val.property.2
  have hK : realRepresentation n (coefficients n K.val) = K.val :=
    realAction_coefficients n K.val K.property.2
  rw [map_mul, map_neg, map_mul, hJ, hK]
  exact hJK

theorem exists_fast_joint_antipodal_diagonalization (J : Space n) (K : SkewSpace n)
    (hJK : J.val.val * K.val = -(K.val * J.val.val))
    (hexp : (Exponential.exp K).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (hnot : gram (toOrthogonalSkew n K) ≠
      Real.pi ^ 2 • (1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) :
    ∃ (U : SpGroup (Fin (n + 1))) (m : Fin (n + 1) → ℕ), 1 ≤ m 0 ∧
      conjugateMatrix U (coefficients n K.val) =
        Matrix.diagonal (fun a ↦ (((2 * (m a : ℝ) + 1) * Real.pi) • QuaternionicScalars.i)) ∧
      conjugateMatrix U (coefficients n J.val.val) =
        Matrix.diagonal (fun _ ↦ QuaternionicScalars.j) := by
  obtain ⟨α, v, hα, hv, hKv, hJv⟩ := exists_fast_joint_unit_eigenvector J K hJK hexp hnot
  obtain ⟨U, hUK, hUJ⟩ := exists_joint_eigenframe J K α v hv hKv hJv
  let B := lowerBlock (conjugateMatrix U (coefficients n K.val))
  let C := lowerBlock (conjugateMatrix U (coefficients n J.val.val))
  have hB : star B = -B := lowerBlock_skew _ (conjugateMatrix_skew U _ (coefficients_skew K))
  have hC : star C = -C := lowerBlock_skew _ (conjugateMatrix_skew U _ (coefficients_skew J.val))
  have hlow := joint_lowerBlock_relations U _ _ (coefficients_complexStructure_square J)
    (coefficients_anticommute J K hJK) α hUK hUJ
  obtain ⟨V, β, hβ, hVB, hVC⟩ := exists_joint_unitary_diagonalization n B C hB hC hlow.1 hlow.2
  let W := U * stabilization n V
  let γ : Fin (n + 1) → ℝ := Fin.cons α β
  have hγ : ∀ a, 0 ≤ γ a := by
    intro a
    cases a using Fin.cases
    · exact le_trans (by positivity : (0 : ℝ) ≤ 3 * Real.pi) hα
    · exact hβ _
  have hdK : conjugateMatrix W (coefficients n K.val) =
      Matrix.diagonal (fun a ↦ γ a • QuaternionicScalars.i) := by
    rw [conjugateMatrix_mul, hUK, conjugateMatrix_stabilization, hVB, splitMatrix_diagonal]
    congr 1
    funext a
    cases a using Fin.cases <;> rfl
  have hdJ : conjugateMatrix W (coefficients n J.val.val) =
      Matrix.diagonal (fun _ ↦ QuaternionicScalars.j) := by
    rw [conjugateMatrix_mul, hUJ, conjugateMatrix_stabilization, hVC, splitMatrix_diagonal]
    congr 1
    funext a
    cases a using Fin.cases <;> rfl
  choose m hm using nonnegative_diagonalization_odd K hexp W γ hγ hdK
  refine ⟨W, m, ?_, by simpa only [hm] using hdK, hdJ⟩
  by_contra h
  have hm0 : m 0 = 0 := by omega
  have he := hm 0
  change α = (2 * (m 0 : ℝ) + 1) * Real.pi at he
  rw [hm0] at he
  norm_num at he
  linarith [Real.pi_pos]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
