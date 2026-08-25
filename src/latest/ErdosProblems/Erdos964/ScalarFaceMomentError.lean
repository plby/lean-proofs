import ErdosProblems.Erdos964.ScalarFaceCoefficients

/-!
# Uniform polynomial-moment errors for the two faces
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem exists_scalar_face_moment_errors (M : ℕ) (hM : 0 < M)
    (h2M : 2 ∣ M) (h3M : 3 ∣ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R Q : ℕ, 0 < Real.log R → 1 ≤ Q → Q ≤ R →
      (|scalarLargeLogMoment M R Q -
          (scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 2) * (Real.log R) ^ 2 *
            scalarLargeFacePrimitive (Real.log Q / Real.log R)| ≤
          392 * (ε * (Real.log R) ^ 2 + C)) ∧
      ∀ z ∈ Set.Icc (0 : ℝ) 1,
        |scalarSmallLogMoment M R Q z -
          (scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 2) * (Real.log R) ^ 2 *
            scalarSmallFacePrimitive z (Real.log Q / Real.log R)| ≤
          512 * (ε * (Real.log R) ^ 2 + C) := by
  obtain ⟨C, hC, hmoment⟩ := exists_scalarLogMoment_two_error M hM h2M h3M ε hε
  refine ⟨C, hC, ?_⟩
  intro R Q hR hQ hQR
  let A := scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 2
  let L := Real.log R
  let q := Real.log Q
  let E := ε * L ^ 2 + C
  let main : ℕ → ℝ := fun j => A / ((2 + j : ℕ) : ℝ) * q ^ (2 + j) / L ^ j
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hbound (j : ℕ) : |scalarLogMoment M 2 R Q j - main j| ≤ 2 * E :=
    hmoment R Q j hR hQ hQR
  constructor
  · have h := abs_linear_moment_error Finset.univ scalarLargeFaceCoefficients
      (fun j : Fin 5 => scalarLogMoment M 2 R Q j) (fun j : Fin 5 => main j) (2 * E)
      (fun j _ => hbound j)
    rw [← scalarLargeLogMoment_eq_sum, scalarLargeFaceCoefficients_main A L q hR.ne',
      sum_abs_scalarLargeFaceCoefficients] at h
    change |scalarLargeLogMoment M R Q - A * L ^ 2 * scalarLargeFacePrimitive (q / L)| ≤ 392 * E
    linarith
  · intro z hz
    have h := abs_linear_moment_error Finset.univ (scalarSmallFaceCoefficients z)
      (fun j : Fin 3 => scalarLogMoment M 2 R Q j) (fun j : Fin 3 => main j) (2 * E)
      (fun j _ => hbound j)
    rw [← scalarSmallLogMoment_eq_sum, scalarSmallFaceCoefficients_main A L q z hR.ne'] at h
    have hcoeff := sum_abs_scalarSmallFaceCoefficients_le z hz
    have h' := h.trans (mul_le_mul_of_nonneg_right hcoeff (show 0 ≤ 2 * E by positivity))
    change |scalarSmallLogMoment M R Q z - A * L ^ 2 * scalarSmallFacePrimitive z (q / L)| ≤ 512 * E
    linarith

end Erdos964
