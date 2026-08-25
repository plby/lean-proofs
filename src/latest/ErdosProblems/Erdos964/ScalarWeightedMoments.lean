import ErdosProblems.Erdos964.PowerMonomialError

/-!
# Uniform logarithmic moments of the two scalar sieve weights
-/

namespace Erdos964

open BoundedGaps.Maynard

noncomputable def scalarLogMoment (M κ R Q j : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 Q, normalizedLogMonomial (Real.log R) j n * scalarMomentAF M κ n

theorem exists_scalarLogMoment_two_error (M : ℕ) (hM : 0 < M)
    (h2M : 2 ∣ M) (h3M : 3 ∣ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R Q j : ℕ, 0 < Real.log R → 1 ≤ Q → Q ≤ R →
      |scalarLogMoment M 2 R Q j -
        scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 2 / ((2 + j : ℕ) : ℝ) *
          (Real.log Q) ^ (2 + j) / (Real.log R) ^ j| ≤ 2 * (ε * (Real.log R) ^ 2 + C) := by
  obtain ⟨C, hC, hbound⟩ := exists_log_mean_uniform_monomial_error (scalarMomentAF M 2)
    (scalarSieveEulerConstant M * (coprimeHarmonicDensity M ^ 2 / 2)) 2 (by decide)
    (tendsto_scalarMomentAF_two_mean M hM h2M h3M) ε hε
  refine ⟨C, hC, ?_⟩
  intro R Q j hR hQ hQR
  have h := hbound R Q j hR hQ hQR
  have hid : (scalarSieveEulerConstant M * (coprimeHarmonicDensity M ^ 2 / 2)) * (2 : ℝ) =
      scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 2 := by ring
  simpa only [scalarLogMoment, Nat.cast_ofNat, hid] using h

theorem exists_scalarLogMoment_three_error (M : ℕ) (hM : 0 < M)
    (h2M : 2 ∣ M) (h3M : 3 ∣ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R Q j : ℕ, 0 < Real.log R → 1 ≤ Q → Q ≤ R →
      |scalarLogMoment M 3 R Q j -
        (scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 3 / 2) / ((3 + j : ℕ) : ℝ) *
          (Real.log Q) ^ (3 + j) / (Real.log R) ^ j| ≤ 2 * (ε * (Real.log R) ^ 3 + C) := by
  obtain ⟨C, hC, hbound⟩ := exists_log_mean_uniform_monomial_error (scalarMomentAF M 3)
    (scalarSieveEulerConstant M * (coprimeHarmonicDensity M ^ 3 / 6)) 3 (by decide)
    (tendsto_scalarMomentAF_three_mean M hM h2M h3M) ε hε
  refine ⟨C, hC, ?_⟩
  intro R Q j hR hQ hQR
  have h := hbound R Q j hR hQ hQR
  have hid : (scalarSieveEulerConstant M * (coprimeHarmonicDensity M ^ 3 / 6)) * (3 : ℝ) =
      scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 3 / 2 := by ring
  simpa only [scalarLogMoment, Nat.cast_ofNat, hid] using h

end Erdos964
