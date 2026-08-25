import ErdosProblems.Erdos964.ScalarFirstMomentPolynomial

/-!
# The quantitative first polynomial main term
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem exists_scalarCandidateFirstMain_polynomial_error (M : ℕ) (hM : 0 < M)
    (h2M : 2 ∣ M) (h3M : 3 ∣ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℕ, 2 ≤ R →
      |scalarCandidateFirstMain M R -
        (scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 3) * (Real.log R) ^ 3 *
          scalarFirstMomentPolynomial (Real.log (R - 1 : ℕ) / Real.log R)| ≤
        338 * (ε * (Real.log R) ^ 3 + C) := by
  obtain ⟨C, hC, hbound⟩ := exists_scalarLogMoment_three_error M hM h2M h3M ε hε
  refine ⟨C, hC, ?_⟩
  intro R hR
  let A := scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 3
  let L := Real.log R
  let q := Real.log (R - 1 : ℕ)
  let E := ε * L ^ 3 + C
  have hL : 0 < L := Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hQ : 1 ≤ R - 1 := by omega
  have hQR : R - 1 ≤ R := Nat.sub_le R 1
  have h0 := hbound R (R - 1) 0 hL hQ hQR
  have h1 := hbound R (R - 1) 1 hL hQ hQR
  have h2 := hbound R (R - 1) 2 hL hQ hQR
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, pow_zero, pow_one, div_one] at h0 h1 h2
  have hm0 : A / 2 / 3 * q ^ 3 = A / 6 * q ^ 3 := by ring
  have hm1 : A / 2 / 4 * q ^ 4 / L = A / 8 * q ^ 4 / L := by ring
  have hm2 : A / 2 / 5 * q ^ 5 / L ^ 2 = A / 10 * q ^ 5 / L ^ 2 := by ring
  change |scalarLogMoment M 3 R (R - 1) 0 - A / 2 / 3 * q ^ 3| ≤ 2 * E at h0
  change |scalarLogMoment M 3 R (R - 1) 1 - A / 2 / 4 * q ^ 4 / L| ≤ 2 * E at h1
  change |scalarLogMoment M 3 R (R - 1) 2 - A / 2 / 5 * q ^ 5 / L ^ 2| ≤ 2 * E at h2
  rw [hm0] at h0
  rw [hm1] at h1
  rw [hm2] at h2
  let e0 := scalarLogMoment M 3 R (R - 1) 0 - A / 6 * q ^ 3
  let e1 := scalarLogMoment M 3 R (R - 1) 1 - A / 8 * q ^ 4 / L
  let e2 := scalarLogMoment M 3 R (R - 1) 2 - A / 10 * q ^ 5 / L ^ 2
  have hid : scalarCandidateFirstMain M R - A * L ^ 3 * scalarFirstMomentPolynomial (q / L) =
      49 * e0 - 84 * e1 + 36 * e2 := by
    rw [scalarCandidateFirstMain_eq_log_moments M R (by omega)]
    dsimp only [e0, e1, e2, scalarFirstMomentPolynomial]
    field_simp [hL.ne']
    ring
  change |scalarCandidateFirstMain M R - A * L ^ 3 * scalarFirstMomentPolynomial (q / L)| ≤ 338 * E
  rw [hid]
  calc
    _ ≤ |49 * e0 - 84 * e1| + |36 * e2| := abs_add_le _ _
    _ ≤ (|49 * e0| + |84 * e1|) + |36 * e2| := add_le_add (abs_sub _ _) le_rfl
    _ = 49 * |e0| + 84 * |e1| + 36 * |e2| := by
      simp only [abs_mul]
      norm_num
    _ ≤ 338 * E := by linarith [h0, h1, h2]

end Erdos964
