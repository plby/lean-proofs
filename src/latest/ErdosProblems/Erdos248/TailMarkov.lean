import ErdosProblems.Erdos248.MomentCombinatorics

/-!
# Erdős Problem 248: numerical tail extraction from moment bounds

The analytic files produce unnormalized moment inequalities.  These two
lemmas isolate the final real-algebra step converting such inequalities into
the reciprocal-square exceptional-mass budget used by the union bound.
-/

noncomputable section

namespace Erdos248

/-- Every positive real moment constant admits a positive natural threshold
whose square (and hence fourth power) dominates sixteen times that constant. -/
theorem exists_natural_moment_threshold (L : ℝ) (hL : 0 < L) :
    ∃ T : ℕ, 0 < T ∧ 16 * L ≤ (T : ℝ) ^ 2 ∧
      16 * L ≤ (T : ℝ) ^ 4 := by
  obtain ⟨T : ℕ, hT⟩ := exists_nat_gt (max 16 (16 * L))
  have hT16 : (16 : ℝ) < T := (le_max_left 16 (16 * L)).trans_lt hT
  have hTL : 16 * L < T := (le_max_right 16 (16 * L)).trans_lt hT
  have hTnat : 0 < T := by exact_mod_cast (show (0 : ℝ) < T by linarith)
  have hTone : (1 : ℝ) ≤ T := by exact_mod_cast hTnat
  have hTsq : (T : ℝ) ≤ (T : ℝ) ^ 2 := by nlinarith
  have hTfour : (T : ℝ) ^ 2 ≤ (T : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((T : ℝ) ^ 2 - 1)]
  exact ⟨T, hTnat, hTL.le.trans hTsq, hTL.le.trans (hTsq.trans hTfour)⟩

/-- A uniform second-moment bound gives the required `1/(16 k^2)` tail once
the threshold coefficient has square at least sixteen times the moment
constant. -/
theorem tail_le_sixteenth_inv_sq_of_secondMoment
    {D L M B k : ℝ} (hD : 0 < D) (hL : 0 < L) (hM : 0 ≤ M)
    (hk : 0 < k) (hB : 0 ≤ B) (hsize : 16 * L ≤ D ^ 2)
    (hmoment : (D * k) ^ 2 * B ≤ L * M) :
    B ≤ M * (1 / (16 * k ^ 2)) := by
  have hDk : 0 < D * k := mul_pos hD hk
  have hden : 0 < (D * k) ^ 2 := sq_pos_of_pos hDk
  have hkden : 0 < 16 * k ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hk)
  have hfirst : B ≤ (L * M) / ((D * k) ^ 2) := by
    exact (le_div_iff₀ hden).2 (by simpa [mul_comm] using hmoment)
  have hcross : (L * M) * (16 * k ^ 2) ≤ M * ((D * k) ^ 2) := by
    have hscale : L * (16 * k ^ 2) ≤ (D * k) ^ 2 := by
      calc
        L * (16 * k ^ 2) = (16 * L) * k ^ 2 := by ring
        _ ≤ D ^ 2 * k ^ 2 :=
          mul_le_mul_of_nonneg_right hsize (sq_nonneg k)
        _ = (D * k) ^ 2 := by ring
    nlinarith [mul_le_mul_of_nonneg_left hscale hM]
  calc
    B ≤ (L * M) / ((D * k) ^ 2) := hfirst
    _ ≤ M / (16 * k ^ 2) := by
      exact (div_le_div_iff₀ hden hkden).2 hcross
    _ = M * (1 / (16 * k ^ 2)) := by ring

/-- A centered fourth-moment bound of size `L k^2 M` gives the same
reciprocal-square tail once the centered threshold coefficient has fourth
power at least sixteen times `L`. -/
theorem tail_le_sixteenth_inv_sq_of_fourthMoment
    {D L M B k : ℝ} (hD : 0 < D) (hL : 0 < L) (hM : 0 ≤ M)
    (hk : 0 < k) (hB : 0 ≤ B) (hsize : 16 * L ≤ D ^ 4)
    (hmoment : (D * k) ^ 4 * B ≤ L * k ^ 2 * M) :
    B ≤ M * (1 / (16 * k ^ 2)) := by
  have hDk : 0 < D * k := mul_pos hD hk
  have hden : 0 < (D * k) ^ 4 := pow_pos hDk 4
  have hkden : 0 < 16 * k ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hk)
  have hfirst : B ≤ (L * k ^ 2 * M) / ((D * k) ^ 4) := by
    exact (le_div_iff₀ hden).2 (by simpa [mul_comm] using hmoment)
  have hcross :
      (L * k ^ 2 * M) * (16 * k ^ 2) ≤ M * ((D * k) ^ 4) := by
    have hscale : L * k ^ 2 * (16 * k ^ 2) ≤ (D * k) ^ 4 := by
      calc
        L * k ^ 2 * (16 * k ^ 2) = (16 * L) * k ^ 4 := by ring
        _ ≤ D ^ 4 * k ^ 4 :=
          mul_le_mul_of_nonneg_right hsize (by positivity)
        _ = (D * k) ^ 4 := by ring
    nlinarith [mul_le_mul_of_nonneg_left hscale hM]
  calc
    B ≤ (L * k ^ 2 * M) / ((D * k) ^ 4) := hfirst
    _ ≤ M / (16 * k ^ 2) := by
      exact (div_le_div_iff₀ hden hkden).2 hcross
    _ = M * (1 / (16 * k ^ 2)) := by ring

end Erdos248
