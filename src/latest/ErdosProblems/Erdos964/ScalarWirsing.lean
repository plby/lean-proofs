import ErdosProblems.Erdos964.ScalarRadical
import BoundedGaps.Maynard.WirsingAllEndpoints
import BoundedGaps.Maynard.ConcreteRoughModulusPrimeLogMass

/-!
# Uniform one-dimensional means for the scalar transform

Passing to the radical removes the squarefree-modulus restriction in the
installed Wirsing estimate. The outer factor `r/φ(r)` then cancels the
density contributed by the coprime outer divisor.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard UniqueFactorizationMonoid

theorem exists_uniform_scalar_coprime_mean_error :
    ∃ K : ℝ, 0 < K ∧ ∀ M Q : ℕ, 0 < M →
      |squarefreeCoprimeInvTotientMean M Q - coprimeHarmonicDensity M * Real.log Q| ≤
        10 * coprimeHarmonicDensity M * (K + primeLogDivisorMass M + Real.log 2) := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_uniform_abs_squarefreeCoprimeInvTotientMean_sub_density_log_le
  refine ⟨K, hK, ?_⟩
  intro M Q hM
  have hsq : Squarefree (primorial 1 * radical M) := by
    simpa only [primorial_one, one_mul] using (squarefree_radical (a := M))
  have h := hbound (D := 1) (P := radical M) (Q := Q) (Nat.radical_pos M) hsq
  simp only [primorial_one, one_mul, Nat.cast_one, Real.log_one, add_zero,
    squarefreeCoprimeInvTotientMean_radical M Q hM.ne', coprimeHarmonicDensity_radical M hM,
    primeLogDivisorMass_radical] at h
  exact h

theorem exists_uniform_scalar_scaled_mean_error :
    ∃ K C : ℝ, 0 < K ∧ 0 ≤ C ∧
      ∀ M r R Q : ℕ, 0 < M → 0 < r → Squarefree r → M.Coprime r → r < R →
        2 ≤ Real.log R →
      |((r : ℝ) / r.totient) * squarefreeCoprimeInvTotientMean (M * r) Q -
        coprimeHarmonicDensity M * Real.log Q| ≤
        10 * coprimeHarmonicDensity M *
          (K + primeLogDivisorMass M + (Real.log (Real.log R) + C + 2) + Real.log 2) := by
  obtain ⟨K, hK, hmean⟩ := exists_uniform_scalar_coprime_mean_error
  obtain ⟨C₀, hmass⟩ := exists_uniform_primeLogDivisorMass_le_log_log_add
  refine ⟨K, max C₀ 0, hK, le_max_right _ _, ?_⟩
  intro M r R Q hM hr hrsq hcop hrR hlogR
  have hscale := scaled_coprimeHarmonicDensity M r hr hcop
  have hrphi : 0 ≤ (r : ℝ) / r.totient := by positivity
  have hδ : 0 ≤ coprimeHarmonicDensity M := by unfold coprimeHarmonicDensity; positivity
  have hbase := hmean (M * r) Q (Nat.mul_pos hM hr)
  have hmassR := hmass hr hrsq hrR hlogR
  have hid : ((r : ℝ) / r.totient) * squarefreeCoprimeInvTotientMean (M * r) Q -
      coprimeHarmonicDensity M * Real.log Q =
      ((r : ℝ) / r.totient) * (squarefreeCoprimeInvTotientMean (M * r) Q -
        coprimeHarmonicDensity (M * r) * Real.log Q) := by
    rw [mul_sub, ← mul_assoc, hscale]
  rw [hid, abs_mul, abs_of_nonneg hrphi]
  calc
    _ ≤ ((r : ℝ) / r.totient) * (10 * coprimeHarmonicDensity (M * r) *
        (K + primeLogDivisorMass (M * r) + Real.log 2)) :=
      mul_le_mul_of_nonneg_left hbase hrphi
    _ = 10 * coprimeHarmonicDensity M *
        (K + primeLogDivisorMass M + primeLogDivisorMass r + Real.log 2) := by
      rw [primeLogDivisorMass_mul_of_coprime M r hcop]
      calc
        _ = 10 * (((r : ℝ) / r.totient) * coprimeHarmonicDensity (M * r)) *
            (K + primeLogDivisorMass M + primeLogDivisorMass r + Real.log 2) := by ring
        _ = _ := by rw [hscale]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [le_max_left C₀ 0]) (by positivity)

end Erdos964
