import BoundedGaps.Maynard.ConcreteParameters

/-! # Absorbing a fixed progression modulus in the sieve cutoff -/

namespace MaynardBFT

open Filter BoundedGaps.Maynard

theorem eventually_mul_primorial_le_rpow (q : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop,
      ((q * primorial (tripleLogCutoff N) : ℕ) : ℝ) ≤ Real.rpow (N : ℝ) eps := by
  have hhalf : 0 < eps / 2 := half_pos heps
  have hq := ((tendsto_rpow_atTop hhalf).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop (q : ℝ))
  filter_upwards [hq, eventually_primorial_tripleLogCutoff_le_rpow hhalf,
    eventually_ge_atTop 1] with N hqN hWN hN
  rw [Nat.cast_mul]
  calc
    (q : ℝ) * primorial (tripleLogCutoff N) ≤
        Real.rpow (N : ℝ) (eps / 2) * Real.rpow (N : ℝ) (eps / 2) :=
      mul_le_mul hqN hWN (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = Real.rpow (N : ℝ) eps := by
      simpa only [Real.rpow_eq_pow, add_halves] using
        (Real.rpow_add (by exact_mod_cast (show 0 < N by omega) : (0 : ℝ) < N)
          (eps / 2) (eps / 2)).symm

theorem eventually_progression_endpoint_cutoff (q : ℕ)
    {theta delta : ℝ} (htheta : 0 ≤ theta) (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop, ∀ h : ℕ,
      q * (engelsmaMaynardModulus N *
          engelsmaMaynardRadius (theta / 2 - delta) N *
          engelsmaMaynardRadius (theta / 2 - delta) N) ≤
        modulusCutoff theta (N + h - 1) := by
  have hbase : ∀ᶠ N : ℕ in atTop,
      (q * primorial (tripleLogCutoff N)) *
          maynardDivisorCutoff (theta / 2 - delta) N *
          maynardDivisorCutoff (theta / 2 - delta) N ≤ modulusCutoff theta N := by
    apply eventually_maynardDivisorCutoff_product_le_modulusCutoff
      (eps := delta) (alpha := theta / 2 - delta)
    · linarith
    · exact eventually_mul_primorial_le_rpow q hdelta
  have hshift := (tendsto_sub_atTop_nat 1).eventually hbase
  filter_upwards [hshift] with N hN h
  have hmono := modulusCutoff_mono htheta (show N - 1 ≤ N + h - 1 by omega)
  simpa only [engelsmaMaynardModulus, engelsmaMaynardRadius, Nat.mul_assoc] using hN.trans hmono

end MaynardBFT
