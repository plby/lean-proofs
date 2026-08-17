/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos175.GranvilleRamare9
import ErdosProblems.Erdos175.NumericCutoff
import ErdosProblems.Erdos175.Section7

/-!
# Final large-power assembly for Erdős Problem 175

This module isolates the last logical step of the proof.  Section 7 gives a
large reciprocal Mangoldt sum under the squarefreeness assumption, the
Granville--Ramaré estimate gives the opposite upper bound, and the explicit
cutoff calculation shows that the two inequalities are incompatible.
-/

namespace Erdos175.FinalLarge

/-- A nonsquarefree natural has a prime-square divisor. -/
lemma exists_prime_sq_dvd_of_not_squarefree {m : ℕ} (hm : ¬ Squarefree m) :
    ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ m := by
  by_contra h
  push Not at h
  apply hm
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp
  simpa [pow_two] using h p hp

/-- The Section 7 and Section 9 definitions describe exactly the same finite
reciprocal von Mangoldt sum. -/
lemma section7_mangoldtSum_eq_granvilleRamare9 (n : ℕ) (x : ℝ) :
    Section7.mangoldtSum n x = GranvilleRamare9.mangoldtSum n x := by
  rw [GranvilleRamare9.mangoldtSum_eq]
  unfold Section7.mangoldtSum
  apply Finset.sum_congr rfl
  intro d _hd
  congr 1
  unfold Sawtooth.e e
  congr 1
  push_cast
  ring

/-- Once the reciprocal-sum upper bound has been established, the large
power-of-two case follows solely from Section 7 and the checked numerical
cutoff. -/
theorem large_power_witness_of_upper
    (hupper : ∀ k : ℕ, 8192 ≤ k → ∀ x : ℝ,
      (((2 : ℕ) ^ k : ℕ) : ℝ) ≤ x →
      x ≤ 6 * (((2 : ℕ) ^ k : ℕ) : ℝ) →
      ‖GranvilleRamare9.mangoldtSum (2 ^ k) x‖ ≤
        (10 ^ 12 : ℝ) * (((2 : ℕ) ^ k : ℕ) : ℝ) ^ (27 / 56 : ℝ) *
          Real.log (256 * (((2 : ℕ) ^ k : ℕ) : ℝ)) ^ 6) :
    ∀ k : ℕ, 8192 ≤ k →
      ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ Nat.choose (2 * 2 ^ k) (2 ^ k) := by
  intro k hk
  apply exists_prime_sq_dvd_of_not_squarefree
  intro hsq
  have hcut : 2 ^ 1728 ≤ (2 : ℕ) ^ k :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨x, hxlo, hxhi, hlower⟩ :=
    Section7.exists_large_reciprocal_mangoldt_sum (2 ^ k) hcut hsq
  have hlower' :
      (1 / 5000 : ℝ) * Real.sqrt (2 ^ k : ℕ) ≤
        ‖GranvilleRamare9.mangoldtSum (2 ^ k) x‖ := by
    simpa only [section7_mangoldtSum_eq_granvilleRamare9] using hlower
  have hpow : 2 ^ 8192 ≤ (2 : ℕ) ^ k :=
    Nat.pow_le_pow_right (by norm_num) hk
  exact not_final_lower_le_upper_of_ge_cutoff hpow
    (hlower'.trans (hupper k hk x hxlo hxhi))

/-- The unconditional large-power case, obtained from the fully explicit
Granville--Ramaré bound proved in `GranvilleRamare9`. -/
theorem large_power_witness (k : ℕ) (hk : 8192 ≤ k) :
    ∃ p : ℕ, p.Prime ∧
      p ^ 2 ∣ Nat.choose (2 * 2 ^ k) (2 ^ k) := by
  exact large_power_witness_of_upper
    (fun k hk x hxlo hxhi =>
      GranvilleRamare9.norm_mangoldtSum_two_pow_le_final
        k x hk hxlo hxhi) k hk

end Erdos175.FinalLarge
