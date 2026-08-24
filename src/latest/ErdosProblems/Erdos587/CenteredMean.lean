import ErdosProblems.Erdos587.CenteredQuadratic
import ErdosProblems.Erdos587.ReciprocalWeighted

/-!
# The centered quadratic mean

Combining the reduced-period pointwise inequality with the already checked
nonzero-residue divisor count gives a polylogarithmic mean, with no divisor
factor from complete-period resonances.
-/

open scoped BigOperators

namespace Erdos587

open External.Erdos438.QuadraticWeyl

lemma sum_norm_centeredQuadraticInterval_sq_le_majorants (a q M L : ℕ) (hq : 0 < q)
    (s : ℕ → ℤ) (l : ℕ → ℕ) (hl : ∀ m ∈ Finset.Icc 1 M, l m ≤ L) :
    (∑ m ∈ Finset.Icc 1 M, ‖centeredQuadraticInterval q ((a * m : ℕ) : ℤ) (s m) (l m)‖ ^ 2) ≤
      10 * M * L + 4 * ∑ m ∈ Finset.Icc 1 M,
        ∑ h ∈ Finset.Icc 1 L, rationalMajorant (a * m) q 0 h := by
  have hpoint (m : ℕ) (hm : m ∈ Finset.Icc 1 M) :
      ‖centeredQuadraticInterval q ((a * m : ℕ) : ℤ) (s m) (l m)‖ ^ 2 ≤
        10 * L + 4 * ∑ h ∈ Finset.Icc 1 L, rationalMajorant (a * m) q 0 h := by
    apply (norm_centeredQuadraticInterval_sq_le hq (a * m) (s m) (l m)).trans
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hl m hm) (by norm_num)
    · apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro h hh
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hh).1, (Finset.mem_Icc.mp hh).2.trans (hl m hm)⟩
      · intro h hh hnot
        exact rationalMajorant_nonneg _ _ _ _
  apply (Finset.sum_le_sum hpoint).trans_eq
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  ring

/-- Uniformity includes independently chosen starting points and lengths.
The fourth-root counting margin is explicit and sufficient for the nearby
mean's low-frequency range. -/
theorem exists_centered_quadratic_mean_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧ ∀ (a q M L : ℕ),
      let X := 2 * M * L
      let D := Nat.sqrt (Nat.sqrt X)
      a.Coprime q → 0 < q → 3 ≤ D → q - 1 ≤ X → q * D ≤ X →
        ∀ (s : ℕ → ℤ) (l : ℕ → ℕ), (∀ m ∈ Finset.Icc 1 M, l m ≤ L) →
          (∑ m ∈ Finset.Icc 1 M,
            ‖centeredQuadraticInterval q ((a * m : ℕ) : ℤ) (s m) (l m)‖ ^ 2) ≤
              C * M * L * Real.log (X : ℝ) ^ O := by
  obtain ⟨K, hK, O, hO, hweighted⟩ := exists_weighted_twistedResiduePairCount_polylog_bound
  refine ⟨10 + 16 * K, by positivity, O, hO, ?_⟩
  intro a q M L
  dsimp only
  let X := 2 * M * L
  let D := Nat.sqrt (Nat.sqrt X)
  intro haq hq hD hqX hqD s l hl
  have hnonzero := hweighted a q M L (q - 1) haq hq hD hqX hqD
  have hnonzero' := hweighted (q - a % q) q M L (q - 1)
    (complementary_numerator_coprime hq haq) hq hD hqX hqD
  have hcount := sum_rationalMajorant_mul_frequency_le a q 0 M L hq
  simp only [Nat.cast_zero, mul_zero, zero_add] at hcount
  have hXthree : 3 ≤ X := hD.trans ((Nat.sqrt_le_self (Nat.sqrt X)).trans (Nat.sqrt_le_self X))
  have hF : 1 ≤ Real.log (X : ℝ) ^ O := one_le_pow₀ (one_le_log_nat_of_three_le hXthree)
  have hsum : (∑ m ∈ Finset.Icc 1 M, ∑ h ∈ Finset.Icc 1 L,
      rationalMajorant (a * m) q 0 h) ≤ 2 * K * (X : ℝ) * Real.log (X : ℝ) ^ O := by
    linarith
  apply (sum_norm_centeredQuadraticInterval_sq_le_majorants a q M L hq s l hl).trans
  calc
    _ ≤ 10 * (M : ℝ) * L + 4 * (2 * K * (X : ℝ) * Real.log (X : ℝ) ^ O) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum (by norm_num))
    _ ≤ (10 * (M : ℝ) * L) * Real.log (X : ℝ) ^ O +
        4 * (2 * K * (X : ℝ) * Real.log (X : ℝ) ^ O) := by
      exact add_le_add (le_mul_of_one_le_right (by positivity) hF) le_rfl
    _ = (10 + 16 * K) * M * L * Real.log (X : ℝ) ^ O := by
      dsimp [X]
      push_cast
      ring

lemma centeredQuadraticInterval_eq_sum (q : ℕ) (a s : ℤ) (L : ℕ) :
    centeredQuadraticInterval q a s L = ∑ n ∈ Finset.range L,
      (quadraticResiduePhase q a (s + n) - completeQuadraticGaussSum q a 0 / q) := by
  rw [centeredQuadraticInterval, exactQuadraticInterval, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

end Erdos587
