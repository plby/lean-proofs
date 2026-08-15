import ErdosProblems.Erdos321.BadPrimeAggregate

namespace Erdos321

/-- Clean lower recurrence with all modularly bad fibres moved into one explicit
additive error. -/
theorem sum_quotientPrimes_mul_extremalSize_le_add_error
    {N T : ℕ} (hT : 1 ≤ T) :
    (∑ t ∈ Finset.Icc 1 T,
      (quotientPrimes N T t).card * extremalSize t) ≤
      extremalSize N + 3 ^ T * T ^ 2 * (T + 1) := by
  let B : ℕ → ℕ := fun t =>
    (badPrimeSetFrom (T + 1) N (chosenExtremizer t)).card
  have hMain := sum_quotient_sub_restrictedBad_mul_extremalSize_le N T
  have hBad := sum_restrictedBad_mul_extremalSize_le (N := N) hT
  calc
    (∑ t ∈ Finset.Icc 1 T,
      (quotientPrimes N T t).card * extremalSize t) ≤
        ∑ t ∈ Finset.Icc 1 T,
          (((quotientPrimes N T t).card - B t) * extremalSize t +
            B t * extremalSize t) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [← Nat.add_mul]
      apply Nat.mul_le_mul_right (extremalSize t)
      dsimp [B]
      omega
    _ = (∑ t ∈ Finset.Icc 1 T,
          ((quotientPrimes N T t).card - B t) * extremalSize t) +
        ∑ t ∈ Finset.Icc 1 T, B t * extremalSize t := by
      rw [Finset.sum_add_distrib]
    _ ≤ extremalSize N + 3 ^ T * T ^ 2 * (T + 1) := by
      apply Nat.add_le_add
      · simpa [B] using hMain
      · simpa [B] using hBad

end Erdos321
