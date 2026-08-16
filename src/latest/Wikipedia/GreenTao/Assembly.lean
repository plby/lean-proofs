import Wikipedia.GreenTao.Primes.Extraction
import Wikipedia.GreenTao.Primes.SmallProgressions

/-!
# Final elementary assembly

This file states the exact remaining analytic obligation in terms of the
W-tricked prime weight.  Once positive off-diagonal mass is supplied for
every `k ≥ 3`, all conversion to the lean-eval statement is proved here.
-/

namespace Wikipedia.SzemeredisTheorem

/-- A compact interface for the combined relative-Szemerédi and sieve
layers.  The modulus is written as `M + 1` so its nonzeroness is available
definitionally without carrying a typeclass through the existential. -/
def HasPrimeProgressionMass : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ∃ (M : ℕ) (α : ℝ) (W b : ℕ),
      0 < α ∧ 0 < W ∧
        0 <
          cyclicAPOffDiagMass k (M + 1)
            (wTrickedPrimeWeight α W b)

/-- A more analytic-facing sufficient interface.  Besides positivity of the
W-trick parameters, it asks for a pointwise height bound and for the
normalized progression count to dominate the resulting diagonal bound. -/
def HasPrimeProgressionCount : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ∃ (M : ℕ) (α : ℝ) (W b : ℕ) (B : ℝ),
      0 < α ∧ 0 < W ∧
        (∀ x : ZMod (M + 1),
          wTrickedPrimeWeight α W b x ≤ B) ∧
        B ^ (k - 1) *
            mean (wTrickedPrimeWeight α W b :
              ZMod (M + 1) → ℝ) <
          (M + 1 : ℝ) *
            cyclicAPCount k (M + 1)
              (wTrickedPrimeWeight α W b)

/-- The normalized-count interface implies positive off-diagonal mass by
the diagonal estimate. -/
theorem HasPrimeProgressionCount.toMass
    (hcount : HasPrimeProgressionCount) :
    HasPrimeProgressionMass := by
  intro k hk
  obtain ⟨M, α, W, b, B, hα, hW, hB, hcount'⟩ :=
    hcount k hk
  refine ⟨M, α, W, b, hα, hW, ?_⟩
  exact cyclicAPOffDiagMass_pos_of_count
    (by omega)
    (wTrickedPrimeWeight_nonneg hα.le W b)
    hB (by simpa [Nat.cast_add, Nat.cast_one] using hcount')

/-- The full benchmark follows from the positive-mass interface. -/
theorem containsArbitraryAPs_primes_of_mass
    (hmass : HasPrimeProgressionMass) :
    SzemeredisTheorem.ContainsArbitraryAPs
      {p : ℕ | Nat.Prime p} := by
  rw [containsArbitraryAPs_iff]
  intro k
  by_cases hk : k ≤ 2
  · exact containsAP_primes_of_le_two hk
  · have hk3 : 3 ≤ k := by omega
    obtain ⟨M, α, W, b, hα, hW, hpositive⟩ :=
      hmass k hk3
    exact containsAP_primes_of_wTricked_offDiagMass_pos
      (by omega) hα hW b hpositive

/-- Final assembly directly from the normalized-count interface. -/
theorem containsArbitraryAPs_primes_of_count
    (hcount : HasPrimeProgressionCount) :
    SzemeredisTheorem.ContainsArbitraryAPs
      {p : ℕ | Nat.Prime p} :=
  containsArbitraryAPs_primes_of_mass hcount.toMass

end Wikipedia.SzemeredisTheorem
