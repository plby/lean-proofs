import Wikipedia.GreenTao.Primes.WTrick
import Wikipedia.GreenTao.Sieve.SmoothCutoff

/-!
# The smooth cutoff instantiated in the Selberg majorant

This file connects `SmoothSieveCutoff` to the previously total divisor-sum
definitions.  The positivity of the cutoff normalizer discharges every
normalization side condition, including the exact value of the majorant on
primes beyond the sieve level.
-/

namespace Wikipedia.SzemeredisTheorem

/-- The structured cutoff version of the truncated divisor sum. -/
noncomputable def SmoothSieveCutoff.divisorSum
    (χ : SmoothSieveCutoff) (R n : ℕ) : ℝ :=
  smoothTruncatedDivisorSum χ.toFun R n

/-- The structured cutoff version of the normalized Selberg majorant. -/
noncomputable def SmoothSieveCutoff.majorant
    (χ : SmoothSieveCutoff) (R W n : ℕ) : ℝ :=
  normalizedSelbergMajorant χ.toFun χ.normalizer R W n

theorem SmoothSieveCutoff.divisorSum_prime_of_lt
    (χ : SmoothSieveCutoff) {R p : ℕ}
    (hp : p.Prime) (hR : 1 < R) (hRp : R < p) :
    χ.divisorSum R p = Real.log R := by
  exact smoothTruncatedDivisorSum_prime_of_lt χ.toFun hp
    χ.value_zero χ.zero_of_one_le hR hRp

theorem SmoothSieveCutoff.majorant_nonneg
    (χ : SmoothSieveCutoff) {R : ℕ} (hR : 1 ≤ R)
    (W n : ℕ) :
    0 ≤ χ.majorant R W n :=
  normalizedSelbergMajorant_nonneg χ.toFun
    χ.normalizer_nonneg hR W n

/-- Exact structured-majorant value on a prime beyond the truncation
level. -/
theorem SmoothSieveCutoff.majorant_prime_of_lt
    (χ : SmoothSieveCutoff) {R W p : ℕ}
    (hR : 1 < R) (hW : 0 < W)
    (hp : p.Prime) (hRp : R < p) :
    χ.majorant R W p =
      (W.totient : ℝ) / W *
        (Real.log R / χ.normalizer) := by
  exact normalizedSelbergMajorant_prime_of_lt χ.toFun
    χ.normalizer_pos.ne' hR hW hp χ.value_zero
    χ.zero_of_one_le hRp

/-- The localized W-tricked majorant associated to a structured cutoff. -/
noncomputable def SmoothSieveCutoff.wTrickedMajorant
    {N : ℕ} [NeZero N] (χ : SmoothSieveCutoff)
    (R W b : ℕ) (n : ZMod N) : ℝ :=
  Wikipedia.SzemeredisTheorem.wTrickedMajorant
    χ.toFun χ.normalizer R W b n

theorem SmoothSieveCutoff.wTrickedMajorant_nonneg
    {N : ℕ} [NeZero N] (χ : SmoothSieveCutoff)
    {R : ℕ} (hR : 1 ≤ R) (W b : ℕ) (n : ZMod N) :
    0 ≤ χ.wTrickedMajorant R W b n := by
  unfold SmoothSieveCutoff.wTrickedMajorant
  unfold Wikipedia.SzemeredisTheorem.wTrickedMajorant
  split
  · exact χ.majorant_nonneg hR W (wTrickedValue W b n)
  · exact zero_le_one

/-- On a supported W-tricked prime beyond `R`, the localized majorant has
the expected exact logarithmic size. -/
theorem SmoothSieveCutoff.wTrickedMajorant_eq_of_prime
    {N : ℕ} [NeZero N] (χ : SmoothSieveCutoff)
    {R W b : ℕ} (hR : 1 < R) (hW : 0 < W)
    {n : ZMod N} (hn : n.val ∈ greenTaoInterval N)
    (hp : Nat.Prime (wTrickedValue W b n))
    (hRp : R < wTrickedValue W b n) :
    χ.wTrickedMajorant R W b n =
      (W.totient : ℝ) / W *
        (Real.log R / χ.normalizer) := by
  rw [SmoothSieveCutoff.wTrickedMajorant]
  simp only [Wikipedia.SzemeredisTheorem.wTrickedMajorant, if_pos hn]
  exact χ.majorant_prime_of_lt hR hW hp hRp

/-- A canonical total majorant, using the explicit standard cutoff. -/
noncomputable def standardSelbergMajorant
    (R W n : ℕ) : ℝ :=
  standardSmoothSieveCutoff.majorant R W n

theorem standardSelbergMajorant_nonneg
    {R : ℕ} (hR : 1 ≤ R) (W n : ℕ) :
    0 ≤ standardSelbergMajorant R W n :=
  standardSmoothSieveCutoff.majorant_nonneg hR W n

end Wikipedia.SzemeredisTheorem
