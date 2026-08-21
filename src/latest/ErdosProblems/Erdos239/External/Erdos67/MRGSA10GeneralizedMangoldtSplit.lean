import ErdosProblems.Erdos239.External.Erdos67.MRGSA10GeneralizedMangoldtBound

/-!
# Prime and higher-prime-power parts of generalized Mangoldt coefficients

The squarefree part of the generalized Mangoldt coefficient of an ordinary
multiplicative function is the familiar exact prime term.  All failure of
the completely multiplicative formula is confined to prime powers of
exponent at least two.  This is the split used in the second GS A.10 Shiu
secondary estimate.
-/

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Restriction of an arithmetic function to primes. -/
def gsPrimePart (u : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n.Prime then u n else 0, by simp⟩

/-- Restriction of an arithmetic function to non-prime prime powers. -/
def gsHigherPrimePowerPart (u : ArithmeticFunction ℂ) :
    ArithmeticFunction ℂ :=
  ⟨fun n ↦ if IsPrimePow n ∧ ¬ n.Prime then u n else 0, by simp⟩

@[simp] theorem gsPrimePart_apply (u : ArithmeticFunction ℂ) (n : ℕ) :
    gsPrimePart u n = if n.Prime then u n else 0 := rfl

@[simp] theorem gsHigherPrimePowerPart_apply
    (u : ArithmeticFunction ℂ) (n : ℕ) :
    gsHigherPrimePowerPart u n =
      if IsPrimePow n ∧ ¬ n.Prime then u n else 0 := rfl

/-- At a prime, the generalized Mangoldt coefficient is exactly
`a(p) log p`; no complete multiplicativity is needed. -/
theorem gsGeneralizedMangoldt_apply_prime
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1))
    (ha1 : a 1 = 1) {p : ℕ} (hp : p.Prime) :
    gsGeneralizedMangoldt a ha p = a p * (Real.log p : ℂ) := by
  have hrec := sum_gsGeneralizedMangoldt_prime_pow_add_self
    a ha ha1 p 1 hp
  simpa [gsGeneralizedMangoldt_one] using hrec

/-- Prime-power support splits the whole generalized Mangoldt coefficient
into its exact prime part and its higher-prime-power error. -/
theorem gsGeneralizedMangoldt_eq_primePart_add_higherPrimePowerPart
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1))
    (haMult : a.IsMultiplicative) :
    gsGeneralizedMangoldt a ha =
      gsPrimePart (gsGeneralizedMangoldt a ha) +
        gsHigherPrimePowerPart (gsGeneralizedMangoldt a ha) := by
  ext n
  by_cases hp : n.Prime
  · rw [ArithmeticFunction.add_apply]
    simp [gsPrimePart, gsHigherPrimePowerPart, hp, hp.isPrimePow]
  · by_cases hpp : IsPrimePow n
    · rw [ArithmeticFunction.add_apply]
      simp [gsPrimePart, gsHigherPrimePowerPart, hp, hpp]
    · rw [gsGeneralizedMangoldt_eq_zero_of_not_isPrimePow
          a ha haMult hpp]
      rw [ArithmeticFunction.add_apply]
      simp [gsPrimePart, gsHigherPrimePowerPart, hp, hpp]

/-- The actual high generalized Mangoldt coefficient has the same exact
prime/higher-prime-power decomposition under ordinary multiplicativity. -/
theorem gsA9HighGeneralizedMangoldt_eq_primePart_add_higherPrimePowerPart
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f) (y : ℕ) :
    gsA9HighGeneralizedMangoldt hmul y =
      gsPrimePart (gsA9HighGeneralizedMangoldt hmul y) +
        gsHigherPrimePowerPart (gsA9HighGeneralizedMangoldt hmul y) := by
  exact gsGeneralizedMangoldt_eq_primePart_add_higherPrimePowerPart
    (gsA9HighArithmetic f y) (gsA9HighArithmeticInvertible hmul y)
    (gsA9HighArithmetic_isMultiplicative hmul y)

/-- Exact actual-high prime value. -/
theorem gsA9HighGeneralizedMangoldt_apply_prime
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y : ℕ) {p : ℕ} (hp : p.Prime) :
    gsA9HighGeneralizedMangoldt hmul y p =
      gsA9HighArithmetic f y p * (Real.log p : ℂ) := by
  exact gsGeneralizedMangoldt_apply_prime
    (gsA9HighArithmetic f y) (gsA9HighArithmeticInvertible hmul y)
    (gsA9HighArithmetic_one hmul y) hp

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.gsGeneralizedMangoldt_apply_prime
#print axioms Erdos67.MRHalaszBands.gsA9HighGeneralizedMangoldt_eq_primePart_add_higherPrimePowerPart
