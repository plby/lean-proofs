import Wikipedia.GreenTao.Sieve.LinearFormsExpansion

/-!
# Uniform bounds for finite smooth-divisor expansions

The finite Selberg expansion contains two smooth Möbius-cutoff coefficients
for every form.  This file records the elementary bounds needed to propagate
a uniform arithmetic-density error through that expansion.

For a `SmoothSieveCutoff`, every cutoff value lies in `[0,1]` and the
Möbius function has absolute value at most one.  Hence each divisor summand
and each product-family coefficient has absolute value at most one.

The choice set is also counted exactly.  There are `R` positive choices in
`[1,R]`, two choices per form, and therefore

`card (smoothDivisorFamilyChoices κ R) = R ^ (2 * card κ)`.

The final theorems combine these facts with the triangle inequality.  A
uniform density perturbation of size `ε` changes the divisor sum by at most
`R ^ (2 * card κ) * ε`; a second theorem retains exactly the two scalar
prefactors occurring in the normalized Selberg expansion.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped ArithmeticFunction.Moebius BigOperators

namespace SmoothSieveCutoff

/-! ## Coefficient bounds -/

/-- Every smooth Möbius-cutoff divisor summand has absolute value at most
one. -/
theorem abs_smoothDivisorSummand_le_one
    (χ : SmoothSieveCutoff) (R d : ℕ) :
    |smoothDivisorSummand χ.toFun R d| ≤ 1 := by
  have hmu :
      |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hchi :
      |χ.toFun (Real.log d / Real.log R)| ≤ 1 := by
    rw [abs_of_nonneg (χ.nonneg _)]
    exact χ.le_one _
  rw [smoothDivisorSummand, abs_mul]
  calc
    |(ArithmeticFunction.moebius d : ℝ)| *
          |χ.toFun (Real.log d / Real.log R)| ≤
        1 * 1 :=
      mul_le_mul hmu hchi (abs_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

/-- A paired divisor coefficient for an arbitrary finite family has
absolute value at most one. -/
theorem abs_smoothDivisorFamilyCoefficient_le_one
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (z : κ → ℕ × ℕ) :
    |smoothDivisorFamilyCoefficient χ.toFun R z| ≤ 1 := by
  unfold smoothDivisorFamilyCoefficient
  rw [Finset.abs_prod]
  apply Finset.prod_le_one
  · intro q _hq
    exact abs_nonneg _
  · intro q _hq
    rw [abs_mul]
    calc
      |smoothDivisorSummand χ.toFun R (z q).1| *
            |smoothDivisorSummand χ.toFun R (z q).2| ≤
          1 * 1 :=
        mul_le_mul
          (χ.abs_smoothDivisorSummand_le_one R (z q).1)
          (χ.abs_smoothDivisorSummand_le_one R (z q).2)
          (abs_nonneg _) (by norm_num)
      _ = 1 := one_mul 1

end SmoothSieveCutoff

/-! ## Exact cardinalities of the bounded choice sets -/

@[simp]
theorem card_smoothDivisorChoices (R : ℕ) :
    (smoothDivisorChoices R).card = R := by
  simp [smoothDivisorChoices]

@[simp]
theorem card_smoothDivisorPairChoices (R : ℕ) :
    (smoothDivisorPairChoices R).card = R ^ 2 := by
  simp [smoothDivisorPairChoices, pow_two]

/-- There are exactly `R ^ (2 * card κ)` paired divisor families. -/
@[simp]
theorem card_smoothDivisorFamilyChoices
    (κ : Type*) [Fintype κ] [DecidableEq κ]
    (R : ℕ) :
    (smoothDivisorFamilyChoices κ R).card =
      R ^ (2 * Fintype.card κ) := by
  rw [smoothDivisorFamilyChoices, Fintype.card_piFinset]
  simp only [card_smoothDivisorPairChoices, Finset.prod_const,
    Finset.card_univ]
  rw [← pow_mul]

/-! ## Generic finite weighted perturbations -/

/-- A finite weighted sum with coefficients in the closed unit ball is
Lipschitz, with constant equal to the cardinality of its support, for the
uniform norm on the attached values. -/
theorem abs_weightedFinsetSum_sub_le_card_mul
    {α : Type*} [DecidableEq α]
    (s : Finset α) (weight f g : α → ℝ)
    {ε : ℝ} (_hε : 0 ≤ ε)
    (hweight : ∀ x ∈ s, |weight x| ≤ 1)
    (herror : ∀ x ∈ s, |f x - g x| ≤ ε) :
    |(∑ x ∈ s, weight x * f x) -
        ∑ x ∈ s, weight x * g x| ≤
      (s.card : ℝ) * ε := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ x ∈ s, (weight x * f x - weight x * g x)| ≤
        ∑ x ∈ s,
          |weight x * f x - weight x * g x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ s, ε := by
      apply Finset.sum_le_sum
      intro x hx
      rw [← mul_sub, abs_mul]
      calc
        |weight x| * |f x - g x| ≤ 1 * ε :=
          mul_le_mul (hweight x hx) (herror x hx)
            (abs_nonneg _) (by norm_num)
        _ = ε := one_mul ε
    _ = (s.card : ℝ) * ε := by
      simp

namespace SmoothSieveCutoff

/-- A uniform density error propagates through the smooth divisor expansion
with the exact polynomial choice-count constant. -/
theorem abs_smoothDivisorExpansion_sub_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (density approximation : (κ → ℕ × ℕ) → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (herror :
      ∀ z ∈ smoothDivisorFamilyChoices κ R,
        |density z - approximation z| ≤ ε) :
    |(∑ z ∈ smoothDivisorFamilyChoices κ R,
          smoothDivisorFamilyCoefficient χ.toFun R z *
            density z) -
        ∑ z ∈ smoothDivisorFamilyChoices κ R,
          smoothDivisorFamilyCoefficient χ.toFun R z *
            approximation z| ≤
      (R ^ (2 * Fintype.card κ) : ℕ) * ε := by
  simpa using
    abs_weightedFinsetSum_sub_le_card_mul
      (smoothDivisorFamilyChoices κ R)
      (smoothDivisorFamilyCoefficient χ.toFun R)
      density approximation hε
      (fun z _hz =>
        χ.abs_smoothDivisorFamilyCoefficient_le_one R z)
      herror

/-- The same perturbation estimate after inserting exactly the normalized
Selberg prefactors.  Absolute values are retained, so the statement is safe
without additional sign hypotheses on the normalization parameters. -/
theorem abs_scaled_smoothDivisorExpansion_sub_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (R W : ℕ)
    (density approximation : (κ → ℕ × ℕ) → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (herror :
      ∀ z ∈ smoothDivisorFamilyChoices κ R,
        |density z - approximation z| ≤ ε) :
    |normalizedSelbergScale χ.normalizer R W ^
            Fintype.card κ *
          ((Real.log R ^ 2) ^ Fintype.card κ *
            ∑ z ∈ smoothDivisorFamilyChoices κ R,
              smoothDivisorFamilyCoefficient χ.toFun R z *
                density z) -
        normalizedSelbergScale χ.normalizer R W ^
            Fintype.card κ *
          ((Real.log R ^ 2) ^ Fintype.card κ *
            ∑ z ∈ smoothDivisorFamilyChoices κ R,
              smoothDivisorFamilyCoefficient χ.toFun R z *
                approximation z)| ≤
      |normalizedSelbergScale χ.normalizer R W| ^
          Fintype.card κ *
        |Real.log R ^ 2| ^ Fintype.card κ *
          ((R ^ (2 * Fintype.card κ) : ℕ) * ε) := by
  let densitySum : ℝ :=
    ∑ z ∈ smoothDivisorFamilyChoices κ R,
      smoothDivisorFamilyCoefficient χ.toFun R z * density z
  let approximationSum : ℝ :=
    ∑ z ∈ smoothDivisorFamilyChoices κ R,
      smoothDivisorFamilyCoefficient χ.toFun R z * approximation z
  have hsum : |densitySum - approximationSum| ≤
      (R ^ (2 * Fintype.card κ) : ℕ) * ε := by
    exact χ.abs_smoothDivisorExpansion_sub_le
      R density approximation hε herror
  change
    |normalizedSelbergScale χ.normalizer R W ^
            Fintype.card κ *
          ((Real.log R ^ 2) ^ Fintype.card κ * densitySum) -
        normalizedSelbergScale χ.normalizer R W ^
            Fintype.card κ *
          ((Real.log R ^ 2) ^ Fintype.card κ *
            approximationSum)| ≤ _
  rw [← mul_sub, ← mul_sub, abs_mul, abs_mul, abs_pow, abs_pow]
  calc
    |normalizedSelbergScale χ.normalizer R W| ^
            Fintype.card κ *
          (|Real.log R ^ 2| ^ Fintype.card κ *
            |densitySum - approximationSum|) ≤
        |normalizedSelbergScale χ.normalizer R W| ^
            Fintype.card κ *
          (|Real.log R ^ 2| ^ Fintype.card κ *
            ((R ^ (2 * Fintype.card κ) : ℕ) * ε)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsum
          (pow_nonneg (abs_nonneg _) _))
        (pow_nonneg (abs_nonneg _) _)
    _ =
        |normalizedSelbergScale χ.normalizer R W| ^
            Fintype.card κ *
          |Real.log R ^ 2| ^ Fintype.card κ *
            ((R ^ (2 * Fintype.card κ) : ℕ) * ε) := by
      ring

end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem
