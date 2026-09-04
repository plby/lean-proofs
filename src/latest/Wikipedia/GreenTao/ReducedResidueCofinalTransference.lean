import Wikipedia.GreenTao.CofinalPrimeTransference

/-!
# Cofinal transference on reduced residue classes

The sieve normalization for the W-tricked majorant uses that the selected
shift is coprime to `W`.  The prime-density theorem already selects such a
shift, but the older cofinal interface retained only the weaker inequality
`b < W`.

There is a second quantifier-order issue.  Converting AP cut discrepancy to
simplex face-cut discrepancy requires

```
Nat.Coprime N (Nat.factorial (r + 1)).
```

This is available after the cofinal argument selects a sufficiently large
prime modulus, but need not hold eventually at every natural modulus.

This file records the corrected interface.  Reduced-residue membership is
preserved through density selection, and the relative-counting comparison
is supplied by a callback invoked only after the prime modulus and its
factorial-coprimality proof have been constructed.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped Polynomial

/-- Cofinal-prime transference restricted to the reduced residue classes
that are actually produced by the W-trick density theorem. -/
def CofinalPrimeUniformReducedResidueWTrickedPrimeProgressionCount
    (k : ℕ) (α : ℝ) (W : ℕ) (δ c : ℝ) : Prop :=
  ∀ M₀ : ℕ,
    ∃ M : ℕ,
      M₀ ≤ M ∧ Nat.Prime (M + 1) ∧
        ∀ b : ℕ, b ∈ reducedResidues W →
          δ ≤
            mean
              (wTrickedPrimeWeight α W b :
                ZMod (M + 1) → ℝ) →
          c ≤
            cyclicAPCount k (M + 1)
              (wTrickedPrimeWeight α W b)

/-- Quantitative cofinal-prime transference with the two corrected
quantifier orders.

The majorization and linear-forms hypotheses are required only for reduced
residue classes.  The comparison callback is not assumed eventually at all
moduli: it is called at the selected prime modulus, after primality has
supplied coprimality with `(r + 1)!`. -/
theorem
    cofinalPrimeUniformReducedResidueWTrickedPrimeProgressionCount_of_eventually
    {r W : ℕ} {α : ℝ}
    (ν : (M : ℕ) → ℕ → ZMod (M + 1) → ℝ)
    {linearFormsError cutError approximationError : ℝ}
    {p : ℝ[X]} {δ denseCount countError : ℝ}
    (hα : 0 ≤ α)
    (happroximationError : 0 ≤ approximationError)
    (hcutError : 0 ≤ cutError)
    (hp :
      ApproximatesPositivePartOnUnitInterval
        p approximationError)
    (hconvert :
      (2 : ℝ) ^ (2 ^ (r + 1)) * linearFormsError ≤
        cutError ^ (2 ^ (r + 1)))
    (hweighted :
      HasUniformWeightedAPCount
        (r + 2) δ denseCount)
    (hν0 :
      ∀ M b (x : ZMod (M + 1)), 0 ≤ ν M b x)
    (hmajor :
      ∀ᶠ M : ℕ in atTop,
        ∀ b, b ∈ reducedResidues W →
          ∀ x : ZMod (M + 1),
            wTrickedPrimeWeight α W b x ≤ ν M b x)
    (hLF :
      ∀ᶠ M : ℕ in atTop,
        ∀ b, b ∈ reducedResidues W →
          HasLinearFormsCondition
            (r + 2) (M + 1) (ν M b)
              linearFormsError)
    (hcomparison :
      ∀ M b,
        Nat.Coprime (M + 1) (Nat.factorial (r + 1)) →
        HasLinearFormsCondition
          (r + 2) (M + 1) (ν M b)
            linearFormsError →
        RelativeAPComparisonLe
          r (M + 1) (ν M b)
          (polynomialDenseModelError
            p cutError approximationError)
          countError) :
    CofinalPrimeUniformReducedResidueWTrickedPrimeProgressionCount
      (r + 2) α W
      (δ + polynomialDenseModelError
        p cutError approximationError)
      (denseCount - countError) := by
  have hall :
      ∀ᶠ M : ℕ in atTop,
        (∀ b, b ∈ reducedResidues W →
          ∀ x : ZMod (M + 1),
            wTrickedPrimeWeight α W b x ≤ ν M b x) ∧
        (∀ b, b ∈ reducedResidues W →
          HasLinearFormsCondition
            (r + 2) (M + 1) (ν M b)
              linearFormsError) :=
    hmajor.and hLF
  rw [eventually_atTop] at hall
  obtain ⟨Mthreshold, hfrom⟩ := hall
  intro M₀
  obtain ⟨q, hqLarge, hqPrime⟩ :=
    Nat.exists_infinite_primes
      (max (max M₀ Mthreshold) (r + 1) + 1)
  let M := q - 1
  have hMsucc : M + 1 = q := by
    dsimp [M]
    omega
  have hM₀ : M₀ ≤ M := by
    dsimp [M]
    omega
  have hMthreshold : Mthreshold ≤ M := by
    dsimp [M]
    omega
  have hrank : r + 1 < M + 1 := by
    dsimp [M]
    omega
  obtain ⟨hmajorM, hLFM⟩ :=
    hfrom M hMthreshold
  refine
    ⟨M, hM₀, by simpa only [hMsucc] using hqPrime, ?_⟩
  intro b hb hmean
  let : NeZero (M + 1) := ⟨Nat.succ_ne_zero M⟩
  have hcoprime :
      Nat.Coprime (M + 1) (Nat.factorial (r + 1)) := by
    have hrankq : r + 1 < q := by
      simpa only [← hMsucc] using hrank
    have hqCoprime :
        Nat.Coprime q (Nat.factorial (r + 1)) :=
      hqPrime.coprime_factorial_of_lt hrankq
    simpa only [hMsucc] using hqCoprime
  exact
    relativeAPCount_lower_bound_of_linearFormsCondition
      happroximationError hcutError
      (wTrickedPrimeWeight_nonneg hα W b)
      (hmajorM b hb)
      (hν0 M b)
      hp
      (hLFM b hb)
      hcoprime
      hconvert
      (hweighted (M + 1))
      hmean
      (hcomparison M b hcoprime (hLFM b hb))

/-- The standard-cutoff cofinal obligation with reduced-residue membership
retained in the transference predicate. -/
def HasCofinalPrimeStandardReducedResidueWTrickedPrimeProgressionCounts :
    Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ∃ (w : ℕ) (c : ℝ), 0 < c ∧
      CofinalPrimeUniformReducedResidueWTrickedPrimeProgressionCount
        k
        (primeScale k
          standardSmoothSieveCutoff.normalizer)
        (primorial w)
        (densityTarget k
          standardSmoothSieveCutoff.normalizer)
        c

/-- Corrected cofinal transference combines directly with the existing
reduced-residue density theorem.  Only the final elementary count-lower
interface forgets coprimality, since prime extraction no longer needs it. -/
theorem
    HasCofinalPrimeStandardReducedResidueWTrickedPrimeProgressionCounts.toCountLower
    (htransfer :
      HasCofinalPrimeStandardReducedResidueWTrickedPrimeProgressionCounts) :
    HasCofinalPrimeWTrickedPrimeProgressionCountLower := by
  intro k hk
  obtain ⟨w, c, hc, htransferCofinal⟩ :=
    htransfer k hk
  refine
    ⟨primeScale k standardSmoothSieveCutoff.normalizer,
      primorial w, c,
      primeScale_pos hk
        standardSmoothSieveCutoff_normalizer_pos,
      primorial_pos w, hc, ?_⟩
  obtain ⟨Ndensity, hdensity⟩ :=
    exists_threshold_reducedResidue_mean_ge_densityTarget
      (w := w) hk
        standardSmoothSieveCutoff_normalizer_pos
  intro M₀
  obtain ⟨M, hMlarge, hprime, htransferM⟩ :=
    htransferCofinal (max M₀ Ndensity)
  have hM₀ : M₀ ≤ M :=
    (le_max_left M₀ Ndensity).trans hMlarge
  have hNdensity : Ndensity ≤ M + 1 :=
    (le_max_right M₀ Ndensity).trans
      (hMlarge.trans (Nat.le_succ M))
  obtain ⟨b, hb, hmean⟩ :=
    hdensity (M + 1) hNdensity (Nat.succ_pos M)
  exact
    ⟨M, hM₀, hprime, b,
      (mem_reducedResidues.mp hb).1,
      htransferM b hb hmean⟩

/-- Benchmark-facing endpoint through the corrected reduced-residue
cofinal interface. -/
theorem
    containsArbitraryAPs_primes_of_standard_reducedResidue_cofinal_prime_counts
    (htransfer :
      HasCofinalPrimeStandardReducedResidueWTrickedPrimeProgressionCounts) :
    SzemeredisTheorem.ContainsArbitraryAPs
      {p : ℕ | Nat.Prime p} :=
  containsArbitraryAPs_primes_of_cofinal_prime_count_lower
    htransfer.toCountLower

end Wikipedia.SzemeredisTheorem
