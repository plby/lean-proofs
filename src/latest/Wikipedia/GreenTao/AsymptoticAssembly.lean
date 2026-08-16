import Wikipedia.GreenTao.DiagonalNegligibility
import Wikipedia.GreenTao.Primes.WTrickDensity

/-!
# Asymptotic Green--Tao assembly

This file separates the already-proved prime-density input from the one
remaining transference output.

Chebyshev's theorem and the reduced-residue pigeonhole principle give, for
every sufficiently large modulus, a possibly modulus-dependent reduced
residue with a fixed positive mean.  The remaining analytic theorem should
uniformly turn that mean bound into a fixed positive progression-count
bound.  Combining the two implications yields the exact eventual interface
consumed by `DiagonalNegligibility`.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter

/-- Uniform eventual transference for the W-tricked prime weight at fixed
parameters.  The statement is uniform over every standard residue `b<W`
whose prime weight has the required mean.

No density theorem is included in this predicate; that input is supplied
separately by `WTrickDensity`. -/
def EventuallyUniformWTrickedPrimeProgressionCount
    (k : ℕ) (α : ℝ) (W : ℕ) (δ c : ℝ) : Prop :=
  ∀ᶠ M : ℕ in atTop,
    ∀ b : ℕ, b < W →
      δ ≤
        mean
          (wTrickedPrimeWeight α W b :
            ZMod (M + 1) → ℝ) →
      c ≤
        cyclicAPCount k (M + 1)
          (wTrickedPrimeWeight α W b)

/-- Chebyshev plus reduced-residue pigeonholing, rewritten with modulus
`M+1` and with only the standard-representative bound on the selected
residue retained. -/
theorem eventually_exists_reducedResidue_mean_ge_densityTarget_succ
    {k w : ℕ} (hk : 3 ≤ k) :
    ∀ᶠ M : ℕ in atTop,
      ∃ b : ℕ, b < primorial w ∧
        densityTarget k standardSmoothSieveCutoff.normalizer ≤
          mean
            (wTrickedPrimeWeight
              (primeScale k
                standardSmoothSieveCutoff.normalizer)
              (primorial w) b :
                ZMod (M + 1) → ℝ) := by
  obtain ⟨N₀, hN₀⟩ :=
    exists_threshold_reducedResidue_mean_ge_densityTarget
      (w := w) hk
        standardSmoothSieveCutoff_normalizer_pos
  filter_upwards [eventually_ge_atTop N₀] with M hM
  have hN₀M : N₀ ≤ M + 1 :=
    hM.trans (Nat.le_succ M)
  obtain ⟨b, hb, hmean⟩ :=
    hN₀ (M + 1) hN₀M (by omega)
  exact ⟨b, (mem_reducedResidues.mp hb).1, hmean⟩

/-- The sole remaining eventual count interface after fixing the canonical
smooth cutoff.  For each nontrivial length one may choose the W-trick cutoff
`w` and a positive count lower bound; all later moduli and all eligible
residue classes use those fixed parameters. -/
def HasEventuallyStandardWTrickedPrimeProgressionCounts : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ∃ (w : ℕ) (c : ℝ), 0 < c ∧
      EventuallyUniformWTrickedPrimeProgressionCount
        k
        (primeScale k
          standardSmoothSieveCutoff.normalizer)
        (primorial w)
        (densityTarget k
          standardSmoothSieveCutoff.normalizer)
        c

/-- Uniform eventual transference, combined with the proved W-tricked
density theorem, supplies the eventual count-lower-bound interface used by
the diagonal extraction. -/
theorem HasEventuallyStandardWTrickedPrimeProgressionCounts.toCountLower
    (htransfer :
      HasEventuallyStandardWTrickedPrimeProgressionCounts) :
    HasEventuallyWTrickedPrimeProgressionCountLower := by
  intro k hk
  obtain ⟨w, c, hc, htransferEventual⟩ :=
    htransfer k hk
  refine ⟨
    primeScale k standardSmoothSieveCutoff.normalizer,
    primorial w, ?_⟩
  refine ⟨c,
    primeScale_pos hk
      standardSmoothSieveCutoff_normalizer_pos,
    primorial_pos w, hc, ?_⟩
  have hdensity :=
    eventually_exists_reducedResidue_mean_ge_densityTarget_succ
      (w := w) hk
  filter_upwards [hdensity, htransferEventual] with
    M hdensityM htransferM
  obtain ⟨b, hb, hmean⟩ := hdensityM
  exact ⟨b, hb, htransferM b hb hmean⟩

/-- Benchmark-facing endpoint: after all dense, relative, and sieve work has
been packaged as the uniform eventual progression-count implication above,
the remaining density selection, diagonal exclusion, cyclic lifting, and
prime extraction are automatic. -/
theorem containsArbitraryAPs_primes_of_standard_eventual_counts
    (htransfer :
      HasEventuallyStandardWTrickedPrimeProgressionCounts) :
    SzemeredisTheorem.ContainsArbitraryAPs
      {p : ℕ | Nat.Prime p} :=
  containsArbitraryAPs_primes_of_eventual_count_lower
    htransfer.toCountLower

end Wikipedia.SzemeredisTheorem
