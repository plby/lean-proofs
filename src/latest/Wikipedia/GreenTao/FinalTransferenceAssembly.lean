import Wikipedia.GreenTao.ReducedResidueCofinalTransference
import Wikipedia.GreenTao.Sieve.CyclicLinearFormsLimitAssembly
import Wikipedia.SzemeredisTheorem
import Wikipedia.GreenTao.Transference.RelativeCountingParameterSelection

/-!
# Final dense/relative/sieve transference assembly

All elementary prime-density and extraction steps are already packaged by
`ReducedResidueCofinalTransference`.  This file performs the remaining
quantifier bookkeeping between the three deep inputs:

* ordered hypergraph removal, hence a positive uniform weighted dense AP
  count;
* the explicit relative-counting parameter package;
* the smooth cyclic-majorant linear-forms estimate.

The output is the corrected reduced-residue, cofinal-prime count predicate
consumed by the benchmark-facing theorem.  In particular the W-trick cutoff
is selected after the relative error, while the cyclic modulus is selected
only afterwards.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter

/-- Uniform ordered removal in precisely the ranks used to count arithmetic
progressions of every nontrivial length. -/
def HasOrderedRemovalForAllAPLengths : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    HasUniformOrderedPatternRemoval k (k - 1)

/-- The exact remaining smooth-sieve interface.

For every requested positive linear-forms error, one may choose a primorial
cutoff covering all fixed CFZ exceptional primes.  At that fixed cutoff the
standard cyclic Selberg majorant satisfies the linear-forms condition
eventually, uniformly over the reduced residue classes. -/
def HasStandardCyclicMajorantLinearForms : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ∀ η : ℝ, 0 < η →
      ∃ w : ℕ,
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w ∧
          ∀ᶠ M : ℕ in atTop,
            ∀ b : ℕ, b ∈ reducedResidues (primorial w) →
              HasLinearFormsCondition k (M + 1)
                (standardSmoothSieveCutoff.cyclicMajorant
                  (sieveLevel k (M + 1))
                  (primorial w) b)
                η

/-- Ordered removal and the standard smooth-sieve linear-forms estimate
supply the corrected cofinal-prime count predicate. -/
theorem
    hasCofinalPrimeStandardReducedResidueWTrickedPrimeProgressionCounts_of_orderedRemoval_of_linearForms
    (hremoval : HasOrderedRemovalForAllAPLengths)
    (hsieve : HasStandardCyclicMajorantLinearForms) :
    HasCofinalPrimeStandardReducedResidueWTrickedPrimeProgressionCounts := by
  intro k hk
  let density := densityTarget k standardSmoothSieveCutoff.normalizer
  have hdensity : 0 < density := by
    exact densityTarget_pos hk standardSmoothSieveCutoff_normalizer_pos
  let denseThreshold := density / 2
  have hdenseThreshold : 0 < denseThreshold := by
    dsimp [denseThreshold]
    linarith
  obtain ⟨denseCount, hdenseCount, hweighted⟩ :=
    exists_uniformWeightedAPCount_of_orderedRemoval_of_two_le
      k (by omega) (hremoval k hk) hdenseThreshold
  let countReserve := denseCount / 2
  have hcountReserve : 0 < countReserve := by
    dsimp [countReserve]
    linarith
  let r := k - 2
  obtain ⟨P⟩ :=
    RelativeCountingTransferenceParameters.nonempty
      r hdenseThreshold hcountReserve
  obtain ⟨w, _hwExceptional, hlinearForms⟩ :=
    hsieve k hk P.linearFormsError P.linearFormsError_pos
  let W := primorial w
  let ν : (M : ℕ) → ℕ → ZMod (M + 1) → ℝ :=
    fun M b =>
      standardSmoothSieveCutoff.cyclicMajorant
        (sieveLevel k (M + 1)) W b
  have hcolors : r + 2 = k := by
    dsimp [r]
    omega
  have hrank : r + 1 = k - 1 := by
    dsimp [r]
    omega
  have hν_nonneg :
      ∀ M b (x : ZMod (M + 1)), 0 ≤ ν M b x := by
    intro M b x
    exact
      standardSmoothSieveCutoff.cyclicMajorant_nonneg
        (one_le_sieveLevel hk (Nat.succ_pos M)) W b x
  have hmajor :
      ∀ᶠ M : ℕ in atTop,
        ∀ b, b ∈ reducedResidues W →
          ∀ x : ZMod (M + 1),
            wTrickedPrimeWeight
                (primeScale k
                  standardSmoothSieveCutoff.normalizer)
                W b x ≤
              ν M b x := by
    have hbase :=
      eventually_all_residues_wTrickedPrimeWeight_le_cyclicMajorant
        standardSmoothSieveCutoff hk (primorial_pos w)
    filter_upwards [hbase] with M hM
    intro b hb x
    exact hM b (mem_reducedResidues.mp hb).1 x
  have hLF :
      ∀ᶠ M : ℕ in atTop,
        ∀ b, b ∈ reducedResidues W →
          HasLinearFormsCondition
            (r + 2) (M + 1) (ν M b)
              P.linearFormsError := by
    simpa only [W, ν, hcolors] using hlinearForms
  have hcofinalSmall :
      CofinalPrimeUniformReducedResidueWTrickedPrimeProgressionCount
        (r + 2)
        (primeScale k standardSmoothSieveCutoff.normalizer)
        W
        (denseThreshold +
          polynomialDenseModelError
            P.polynomial P.cutError P.approximationError)
        (denseCount - countReserve) := by
    apply
      cofinalPrimeUniformReducedResidueWTrickedPrimeProgressionCount_of_eventually
        ν
        (r := r)
        (α := primeScale k standardSmoothSieveCutoff.normalizer)
        (linearFormsError := P.linearFormsError)
        (cutError := P.cutError)
        (approximationError := P.approximationError)
        (p := P.polynomial)
        (δ := denseThreshold)
        (denseCount := denseCount)
        (countError := countReserve)
    · exact
        primeScale_nonneg hk
          standardSmoothSieveCutoff_normalizer_pos
    · exact P.approximationError_pos.le
    · exact P.cutError_pos.le
    · exact P.approximates
    · exact P.denseModel_conversion
    · simpa only [hcolors] using hweighted
    · exact hν_nonneg
    · exact hmajor
    · exact hLF
    · intro M b hcoprime hLFM
      exact
        P.relativeAPComparisonLe hLFM
          (hν_nonneg M b) hcoprime
  have hdensityThreshold :
      denseThreshold +
          polynomialDenseModelError
            P.polynomial P.cutError P.approximationError ≤
        density := by
    have hmodel := P.denseModelError_lt
    dsimp [denseThreshold] at hmodel ⊢
    linarith
  have hcountPositive :
      0 < denseCount - countReserve := by
    dsimp [countReserve]
    linarith
  refine ⟨w, denseCount - countReserve, hcountPositive, ?_⟩
  simpa only [hcolors, W, density] using
    (show
      CofinalPrimeUniformReducedResidueWTrickedPrimeProgressionCount
        (r + 2)
        (primeScale k standardSmoothSieveCutoff.normalizer)
        W density (denseCount - countReserve) from
      by
        intro M₀
        obtain ⟨M, hM, hprime, hMtransfer⟩ :=
          hcofinalSmall M₀
        refine ⟨M, hM, hprime, ?_⟩
        intro b hb hmean
        exact
          hMtransfer b hb
            (hdensityThreshold.trans hmean))

/-- Benchmark-facing endpoint with the two research-scale inputs exposed
and every parameter-selection and elementary extraction step discharged. -/
theorem containsArbitraryAPs_primes_of_orderedRemoval_of_linearForms
    (hremoval : HasOrderedRemovalForAllAPLengths)
    (hsieve : HasStandardCyclicMajorantLinearForms) :
    SzemeredisTheorem.ContainsArbitraryAPs
      {p : ℕ | Nat.Prime p} :=
  containsArbitraryAPs_primes_of_standard_reducedResidue_cofinal_prime_counts
    (hasCofinalPrimeStandardReducedResidueWTrickedPrimeProgressionCounts_of_orderedRemoval_of_linearForms
      hremoval hsieve)

end Wikipedia.SzemeredisTheorem
