import ErdosProblems.Erdos67b.MRTypicalCofactorRestoredPrefix
import ErdosProblems.Erdos67b.MRCofactorProjectionLimit
import ErdosProblems.Erdos67b.MRCofactorSecondaryLimit

/-!
# Uniform small mean for the original actual typical cofactor

The cutoff exponent is chosen first, the nonpretentiousness threshold
second, and one ambient threshold last. All finite-mask and block conditions
remain explicit, and the typicality blocks contain only primes at least 23.
The denominator set may contain small primes. This is not a short-interval theorem.
-/

open Filter
open scoped Topology

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrExists_uniform_small_mean_restoredTypicalCofactor_of_localDistance {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∃ N₀ X₀ : ℕ, 0 < N₀ ∧
      ∀ {N X : ℕ}, N₀ ≤ N → X₀ ≤ X →
      ∀ (A : Finset ℕ), (∀ p ∈ A, p.Prime) →
      ∀ (J : Finset ℕ) (B : ℕ → Finset ℕ),
        (∀ j ∈ J, 1 ≤ j) → (∀ j ∈ J, B j ⊆ primesUpTo X) →
        Set.PairwiseDisjoint (↑J : Set ℕ) B →
        (∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16) →
        (∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ)) →
        (∀ p ∈ A, p ≤ mrCofactorPowerCutoff delta X) →
        (∀ j ∈ J, ∀ p ∈ B j, p ≤ mrCofactorPowerCutoff delta X) →
        (∀ j ∈ J, ∀ p ∈ B j, 23 ≤ p) →
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → (∀ t : ℝ, |t| ≤ Real.log (X : ℝ) ^ 2 →
          (N : ℝ) ≤ pretentiousDistSq f (archimedeanTwist t) X) →
        ‖positivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B f) X‖ / (X : ℝ) ≤ epsilon := by
  obtain ⟨C, Y, hC, hprefix⟩ := mrExists_norm_positivePrefix_typicalCofactor_div_le_restoredBudgets_of_localDistance
  let S := mrCofactorSecondaryMeanConstant
  let M := mrCofactorRestoredMeanConstant C
  have hS : 0 ≤ S := mrCofactorSecondaryMeanConstant_nonneg
  have hM : 0 ≤ M := mrCofactorRestoredMeanConstant_nonneg hC
  let delta := min (1 / 2 : ℝ) (epsilon / (4 * (S + 1)))
  have hdelta : 0 < delta := lt_min (by norm_num) (div_pos hepsilon (by positivity))
  have hdeltaOne : delta ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hsecondary : S * delta ≤ epsilon / 4 := by
    have hbound : delta ≤ epsilon / (4 * (S + 1)) := min_le_right _ _
    have hmul := (le_div_iff₀ (by positivity : 0 < 4 * (S + 1))).1 hbound
    nlinarith
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max (1 : ℝ) (4 * M / (delta * epsilon)))
  have hN₀pos : 0 < N₀ := by
    have hreal : (1 : ℝ) < N₀ := (le_max_left _ _).trans_lt hN₀
    exact_mod_cast (zero_lt_one.trans hreal)
  have hNbound : 4 * M / (delta * epsilon) ≤ (N₀ : ℝ) :=
    ((le_max_right _ _).trans_lt hN₀).le
  have hcontourSmall {N : ℕ} (hN : N₀ ≤ N) : M / (N * delta) ≤ epsilon / 4 := by
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN₀pos.trans_le hN
    have hcast : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
    have hbudget : 4 * M ≤ (N : ℝ) * (delta * epsilon) :=
      (div_le_iff₀ (mul_pos hdelta hepsilon)).1 (hNbound.trans hcast)
    apply (div_le_iff₀ (mul_pos hNreal hdelta)).2
    nlinarith
  have hrem := (mrTendsto_cofactorOrdinaryProjection hdelta).add
    (mrTendsto_cofactorSecondaryRemainder hdelta)
  simp only [zero_add] at hrem
  have hsmall := (tendsto_order.1 hrem).2 (epsilon / 2) (by positivity)
  have hconditions := mrEventually_cofactorPowerCutoff_conditions hdelta hdeltaOne Y
  have hall : ∀ᶠ X : ℕ in atTop,
      (let y := mrCofactorPowerCutoff delta X
      Y ≤ y ∧ 23 ≤ y ∧ y ≤ X ∧ 6 ≤ Real.log (y : ℝ) ∧
        Real.log (X : ℝ) ^ 12 ≤ (y : ℝ) ∧
        4 * Real.log (X : ℝ) ≤ Real.log (y : ℝ) ^ 2 ∧
        delta * Real.log (X : ℝ) ≤ Real.log (y : ℝ) ∧
        Real.log (y : ℝ) ≤ 2 * delta * Real.log (X : ℝ)) ∧
      4 ≤ X ∧ 1 ≤ Real.log (X : ℝ) ∧
      Real.log (X : ℝ) ^ 2 / (X : ℝ) ≤ 1 ∧
      PrimeEstimates.primeReciprocals X ≤ Real.log (X : ℝ) ∧
      mrTypicalCofactorSecondaryBound (mrCofactorPowerCutoff delta X) X ≤
        S * delta + mrCofactorSecondaryRemainder delta X ∧
      gsA10OrdinaryMovingProjectionAveragedBound (mrCofactorPowerCutoff delta X) X
          (Real.log (mrCofactorPowerCutoff delta X : ℝ))⁻¹ +
        mrCofactorSecondaryRemainder delta X < epsilon / 2 := by
    filter_upwards [hconditions, eventually_ge_atTop 4,
      EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop 1),
      MRHalaszBands.eventually_log_pow_div_self_le 2 zero_lt_one,
      mrEventually_primeReciprocals_le_log, mrEventually_cofactorSecondary_le hdelta, hsmall]
      with X hcond hX hlog hheight hprime hsec hr
    exact ⟨hcond, hX, hlog, hheight, hprime, hsec, hr⟩
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 hall
  refine ⟨delta, hdelta, hdeltaOne, N₀, X₀, hN₀pos, ?_⟩
  intro N X hN hX A hA J B hJ hB hdisj hsmallPrimes hmass hAy hBy hlarge f hmul hbound hdistance
  obtain ⟨hcond, hXfour, hlogX, hheight, hprime, hsec, hrem⟩ := hX₀ X hX
  obtain ⟨hY, hy, hyX, hlogy, hlogTwelve, hlogSquare, hcutoff, _⟩ := hcond
  have hNpos : 0 < N := hN₀pos.trans_le hN
  have hXpos : (0 : ℝ) < X := by positivity
  have hTX : Real.log (X : ℝ) ^ 2 ≤ (X : ℝ) := (div_le_one hXpos).1 hheight
  have hfour : Real.log (X : ℝ) ^ 4 ≤ (mrCofactorPowerCutoff delta X : ℝ) :=
    (pow_le_pow_right₀ hlogX (by norm_num : 4 ≤ 12)).trans hlogTwelve
  have hp := hprefix A hA J B hNpos hY hy hyX hJ hB hdisj hsmallPrimes hmass hAy hBy hlarge
    hmul hbound hdistance (mrCofactorDyadicHeight X) hlogX hlogy hTX
    (mrCofactor_sourceHeight_le_two_pow X) hprime hfour
  have hc := mrCofactor_restoredContourBudget_le_inverse_nonpretentious hC hdelta hNpos hXfour
    (show 3 ≤ mrCofactorPowerCutoff delta X by omega) hlogX hprime hlogSquare hlogTwelve hcutoff
  have hcsmall := hc.trans (hcontourSmall hN)
  linarith

theorem mrExists_uniform_small_mean_restoredTypicalCofactor {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∃ N₀ X₀ : ℕ, 0 < N₀ ∧
      ∀ {N X : ℕ}, N₀ ≤ N → X₀ ≤ X →
      ∀ (A : Finset ℕ), (∀ p ∈ A, p.Prime) →
      ∀ (J : Finset ℕ) (B : ℕ → Finset ℕ),
        (∀ j ∈ J, 1 ≤ j) → (∀ j ∈ J, B j ⊆ primesUpTo X) →
        Set.PairwiseDisjoint (↑J : Set ℕ) B →
        (∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16) →
        (∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ)) →
        (∀ p ∈ A, p ≤ mrCofactorPowerCutoff delta X) →
        (∀ j ∈ J, ∀ p ∈ B j, p ≤ mrCofactorPowerCutoff delta X) →
        (∀ j ∈ J, ∀ p ∈ B j, 23 ≤ p) →
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f N X →
        ‖positivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B f) X‖ / (X : ℝ) ≤ epsilon := by
  obtain ⟨delta, hdelta, hdeltaOne, N₀, X₀, hN₀, hlocal⟩ :=
    mrExists_uniform_small_mean_restoredTypicalCofactor_of_localDistance hepsilon
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.1
    (MRHalaszBands.eventually_log_pow_div_self_le 2 zero_lt_one)
  refine ⟨delta, hdelta, hdeltaOne, N₀, max X₀ (max X₁ 1), hN₀, ?_⟩
  intro N X hN hX A hA J B hJ hB hdisj hsmall hmass hAy hBy hlarge f hmul hbound hnonpret
  have hX₀ : X₀ ≤ X := (le_max_left _ _).trans hX
  have hX₁le : X₁ ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hX)
  have hXpos : 0 < X := (le_max_right _ _).trans ((le_max_right _ _).trans hX)
  have hheight : Real.log (X : ℝ) ^ 2 ≤ (X : ℝ) :=
    (div_le_one (by exact_mod_cast hXpos : (0 : ℝ) < X)).1 (hX₁ X hX₁le)
  exact hlocal hN hX₀ A hA J B hJ hB hdisj hsmall hmass hAy hBy hlarge hmul hbound
    (fun t ht ↦ hnonpret t (ht.trans hheight))

end

end Erdos67b
