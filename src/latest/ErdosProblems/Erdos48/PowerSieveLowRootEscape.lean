/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PowerSieveVaughanBudgetAbsorption
import ErdosProblems.Erdos48.PowerSieveDyadicBadRoots
import ErdosProblems.Erdos48.PowerSieveProgressionEnvelopeAbsorption
import ErdosProblems.Erdos48.PowerSievePrimeChainAssembly
import ErdosProblems.Erdos48.EndpointSmallConductors
import ErdosProblems.Erdos48.PowerSieveEndpoint

/-!
# Escape of fixed bad roots at the power-sieve scale

For a fixed root cutoff, the auxiliary interval eventually starts above
every possible root.  Thus the full auxiliary reciprocal mass can be used:
there is no need to erase the root and consequently no artificial lower
bound such as `1000 * L ≤ q`.
-/

namespace Erdos48

open Filter
open scoped Topology BigOperators

noncomputable section

/-- The literal bad-root set defined from the progression weight is the
canonical bad-root set used by the prime-chain assembly. -/
theorem powerSieveShiftedSmoothBadRoots_goodRootWeight_eq
    (n L : ℕ) :
    powerSieveShiftedSmoothBadRoots n L (powerSieveGoodRootWeight n L) =
      shiftedSmoothBadRoots (powerSieveX n L)
        (powerSieveSmoothBound n L) (powerSieveRawLower n L) := by
  unfold powerSieveShiftedSmoothBadRoots
  congr 1
  funext q
  exact (powerSieveRawLower_eq_goodRootWeight_div n L q).symm

/-- Every fixed cutoff is eventually below every auxiliary prime interval,
uniformly in its dyadic block parameter. -/
theorem eventually_lt_powerSieveAuxLower (L Q₀ : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ Q : ℕ, Q₀ < powerSieveAuxLower n L Q := by
  filter_upwards [eventually_gt_atTop Q₀] with n hn Q
  have hnCore : n ≤ powerSieveAuxCore n L Q := by
    unfold powerSieveAuxCore powerSieveAuxScale
    exact le_max_right _ _
  unfold powerSieveAuxLower
  omega

/-- Elementary block-size bound used by the fixed-root contradiction. -/
theorem card_powerSieveDyadicPrimeBlock_le_base (Q : ℕ) :
    (powerSieveDyadicPrimeBlock Q).card ≤ Q := by
  calc
    (powerSieveDyadicPrimeBlock Q).card ≤ (Finset.Ioc Q (2 * Q)).card :=
      Finset.card_filter_le _ _
    _ = 2 * Q - Q := by rw [Nat.card_Ioc]
    _ = Q := by omega

/-- Fixed conductors have small endpoint mass at every fixed power-sieve
scale.  This is the pointwise consequence of the existing
Siegel--Walfisz small-conductor aggregate. -/
theorem eventually_powerSieve_fixedRoots_endpointGood
    (L Q₀ : ℕ) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop, ∀ q : ℕ, q.Prime → q ≤ Q₀ →
      primitiveEndpointMass (powerSieveX n L) q ≤
        (powerSieveX n L : ℝ) / 10 := by
  have hxTop : Tendsto (fun n : ℕ ↦ powerSieveX n L) atTop atTop := by
    unfold powerSieveX
    exact tendsto_nat_pow_fixed_atTop (240 * L) (by omega)
  have hsmallX := eventually_sum_primitiveEndpointMass_Icc_le_mul
    (1 : ℝ) (1 / 10 : ℝ) (by norm_num) (by norm_num)
  have hsmall := hxTop.eventually hsmallX
  have hlogTop : Tendsto
      (fun n : ℕ ↦ Real.log (powerSieveX n L : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hxTop)
  have hQlog : ∀ᶠ n : ℕ in atTop,
      (Q₀ : ℝ) ≤ Real.log (powerSieveX n L : ℝ) :=
    hlogTop.eventually_ge_atTop Q₀
  filter_upwards [hsmall, hQlog] with n hn hQlog q hq hqQ₀
  have hsum := hn Q₀ (by simpa using hQlog)
  have hqMem : q ∈ Finset.Icc 2 Q₀ :=
    Finset.mem_Icc.mpr ⟨hq.two_le, hqQ₀⟩
  have hsingle : primitiveEndpointMass (powerSieveX n L) q ≤
      ∑ d ∈ Finset.Icc 2 Q₀,
        primitiveEndpointMass (powerSieveX n L) d :=
    Finset.single_le_sum
      (fun d _ ↦ primitiveEndpointMass_nonneg (powerSieveX n L) d) hqMem
  norm_num [div_eq_mul_inv] at hsum ⊢
  linarith

/-- The endpoint-good auxiliary partners without deleting the root.  This
is the useful family when the root is below the auxiliary interval. -/
def powerSieveEndpointGoodAuxiliaryPartners
    (n L Q q : ℕ) : Finset ℕ :=
  endpointGoodAuxiliaryPartners (powerSieveX n L) q
    (powerSieveAuxPrimes n L Q)

/-- At a literal bad root below the auxiliary interval, the endpoint-good
auxiliary partners have reciprocal mass strictly below `1/(1000L)`.
Unlike the global dyadic version, no auxiliary prime is erased. -/
theorem sum_inv_powerSieveEndpointGoodAuxiliaryPartners_lt
    {n L Q q B : ℕ} {W : ℕ → ℝ}
    (hn : 2 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q)
    (hqAux : q ≤ powerSieveAuxLower n L Q)
    (hW : 0 < W q)
    (hqBad : q ∈ powerSieveShiftedSmoothBadRoots n L W)
    (hqGood : primitiveEndpointMass (powerSieveX n L) q ≤
      (powerSieveX n L : ℝ) / 10)
    (hcofactor : ∀ r ∈ powerSieveAuxPrimes n L Q,
      ∀ p ∈ primesInProgression
        (powerSieveX n L) (q * r) (q * r - 1),
        ∀ s : ℕ, s.Prime → powerSieveSmoothBound n L < s →
          s ∣ p + 1 → (p + 1) / (q * r * s) ≤ B)
    (hnumeric : ∀ r ∈ powerSieveAuxPrimes n L Q,
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r B).card : ℝ) +
          W q * (r : ℝ)⁻¹ ≤
        powerSieveProgressionBudget (powerSieveX n L) q r) :
    (∑ r ∈ powerSieveEndpointGoodAuxiliaryPartners n L Q q,
      (r : ℝ)⁻¹) < 1 / (1000 * (L : ℝ)) := by
  let G := powerSieveEndpointGoodAuxiliaryPartners n L Q q
  have hqData := mem_powerSieveShiftedSmoothBadRoots.mp hqBad
  have hbridge :
      W q * ∑ r ∈ G, (r : ℝ)⁻¹ ≤
        ((240 * L : ℕ) : ℝ) *
          (((smoothShiftedPrimes
            (powerSieveX n L) (powerSieveSmoothBound n L)).filter
              fun p ↦ q ∣ p + 1).card : ℝ) := by
    apply mul_sum_inv_le_mul_card_smoothShiftedFiber_of_endpoint_good_of_ne
      (x := powerSieveX n L) (u := powerSieveSmoothBound n L)
      (q := q) (B := B) (D := 240 * L)
      (R0 := powerSieveAuxLower n L Q) (R := G) (W := W q)
    · rw [powerSieveX_eq_auxScale_pow]
      have hscale : 2 ≤ powerSieveAuxScale n L := by
        simpa only [powerSieveAuxScale] using hn
      exact hscale.trans (Nat.le_pow (by omega : 0 < 240 * L))
    · exact hW.le
    · exact hqData.1
    · intro r hr
      exact (mem_powerSieveAuxPrimes.mp
        (mem_endpointGoodAuxiliaryPartners.mp hr).1).2.2
    · exact hqData.2.1
    · intro r hr
      have hrAux := (mem_endpointGoodAuxiliaryPartners.mp hr).1
      exact ((mem_powerSieveAuxPrimes.mp hrAux).2.1).trans
        (powerSieveAuxUpper_le_smoothBound (by omega) hL hQ)
    · intro r hr
      exact (mem_powerSieveAuxPrimes.mp
        (mem_endpointGoodAuxiliaryPartners.mp hr).1).1
    · exact powerSieveX_add_one_lt_auxLower_pow hn hL
    · intro r hr
      have hrLower := (mem_powerSieveAuxPrimes.mp
        (mem_endpointGoodAuxiliaryPartners.mp hr).1).1
      omega
    · exact hqGood
    · intro r hr
      exact (mem_endpointGoodAuxiliaryPartners.mp hr).2.1
    · intro r hr
      exact (mem_endpointGoodAuxiliaryPartners.mp hr).2.2
    · intro r hr
      exact hcofactor r (mem_endpointGoodAuxiliaryPartners.mp hr).1
    · intro r hr
      exact hnumeric r (mem_endpointGoodAuxiliaryPartners.mp hr).1
  have hcardBad := hqData.2.2
  have hscaled :
      ((240 * L : ℕ) : ℝ) *
          (((smoothShiftedPrimes
            (powerSieveX n L) (powerSieveSmoothBound n L)).filter
              fun p ↦ q ∣ p + 1).card : ℝ) <
        W q * (1 / (1000 * (L : ℝ))) := by
    calc
      ((240 * L : ℕ) : ℝ) *
          (((smoothShiftedPrimes
            (powerSieveX n L) (powerSieveSmoothBound n L)).filter
              fun p ↦ q ∣ p + 1).card : ℝ) <
          ((240 * L : ℕ) : ℝ) *
            (W q / (240000 * (L : ℝ) ^ 2)) :=
        mul_lt_mul_of_pos_left hcardBad (by positivity)
      _ = W q * (1 / (1000 * (L : ℝ))) := by
        push_cast
        field_simp
        ring
  have hmul : W q * ∑ r ∈ G, (r : ℝ)⁻¹ <
      W q * (1 / (1000 * (L : ℝ))) := hbridge.trans_lt hscaled
  nlinarith

/-- A fixed low bad root has the exact Vaughan partner threshold worth of
endpoint-bad auxiliary primes.  The full reciprocal mass gives a gap twice
as large as the one required by the denominator `2000L`. -/
theorem powerSieveVaughanPartnerThreshold_le_card_of_root_le_auxLower
    {n L Q q B : ℕ} {W : ℕ → ℝ}
    (hn : 2 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q)
    (hqAux : q ≤ powerSieveAuxLower n L Q)
    (hmass : (1 / (500 * (L : ℝ)) : ℝ) ≤
      ∑ r ∈ powerSieveAuxPrimes n L Q, (r : ℝ)⁻¹)
    (hW : 0 < W q)
    (hqBad : q ∈ powerSieveShiftedSmoothBadRoots n L W)
    (hqGood : primitiveEndpointMass (powerSieveX n L) q ≤
      (powerSieveX n L : ℝ) / 10)
    (hcofactor : ∀ r ∈ powerSieveAuxPrimes n L Q,
      ∀ p ∈ primesInProgression
        (powerSieveX n L) (q * r) (q * r - 1),
        ∀ s : ℕ, s.Prime → powerSieveSmoothBound n L < s →
          s ∣ p + 1 → (p + 1) / (q * r * s) ≤ B)
    (hnumeric : ∀ r ∈ powerSieveAuxPrimes n L Q,
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r B).card : ℝ) +
          W q * (r : ℝ)⁻¹ ≤
        powerSieveProgressionBudget (powerSieveX n L) q r) :
    powerSieveVaughanPartnerThreshold n L Q 2000 ≤
      (endpointBadAuxiliaryPartners (powerSieveX n L) q
        (powerSieveAuxPrimes n L Q)).card := by
  have hgood := sum_inv_powerSieveEndpointGoodAuxiliaryPartners_lt
    hn hL hQ hqAux hW hqBad hqGood hcofactor hnumeric
  unfold powerSieveVaughanPartnerThreshold
  apply div_le_card_endpointBadAuxiliaryPartners
    (R0 := powerSieveAuxCore n L Q) (D := 2000 * L)
    (S := 1 / (500 * (L : ℝ)))
    (G := 1 / (1000 * (L : ℝ)))
  · exact powerSieveAuxCore_pos (by omega)
  · positivity
  · intro r hr
    have hrLower := (mem_powerSieveAuxPrimes.mp hr).1
    unfold powerSieveAuxLower at hrLower
    omega
  · exact hmass
  · simpa only [powerSieveEndpointGoodAuxiliaryPartners] using hgood
  · push_cast
    field_simp
    norm_num

/-- The chosen fixed cofactor bound follows from the root--auxiliary product
lower bound and the fact that the residual prime exceeds the smoothness
cutoff. -/
theorem powerSieve_largeCofactor_le
    {n L Q q r p s : ℕ}
    (hn : 4 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q)
    (hqLower : Q < q)
    (hr : r ∈ powerSieveAuxPrimes n L Q)
    (hp : p ∈ primesInProgression
      (powerSieveX n L) (q * r) (q * r - 1))
    (hs : powerSieveSmoothBound n L < s) :
    (p + 1) / (q * r * s) ≤ powerSieveCofactorBound n L := by
  have hqr : powerSieveProductBase n L < q * r :=
    powerSieveProductBase_lt_root_mul_aux hn hQ hqLower hr
  have hpX : p ≤ powerSieveX n L :=
    (mem_primesInProgression.mp hp).1
  have hden : powerSieveX n L + 1 ≤
      (q * r * s) * powerSieveCofactorBound n L := by
    have hpow : powerSieveX n L + 1 ≤ n ^ (240 * L + 1) := by
      unfold powerSieveX
      rw [pow_succ]
      have hxPos : 0 < n ^ (240 * L) := by positivity
      nlinarith
    calc
      powerSieveX n L + 1 ≤ n ^ (240 * L + 1) := hpow
      _ = powerSieveProductBase n L *
          powerSieveSmoothBound n L * powerSieveCofactorBound n L := by
        unfold powerSieveProductBase powerSieveSmoothBound
          powerSieveCofactorBound
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      _ ≤ (q * r * s) * powerSieveCofactorBound n L := by
        gcongr
  apply Nat.div_le_of_le_mul
  simpa [mul_comm] using (Nat.add_le_add_right hpX 1).trans hden

/-- Finite square-root contradiction package for one bad root below the
auxiliary interval.  It is stated independently of eventual estimates so
that both the original and retargeted Page branches can reuse it. -/
theorem powerSieve_sqrt_le_dyadicBlock_card_of_low_badRoot
    {n L Q q B : ℕ} {W : ℕ → ℝ}
    (hn : 2 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q)
    (hQupper : Q ≤ powerSieveSmoothBound n L)
    (hqBlock : q ∈ powerSieveDyadicPrimeBlock Q)
    (hqAux : q ≤ powerSieveAuxLower n L Q)
    (hthreshold : 2000 * L ≤ powerSieveAuxCore n L Q)
    (hmass : (1 / (500 * (L : ℝ)) : ℝ) ≤
      ∑ r ∈ powerSieveAuxPrimes n L Q, (r : ℝ)⁻¹)
    (hW : 0 < W q)
    (hqBad : q ∈ powerSieveShiftedSmoothBadRoots n L W)
    (hqGood : primitiveEndpointMass (powerSieveX n L) q ≤
      (powerSieveX n L : ℝ) / 10)
    (hcofactor : ∀ r ∈ powerSieveAuxPrimes n L Q,
      ∀ p ∈ primesInProgression
        (powerSieveX n L) (q * r) (q * r - 1),
        ∀ s : ℕ, s.Prime → powerSieveSmoothBound n L < s →
          s ∣ p + 1 → (p + 1) / (q * r * s) ≤ B)
    (hnumeric : ∀ r ∈ powerSieveAuxPrimes n L Q,
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r B).card : ℝ) +
          W q * (r : ℝ)⁻¹ ≤
        powerSieveProgressionBudget (powerSieveX n L) q r)
    (hauxBudget :
      20 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveAuxUpper n L Q) ≤
        (powerSieveVaughanPartnerThreshold n L Q 2000 : ℝ) *
          (powerSieveX n L : ℝ))
    (hprodBudget :
      40 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveProductVaughanCutoff n L Q) ≤
        ((powerSieveDyadicPrimeBlock Q).card : ℝ) *
          (powerSieveVaughanPartnerThreshold n L Q 2000 : ℝ) *
            (powerSieveX n L : ℝ)) :
    Real.sqrt (n : ℝ) ≤ (powerSieveDyadicPrimeBlock Q).card := by
  classical
  have hmain := powerSieve_badRoots_card_mul_sqrt_le_card
    (E := {q}) (Q := powerSieveDyadicPrimeBlock Q)
    hn hL hQ (by norm_num : 0 < (2000 : ℕ)) hQupper hthreshold
  have hmain' := hmain
    (by simpa only [Finset.singleton_subset_iff] using hqBlock)
    (fun d hd ↦ (mem_powerSieveDyadicPrimeBlock.mp hd).2.2)
    (fun d hd ↦ (mem_powerSieveDyadicPrimeBlock.mp hd).2.1)
    (by
      intro d hd
      have hdq : d = q := Finset.mem_singleton.mp hd
      subst d
      exact powerSieveVaughanPartnerThreshold_le_card_of_root_le_auxLower
        hn hL hQ hqAux hmass hW hqBad hqGood hcofactor hnumeric)
    hauxBudget hprodBudget
  simpa using hmain'

/-- Once the pointwise progression estimate is available at a fixed
exponent, every fixed initial segment is eventually disjoint from the
literal bad-root set.  This is the low-root escape used before dyadic
aggregation. -/
theorem eventually_powerSieveShiftedSmoothBadRoots_above
    (L Q₀ : ℕ) (hL : 1 ≤ L)
    (hnumeric : ∀ᶠ n : ℕ in atTop, ∀ Q q r : ℕ,
      1 ≤ Q → Q < q → q ≤ 2 * Q →
      2 * Q ≤ powerSieveSmoothBound n L →
      r ∈ powerSieveAuxPrimes n L Q →
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r
          (powerSieveCofactorBound n L)).card : ℝ) +
            powerSieveGoodRootWeight n L q * (r : ℝ)⁻¹ ≤
          powerSieveProgressionBudget (powerSieveX n L) q r) :
    ∀ᶠ n : ℕ in atTop, ∀ q ∈
      powerSieveShiftedSmoothBadRoots n L (powerSieveGoodRootWeight n L),
        Q₀ < q := by
  have hmass := eventually_powerSieveAuxPrimes_reciprocal_lower L hL
  have hendpoint := eventually_powerSieve_fixedRoots_endpointGood L Q₀ hL
  have hauxLower := eventually_lt_powerSieveAuxLower L Q₀
  have hbudgets := eventually_powerSieve_twoVaughanBudgets_absorbed
    L 2000 hL (by norm_num)
  have hsqrtTop : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hsqrtLarge : ∀ᶠ n : ℕ in atTop,
      (Q₀ : ℝ) < Real.sqrt (n : ℝ) :=
    hsqrtTop.eventually_gt_atTop Q₀
  filter_upwards [hmass, hendpoint, hauxLower, hbudgets, hnumeric,
      hsqrtLarge, eventually_ge_atTop (max 4 (max (2000 * L) (2 * Q₀)))]
    with n hmassN hendpointN hauxLowerN hbudgetsN hnumericN hsqrtN hnlarge
  intro q hqBad
  by_contra hnot
  have hqQ₀ : q ≤ Q₀ := Nat.le_of_not_gt hnot
  have hqPrime := (mem_powerSieveShiftedSmoothBadRoots.mp hqBad).1
  have hqTwo : 2 ≤ q := hqPrime.two_le
  let Q := q - 1
  have hQ : 1 ≤ Q := by dsimp [Q]; omega
  have hqLower : Q < q := by dsimp [Q]; omega
  have hqUpper : q ≤ 2 * Q := by dsimp [Q]; omega
  have hQQ₀ : Q ≤ Q₀ := by omega
  have hn4 : 4 ≤ n := (le_max_left 4 (max (2000 * L) (2 * Q₀))).trans hnlarge
  have hnThreshold : 2000 * L ≤ n :=
    (le_max_left (2000 * L) (2 * Q₀)).trans
      ((le_max_right 4 (max (2000 * L) (2 * Q₀))).trans hnlarge)
  have hnCut : 2 * Q₀ ≤ n :=
    (le_max_right (2000 * L) (2 * Q₀)).trans
      ((le_max_right 4 (max (2000 * L) (2 * Q₀))).trans hnlarge)
  have hcut : 2 * Q₀ ≤ powerSieveSmoothBound n L := by
    exact hnCut.trans (Nat.le_pow (by omega : 0 < 120 * L - 6))
  have hQupper : Q ≤ powerSieveSmoothBound n L :=
    hQQ₀.trans (by omega)
  have htwoQupper : 2 * Q ≤ powerSieveSmoothBound n L := by omega
  have hqBlock : q ∈ powerSieveDyadicPrimeBlock Q :=
    mem_powerSieveDyadicPrimeBlock.mpr ⟨hqLower, hqUpper, hqPrime⟩
  have hqAux : q ≤ powerSieveAuxLower n L Q :=
    hqQ₀.trans (hauxLowerN Q).le
  have hthreshold : 2000 * L ≤ powerSieveAuxCore n L Q := by
    exact hnThreshold.trans (by
      unfold powerSieveAuxCore powerSieveAuxScale
      exact le_max_right _ _)
  have hxTwo : 2 ≤ powerSieveX n L := by
    unfold powerSieveX
    exact (show 2 ≤ n by omega).trans
      (Nat.le_pow (by omega : 0 < 240 * L))
  have hW : 0 < powerSieveGoodRootWeight n L q := by
    unfold powerSieveGoodRootWeight
    have hqPos : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
    have hlog : 0 < Real.log (powerSieveX n L : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < powerSieveX n L by omega))
    positivity
  have hcardOne : (1 : ℝ) ≤ (powerSieveDyadicPrimeBlock Q).card := by
    exact_mod_cast Finset.one_le_card.mpr ⟨q, hqBlock⟩
  have hrootDensity : (Q : ℝ) ≤ Real.sqrt (n : ℝ) *
      ((powerSieveDyadicPrimeBlock Q).card : ℝ) := by
    have hQsqrt : (Q : ℝ) ≤ Real.sqrt (n : ℝ) := by
      exact (show (Q : ℝ) ≤ Q₀ by exact_mod_cast hQQ₀).trans hsqrtN.le
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have hbudget := hbudgetsN Q (powerSieveDyadicPrimeBlock Q).card
    hQ hQupper hrootDensity
  have hsqrtCard :=
    powerSieve_sqrt_le_dyadicBlock_card_of_low_badRoot
      (B := powerSieveCofactorBound n L)
      (W := powerSieveGoodRootWeight n L)
      (q := q) (by omega : 2 ≤ n) hL hQ hQupper hqBlock hqAux hthreshold
      (hmassN Q hQ) hW hqBad (hendpointN q hqPrime hqQ₀)
      (by
        intro r hr p hp s _hsPrime hs _hsDiv
        exact powerSieve_largeCofactor_le hn4 hL hQ hqLower hr hp hs)
      (hnumericN Q q · hQ hqLower hqUpper htwoQupper)
      hbudget.1 hbudget.2
  have hcardUpper : (powerSieveDyadicPrimeBlock Q).card ≤ Q :=
    card_powerSieveDyadicPrimeBlock_le_base Q
  have hrealUpper : ((powerSieveDyadicPrimeBlock Q).card : ℝ) ≤ Q₀ := by
    exact_mod_cast hcardUpper.trans hQQ₀
  linarith

/-- Unconditional low-root escape at every sufficiently large fixed
power-sieve exponent, in the canonical `shiftedSmoothBadRoots` notation
consumed by prime-chain assembly. -/
theorem exists_eventually_powerSieveLowRootEscape :
    ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∀ L : ℕ, L₀ ≤ L → ∀ Q₀ : ℕ,
      ∀ᶠ n : ℕ in atTop, ∀ q ∈
        shiftedSmoothBadRoots (powerSieveX n L)
          (powerSieveSmoothBound n L) (powerSieveRawLower n L),
        Q₀ < q := by
  obtain ⟨Aβ, Cπ, CV, CBV, S, X₀, L₀, hAβ, hCπ, hCV, hCBV,
      hS, hlogAβ, hw, hSL₀, hnumeric⟩ :=
    exists_eventually_represented_add_goodRootWeight_le_budget
  refine ⟨L₀, ?_, ?_⟩
  · omega
  intro L hLL₀ Q₀
  have hL : 1 ≤ L := by omega
  have hescape := eventually_powerSieveShiftedSmoothBadRoots_above
    L Q₀ hL (hnumeric L hLL₀)
  filter_upwards [hescape] with n hn q hq
  apply hn q
  rw [powerSieveShiftedSmoothBadRoots_goodRootWeight_eq]
  exact hq

end

end Erdos48
