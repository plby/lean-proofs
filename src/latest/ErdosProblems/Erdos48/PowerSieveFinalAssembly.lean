/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PowerSieveAnalyticAssembly
import ErdosProblems.Erdos48.PowerSieveBadRootPrefix
import ErdosProblems.Erdos48.PowerSieveExceptionalRetarget
import ErdosProblems.Erdos48.PowerSieveLowRootEscape
import ErdosProblems.Erdos48.PowerSieveProgressionEnvelopeAbsorption
import ErdosProblems.Erdos48.PowerSieveVaughanDyadicAbsorption

/-!
# Final power-sieve assembly interfaces

This file exposes the prime-chain estimate in the pointwise form needed by
the Page dichotomy.  All asymptotic estimates remain eventual in the base,
but bad-root escape and prefix sparsity are hypotheses at that one base.
Consequently an unbounded collection of good original or retargeted Page
scales is enough; no branch has to hold eventually on every natural number.

The last section records a precise effective-constructor interface for the
remaining Page/power-sieve splice.
-/

namespace Erdos48

open Filter
open scoped Topology BigOperators

noncomputable section

private theorem eventually_const_mul_log_sq_le_rpow_quarter_final (D : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      D * Real.log (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
  by_cases hD : D ≤ 0
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (mul_nonpos_of_nonpos_of_nonneg hD (sq_nonneg _)).trans
      (Real.rpow_nonneg (by positivity) _)
  · have hDpos : 0 < D := lt_of_not_ge hD
    have hbound :=
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 4)).bound
          (show 0 < (1 / D : ℝ) by positivity)
    have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hbound
    filter_upwards [hnat, eventually_ge_atTop 1] with n hn hn1
    have hlog0 : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hn1)
    have hn0 : (0 : ℝ) ≤ n := by positivity
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg
      (Real.rpow_nonneg hn0 _)] at hn
    have := mul_le_mul_of_nonneg_left hn hDpos.le
    field_simp [hDpos.ne'] at this
    simpa [Real.rpow_natCast] using this

private theorem powerSieveSmoothBound_rpow_epsilon_le_final
    {n L : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L) :
    (powerSieveSmoothBound n L : ℝ) ^
        powerSievePrimeChainEpsilon L ≤
      (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hexp :
      ((120 * L - 6 : ℕ) : ℝ) * powerSievePrimeChainEpsilon L ≤
        (1 / 4 : ℝ) := by
    have hnat : 120 * L - 6 ≤ 120 * L := Nat.sub_le _ _
    have hcast : (((120 * L - 6 : ℕ) : ℝ)) ≤ 120 * (L : ℝ) := by
      exact_mod_cast hnat
    unfold powerSievePrimeChainEpsilon
    rw [div_eq_mul_inv]
    calc
      ((120 * L - 6 : ℕ) : ℝ) * (1 * (480 * (L : ℝ))⁻¹) ≤
          (120 * (L : ℝ)) * (480 * (L : ℝ))⁻¹ := by
        simp only [one_mul]
        gcongr
      _ = 1 / 4 := by field_simp; ring
  rw [powerSieveSmoothBound, Nat.cast_pow]
  calc
    ((n : ℝ) ^ (120 * L - 6)) ^ powerSievePrimeChainEpsilon L =
        ((n : ℝ) ^ (((120 * L - 6 : ℕ) : ℝ))) ^
          powerSievePrimeChainEpsilon L := by
      rw [Real.rpow_natCast]
    _ = (n : ℝ) ^
        ((((120 * L - 6 : ℕ) : ℝ)) *
          powerSievePrimeChainEpsilon L) := by
      rw [Real.rpow_mul (by positivity)]
    _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hnR hexp

private theorem natLog_smoothBound_le_final
    {n L : ℕ} (hn : 2 ≤ n) :
    (Nat.log 2 (powerSieveSmoothBound n L) : ℝ) ≤
      (((120 * L - 6 : ℕ) : ℝ) * Real.log (n : ℝ)) /
        Real.log 2 := by
  calc
    (Nat.log 2 (powerSieveSmoothBound n L) : ℝ) ≤
        Real.logb 2 (powerSieveSmoothBound n L : ℝ) :=
      Real.natLog_le_logb _ _
    _ = Real.log (powerSieveSmoothBound n L : ℝ) / Real.log 2 := rfl
    _ = _ := by
      rw [powerSieveSmoothBound, Nat.cast_pow, Real.log_pow]

private theorem log_powerSieveX_eq_final {n L : ℕ} :
    Real.log (powerSieveX n L : ℝ) =
      ((240 * L : ℕ) : ℝ) * Real.log (n : ℝ) := by
  rw [powerSieveX, Nat.cast_pow, Real.log_pow]

/-- Pointwise-implication form of the prime-chain harmonic estimate.

The cutoff `Q` is fixed once `L`, `A`, and the FKL closure constant are
fixed.  For all sufficiently large bases, escape above `Q` and the prefix
bound are then consumed at that same base. -/
theorem exists_powerSievePrimeChainClosure_eventually_le_pointwise
    (L : ℕ) (hL : 1 ≤ L) (A : ℝ) (hA : 0 < A)
    (rawLower : ℕ → ℕ → ℝ) :
    ∃ Q : ℕ, ∃ C : ℝ, 2 ≤ Q ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        (∀ q ∈ shiftedSmoothBadRoots (powerSieveX n L)
          (powerSieveSmoothBound n L) (rawLower n), Q < q) →
        (∀ y : ℕ,
          ((((shiftedSmoothBadRoots (powerSieveX n L)
            (powerSieveSmoothBound n L) (rawLower n)).filter
              fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
            (A / Real.sqrt (n : ℝ)) * y) →
        (∑ t ∈ primeChainClosureTargets (powerSieveSmoothBound n L)
          (shiftedSmoothBadRoots (powerSieveX n L)
            (powerSieveSmoothBound n L) (rawLower n)), (t : ℝ)⁻¹) ≤
          powerSievePrimeChainBudget n L := by
  have heps : 0 < powerSievePrimeChainEpsilon L := by
    unfold powerSievePrimeChainEpsilon
    positivity
  obtain ⟨Q, C, hC, hclosure⟩ :=
    exists_primeChainClosureTargets_harmonic_bound_of_prefix_sparse heps
  refine ⟨max 2 Q, C, le_max_left _ _, hC, ?_⟩
  let D : ℝ :=
    2 * A * C * (120 * (L : ℝ)) * (240 * (L : ℝ)) *
      (Real.log 2)⁻¹ * (960000000000 * (L : ℝ) ^ 4)
  have hdecay := eventually_const_mul_log_sq_le_rpow_quarter_final D
  filter_upwards [hdecay, eventually_ge_atTop 2]
      with n hnDecay hn
  intro hnLarge hnPrefix
  let x := powerSieveX n L
  let u := powerSieveSmoothBound n L
  let E := shiftedSmoothBadRoots x u (rawLower n)
  let eps := powerSievePrimeChainEpsilon L
  have hraw := hclosure E u (A / Real.sqrt (n : ℝ))
    (fun q hq ↦ ⟨(shiftedSmoothBadRoots_prime_bound hq).1,
      (le_max_right 2 Q).trans_lt (hnLarge q hq),
      (shiftedSmoothBadRoots_prime_bound hq).2⟩)
    hnPrefix
  have huEps : (u : ℝ) ^ eps ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
    simpa only [u, eps] using
      powerSieveSmoothBound_rpow_epsilon_le_final (by omega : 1 ≤ n) hL
  have hlogu := natLog_smoothBound_le_final (L := L) hn
  have hlogx : Real.log (x : ℝ) =
      (240 * (L : ℝ)) * Real.log (n : ℝ) := by
    simpa only [x, Nat.cast_mul, Nat.cast_ofNat] using
      log_powerSieveX_eq_final (n := n) (L := L)
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogxPos : 0 < Real.log (x : ℝ) := by
    rw [hlogx]
    positivity
  have hsqrt : Real.sqrt (n : ℝ) =
      (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hquarterPos : 0 < (n : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hsqrtEq : Real.sqrt (n : ℝ) =
      ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
    calc
      Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := hsqrt
      _ = (n : ℝ) ^ ((1 / 4 : ℝ) * (2 : ℝ)) := by norm_num
      _ = ((n : ℝ) ^ (1 / 4 : ℝ)) ^ (2 : ℝ) := by
        rw [Real.rpow_mul (by positivity)]
      _ = ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 :=
        Real.rpow_natCast _ 2
  have hbudget :
      C * (u : ℝ) ^ eps *
          ((Nat.log 2 u : ℝ) * (2 * (A / Real.sqrt (n : ℝ)))) ≤
        powerSievePrimeChainBudget n L := by
    rw [powerSievePrimeChainBudget]
    rw [show Real.log (powerSieveX n L : ℝ) = Real.log (x : ℝ) by rfl]
    have hscalePos : 0 < 960000000000 * (L : ℝ) ^ 4 := by positivity
    rw [show 1 / (960000000000 * (L : ℝ) ^ 4 * Real.log (x : ℝ)) =
        (1 / (960000000000 * (L : ℝ) ^ 4)) / Real.log (x : ℝ) by
      field_simp [hscalePos.ne', hlogxPos.ne']]
    rw [le_div_iff₀ hlogxPos]
    calc
      C * (u : ℝ) ^ eps *
            ((Nat.log 2 u : ℝ) * (2 * (A / Real.sqrt (n : ℝ)))) *
          Real.log (x : ℝ) ≤
        C * (n : ℝ) ^ (1 / 4 : ℝ) *
            ((((120 * L - 6 : ℕ) : ℝ) * Real.log (n : ℝ)) /
              Real.log 2 * (2 * (A / Real.sqrt (n : ℝ)))) *
          ((240 * (L : ℝ)) * Real.log (n : ℝ)) := by
        rw [hlogx]
        gcongr
      _ ≤
          D * Real.log (n : ℝ) ^ 2 *
            ((n : ℝ) ^ (1 / 4 : ℝ) *
              (Real.sqrt (n : ℝ))⁻¹) /
                (960000000000 * (L : ℝ) ^ 4) := by
        have hk : (((120 * L - 6 : ℕ) : ℝ)) ≤
            120 * (L : ℝ) := by
          exact_mod_cast (Nat.sub_le (120 * L) 6)
        let F : ℝ :=
          2 * A * C * (240 * (L : ℝ)) * (Real.log 2)⁻¹ *
            Real.log (n : ℝ) ^ 2 * (n : ℝ) ^ (1 / 4 : ℝ) *
              (Real.sqrt (n : ℝ))⁻¹
        calc
          C * (n : ℝ) ^ (1 / 4 : ℝ) *
                ((((120 * L - 6 : ℕ) : ℝ) * Real.log (n : ℝ)) /
                  Real.log 2 * (2 * (A / Real.sqrt (n : ℝ)))) *
              ((240 * (L : ℝ)) * Real.log (n : ℝ)) =
              (((120 * L - 6 : ℕ) : ℝ)) * F := by
            dsimp [F]
            rw [div_eq_mul_inv]
            ring
          _ ≤ (120 * (L : ℝ)) * F := by
            apply mul_le_mul_of_nonneg_right hk
            dsimp [F]
            positivity
          _ = D * Real.log (n : ℝ) ^ 2 *
                ((n : ℝ) ^ (1 / 4 : ℝ) *
                  (Real.sqrt (n : ℝ))⁻¹) /
                    (960000000000 * (L : ℝ) ^ 4) := by
            dsimp [F, D]
            field_simp [hscalePos.ne']
      _ = D * Real.log (n : ℝ) ^ 2 *
            ((n : ℝ) ^ (1 / 4 : ℝ))⁻¹ /
              (960000000000 * (L : ℝ) ^ 4) := by
        rw [hsqrtEq, pow_two]
        field_simp [hquarterPos.ne']
      _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) *
            ((n : ℝ) ^ (1 / 4 : ℝ))⁻¹ /
              (960000000000 * (L : ℝ) ^ 4) := by gcongr
      _ = 1 / (960000000000 * (L : ℝ) ^ 4) := by
        rw [mul_inv_cancel₀ hquarterPos.ne']
  exact hraw.trans hbudget

/-- Pointwise eventual form of the final analytic constructor.  It is the
branch-compatible counterpart of
`eventually_nonempty_FLPAnalyticScale_of_powerSieve_badRoots`. -/
theorem exists_eventually_nonempty_FLPAnalyticScale_of_powerSieve_badRoots_pointwise
    (K L : ℕ) (hL : 1 ≤ L) (A : ℝ) (hA : 0 < A)
    (rawLower : ℕ → ℕ → ℝ)
    (hraw : ∀ᶠ n : ℕ in atTop, ∀ q : ℕ, q.Prime →
      q ≤ powerSieveSmoothBound n L →
        powerSieveRawLower n L q ≤ rawLower n q) :
    ∃ Q : ℕ, ∀ᶠ n : ℕ in atTop,
      (∀ q ∈ shiftedSmoothBadRoots (powerSieveX n L)
        (powerSieveSmoothBound n L) (rawLower n), Q < q) →
      (∀ y : ℕ,
        ((((shiftedSmoothBadRoots (powerSieveX n L)
          (powerSieveSmoothBound n L) (rawLower n)).filter
            fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
          (A / Real.sqrt (n : ℝ)) * y) →
      Nonempty (FLPAnalyticScale K) := by
  obtain ⟨Q, C, hQ, hC, hclosure⟩ :=
    exists_powerSievePrimeChainClosure_eventually_le_pointwise
      L hL A hA rawLower
  have hnumeric := eventually_powerSieve_goodScale_numerics K L hL
  refine ⟨Q, ?_⟩
  filter_upwards [hclosure, hraw, hnumeric, eventually_ge_atTop 2]
      with n hclosure hraw hnumeric hn
  intro hlarge hprefix
  have hmass := hclosure hlarge hprefix
  have hu : 2 ≤ powerSieveSmoothBound n L := by
    unfold powerSieveSmoothBound
    have hexp : 0 < 120 * L - 6 := by omega
    exact hn.trans (Nat.le_pow hexp)
  have htwo : 2 ∉ shiftedSmoothBadRoots (powerSieveX n L)
      (powerSieveSmoothBound n L) (rawLower n) := by
    intro hbad
    have := hlarge 2 hbad
    omega
  refine ⟨FLPAnalyticScale.of_powerSievePrimeChainAssembly
    hL hu htwo hmass hraw hnumeric.1 ?_⟩
  intro q hq _hqClosure hqu
  exact hnumeric.2 q hq hqu

/-! ## The endpoint-split prefix input -/

/-- All unconditional fixed-exponent estimates, together with low-root
escape and the literal-root progression budget, assemble the exact prefix
input.  Only Page endpoint-goodness through the current base remains a
pointwise hypothesis. -/
theorem eventually_powerSieveEndpointSplitPrefixInput_of_root_le_budget
    (L J₀ : ℕ) (hL : 1 ≤ L) (hJlarge : 2000 * L ≤ 2 ^ J₀)
    (hescape : ∀ᶠ n : ℕ in atTop, ∀ q ∈
      shiftedSmoothBadRoots (powerSieveX n L)
        (powerSieveSmoothBound n L) (powerSieveRawLower n L),
      2 ^ J₀ < q)
    (hnumeric : ∀ᶠ n : ℕ in atTop, ∀ Q q r : ℕ,
      1 ≤ Q → Q < q → q ≤ 2 * Q →
      q ≤ powerSieveSmoothBound n L →
      r ∈ powerSieveAuxPrimes n L Q →
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r
          (powerSieveCofactorBound n L)).card : ℝ) +
            powerSieveGoodRootWeight n L q * (r : ℝ)⁻¹ ≤
          powerSieveProgressionBudget (powerSieveX n L) q r) :
    ∀ᶠ n : ℕ in atTop, ∀ m₀ : ℕ,
      (∀ q ∈ Finset.Ioc 1 n, q ≠ m₀ →
        primitiveEndpointMass (powerSieveX n L) q ≤
          (powerSieveX n L : ℝ) / 20) →
      PowerSieveEndpointSplitPrefixInput n L J₀ m₀
        (powerSieveCofactorBound n L) (powerSieveGoodRootWeight n L) := by
  have hmass := eventually_powerSieveAuxPrimes_reciprocal_lower L hL
  have hpartner := eventually_powerSieveDyadicPartnerLower_pos L hL
  have hbudgets := eventually_powerSieve_dyadicVaughanBudgets_absorbed L hL
  have hroot := eventually_powerSieve_rootVaughanBudget_absorbed L hL
  filter_upwards [hescape, hnumeric, hmass, hpartner, hbudgets, hroot,
      eventually_ge_atTop 4]
    with n hescapeN hnumericN hmassN hpartnerN hbudgetsN hrootN hn
  intro m₀ hPage
  refine
    { hn := by omega
      hL := hL
      hJlarge := hJlarge
      hbelow := ?_
      hPageGood := ?_
      hmass := ?_
      hpartnerPos := ?_
      hW := ?_
      hcofactor := ?_
      hnumeric := ?_
      hauxBudget := ?_
      hprodBudget := ?_
      hrootBudget := ?_ }
  · intro q hqBad _hqm₀ hqLow
    have hqCanonical : q ∈ shiftedSmoothBadRoots (powerSieveX n L)
        (powerSieveSmoothBound n L) (powerSieveRawLower n L) := by
      rw [← powerSieveShiftedSmoothBadRoots_goodRootWeight_eq]
      exact hqBad
    exact (not_lt_of_ge hqLow) (hescapeN q hqCanonical)
  · intro q hqBad hqm₀ hqn
    have hqPrime := (mem_powerSieveShiftedSmoothBadRoots.mp hqBad).1
    have htwentieth := hPage q
      (Finset.mem_Ioc.mpr ⟨hqPrime.one_lt, hqn⟩) hqm₀
    exact htwentieth.trans (by
      have hx : (0 : ℝ) ≤ powerSieveX n L := by positivity
      linarith)
  · intro Q hQ _hQupper
    exact hmassN Q hQ
  · intro Q hQ _hQupper
    exact hpartnerN Q hQ
  · intro q hqBad _hqm₀
    have hqPrime := (mem_powerSieveShiftedSmoothBadRoots.mp hqBad).1
    unfold powerSieveGoodRootWeight
    have hqPos : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
    have hxOne : 1 < powerSieveX n L := by
      unfold powerSieveX
      exact (show 1 < n by omega).trans_le
        (Nat.le_pow (by omega : 0 < 240 * L))
    have hlog : 0 < Real.log (powerSieveX n L : ℝ) :=
      Real.log_pos (by exact_mod_cast hxOne)
    positivity
  · intro Q hQ _hQupper q _hqBad _hqm₀ hqBlock r hr p hp s
      _hsPrime hs _hsDiv
    have hqLower := (mem_powerSieveDyadicPrimeBlock.mp hqBlock).1
    exact powerSieve_largeCofactor_le hn hL hQ hqLower hr hp hs
  · intro Q hQ _hQupper q hqBad _hqm₀ hqBlock r hr
    have hqData := mem_powerSieveDyadicPrimeBlock.mp hqBlock
    have hqSmooth :=
      (mem_powerSieveShiftedSmoothBadRoots.mp hqBad).2.1
    exact hnumericN Q q r hQ hqData.1 hqData.2.1 hqSmooth hr
  · intro Q hQ hQupper
    exact (hbudgetsN Q hQ hQupper).1
  · intro Q hQ hQupper
    exact (hbudgetsN Q hQ hQupper).2
  · intro Q hQ hQupper hnQ
    exact hrootN Q hQ hQupper hnQ

/-! ## Effective Page-branch interface -/

/-- Endpoint-goodness on the original Page range, in the stronger
one-twentieth normalization returned by the Page theorem. -/
def PowerSieveOriginalEndpointGood (n L : ℕ) : Prop :=
  ∀ q ∈ Finset.Ioc 1 (n ^ 240),
    primitiveEndpointMass (powerSieveX n L) q ≤
      (powerSieveX n L : ℝ) / 20

/-- Endpoint-goodness after retargeting to the exceptional conductor. -/
def PowerSieveRetargetEndpointGood (m L : ℕ) : Prop :=
  ∀ q ∈ Finset.Ioc 1 m, q ≠ m →
    primitiveEndpointMass (powerSieveX m L) q ≤
      (powerSieveX m L : ℝ) / 20

/-- A fixed exponent is effectively usable on each of the two Page
branches.  The cutoffs may depend on `K` and `L`, but not on the selected
base. -/
def PowerSieveEffectiveBranchConstructor (K L : ℕ) : Prop :=
  ∃ Noriginal Nretarget : ℕ,
    (∀ n : ℕ, Noriginal ≤ n → PowerSieveOriginalEndpointGood n L →
      Nonempty (FLPAnalyticScale K)) ∧
    (∀ m : ℕ, Nretarget ≤ m → PowerSieveRetargetEndpointGood m L →
      Nonempty (FLPAnalyticScale K))

/-- Low-root escape and the literal-root progression budget produce the
effective constructors required on both Page branches. -/
theorem powerSieveEffectiveBranchConstructor_of_escape_and_budget
    (K L : ℕ) (hL : 1 ≤ L)
    (hescape : ∀ Q₀ : ℕ, ∀ᶠ n : ℕ in atTop, ∀ q ∈
      shiftedSmoothBadRoots (powerSieveX n L)
        (powerSieveSmoothBound n L) (powerSieveRawLower n L),
      Q₀ < q)
    (hnumeric : ∀ᶠ n : ℕ in atTop, ∀ Q q r : ℕ,
      1 ≤ Q → Q < q → q ≤ 2 * Q →
      q ≤ powerSieveSmoothBound n L →
      r ∈ powerSieveAuxPrimes n L Q →
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r
          (powerSieveCofactorBound n L)).card : ℝ) +
            powerSieveGoodRootWeight n L q * (r : ℝ)⁻¹ ≤
          powerSieveProgressionBudget (powerSieveX n L) q r) :
    PowerSieveEffectiveBranchConstructor K L := by
  let J₀ := Nat.clog 2 (2000 * L)
  have hJlarge : 2000 * L ≤ 2 ^ J₀ := by
    dsimp only [J₀]
    exact Nat.le_pow_clog (by omega) _
  have hinput :=
    eventually_powerSieveEndpointSplitPrefixInput_of_root_le_budget
      L J₀ hL hJlarge (hescape (2 ^ J₀)) hnumeric
  have hraw : ∀ᶠ n : ℕ in atTop, ∀ q : ℕ, q.Prime →
      q ≤ powerSieveSmoothBound n L →
        powerSieveRawLower n L q ≤ powerSieveRawLower n L q :=
    Filter.Eventually.of_forall fun _ _ _ _ ↦ le_rfl
  obtain ⟨Qchain, hanalytic⟩ :=
    exists_eventually_nonempty_FLPAnalyticScale_of_powerSieve_badRoots_pointwise
      K L hL 5 (by norm_num) (powerSieveRawLower · L) hraw
  have hescapeChain := hescape Qchain
  have hOriginal : ∀ᶠ n : ℕ in atTop,
      PowerSieveOriginalEndpointGood n L →
        Nonempty (FLPAnalyticScale K) := by
    filter_upwards [hinput, hescapeChain, hanalytic,
        eventually_ge_atTop 2]
      with n hinputN hescapeN hanalyticN hn
    intro hendpoint
    have hpage : ∀ q ∈ Finset.Ioc 1 n, q ≠ 0 →
        primitiveEndpointMass (powerSieveX n L) q ≤
          (powerSieveX n L : ℝ) / 20 := by
      intro q hq _hq0
      have hqData := Finset.mem_Ioc.mp hq
      apply hendpoint q
      exact Finset.mem_Ioc.mpr ⟨hqData.1, hqData.2.trans
        (Nat.le_pow (by norm_num : 0 < (240 : ℕ)))⟩
    have hpref := (hinputN 0 hpage).full_prefix_bound_of_zero
    apply hanalyticN hescapeN
    intro y
    rw [← powerSieveShiftedSmoothBadRoots_goodRootWeight_eq n L]
    calc
      ((((powerSieveShiftedSmoothBadRoots n L
          (powerSieveGoodRootWeight n L)).filter
            fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
          (4 / Real.sqrt (n : ℝ)) * (y : ℝ) := hpref y
      _ ≤ (5 / Real.sqrt (n : ℝ)) * (y : ℝ) := by
        have hsqrt : 0 < Real.sqrt (n : ℝ) := by positivity
        gcongr <;> norm_num
  have hRetarget : ∀ᶠ n : ℕ in atTop,
      PowerSieveRetargetEndpointGood n L →
        Nonempty (FLPAnalyticScale K) := by
    filter_upwards [hinput, hescapeChain, hanalytic]
      with n hinputN hescapeN hanalyticN
    intro hendpoint
    have hpref := (hinputN n hendpoint).full_prefix_bound_of_base
    apply hanalyticN hescapeN
    intro y
    rw [← powerSieveShiftedSmoothBadRoots_goodRootWeight_eq n L]
    exact hpref y
  obtain ⟨Noriginal, hNoriginal⟩ := eventually_atTop.1 hOriginal
  obtain ⟨Nretarget, hNretarget⟩ := eventually_atTop.1 hRetarget
  exact ⟨Noriginal, Nretarget,
    fun n hn ↦ hNoriginal n hn, fun n hn ↦ hNretarget n hn⟩

/-- The uniform endpoint/retarget dichotomy turns effective constructors at
the two selected exponents into the desired analytic scale. -/
theorem nonempty_FLPAnalyticScale_of_effective_powerSieve_constructors
    (K Lmin : ℕ)
    (hconstruct : ∀ L : ℕ, Lmin ≤ L →
      PowerSieveEffectiveBranchConstructor K L) :
    Nonempty (FLPAnalyticScale K) := by
  obtain ⟨cPage, hcPage, hquadratic, L, Lretarget,
      hL64, hLretarget64, hLretargetMin, hLretarget, hendpoint⟩ :=
    eventually_powerSieveEndpoint_pointwise_or_retarget_uniform_above Lmin
  have hLmin : Lmin ≤ L := by omega
  obtain ⟨Noriginal, _NretargetOriginal, hOriginal, _hRetargetOriginal⟩ :=
    hconstruct L hLmin
  obtain ⟨_NoriginalRetarget, Nretarget, _hOriginalRetarget, hRetarget⟩ :=
    hconstruct Lretarget hLretargetMin
  have hcases := hendpoint Nretarget
  have hfinal : ∀ᶠ n : ℕ in atTop, Nonempty (FLPAnalyticScale K) := by
    filter_upwards [hcases, eventually_ge_atTop Noriginal] with n hn hnCutoff
    rcases hn with hgood | ⟨m, hm, hmCutoff, _hmbad, _hmWitness, hmGood⟩
    · exact hOriginal n hnCutoff hgood
    · exact hRetarget m hmCutoff hmGood
  rcases hfinal.exists with ⟨n, hn⟩
  exact hn

/-- The complete power-sieve/Page assembly: every requested finite analytic
scale is inhabited. -/
theorem nonempty_FLPAnalyticScale_of_powerSieve (K : ℕ) :
    Nonempty (FLPAnalyticScale K) := by
  obtain ⟨Lescape, hLescape, hescape⟩ :=
    exists_eventually_powerSieveLowRootEscape
  obtain ⟨Aβ, Cπ, CV, CBV, S, X₀, Lbudget,
      hAβ, hCπ, hCV, hCBV, hS, hlogAβ, hw, hSLbudget, hbudget⟩ :=
    exists_eventually_represented_add_goodRootWeight_le_budget_of_root_le
  let Lmin := max Lescape Lbudget
  apply nonempty_FLPAnalyticScale_of_effective_powerSieve_constructors K Lmin
  intro L hLmin
  have hL : 1 ≤ L := hLescape.trans
    ((le_max_left Lescape Lbudget).trans hLmin)
  apply powerSieveEffectiveBranchConstructor_of_escape_and_budget K L hL
  · exact hescape L ((le_max_left Lescape Lbudget).trans hLmin)
  · exact hbudget L ((le_max_right Lescape Lbudget).trans hLmin)

/-- Uniform form used by the final Erdős-48 theorem. -/
theorem all_nonempty_FLPAnalyticScale :
    ∀ K : ℕ, Nonempty (FLPAnalyticScale K) :=
  nonempty_FLPAnalyticScale_of_powerSieve

end

end Erdos48
