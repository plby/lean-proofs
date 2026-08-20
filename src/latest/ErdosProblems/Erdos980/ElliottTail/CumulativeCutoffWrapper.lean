import ErdosProblems.Erdos980.ElliottTail.CumulativeMediumApplication

/-!
# Completing a cumulative estimate below a fixed cutoff

A ray or congruence sieve is often stated only from a fixed numerical
threshold `T₀` onward.  Below that threshold the trivial prime-counting
bound is sufficient: multiplying its constant by `T₀²` supplies the
missing inverse-square denominators.  This file packages that finite
completion independently of any particular sieve construction.
-/

open Filter
open scoped Topology

namespace Erdos980.ElliottTail

noncomputable section

/-- The exceptional set is a subset of the rational primes at most `x`. -/
theorem exceptionalPrimes_card_le_primeCounting (ell t x : ℕ) :
    (exceptionalPrimes ell t x).card ≤ Nat.primeCounting x := by
  calc
    (exceptionalPrimes ell t x).card ≤ (primesBelow x).card := by
      unfold exceptionalPrimes
      exact Finset.card_filter_le _ _
    _ ≤ (Nat.primesLE x).card := by
      apply Finset.card_le_card
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpx := Finset.mem_range.mp hp'.1
      exact Nat.mem_primesLE.mpr ⟨hpx.le, hp'.2⟩
    _ = Nat.primeCounting x := Nat.primesLE_card_eq_primeCounting x

/-- A single unconditional Chebyshev constant gives the crude estimate
needed below every fixed numerical cutoff, uniformly in both `ell` and
`t`. -/
theorem exists_eventually_exceptionalPrimes_card_le_mul_div_log :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in atTop, ∀ ell t : ℕ,
      ((exceptionalPrimes ell t x).card : ℝ) ≤
        B * ((x : ℝ) / Real.log (x : ℝ)) := by
  have hupperR := Chebyshev.eventually_primeCounting_le
    (ε := (1 : ℝ)) (by norm_num)
  have hupperN := (tendsto_natCast_atTop_atTop (R := ℝ)) hupperR
  refine ⟨Real.log 4 + 1, by
    have : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    linarith, ?_⟩
  filter_upwards [hupperN] with x hx
  intro ell t
  calc
    ((exceptionalPrimes ell t x).card : ℝ) ≤
        (Nat.primeCounting x : ℝ) := by
      exact_mod_cast exceptionalPrimes_card_le_primeCounting ell t x
    _ ≤ (Real.log 4 + 1) * (x : ℝ) / Real.log (x : ℝ) := by
      change (Nat.primeCounting ⌊(x : ℝ)⌋₊ : ℝ) ≤
        (Real.log 4 + 1) * (x : ℝ) / Real.log (x : ℝ) at hx
      simpa only [Nat.floor_natCast] using hx
    _ = (Real.log 4 + 1) *
        ((x : ℝ) / Real.log (x : ℝ)) := by ring

/-- An eventual inverse-square bound above `T₀`, together with a crude
eventual bound at every numerical cutoff, gives the full cumulative bound.
The enlarged constant is explicit and is at least the original tail
constant. -/
theorem exists_cumulativeExceptionalPrimeScaleBound_of_tail_and_crude
    (ell T₀ : ℕ) (C B : ℝ) (hB : 0 ≤ B)
    (htail : ∀ᶠ x : ℕ in atTop, ∀ t : ℕ,
      T₀ ≤ t → t ≤ smoothParameterY x →
        ((exceptionalPrimes ell t x).card : ℝ) ≤
          (x : ℝ) / Real.log (x : ℝ) * inverseSquareMajorant C t)
    (hcrude : ∀ᶠ x : ℕ in atTop, ∀ t : ℕ,
      ((exceptionalPrimes ell t x).card : ℝ) ≤
        B * ((x : ℝ) / Real.log (x : ℝ))) :
    ∃ C' : ℝ, 0 ≤ C' ∧ C ≤ C' ∧
      CumulativeExceptionalPrimeScaleBound ell
        (inverseSquareMajorant C') := by
  let C' : ℝ := max C (B * (T₀ : ℝ) ^ 2)
  have hC' : 0 ≤ C' := by
    dsimp [C']
    exact (mul_nonneg hB (sq_nonneg _)).trans (le_max_right _ _)
  have hCC' : C ≤ C' := by
    dsimp [C']
    exact le_max_left _ _
  have hfinal : ∀ᶠ x : ℕ in atTop, ∀ t : ℕ,
      t ≤ smoothParameterY x →
        ((exceptionalPrimes ell t x).card : ℝ) ≤
          (x : ℝ) / Real.log (x : ℝ) *
            inverseSquareMajorant C' t := by
    filter_upwards [htail, hcrude, eventually_ge_atTop 2]
        with x hxtail hxcrude hx2
    intro t htY
    have hscale : 0 ≤ (x : ℝ) / Real.log (x : ℝ) := by
      have hlog : 0 < Real.log (x : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < x by omega))
      positivity
    by_cases ht₀ : T₀ ≤ t
    · have hmajor : inverseSquareMajorant C t ≤
          inverseSquareMajorant C' t := by
        unfold inverseSquareMajorant
        exact div_le_div_of_nonneg_right hCC' (sq_nonneg _)
      exact (hxtail t ht₀ htY).trans
        (mul_le_mul_of_nonneg_left hmajor hscale)
    · have htlt : t < T₀ := by omega
      have htcast : (((t + 1 : ℕ) : ℝ)) ≤ (T₀ : ℝ) := by
        exact_mod_cast (show t + 1 ≤ T₀ by omega)
      have hdenle : (((t + 1 : ℕ) : ℝ) ^ 2) ≤ (T₀ : ℝ) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) htcast _
      have hBden : B * (((t + 1 : ℕ) : ℝ) ^ 2) ≤ C' := by
        calc
          B * (((t + 1 : ℕ) : ℝ) ^ 2) ≤ B * (T₀ : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hdenle hB
          _ ≤ C' := by
            dsimp [C']
            exact le_max_right _ _
      have hden : 0 < (((t + 1 : ℕ) : ℝ) ^ 2) := by positivity
      have hBmajor : B ≤ inverseSquareMajorant C' t := by
        unfold inverseSquareMajorant
        exact (le_div_iff₀ hden).2 hBden
      calc
        ((exceptionalPrimes ell t x).card : ℝ) ≤
            B * ((x : ℝ) / Real.log (x : ℝ)) := hxcrude t
        _ = ((x : ℝ) / Real.log (x : ℝ)) * B := by ring
        _ ≤ ((x : ℝ) / Real.log (x : ℝ)) *
            inverseSquareMajorant C' t :=
          mul_le_mul_of_nonneg_left hBmajor hscale
  obtain ⟨X, hX⟩ := eventually_atTop.mp hfinal
  refine ⟨C', hC', hCC', ?_⟩
  exact ⟨X, fun x hx t ht ↦ hX x hx t ht⟩

/-- Immediate medium-tail consequence of the finite-cutoff completion. -/
theorem primeExponentMediumEstimate_of_eventually_tail_and_crude
    (ell T₀ : ℕ) (hell : 2 ≤ ell) (C B : ℝ) (hB : 0 ≤ B)
    (htail : ∀ᶠ x : ℕ in atTop, ∀ t : ℕ,
      T₀ ≤ t → t ≤ smoothParameterY x →
        ((exceptionalPrimes ell t x).card : ℝ) ≤
          (x : ℝ) / Real.log (x : ℝ) * inverseSquareMajorant C t)
    (hcrude : ∀ᶠ x : ℕ in atTop, ∀ t : ℕ,
      ((exceptionalPrimes ell t x).card : ℝ) ≤
        B * ((x : ℝ) / Real.log (x : ℝ))) :
    PrimeExponentMediumEstimate ell := by
  obtain ⟨C', hC', _hCC', hcount⟩ :=
    exists_cumulativeExceptionalPrimeScaleBound_of_tail_and_crude
      ell T₀ C B hB htail hcrude
  exact primeExponentMediumEstimate_of_inverseSquare_cumulative_bound
    ell hell C' hC' hcount

/-- Version in which the crude finite-cutoff bound is discharged
unconditionally by Chebyshev's estimate. -/
theorem exists_cumulativeExceptionalPrimeScaleBound_of_tail
    (ell T₀ : ℕ) (C : ℝ)
    (htail : ∀ᶠ x : ℕ in atTop, ∀ t : ℕ,
      T₀ ≤ t → t ≤ smoothParameterY x →
        ((exceptionalPrimes ell t x).card : ℝ) ≤
          (x : ℝ) / Real.log (x : ℝ) * inverseSquareMajorant C t) :
    ∃ C' : ℝ, 0 ≤ C' ∧ C ≤ C' ∧
      CumulativeExceptionalPrimeScaleBound ell
        (inverseSquareMajorant C') := by
  obtain ⟨B, hB, hcrude⟩ :=
    exists_eventually_exceptionalPrimes_card_le_mul_div_log
  have hcrude' : ∀ᶠ x : ℕ in atTop, ∀ t : ℕ,
      ((exceptionalPrimes ell t x).card : ℝ) ≤
        B * ((x : ℝ) / Real.log (x : ℝ)) := by
    filter_upwards [hcrude] with x hx
    exact hx ell
  exact exists_cumulativeExceptionalPrimeScaleBound_of_tail_and_crude
    ell T₀ C B hB.le htail hcrude'

/-- The final assumption-minimal wrapper: an eventual inverse-square sieve
estimate only for `t ≥ T₀` implies the exact medium estimate. -/
theorem primeExponentMediumEstimate_of_eventually_tail
    (ell T₀ : ℕ) (hell : 2 ≤ ell) (C : ℝ)
    (htail : ∀ᶠ x : ℕ in atTop, ∀ t : ℕ,
      T₀ ≤ t → t ≤ smoothParameterY x →
        ((exceptionalPrimes ell t x).card : ℝ) ≤
          (x : ℝ) / Real.log (x : ℝ) * inverseSquareMajorant C t) :
    PrimeExponentMediumEstimate ell := by
  obtain ⟨C', hC', _hCC', hcount⟩ :=
    exists_cumulativeExceptionalPrimeScaleBound_of_tail ell T₀ C htail
  exact primeExponentMediumEstimate_of_inverseSquare_cumulative_bound
    ell hell C' hC' hcount

end

end Erdos980.ElliottTail
