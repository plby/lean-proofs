import ErdosProblems.Erdos980.ElliottTail.CumulativeMediumTail
import ErdosProblems.Erdos980.ElliottTail.FinalAssembly
import ErdosProblems.Erdos980.ElliottTail.MediumTail

/-!
# Applying a cumulative prime-scale bound to Elliott's medium tail

This is the numerical-cutoff interface for the quadratic Rosser sieve and
the odd-prime ray-class sieve.  It isolates their common analytic output:
a uniform cumulative exceptional-prime bound with a summable layer-cake
majorant.
-/

namespace Erdos980.ElliottTail

open Filter
open scoped Topology BigOperators

noncomputable section

/-- A uniform prime-scale upper bound for all cumulative cutoffs up to the
moving smooth cutoff. -/
def CumulativeExceptionalPrimeScaleBound (k : ℕ) (g : ℕ → ℝ) : Prop :=
  ∃ X : ℕ, ∀ x : ℕ, X ≤ x → ∀ t : ℕ, t ≤ smoothParameterY x →
    ((exceptionalPrimes k t x).card : ℝ) ≤
      (x : ℝ) / Real.log (x : ℝ) * g t

/-- The layer-cake majorant beyond the numerical cutoff `y`. -/
def cumulativeMajorantTail (g : ℕ → ℝ) (y : ℕ) : ℝ :=
  (y + 1 : ℝ) * g y + ∑' t : ℕ, if y < t then g t else 0

/-- The strict numerical tail is the usual shifted tail of the series. -/
theorem tsum_strictTail_eq_tsum_shift (g : ℕ → ℝ) (M : ℕ) :
    (∑' t : ℕ, if M < t then g t else 0) =
      ∑' n : ℕ, g (n + (M + 1)) := by
  let tailSet : Set ℕ := {t | M < t}
  rw [show (fun t : ℕ ↦ if M < t then g t else 0) =
      tailSet.indicator g by
    funext t
    by_cases ht : M < t <;> simp [tailSet, Set.indicator, ht]]
  rw [← _root_.tsum_subtype tailSet g]
  let e : ℕ ≃ tailSet :=
    { toFun := fun n ↦ ⟨n + (M + 1), by dsimp [tailSet]; omega⟩
      invFun := fun t ↦ t.1 - (M + 1)
      left_inv := fun n ↦ by simp
      right_inv := fun t ↦ by
        apply Subtype.ext
        dsimp
        have ht : M + 1 ≤ t.1 := by
          have := t.2
          change M < t.1 at this
          omega
        exact Nat.sub_add_cancel ht }
  simpa [e] using (e.tsum_eq (fun t ↦ g t.1)).symm

/-- A summable majorant has a vanishing cumulative layer-cake tail once its
first weighted term vanishes. -/
theorem cumulativeMajorantTail_tendsto_zero
    (g : ℕ → ℝ)
    (hfirst : Tendsto (fun y : ℕ ↦ (y + 1 : ℝ) * g y) atTop (nhds 0)) :
    Tendsto (cumulativeMajorantTail g) atTop (nhds 0) := by
  have hshift := tendsto_tsum_shift_zero g
  have hstrict :
      Tendsto (fun M : ℕ ↦ ∑' t : ℕ, if M < t then g t else 0)
        atTop (nhds 0) :=
    hshift.congr' (Filter.Eventually.of_forall fun M ↦
      (tsum_strictTail_eq_tsum_shift g M).symm)
  change Tendsto
    (fun y : ℕ ↦ (y + 1 : ℝ) * g y +
      ∑' t : ℕ, if y < t then g t else 0) atTop (nhds 0)
  convert hfirst.add hstrict using 1 <;> norm_num

/-- A convenient inverse-square cumulative majorant. -/
def inverseSquareMajorant (C : ℝ) (t : ℕ) : ℝ :=
  C / ((t + 1 : ℕ) : ℝ) ^ 2

theorem inverseSquareMajorant_nonneg {C : ℝ} (hC : 0 ≤ C) (t : ℕ) :
    0 ≤ inverseSquareMajorant C t := by
  unfold inverseSquareMajorant
  positivity

theorem summable_inverseSquareMajorant (C : ℝ) :
    Summable (inverseSquareMajorant C) := by
  have hbase : Summable (fun t : ℕ ↦
      1 / (((t + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff 1).2
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)))
  apply (hbase.mul_left C).congr
  intro t
  unfold inverseSquareMajorant
  push_cast
  ring

theorem cumulativeMajorantTail_inverseSquare_tendsto_zero (C : ℝ) :
    Tendsto (cumulativeMajorantTail (inverseSquareMajorant C))
      atTop (nhds 0) := by
  apply cumulativeMajorantTail_tendsto_zero
  have hdiv : Tendsto (fun y : ℕ ↦ C / (y + 1 : ℕ)) atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat C).comp (tendsto_add_atTop_nat 1)
  convert hdiv using 1
  ext y
  unfold inverseSquareMajorant
  push_cast
  have hy : (y : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- A cumulative prime-scale sieve bound with a vanishing layer-cake tail
implies the exact prime-exponent medium estimate used by the final
assembly. -/
theorem primeExponentMediumEstimate_of_cumulativeExceptional_bound
    (k : ℕ) (hk : 2 ≤ k) (g : ℕ → ℝ)
    (hg : ∀ t, 0 ≤ g t) (hsum : Summable g)
    (htail : Tendsto (cumulativeMajorantTail g) atTop (nhds 0))
    (hcount : CumulativeExceptionalPrimeScaleBound k g) :
    PrimeExponentMediumEstimate k := by
  intro ε hε
  have hevent : ∀ᶠ y : ℕ in atTop, cumulativeMajorantTail g y < ε :=
    (tendsto_order.1 htail).2 ε hε
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.mp hevent
  obtain ⟨Xcount, hcount⟩ := hcount
  let M := y₀
  let y := rationalPrime M - 1
  have hMy : M ≤ y := by
    have hp : M + 2 ≤ rationalPrime M := by
      simpa [rationalPrime] using Nat.add_two_le_nth_prime M
    dsimp [y]
    omega
  have hsmooth : ∀ᶠ x : ℕ in atTop, y ≤ smoothParameterY x :=
    tendsto_smoothParameterY_atTop.eventually (eventually_ge_atTop y)
  obtain ⟨Xsmooth, hXsmooth⟩ := eventually_atTop.mp hsmooth
  refine ⟨M, max (max Xcount Xsmooth) 2, ?_⟩
  intro x hx
  have hxcount : Xcount ≤ x := (le_max_left Xcount Xsmooth).trans
    ((le_max_left (max Xcount Xsmooth) 2).trans hx)
  have hxsmooth : Xsmooth ≤ x := (le_max_right Xcount Xsmooth).trans
    ((le_max_left (max Xcount Xsmooth) 2).trans hx)
  have hx2 : 2 ≤ x := (le_max_right (max Xcount Xsmooth) 2).trans hx
  have hyY : y ≤ smoothParameterY x := hXsmooth x hxsmooth
  have hxR : (0 : ℝ) < x := by exact_mod_cast (lt_of_lt_of_le (by omega) hx2)
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx2)
  have hscale : 0 ≤ (x : ℝ) / Real.log (x : ℝ) := by positivity
  have hnorm : 0 ≤ Real.log (x : ℝ) / (x : ℝ) := by positivity
  have hfiniteTail :
      (∑ t ∈ Finset.Ico (y + 1) (smoothParameterY x), g t) ≤
        ∑' t : ℕ, if y < t then g t else 0 := by
    have hs : Summable (fun t : ℕ ↦ if y < t then g t else 0) :=
      Summable.of_nonneg_of_le
        (fun t ↦ by by_cases h : y < t <;> simp [h, hg t])
        (fun t ↦ by by_cases h : y < t <;> simp [h, hg t]) hsum
    calc
      (∑ t ∈ Finset.Ico (y + 1) (smoothParameterY x), g t) =
          ∑ t ∈ Finset.Ico (y + 1) (smoothParameterY x),
            if y < t then g t else 0 := by
        apply Finset.sum_congr rfl
        intro t ht
        simp only [Finset.mem_Ico] at ht
        rw [if_pos (by omega)]
      _ ≤ ∑' t : ℕ, if y < t then g t else 0 :=
        hs.sum_le_tsum _ (fun t _ ↦ by
          by_cases h : y < t <;> simp [h, hg t])
  have hraw : mediumWeightedTailSum k y (smoothParameterY x) x ≤
      (x : ℝ) / Real.log (x : ℝ) * cumulativeMajorantTail g y := by
    calc
      mediumWeightedTailSum k y (smoothParameterY x) x ≤
          (y + 1 : ℝ) * (exceptionalPrimes k y x).card +
            ∑ t ∈ Finset.Ico (y + 1) (smoothParameterY x),
              ((exceptionalPrimes k t x).card : ℝ) :=
        mediumWeightedTailSum_le_cumulativeExceptional _ _ _ _
      _ ≤ (y + 1 : ℝ) *
            ((x : ℝ) / Real.log (x : ℝ) * g y) +
          ∑ t ∈ Finset.Ico (y + 1) (smoothParameterY x),
            ((x : ℝ) / Real.log (x : ℝ) * g t) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left
            (hcount x hxcount y hyY) (by positivity)
        · apply Finset.sum_le_sum
          intro t ht
          exact hcount x hxcount t (by
            simp only [Finset.mem_Ico] at ht
            omega)
      _ = (x : ℝ) / Real.log (x : ℝ) *
          ((y + 1 : ℝ) * g y +
            ∑ t ∈ Finset.Ico (y + 1) (smoothParameterY x), g t) := by
        rw [mul_add, Finset.mul_sum]
        ring
      _ ≤ (x : ℝ) / Real.log (x : ℝ) * cumulativeMajorantTail g y := by
        apply mul_le_mul_of_nonneg_left _ hscale
        unfold cumulativeMajorantTail
        linarith
  unfold normalizedMediumWeightedTail
  calc
    Real.log (x : ℝ) / (x : ℝ) *
        mediumWeightedTailSum k (rationalPrime M - 1)
          (smoothParameterY x) x =
        Real.log (x : ℝ) / (x : ℝ) *
          mediumWeightedTailSum k y (smoothParameterY x) x := by rfl
    _ ≤ Real.log (x : ℝ) / (x : ℝ) *
          ((x : ℝ) / Real.log (x : ℝ) * cumulativeMajorantTail g y) :=
      mul_le_mul_of_nonneg_left hraw hnorm
    _ = cumulativeMajorantTail g y := by
      field_simp
    _ ≤ ε := (hy₀ y hMy).le

/-- Ready-to-use specialization: an inverse-square cumulative exceptional
prime bound is sufficient for the exact medium estimate. -/
theorem primeExponentMediumEstimate_of_inverseSquare_cumulative_bound
    (k : ℕ) (hk : 2 ≤ k) (C : ℝ) (hC : 0 ≤ C)
    (hcount : CumulativeExceptionalPrimeScaleBound k
      (inverseSquareMajorant C)) :
    PrimeExponentMediumEstimate k :=
  primeExponentMediumEstimate_of_cumulativeExceptional_bound k hk
    (inverseSquareMajorant C)
    (inverseSquareMajorant_nonneg hC)
    (summable_inverseSquareMajorant C)
    (cumulativeMajorantTail_inverseSquare_tendsto_zero C)
    hcount

end

end Erdos980.ElliottTail
