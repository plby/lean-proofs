import ErdosProblems.Erdos67b.MRPrimeBlockMass
import ErdosProblems.Erdos67b.MRCofactorPowerCutoff

/-!
# Source scheduled blocks at a lower cofactor scale

The source upper endpoint `sqrt (log X)` is compared with `log Y / 16`
and the fixed-power cutoff at `Y`. Rounded prime endpoints, reciprocal
mass, disjointness, and exclusion of primes below 23 are retained.
-/

open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mrCofactor_sqrt_log_le_sixteenth {X Y : ℕ}
    (hX : 1024 ≤ Real.log (X : ℝ))
    (hXY : Real.log (X : ℝ) ≤ 2 * Real.log (Y : ℝ)) :
    Real.sqrt (Real.log (X : ℝ)) ≤ Real.log (Y : ℝ) / 16 := by
  have hL : 0 ≤ Real.log (X : ℝ) := by linarith
  have hs := Real.sqrt_nonneg (Real.log (X : ℝ))
  have hsq := Real.sq_sqrt hL
  have hs32 : 32 ≤ Real.sqrt (Real.log (X : ℝ)) := by nlinarith
  have hprod := mul_nonneg hs (sub_nonneg.mpr hs32)
  nlinarith

theorem mrCofactor_sqrt_log_le_power {delta : ℝ} (hdelta : 0 < delta)
    {X Y : ℕ} (hX : 0 ≤ Real.log (X : ℝ))
    (hXY : Real.log (X : ℝ) ≤ 2 * Real.log (Y : ℝ))
    (hlarge : 4 ≤ delta ^ 2 * Real.log (X : ℝ)) :
    Real.sqrt (Real.log (X : ℝ)) ≤ delta * Real.log (Y : ℝ) := by
  have hs := Real.sqrt_nonneg (Real.log (X : ℝ))
  have hsq := Real.sq_sqrt hX
  have hds : 0 ≤ delta * Real.sqrt (Real.log (X : ℝ)) := mul_nonneg hdelta.le hs
  have hdsq : (delta * Real.sqrt (Real.log (X : ℝ))) ^ 2 =
      delta ^ 2 * Real.log (X : ℝ) := by rw [mul_pow, hsq]
  have htwo : 2 ≤ delta * Real.sqrt (Real.log (X : ℝ)) := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right htwo hs
  have hscale := mul_le_mul_of_nonneg_left hXY hdelta.le
  nlinarith [show delta * Real.sqrt (Real.log (X : ℝ)) *
      Real.sqrt (Real.log (X : ℝ)) = delta * Real.log (X : ℝ) by
    rw [mul_assoc, ← sq, hsq]]

theorem mrScheduledPrime_log_le_sqrt
    {eta p₁ q₁ : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p₁)
    (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {J X : ℕ}
    (hupper : mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)))
    {j p : ℕ} (hj : j ∈ Finset.Icc 1 J)
    (hprime : p ∈ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) :
    Real.log (p : ℝ) ≤ Real.sqrt (Real.log (X : ℝ)) := by
  have hi := Finset.mem_Icc.mp hj
  exact (mem_primesInBlock_mrLogPrimeInterval_bounds hprime).2.trans
    ((mrLogScheduleUpper_mono_positive heta hp hq hpq hlogq hbudget hi.1 hi.2).trans hupper)

theorem mrScheduledPrime_ge_twentyThree
    {eta p₁ q₁ : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p₁)
    (hq : 1 ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {j p : ℕ} (hj : 1 ≤ j)
    (hprime : p ∈ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) :
    23 ≤ p := by
  have he := mul_le_mul_of_nonneg_right heta (show 0 ≤ p₁ by linarith)
  have hbase : 22 ≤ p₁ := by nlinarith
  have hlower := (mem_primesInBlock_mrLogPrimeInterval_bounds hprime).1
  have hschedule := mrLogScheduleLower_ge (show 0 ≤ p₁ by linarith) hq hj
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_primesInBlock.mp hprime).1.pos
  have hexp := Real.add_one_le_exp (Real.log (p : ℝ))
  rw [Real.exp_log hp0] at hexp
  have hreal : (23 : ℝ) ≤ p := by linarith
  exact_mod_cast hreal

/-- All block hypotheses of the cofactor mean theorem follow from the
source schedule and two explicit lower-scale comparisons. -/
theorem mrScheduledBlocks_cofactor_conditions
    {eta p₁ q₁ delta : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p₁)
    (hq : 1 ≤ q₁) (hpq : 2 * p₁ ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    (hmertens : Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q₁ - Real.log p₁)
    (hdelta : 0 < delta) {J X Y : ℕ} (hY : 2 ≤ Y)
    (hX : 1024 ≤ Real.log (X : ℝ))
    (hXY : Real.log (X : ℝ) ≤ 2 * Real.log (Y : ℝ))
    (hlarge : 4 ≤ delta ^ 2 * Real.log (X : ℝ))
    (hupper : mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ))) :
    (∀ j ∈ Finset.Icc 1 J,
      primesInBlock (mrScheduledPrimeInterval p₁ q₁ j) ⊆ primesUpTo Y) ∧
    Set.PairwiseDisjoint (↑(Finset.Icc 1 J) : Set ℕ)
      (fun j ↦ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) ∧
    (∀ j ∈ Finset.Icc 1 J, ∀ p ∈ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j),
      Real.log (p : ℝ) ≤ Real.log (Y : ℝ) / 16) ∧
    (∀ j ∈ Finset.Icc 1 J, 2 * Real.log (j : ℝ) ≤
      ∑ p ∈ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j), 1 / (p : ℝ)) ∧
    (∀ j ∈ Finset.Icc 1 J, ∀ p ∈ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j),
      p ≤ mrCofactorPowerCutoff delta Y) ∧
    (∀ j ∈ Finset.Icc 1 J, ∀ p ∈ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j),
      23 ≤ p) := by
  have hpq' : p₁ ≤ q₁ := by linarith
  have hlogs := mrCofactor_sqrt_log_le_sixteenth hX hXY
  have hlogp := mrCofactor_sqrt_log_le_power hdelta (by linarith : 0 ≤ Real.log (X : ℝ)) hXY hlarge
  have hb : ∀ {j p : ℕ}, j ∈ Finset.Icc 1 J →
      p ∈ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j) →
      Real.log (p : ℝ) ≤ Real.sqrt (Real.log (X : ℝ)) :=
    fun hj hpB ↦ mrScheduledPrime_log_le_sqrt heta hp hq hpq' hlogq hbudget hupper hj hpB
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hYlog : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj p hpB
    have hpprime := (mem_primesInBlock.mp hpB).1
    apply mem_primesUpTo.mpr
    refine ⟨hpprime, ?_⟩
    have hh : Real.log (p : ℝ) ≤ Real.log (Y : ℝ) := (hb hj hpB).trans (by linarith)
    have hreal := Real.exp_le_exp.mpr hh
    rw [Real.exp_log (show (0 : ℝ) < p by exact_mod_cast hpprime.pos), Real.exp_log hYpos] at hreal
    exact_mod_cast hreal
  · intro i hi j hj hij
    exact mrScheduledPrimeInterval_disjoint heta hp hq hpq' hlogq hbudget
      (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hj).1 hij
  · intro j hj p hpB
    exact (hb hj hpB).trans hlogs
  · intro j hj
    exact mrScheduledPrimeInterval_reciprocalMass_ge_two_log hp hq hpq hmertens
      (Finset.mem_Icc.mp hj).1
  · intro j hj p hpB
    have hpprime := (mem_primesInBlock.mp hpB).1
    have hh := Real.exp_le_exp.mpr ((hb hj hpB).trans hlogp)
    rw [Real.exp_log (show (0 : ℝ) < p by exact_mod_cast hpprime.pos)] at hh
    exact_mod_cast hh.trans (mrCofactorPowerCutoff_exp_le delta Y)
  · intro j hj p hpB
    exact mrScheduledPrime_ge_twentyThree heta hp hq hlogq hbudget (Finset.mem_Icc.mp hj).1 hpB

end

end Erdos67b
