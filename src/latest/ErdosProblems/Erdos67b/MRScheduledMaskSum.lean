import ErdosProblems.Erdos67b.MRMaskedDistance
import ErdosProblems.Erdos67b.MRPrimeBlockMass

/-!
# Uniform exponential-distance sum for the actual scheduled masks

The initial reciprocal-mass budget and schedule separation bound the
entire family of masks independently of its size. A mean-value theorem
for the corresponding cofactor polynomials remains a separate input to
be proved.
-/

open scoped BigOperators
open Finset

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrScheduledPrimeBlocks_subset_primesUpTo
    {eta p₁ q₁ : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p₁)
    (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {X J : ℕ} (hX : 0 < X) (hlogX : 1 ≤ Real.log (X : ℝ))
    (hJX : mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)))
    {j : ℕ} (hj : j ∈ Finset.Icc 1 J) :
    primesInBlock (mrScheduledPrimeInterval p₁ q₁ j) ⊆ primesUpTo X := by
  intro p hpB
  have hprime := (mem_primesInBlock.mp hpB).1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hqj := mrLogScheduleUpper_mono_positive heta hp hq hpq hlogq hbudget
    (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
  have hs : Real.sqrt (Real.log (X : ℝ)) ≤ Real.log (X : ℝ) := by
    have hsq := Real.sq_sqrt (show 0 ≤ Real.log (X : ℝ) by linarith)
    have hs0 := Real.sqrt_nonneg (Real.log (X : ℝ))
    nlinarith
  have hlogp := (mem_primesInBlock_mrLogPrimeInterval_bounds hpB).2
  have hlog : Real.log (p : ℝ) ≤ Real.log (X : ℝ) :=
    hlogp.trans (hqj.trans (hJX.trans hs))
  have hpX : (p : ℝ) ≤ X := by
    have hh := Real.exp_le_exp.mpr hlog
    simpa only [Real.exp_log hp0, Real.exp_log hX0] using hh
  exact mem_primesUpTo.mpr ⟨hprime, by exact_mod_cast hpX⟩

theorem mrScheduled_sum_exp_neg_mask_distance_le
    {eta p₁ q₁ : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p₁)
    (hq : 1 ≤ q₁) (hpq : 2 * p₁ ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    (hmertens : Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q₁ - Real.log p₁)
    {X J : ℕ} (hX : 0 < X) (hlogX : 1 ≤ Real.log (X : ℝ))
    (hJX : mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)))
    {f g : ℕ → ℂ}
    (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) :
    (∑ S ∈ (Finset.Icc 1 J).powerset, Real.exp (-pretentiousDistSq
      (primeBandCoefficient f (fun p ↦ p ∉ S.biUnion
        (fun j ↦ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)))) g X)) ≤
      Real.exp (mrMaskProductSeries - pretentiousDistSq f g X / 8) := by
  let B : ℕ → Finset ℕ := fun j ↦ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)
  have hpq' : p₁ ≤ q₁ := by linarith
  have hB : ∀ j ∈ Finset.Icc 1 J, B j ⊆ primesUpTo X := by
    intro j hj
    exact mrScheduledPrimeBlocks_subset_primesUpTo heta hp hq hpq' hlogq hbudget hX hlogX hJX hj
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 J) : Set ℕ) B := by
    intro i hi j hj hij
    exact mrScheduledPrimeInterval_disjoint heta hp hq hpq' hlogq hbudget
      (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hj).1 hij
  have hmass : ∀ j ∈ Finset.Icc 1 J, (3 / 2 : ℝ) * Real.log (j : ℝ) ≤
      (1 : ℝ) * (1 - 2 * (1 / 8)) * (∑ p ∈ B j, 1 / (p : ℝ)) := by
    intro j hj
    have hh := mrScheduledPrimeInterval_reciprocalMass_ge_two_log hp hq hpq hmertens
      (Finset.mem_Icc.mp hj).1
    change 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ) at hh
    nlinarith
  have hh := mrSum_exp_neg_mask_distance_le_uniform (Finset.Icc 1 J) B
    (fun j hj ↦ (Finset.mem_Icc.mp hj).1) hB hdisj hf hg
    (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 / 8 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1) hmass
  simpa only [neg_one_mul, one_mul, one_div, inv_mul_eq_div] using hh

/-- The additional mass condition is compatible with the original initial
schedule, any upper-endpoint threshold, and any positive ratio budget. -/
theorem exists_mrLogSchedule_initial_with_mask_mass
    {eta epsilon : ℝ} (heta : 0 < eta) (hepsilon : 0 < epsilon) (Q : ℝ) :
    ∃ p q : ℝ, Q ≤ q ∧ Real.exp 1 ≤ q ∧ 2 ≤ p ∧ 2 * p ≤ q ∧ p / q ≤ epsilon ∧
      4096 * Real.log q ≤ eta * p ∧
      Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q - Real.log p := by
  let K := Real.log 2 + 2 * PrimeEstimates.mertensBound
  let delta := min epsilon (min (1 / 2) (Real.exp (-K)))
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  obtain ⟨p, q, hQ, hq, hp, hpq, hratio, hbudget⟩ := exists_mrLogSchedule_initial heta hdelta Q
  have hq0 : 0 < q := (Real.exp_pos 1).trans_le hq
  have hp0 : 0 < p := by linarith
  have hhalf : p / q ≤ 1 / 2 := hratio.trans ((min_le_right _ _).trans (min_le_left _ _))
  have htwop : 2 * p ≤ q := by
    have hh := (div_le_iff₀ hq0).mp hhalf
    linarith
  have heps : p / q ≤ epsilon := hratio.trans (min_le_left _ _)
  have he : p / q ≤ Real.exp (-K) := hratio.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hlog := Real.log_le_log (div_pos hp0 hq0) he
  rw [Real.log_div hp0.ne' hq0.ne', Real.log_exp] at hlog
  refine ⟨p, q, hQ, hq, hp, htwop, heps, hbudget, ?_⟩
  change K ≤ Real.log q - Real.log p
  linarith

end

end Erdos67b
