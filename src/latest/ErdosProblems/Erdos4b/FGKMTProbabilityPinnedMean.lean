/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTWeightProbability

/-! # The pinned prime mean after finite normalization -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem CommonWeightEstimates.pinned_probability_error {x m B Q : ℕ} {y e : ℝ}
    {h : Fin (m + 1) → ℕ} (H : CommonWeightEstimates x m B y h e)
    (hx : 0 < x) (hy : 0 < y) (hL : 0 < Real.log (x : ℝ))
    (herror : 1 / Real.log (Real.log (x : ℝ)) ^ 10 ≤ (1 / 2 : ℝ))
    (hQ : Q.Prime) (hxQ : x < Q) (hQy : (Q : ℝ) ≤ y) (j : Fin (m + 1)) :
    let W := dimensionPreSieveModulus (m + 1) B
    let R := dimensionSieveRadius x
    let u := commonWeightGain m B W R x
    |(∑ p ∈ commonPinnedPrimeSet (x / 2) x,
        commonPrimeSieveProbability (m + 1) W (B * W) R y h p
          ((Q : ℤ) - (h j : ℤ) * p)) - (u / (m + 1 : ℕ)) * x / (2 * y)| ≤
      (4 / Real.log (Real.log (x : ℝ)) ^ 10) * ((u / (m + 1 : ℕ)) * x / (2 * y)) := by
  let W := dimensionPreSieveModulus (m + 1) B
  let R := dimensionSieveRadius x
  let tau := commonWeightTau (m + 1) W (B * W) R x h
  let u := commonWeightGain m B W R x
  let d := 1 / Real.log (Real.log (x : ℝ)) ^ 10
  let T := tau * y / Real.log (x : ℝ) ^ (m + 1)
  let U := tau * (u / (m + 1 : ℕ)) * x / (2 * Real.log (x : ℝ) ^ (m + 1))
  let P := commonPinnedPrimeSet (x / 2) x
  let a := fun p => commonPrimeSieveWeight (m + 1) W (B * W) R y h p
    ((Q : ℤ) - (h j : ℤ) * p)
  let M := fun p => commonPrimeSieveTotalMass (m + 1) W (B * W) R y h p
  obtain ⟨htau, hu, _htlow, _hulow, _huup, hnonneg, _hsupp, _hpoint, htotal, hpin⟩ := H
  change 0 < tau at htau
  change 0 < u at hu
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hT : 0 < T := by dsimp only [T]; positivity
  have hU : 0 < U := by dsimp only [U]; positivity
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hM (p : ℕ) (hp : p ∈ P) : |M p - T| ≤ d * T := by
    have ht := htotal p hp
    rw [commonPrimeSieveWeight_tsum_eq_totalMass] at ht
    exact (div_le_iff₀ hT).mp ht
  have hA : |(∑ p ∈ P, a p) - U| ≤ d * U := by
    have hp := hpin Q hQ hxQ hQy j
    exact (div_le_iff₀ hU).mp hp
  have hb := normalized_finite_sum_error P a M (fun p _hp => hnonneg p _)
    hT hU hd herror hM hA
  have hid : U / T = (u / (m + 1 : ℕ)) * x / (2 * y) := by
    dsimp only [U, T]
    field_simp
  rw [hid] at hb
  simpa only [commonPrimeSieveProbability, a, M, P, d, mul_one_div] using hb

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.CommonWeightEstimates.pinned_probability_error
