/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos446

def intervalLcm (n : ℕ) : ℕ :=
  (Finset.Ioo n (2 * n)).lcm id

def divisorCount (n m : ℕ) : ℕ :=
  ((Finset.Ioo n (2 * n)).filter fun d ↦ d ∣ m).card

noncomputable def delta (n : ℕ) : ℝ :=
  (((((Finset.range (intervalLcm n)).filter
    (fun m ↦ 0 < divisorCount n m)).card : ℕ) : ℝ) /
      (intervalLcm n : ℝ))

noncomputable def alpha446 : ℝ :=
  1 - (1 + Real.log (Real.log 2)) / Real.log 2

noncomputable def growthDenominator446 (n : ℕ) : ℝ :=
  Real.log (n : ℝ) ^ alpha446 *
    Real.log (Real.log (n : ℝ)) ^ (3 / 2 : ℝ)

noncomputable def growth446 (n : ℕ) : ℝ :=
  (growthDenominator446 n)⁻¹

noncomputable def deltaR (r n : ℕ) : ℝ :=
  (((((Finset.range (intervalLcm n)).filter
    (fun m ↦ divisorCount n m = r)).card : ℕ) : ℝ) /
      (intervalLcm n : ℝ))

theorem erdos_446 :
    (delta =Θ[atTop] growth446) ∧
      (∀ r : ℕ, 1 ≤ r → delta =O[atTop] (deltaR r)) ∧
        ¬ (deltaR 1 =o[atTop] delta) := by
  sorry

end Erdos446
