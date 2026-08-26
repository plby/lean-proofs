import ErdosProblems.Erdos394.FactorialTail
import ErdosProblems.Erdos394.PrimeEuler

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Verifying the Brun factorial-tail hypothesis on moving prime intervals
-/

open Nat Finset

namespace Erdos394

/-- On every sufficiently late geometric prime interval, the explicit even
Brun order makes the factorial tail no larger than the local Euler density. -/
theorem exists_geometric_primeInterval_brun_tail :
    ∃ Jmin : ℕ, 2 ≤ Jmin ∧ ∀ Jz Jy : ℕ, Jmin ≤ Jz → Jz ≤ Jy →
      (∑ p ∈ primeInterval (16 ^ Jz) (16 ^ Jy), (1 / (p : ℝ))) ^
            (geometricBrunOrder Jy + 1) /
          ((geometricBrunOrder Jy + 1).factorial : ℝ) ≤
        localEulerProduct (primeInterval (16 ^ Jz) (16 ^ Jy))
          (fun p ↦ 1 / (p : ℝ)) := by
  obtain ⟨Jr, hJr, hrecip⟩ :=
    exists_geometric_interval_primeReciprocal_bounds
  obtain ⟨Je, hJe, heuler⟩ := exists_geometric_interval_euler_bounds
  let Jmin := max Jr Je
  refine ⟨Jmin, (hJr.trans (le_max_left Jr Je)), ?_⟩
  intro Jz Jy hmin hzY
  have hrmin : Jr ≤ Jz := (le_max_left Jr Je).trans (by simpa [Jmin] using hmin)
  have hemin : Je ≤ Jz := (le_max_right Jr Je).trans (by simpa [Jmin] using hmin)
  have hpow : 16 ^ Jz ≤ 16 ^ Jy := Nat.pow_le_pow_right (by omega) hzY
  have hsum := sum_primeInterval_one_div hpow
  obtain ⟨_, hΛupper⟩ := hrecip Jz Jy hrmin hzY
  obtain ⟨_, hVlower⟩ := heuler Jz Jy hemin hzY
  have hJy : 1 ≤ Jy := by omega
  have hΛ0 : 0 ≤ ∑ p ∈ primeInterval (16 ^ Jz) (16 ^ Jy),
      (1 / (p : ℝ)) := by
    apply Finset.sum_nonneg
    intro p hp
    positivity
  apply geometricBrun_tail_le_of_bounds hJy hΛ0
  · rwa [hsum]
  · exact hVlower

end Erdos394
