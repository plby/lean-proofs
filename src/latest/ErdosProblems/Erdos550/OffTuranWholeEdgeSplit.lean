import Mathlib
import ErdosProblems.Erdos550.OffTuranParams
import ErdosProblems.Erdos550.WholeMatchingAllocation

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Ratio-chosen allocation of whole matching edges

The two head demands determine a feasible Bernoulli parameter.  The existing
second-moment theorem then assigns every matching edge wholly to one head and
simultaneously meets both requested weighted lower bounds.
-/

open Finset

namespace Erdos550

/-- If the two error-inflated demands occupy strictly less than the two total
supplies in ratio, a complete-edge split meeting both demands exists. -/
theorem exists_whole_matching_split_of_ratio_room
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (wX wY : κ → ℝ) (M t needX needY : ℝ)
    (hX0 : ∀ i, 0 ≤ wX i) (hXM : ∀ i, wX i ≤ M)
    (hY0 : ∀ i, 0 ≤ wY i) (hYM : ∀ i, wY i ≤ M)
    (ht : 0 < t)
    (hroom : (Fintype.card κ : ℝ) * M ^ 2 / 2 < t ^ 2)
    (hDX : 0 < ∑ i, wX i) (hDY : 0 < ∑ i, wY i)
    (hneedX0 : 0 ≤ needX + t) (hneedY0 : 0 ≤ needY + t)
    (hratio :
      (needX + t) / (∑ i, wX i) +
          (needY + t) / (∑ i, wY i) < 1) :
    ∃ K : Finset κ,
      needX ≤ ∑ i ∈ K, wX i ∧
      needY ≤ ∑ i ∈ Finset.univ \ K, wY i := by
  obtain ⟨lam, hlo, hhi, hlam0, hlam1⟩ :=
    lambda_feasible
      (∑ i, wX i) (∑ i, wY i)
      (needX + t) (needY + t) 0
      hDX hDY hneedX0 hneedY0 (by positivity) (by simpa using! hratio)
  let p : NNReal := ⟨lam, hlam0⟩
  have hp : p ≤ 1 := by
    change lam ≤ (1 : ℝ)
    exact hlam1
  have hcaps :=
    lambda_caps
      (∑ i, wX i) (∑ i, wY i)
      (needX + t) (needY + t) 0 lam
      hDX hDY hlo hhi
  apply exists_whole_matching_split_lower
    p hp wX wY M t needX needY
      hX0 hXM hY0 hYM ht hroom
  · simpa [p] using! hcaps.1
  · simpa [p] using! hcaps.2

end Erdos550
