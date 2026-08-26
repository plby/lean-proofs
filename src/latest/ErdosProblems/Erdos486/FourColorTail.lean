import ErdosProblems.Erdos486.FiniteAveraging

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A finite tail bound for four-colourings

This file derives the biased-colouring tail estimate used when the number of
coordinates is `6 * r`.  The argument is only finite counting: apply the
finite Markov inequality to the weight `2 ^ blackCount`, then use its exact
uniform sum from `FiniteAveraging`.
-/

open scoped BigOperators

namespace Erdos486

noncomputable section

variable {ι : Type*} [Fintype ι]

local instance : DecidableEq ι := Classical.decEq ι

/-- The four-colourings having more than `2 * r` black coordinates. -/
def fourColorTail (r : ℕ) : Finset (FourColoring ι) :=
  Finset.univ.filter fun c ↦ 2 * r < blackCount c

/-- The exact cross-multiplied Markov bound before imposing
`Fintype.card ι = 6 * r`. -/
theorem fourColorTail_card_mul_two_pow_le (r : ℕ) :
    ((fourColorTail (ι := ι) r).card : ℚ) * (2 : ℚ) ^ (2 * r) ≤
      (5 : ℚ) ^ Fintype.card ι := by
  let threshold : ℚ := (2 : ℚ) ^ (2 * r)
  let thresholdSet : Finset (FourColoring ι) :=
    Finset.univ.filter fun c ↦ threshold ≤ (2 : ℚ) ^ blackCount c
  have hsubset : fourColorTail (ι := ι) r ⊆ thresholdSet := by
    intro c hc
    have hcTail : 2 * r < blackCount c := (Finset.mem_filter.mp hc).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ c, ?_⟩
    exact pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hcTail.le
  have hcard :
      ((fourColorTail (ι := ι) r).card : ℚ) ≤
        (thresholdSet.card : ℚ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hmarkov :=
    fintype_markov (𝕜 := ℚ)
      (fun c : FourColoring ι ↦ (2 : ℚ) ^ blackCount c)
      (fun _ ↦ by positivity) threshold
  calc
    ((fourColorTail (ι := ι) r).card : ℚ) * (2 : ℚ) ^ (2 * r) =
        ((fourColorTail (ι := ι) r).card : ℚ) * threshold := by
      rfl
    _ ≤ (thresholdSet.card : ℚ) * threshold := by
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ ∑ c : FourColoring ι, (2 : ℚ) ^ blackCount c := by
      exact hmarkov
    _ = (5 : ℚ) ^ Fintype.card ι :=
      sum_two_pow_blackCount

/-- Natural-number form of the exact cross-multiplied tail bound when there
are `6 * r` coordinates. -/
theorem fourColorTail_card_mul_two_pow_le_of_card_eq (r : ℕ)
    (hι : Fintype.card ι = 6 * r) :
    (fourColorTail (ι := ι) r).card * 2 ^ (2 * r) ≤ 5 ^ (6 * r) := by
  have h := fourColorTail_card_mul_two_pow_le (ι := ι) r
  rw [hι] at h
  exact_mod_cast h

/-- Rational proportion form of the biased-colouring tail estimate. -/
theorem fourColorTail_ratio_le_rat (r : ℕ)
    (hι : Fintype.card ι = 6 * r) :
    ((fourColorTail (ι := ι) r).card : ℚ) /
        Fintype.card (FourColoring ι) ≤
      ((125 : ℚ) / 128) ^ (2 * r) := by
  have hmarkov := fourColorTail_card_mul_two_pow_le (ι := ι) r
  rw [hι] at hmarkov
  have htwo : 0 < (2 : ℚ) ^ (2 * r) := by positivity
  have htail :
      ((fourColorTail (ι := ι) r).card : ℚ) ≤
        (5 : ℚ) ^ (6 * r) / (2 : ℚ) ^ (2 * r) :=
    (le_div_iff₀ htwo).2 hmarkov
  have hcolorCard :
      (Fintype.card (FourColoring ι) : ℚ) = (4 : ℚ) ^ (6 * r) := by
    rw [card_fourColoring, hι, Nat.cast_pow]
    norm_num
  have hfour : (4 : ℚ) ^ (6 * r) = (64 : ℚ) ^ (2 * r) := by
    rw [show 6 * r = 3 * (2 * r) by omega, pow_mul]
    norm_num
  have hfive : (5 : ℚ) ^ (6 * r) = (125 : ℚ) ^ (2 * r) := by
    rw [show 6 * r = 3 * (2 * r) by omega, pow_mul]
    norm_num
  have hdenominator :
      (2 : ℚ) ^ (2 * r) * (4 : ℚ) ^ (6 * r) =
        (128 : ℚ) ^ (2 * r) := by
    rw [hfour, ← mul_pow]
    norm_num
  rw [hcolorCard]
  calc
    ((fourColorTail (ι := ι) r).card : ℚ) / (4 : ℚ) ^ (6 * r) ≤
        ((5 : ℚ) ^ (6 * r) / (2 : ℚ) ^ (2 * r)) /
          (4 : ℚ) ^ (6 * r) := by
      exact div_le_div_of_nonneg_right htail (by positivity)
    _ = ((125 : ℚ) / 128) ^ (2 * r) := by
      rw [div_div, hfive, hdenominator, div_pow]

end

end Erdos486
