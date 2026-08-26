import ErdosProblems.Erdos796.CofactorFunctional
import Mathlib.Analysis.PSeries

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A summable `j^(5/6)` cofactor majorant
-/

namespace Erdos796

/-- A convenient coarse form of the explicit multiplicative-Sidon excess
bound.  The sharper two-term bound is used later for `Gamma < 13`; this one
already proves finiteness. -/
noncomputable def sidonMajorant (j : ℕ) : ℝ :=
  3 * (j : ℝ) ^ (5 / 6 : ℝ)

theorem sidonMajorant_nonneg (j : ℕ) : 0 ≤ sidonMajorant j := by
  rw [sidonMajorant]
  positivity

theorem weightedMajorant_sidon_nonneg (k : ℕ) :
    0 ≤ weightedMajorant sidonMajorant k := by
  rw [weightedMajorant]
  exact mul_nonneg (cofactorWeight_nonneg _) (sidonMajorant_nonneg _)

/-- The cofactor weight turns `j^(5/6)` into a convergent `j^(-7/6)`
majorant. -/
theorem weightedMajorant_sidon_le_pseries (k : ℕ) :
    weightedMajorant sidonMajorant k ≤
      3 * (1 / |(k : ℝ) + 1| ^ (7 / 6 : ℝ)) := by
  let x : ℝ := (k : ℝ) + 1
  have hx : 0 < x := by positivity
  have hx1 : 0 < x + 1 := by positivity
  have hden : 0 < x * (x + 1) := mul_pos hx hx1
  have hpow : 0 < x ^ (7 / 6 : ℝ) := Real.rpow_pos_of_pos hx _
  have hpowadd :
      x ^ (5 / 6 : ℝ) * x ^ (7 / 6 : ℝ) = x ^ (2 : ℝ) := by
    rw [← Real.rpow_add hx]
    norm_num
  have hsquare : x ^ (2 : ℝ) = x * x := by
    calc
      x ^ (2 : ℝ) = x ^ (2 : ℕ) := Real.rpow_natCast x 2
      _ = x * x := pow_two x
  change
    (1 / (((k + 1 : ℕ) : ℝ) * ((k + 1 + 1 : ℕ) : ℝ))) *
        (3 * (((k + 1 : ℕ) : ℝ) ^ (5 / 6 : ℝ))) ≤ _
  push_cast
  rw [abs_of_pos hx]
  change (1 / (x * (x + 1))) * (3 * x ^ (5 / 6 : ℝ)) ≤
    3 * (1 / x ^ (7 / 6 : ℝ))
  rw [one_div, one_div]
  rw [show (x * (x + 1))⁻¹ * (3 * x ^ (5 / 6 : ℝ)) =
      (3 * x ^ (5 / 6 : ℝ)) / (x * (x + 1)) by ring]
  change (3 * x ^ (5 / 6 : ℝ)) / (x * (x + 1)) ≤
    3 / x ^ (7 / 6 : ℝ)
  rw [div_le_div_iff₀ hden hpow]
  rw [mul_assoc, hpowadd, hsquare]
  nlinarith

theorem summable_weightedMajorant_sidon :
    Summable (weightedMajorant sidonMajorant) := by
  have hp : Summable
      (fun k : ℕ => 1 / |(k : ℝ) + 1| ^ (7 / 6 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow 1 (7 / 6 : ℝ)).2 (by norm_num)
  have h3 : Summable
      (fun k : ℕ => 3 * (1 / |(k : ℝ) + 1| ^ (7 / 6 : ℝ))) :=
    hp.mul_left 3
  exact Summable.of_nonneg_of_le
    weightedMajorant_sidon_nonneg weightedMajorant_sidon_le_pseries h3

/-- Any uniform `3 j^(5/6)` excess estimate suffices to make the variational
score set bounded above. -/
theorem gammaScores_bddAbove_of_sidonMajorant
    (hBound : ∀ (U : ℕ → Finset ℕ), Compatible U →
      ∀ j : ℕ, excess U j ≤ sidonMajorant j) :
    BddAbove gammaScores :=
  gammaScores_bddAbove_of_uniform_majorant hBound
    summable_weightedMajorant_sidon

end Erdos796
