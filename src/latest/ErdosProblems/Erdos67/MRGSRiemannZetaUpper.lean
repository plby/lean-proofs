import ErdosProblems.Erdos67.EulerLower
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# An explicit upper bound for zeta immediately to the right of one

The post-contour scalar estimate in the GS argument uses only the elementary
integral-test bound `ζ(1 + σ) ≤ 1 + 1 / σ`.  This file records that bound
with the exact real-axis normalization used by the existing Euler modules.
-/

open scoped BigOperators
open Set MeasureTheory

namespace Erdos67

noncomputable section

/-- The positive real Dirichlet series at exponent `u > 1` is at most its
first term plus the corresponding improper integral. -/
theorem realZetaSum_le_one_add_inv_sub_one {u : ℝ} (hu : 1 < u) :
    (∑' n : ℕ, 1 / (n : ℝ) ^ u) ≤ 1 + (u - 1)⁻¹ := by
  let f : ℝ → ℝ := fun x ↦ x ^ (-u)
  have hanti : AntitoneOn f (Set.Ici (1 : ℝ)) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
      (show -u ≤ 0 by linarith)).mono
    intro x hx
    exact zero_lt_one.trans_le (by simpa only [Set.mem_Ici] using hx)
  have hint : IntegrableOn f (Set.Ioi (1 : ℝ)) := by
    exact integrableOn_Ioi_rpow_of_lt (show -u < -1 by linarith) zero_lt_one
  have hnonneg : ∀ x ∈ Set.Ioi (1 : ℝ), 0 ≤ f x := by
    intro x hx
    exact Real.rpow_nonneg (zero_lt_one.trans hx).le _
  have htail := AntitoneOn.tsum_comp_add_le_integral
    (f := f) 1
      (by simpa only [Nat.cast_one] using hanti)
      (by simpa only [Nat.cast_one] using hint)
      (by simpa only [Nat.cast_one] using hnonneg)
  have hintegral :
      (∫ x : ℝ in Set.Ioi (1 : ℝ), f x) = (u - 1)⁻¹ := by
    dsimp only [f]
    rw [integral_Ioi_rpow_of_lt (show -u < -1 by linarith) zero_lt_one,
      Real.one_rpow]
    have hleft : -u + 1 ≠ 0 := by linarith
    have hright : u - 1 ≠ 0 := by linarith
    field_simp [hleft, hright]
    ring_nf
  have hintegral' :
      (∫ x : ℝ in Set.Ioi (((1 : ℕ) : ℝ)), f x) = (u - 1)⁻¹ := by
    simpa only [Nat.cast_one] using hintegral
  rw [hintegral'] at htail
  have hsum : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ u) := by
    simpa only [one_div] using Real.summable_nat_rpow_inv.mpr hu
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have hfirst : ∑ n ∈ Finset.range 2, 1 / (n : ℝ) ^ u = (1 : ℝ) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    norm_num [Real.zero_rpow (by linarith : u ≠ 0), Real.one_rpow]
  have htailEq :
      (∑' n : ℕ, f ((n + 1 + 1 : ℕ) : ℝ)) =
        ∑' n : ℕ, 1 / ((n + 2 : ℕ) : ℝ) ^ u := by
    apply tsum_congr
    intro n
    dsimp only [f]
    rw [Real.rpow_neg (Nat.cast_nonneg _) u]
    push_cast
    ring_nf
  rw [htailEq] at htail
  have hshift :
      (∑' n : ℕ, 1 / ((n + 2 : ℕ) : ℝ) ^ u) =
        (∑' n : ℕ, 1 / (n : ℝ) ^ u) - 1 := by
    calc
      (∑' n : ℕ, 1 / ((n + 2 : ℕ) : ℝ) ^ u) =
          (∑' n : ℕ, 1 / (n : ℝ) ^ u) -
            ∑ n ∈ Finset.range 2, 1 / (n : ℝ) ^ u := by
              linarith [hsplit]
      _ = (∑' n : ℕ, 1 / (n : ℝ) ^ u) - 1 := by rw [hfirst]
  rw [hshift] at htail
  linarith

/-- Explicit pole-size upper bound on the real axis: `‖ζ(1+σ)‖ ≤ 1+σ⁻¹`. -/
theorem norm_riemannZeta_real_le_one_add_inv {sigma : ℝ} (hsigma : 0 < sigma) :
    ‖riemannZeta (((1 + sigma : ℝ) : ℂ))‖ ≤ 1 + sigma⁻¹ := by
  rw [EulerLower.norm_riemannZeta_real_eq_realZetaSum
    (by linarith : 1 < 1 + sigma)]
  simpa only [add_sub_cancel_left] using
    (realZetaSum_le_one_add_inv_sub_one (u := 1 + sigma) (by linarith))

end

end Erdos67
