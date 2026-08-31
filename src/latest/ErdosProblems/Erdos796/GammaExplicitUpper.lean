import ErdosProblems.Erdos796.GammaFinite
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# An explicit upper bound for the cofactor constant

The sharp two-term fibre estimate is summed by comparison with the
`7/6`- and `4/3`-series.  An elementary integral-test lemma supplies explicit
bounds for those series, leading to `Gamma < 13`.
-/

namespace Erdos796

open scoped BigOperators Interval

/-- The positive `p`-series indexed from one, but represented as a sequence
on `ℕ`. -/
noncomputable def shiftedPSeriesTerm (s : ℝ) (k : ℕ) : ℝ :=
  (((k + 1 : ℕ) : ℝ)) ^ (-s)

theorem shiftedPSeriesTerm_nonneg (s : ℝ) (k : ℕ) :
    0 ≤ shiftedPSeriesTerm s k := by
  rw [shiftedPSeriesTerm]
  positivity

theorem summable_shiftedPSeriesTerm {s : ℝ} (hs : 1 < s) :
    Summable (shiftedPSeriesTerm s) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 s).2 hs
  refine h.congr fun k => ?_
  rw [shiftedPSeriesTerm]
  push_cast
  rw [abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
  rw [one_div, Real.rpow_neg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]

/-- Integral-test estimate for a `p`-series.  This deliberately gives a
non-strict inequality; strictness in the final bound comes from the strict
cofactor-weight comparison at the first term. -/
theorem tsum_shiftedPSeriesTerm_le {s : ℝ} (hs : 1 < s) :
    (∑' k : ℕ, shiftedPSeriesTerm s k) ≤ 1 + 1 / (s - 1) := by
  apply Real.tsum_le_of_sum_range_le
  · exact shiftedPSeriesTerm_nonneg s
  · intro n
    rcases n with _ | n
    · simp only [Finset.range_zero, Finset.sum_empty, one_div]
      positivity
    · let f : ℝ → ℝ := fun x => x ^ (-s)
      have hanti : AntitoneOn f
          (Set.Icc (1 : ℝ) ((1 : ℝ) + n)) := by
        apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
          (by linarith : -s ≤ 0)).mono
        intro x hx
        exact (show 0 < x by linarith [hx.1])
      have htail :
          (∑ k ∈ Finset.range n, f (1 + (k + 1 : ℕ))) ≤
            ∫ x in (1 : ℝ)..(1 + n : ℕ), f x := by
        simpa only [Nat.cast_add, Nat.cast_one] using! hanti.sum_le_integral
      have hzero :
          (0 : ℝ) ∉ [[(1 : ℝ), (1 + n : ℕ)]] := by
        have hone : (1 : ℝ) ≤ ((1 + n : ℕ) : ℝ) := by
          exact_mod_cast (show 1 ≤ 1 + n by omega)
        rw [Set.uIcc_of_le hone]
        simp
      have hint :
          (∫ x in (1 : ℝ)..(1 + n : ℕ), f x) ≤ 1 / (s - 1) := by
        rw [show (∫ x in (1 : ℝ)..(1 + n : ℕ), f x) =
            ((((1 + n : ℕ) : ℝ) ^ (-s + 1) - 1) / (-s + 1)) by
          rw [show f = fun x : ℝ => x ^ (-s) by rfl]
          rw [integral_rpow (Or.inr ⟨by linarith, hzero⟩)]
          norm_num]
        have hden : 0 < s - 1 := by linarith
        have hp : 0 ≤ (((1 + n : ℕ) : ℝ) ^ (-s + 1)) := by
          positivity
        have hid :
            ((((1 + n : ℕ) : ℝ) ^ (-s + 1) - 1) / (-s + 1)) =
              (1 - (((1 + n : ℕ) : ℝ) ^ (-s + 1))) / (s - 1) := by
          rw [show -s + 1 = -(s - 1) by ring, div_neg]
          ring
        rw [hid]
        exact div_le_div_of_nonneg_right (by linarith) hden.le
      calc
        (∑ k ∈ Finset.range (n + 1), shiftedPSeriesTerm s k) =
            (∑ k ∈ Finset.range n, f (1 + (k + 1 : ℕ))) + 1 := by
          rw [Finset.sum_range_succ']
          congr 1
          · apply Finset.sum_congr rfl
            intro k hk
            simp only [shiftedPSeriesTerm, f]
            push_cast
            ring_nf
          · simp [shiftedPSeriesTerm]
        _ ≤ (∫ x in (1 : ℝ)..(1 + n : ℕ), f x) + 1 :=
          add_le_add_left htail 1
        _ ≤ 1 / (s - 1) + 1 := add_le_add_left hint 1
        _ = 1 + 1 / (s - 1) := by ring

/-- Below the factorization cutoff the trivial fibre estimate is still
dominated by the sharp two-term expression. -/
theorem index_le_explicitSidonMajorant {j : ℕ} (hj : j < 8) :
    (j : ℝ) ≤ explicitSidonMajorant j := by
  by_cases hj0 : j = 0
  · subst j
    norm_num [explicitSidonMajorant]
  · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
    have hx1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    have hx8 : (j : ℝ) ≤ 8 := by exact_mod_cast hj.le
    have hthird : (j : ℝ) ^ (1 / 3 : ℝ) ≤ 2 := by
      have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ j) hx8
        (by norm_num : (0 : ℝ) ≤ 1 / 3)
      norm_num at h ⊢
      exact h
    have hsplit :
        (j : ℝ) ^ (1 / 3 : ℝ) * (j : ℝ) ^ (2 / 3 : ℝ) = j := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < j)]
      norm_num
    have htwo :
        (j : ℝ) ≤ 2 * (j : ℝ) ^ (2 / 3 : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hthird
        (by positivity : 0 ≤ (j : ℝ) ^ (2 / 3 : ℝ))
      rw [hsplit] at h
      exact h
    have hpowers :
        (j : ℝ) ^ (2 / 3 : ℝ) ≤ (j : ℝ) ^ (5 / 6 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    rw [explicitSidonMajorant]
    nlinarith

theorem fullSidonMajorant_le_explicitSidonMajorant (j : ℕ) :
    fullSidonMajorant j ≤ explicitSidonMajorant j := by
  by_cases hj : j < 8
  · rw [fullSidonMajorant, if_pos hj]
    exact index_le_explicitSidonMajorant hj
  · rw [fullSidonMajorant, if_neg hj]

/-- The sharp majorant is valid at every fibre, including the finitely many
small fibres. -/
theorem compatible_excess_le_explicitSidonMajorant
    (U : ℕ → Finset ℕ) (hU : Compatible U) (j : ℕ) :
    excess U j ≤ explicitSidonMajorant j :=
  (compatible_excess_le_fullSidonMajorant U hU j).trans
    (fullSidonMajorant_le_explicitSidonMajorant j)

/-- Multiplication by the cofactor weight converts an `a`-power into the
complementary `(2-a)` p-series term. -/
theorem cofactorWeight_mul_rpow_le_shiftedPSeriesTerm
    (k : ℕ) (a b : ℝ) (hab : a + b = 2) :
    cofactorWeight (k + 1) * (((k + 1 : ℕ) : ℝ) ^ a) ≤
      shiftedPSeriesTerm b k := by
  let x : ℝ := (k : ℝ) + 1
  have hx : 0 < x := by positivity
  have hx1 : 0 < x + 1 := by positivity
  have hden : 0 < x * (x + 1) := mul_pos hx hx1
  have hpow : 0 < x ^ b := Real.rpow_pos_of_pos hx _
  rw [cofactorWeight, shiftedPSeriesTerm]
  push_cast
  change (1 / (x * (x + 1))) * x ^ a ≤ x ^ (-b)
  rw [Real.rpow_neg hx.le]
  rw [show (1 / (x * (x + 1))) * x ^ a = x ^ a / (x * (x + 1)) by ring]
  rw [← one_div]
  rw [div_le_div_iff₀ hden hpow]
  rw [← Real.rpow_add hx, hab, Real.rpow_two]
  nlinarith

/-- The two p-series which dominate the sharp weighted fibre estimate. -/
noncomputable def explicitPSeriesMajorant (k : ℕ) : ℝ :=
  shiftedPSeriesTerm (7 / 6 : ℝ) k +
    (3 / 2 : ℝ) * shiftedPSeriesTerm (4 / 3 : ℝ) k

theorem explicitPSeriesMajorant_nonneg (k : ℕ) :
    0 ≤ explicitPSeriesMajorant k := by
  rw [explicitPSeriesMajorant]
  exact add_nonneg (shiftedPSeriesTerm_nonneg _ _)
    (mul_nonneg (by norm_num) (shiftedPSeriesTerm_nonneg _ _))

theorem weightedMajorant_explicit_le_pseries (k : ℕ) :
    weightedMajorant explicitSidonMajorant k ≤ explicitPSeriesMajorant k := by
  have hfirst := cofactorWeight_mul_rpow_le_shiftedPSeriesTerm k
    (5 / 6 : ℝ) (7 / 6 : ℝ) (by norm_num)
  have hsecond := cofactorWeight_mul_rpow_le_shiftedPSeriesTerm k
    (2 / 3 : ℝ) (4 / 3 : ℝ) (by norm_num)
  rw [weightedMajorant, explicitSidonMajorant, explicitPSeriesMajorant]
  calc
    cofactorWeight (k + 1) *
        ((((k + 1 : ℕ) : ℝ) ^ (5 / 6 : ℝ)) +
          (3 / 2 : ℝ) * (((k + 1 : ℕ) : ℝ) ^ (2 / 3 : ℝ))) =
        cofactorWeight (k + 1) *
            (((k + 1 : ℕ) : ℝ) ^ (5 / 6 : ℝ)) +
          (3 / 2 : ℝ) *
            (cofactorWeight (k + 1) *
              (((k + 1 : ℕ) : ℝ) ^ (2 / 3 : ℝ))) := by ring
    _ ≤ shiftedPSeriesTerm (7 / 6 : ℝ) k +
        (3 / 2 : ℝ) * shiftedPSeriesTerm (4 / 3 : ℝ) k := by
      gcongr

theorem summable_explicitPSeriesMajorant :
    Summable explicitPSeriesMajorant := by
  exact (summable_shiftedPSeriesTerm (by norm_num : (1 : ℝ) < 7 / 6)).add
    ((summable_shiftedPSeriesTerm (by norm_num : (1 : ℝ) < 4 / 3)).mul_left
      (3 / 2 : ℝ))

theorem tsum_explicitPSeriesMajorant_le_thirteen :
    (∑' k : ℕ, explicitPSeriesMajorant k) ≤ 13 := by
  change (∑' k : ℕ, (shiftedPSeriesTerm (7 / 6 : ℝ) k +
    (3 / 2 : ℝ) * shiftedPSeriesTerm (4 / 3 : ℝ) k)) ≤ 13
  rw [Summable.tsum_add
    (summable_shiftedPSeriesTerm (by norm_num : (1 : ℝ) < 7 / 6))
    ((summable_shiftedPSeriesTerm (by norm_num : (1 : ℝ) < 4 / 3)).mul_left
      (3 / 2 : ℝ)), tsum_mul_left]
  have h₇ := tsum_shiftedPSeriesTerm_le (by norm_num : (1 : ℝ) < 7 / 6)
  have h₄ := tsum_shiftedPSeriesTerm_le (by norm_num : (1 : ℝ) < 4 / 3)
  norm_num at h₇ h₄ ⊢
  linarith

/-- The pointwise comparison is strict already at the first summand. -/
theorem weightedMajorant_explicit_zero_lt_pseries :
    weightedMajorant explicitSidonMajorant 0 < explicitPSeriesMajorant 0 := by
  norm_num [weightedMajorant, explicitSidonMajorant, explicitPSeriesMajorant,
    cofactorWeight, shiftedPSeriesTerm]

theorem tsum_weightedMajorant_explicit_lt_thirteen :
    (∑' k : ℕ, weightedMajorant explicitSidonMajorant k) < 13 := by
  have hlt :
      (∑' k : ℕ, weightedMajorant explicitSidonMajorant k) <
        ∑' k : ℕ, explicitPSeriesMajorant k :=
    Summable.tsum_lt_tsum_of_nonneg weightedMajorant_explicit_nonneg
      weightedMajorant_explicit_le_pseries
      weightedMajorant_explicit_zero_lt_pseries
      summable_explicitPSeriesMajorant
  exact hlt.trans_le tsum_explicitPSeriesMajorant_le_thirteen

/-- The explicit numerical estimate asserted in the manuscript. -/
theorem Gamma_lt_thirteen : Gamma < 13 := by
  have hGamma := Gamma_le_tsum_majorant
    (fun U hU j => compatible_excess_le_explicitSidonMajorant U hU j)
    summable_weightedMajorant_explicit
  exact hGamma.trans_lt tsum_weightedMajorant_explicit_lt_thirteen

end Erdos796
