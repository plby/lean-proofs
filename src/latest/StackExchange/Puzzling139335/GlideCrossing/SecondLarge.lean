import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic
import StackExchange.Puzzling139335.GlideCrossing.SecondLarge.Arc

namespace Puzzling139335.GlideCrossing

noncomputable section

private def largeA (S : ℝ) : ℝ := 1 - S / 2

private def largeB (C S : ℝ) : ℝ :=
  1 / 2 + C * (S - 1 - 4 * C) / (2 * (1 + S))

private theorem large_coefficients {C S : ℝ}
    (hC : 0 < C) (hCh : C ≤ 1 / 2) (hS : 0 ≤ S)
    (hcircle : S ^ 2 + C ^ 2 = 1) :
    0 < largeA S ∧ 1 / 5 < largeB C S ∧ S < 1 ∧ 17 / 20 < S := by
  have hS1 : S < 1 := by nlinarith [sq_pos_of_pos hC]
  have hS17 : 17 / 20 < S := by nlinarith
  have hden : 0 < 2 * (1 + S) := by positivity
  have hterm : 0 < 1 - S + 4 * C := by positivity
  have hmul : C * (1 - S + 4 * C) < 43 / 40 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 2 - C by linarith) hterm.le]
  refine ⟨?_, ?_, hS1, hS17⟩
  · unfold largeA
    linarith
  · unfold largeB
    have hq : -(3 / 10 : ℝ) < C * (S - 1 - 4 * C) / (2 * (1 + S)) := by
      rw [lt_div_iff₀ hden]
      nlinarith
    linarith

private theorem large_top {C S : ℝ}
    (hC : 0 < C) (hCh : C ≤ 1 / 2) (hS : 0 ≤ S)
    (hcircle : S ^ 2 + C ^ 2 = 1) :
    1 / 2 < largeA S * S + largeB C S * C := by
  obtain ⟨hA, hB, hS1, hS17⟩ := large_coefficients hC hCh hS hcircle
  have hden : 0 < 1 + S := by positivity
  have hSC : C < S := by linarith
  have hq : C * (1 - S + 2 * C) / (1 + S) < C := by
    rw [div_lt_iff₀ hden]
    nlinarith [mul_pos hC (sub_pos.mpr hSC)]
  have hpos : 0 < C * (1 / 2 - C * (1 - S + 2 * C) / (1 + S)) := by
    apply mul_pos hC
    linarith
  have hid : largeA S * S + largeB C S * C - 1 / 2 =
      C * (1 / 2 - C * (1 - S + 2 * C) / (1 + S)) := by
    unfold largeA largeB
    field_simp
    nlinarith [hcircle]
  linarith

private theorem large_complement {C S : ℝ}
    (hC : 0 < C) (hCh : C ≤ 2 / 5) (hS : 0 ≤ S)
    (hcircle : S ^ 2 + C ^ 2 = 1) :
    1 / 2 < largeA S * C + largeB C S * S := by
  obtain ⟨hA, hB, hS1, hS17⟩ :=
    large_coefficients hC (by linarith : C ≤ 1 / 2) hS hcircle
  have hden : 0 < 1 + S := by positivity
  have hsmall : C * (1 / 2 + 2 * S) < 1 := by
    have hm := mul_lt_mul_of_pos_left hS1 hC
    nlinarith
  have hpos : 0 < C * (1 - C * (1 / 2 + 2 * S)) / (1 + S) := by
    exact div_pos (mul_pos hC (by linarith)) hden
  have hid : largeA S * C + largeB C S * S - 1 / 2 =
      C * (1 - C * (1 / 2 + 2 * S)) / (1 + S) := by
    unfold largeA largeB
    field_simp
    nlinarith [hcircle]
  linarith

private theorem large_fixed_left {C S : ℝ}
    (hCl : 2 / 5 ≤ C) (hCh : C ≤ 1 / 2) (hS : 0 ≤ S)
    (hcircle : S ^ 2 + C ^ 2 = 1) :
    1 / 2 < largeA S * Real.sin (Real.arccos (5 / 8)) +
      largeB C S * Real.cos (Real.arccos (5 / 8)) := by
  have hC : 0 < C := by linarith
  obtain ⟨hA, hB, hS1, hS17⟩ := large_coefficients hC hCh hS hcircle
  have hS23 : S < 23 / 25 := by nlinarith
  have hA27 : 27 / 50 < largeA S := by unfold largeA; linarith
  have hc : Real.cos (Real.arccos (5 / 8)) = 5 / 8 :=
    Real.cos_arccos (by norm_num) (by norm_num)
  have hs0 : 0 ≤ Real.sin (Real.arccos (5 / 8)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)
  have hs : 3 / 4 < Real.sin (Real.arccos (5 / 8)) := by
    have hcircle0 := Real.sin_sq_add_cos_sq (Real.arccos (5 / 8))
    rw [hc] at hcircle0
    nlinarith
  have hm : 81 / 200 < largeA S * Real.sin (Real.arccos (5 / 8)) := calc
    81 / 200 < largeA S * (3 / 4) := by nlinarith
    _ < largeA S * Real.sin (Real.arccos (5 / 8)) := mul_lt_mul_of_pos_left hs hA
  rw [hc]
  nlinarith

/-- The large-sum branch of the second strict crossing inequality. -/
theorem secondLarge_pos (α β : ℝ)
    (hαlo : Real.pi / 3 ≤ α) (hβpos : 0 < β) (hβα : β ≤ α)
    (hαhi : α < Real.pi / 2) (hprod : 4 * Real.cos α * Real.cos β ≤ 1)
    (hsum : Real.pi / 2 ≤ α + β) :
    0 < (1 - Real.sin α / 2) * Real.sin β +
      (1 / 2 + Real.cos α * (Real.sin α - 1 - 4 * Real.cos α) /
        (2 * (1 + Real.sin α))) * Real.cos β - 1 / 2 := by
  have hπ := Real.pi_pos
  have hα0 : 0 < α := by linarith
  have hαπ : α ≤ Real.pi := by linarith
  have hβπ : β ≤ Real.pi := by linarith
  have hC : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hαhi⟩
  have hCh : Real.cos α ≤ 1 / 2 := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi
      (show 0 ≤ Real.pi / 3 by positivity) hαπ hαlo
    simpa only [Real.cos_pi_div_three] using h
  have hS : 0 ≤ Real.sin α := Real.sin_nonneg_of_nonneg_of_le_pi hα0.le hαπ
  have hcircle := Real.sin_sq_add_cos_sq α
  obtain ⟨hA, hB, hS1, hS17⟩ := large_coefficients hC hCh hS hcircle
  have htop := large_top hC hCh hS hcircle
  suffices h : 1 / 2 < largeA (Real.sin α) * Real.sin β +
      largeB (Real.cos α) (Real.sin α) * Real.cos β by
    simpa only [largeA, largeB, sub_pos] using h
  by_cases hsmall : Real.cos α ≤ 2 / 5
  · apply sin_cos_arc_lower_bound hA.le (by linarith : 0 ≤ largeB (Real.cos α) (Real.sin α))
      (show 0 ≤ Real.pi / 2 - α by linarith) hαhi.le
      (show Real.pi / 2 - α ≤ β by linarith) hβα
    · simpa only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub] using
        large_complement hC hsmall hS hcircle
    · exact htop
  · have hCl : 2 / 5 ≤ Real.cos α := le_of_lt (lt_of_not_ge hsmall)
    have hcosβ : 0 ≤ Real.cos β :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
    have hcβ : Real.cos β ≤ 5 / 8 := by
      nlinarith [mul_nonneg (show 0 ≤ Real.cos α - 2 / 5 by linarith) hcosβ]
    have hloβ : Real.arccos (5 / 8) ≤ β := by
      have h := Real.arccos_le_arccos hcβ
      simpa only [Real.arccos_cos hβpos.le hβπ] using h
    exact sin_cos_arc_lower_bound hA.le (by linarith) (Real.arccos_nonneg _)
      hαhi.le hloβ hβα (large_fixed_left hCl hCh hS hcircle) htop

end

end Puzzling139335.GlideCrossing
