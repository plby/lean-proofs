import Arxiv.Arxiv2411_18291.FiniteSparseFlattening
import Arxiv.Arxiv2411_18291.PaperFlatteningThreshold
import Arxiv.Arxiv2411_18291.FlatteningCostObstruction

/-! # The paper's flattening input with a corrected explicit threshold -/

noncomputable section

namespace Arxiv2411_18291

theorem paper_flattening_input_normalization {q r n M : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hM : M ≤ absorberExchangeEdges q (r + 1)) :
    ((2 ^ (q + 2) * (4 * q) ^ (r + 1) * paperColourCount q (r + 1) M : ℕ) : ℝ) *
        (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)) ≤
      (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) := by
  have hq : 2 ≤ q := by omega
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hc : 2 ^ (q + 2) * (4 * q) ^ (r + 1) * paperColourCount q (r + 1) M ≤
      (4 * q) ^ (6 * q + 5) := by
    calc
      _ ≤ 2 ^ (5 * q) * (4 * q) ^ (r + 1) * paperColourCount q (r + 1) M :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
          (Nat.pow_le_pow_right (by decide) (by omega)))
      _ ≤ _ := paper_flattening_coefficient_le (Nat.succ_pos r) hqr hM
  have hgrowth : (4 * q : ℝ) ^ (6 * q + 5) ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) / 10) := by
    have hh := paper_threshold_alpha_rpow_lower hqr hn (s := 6 * q + 5)
      (t := (1 / 10 : ℝ)) (by norm_num) (by push_cast; linarith only [hqR])
    convert hh using 1
    congr 1
    ring
  have hcR : ((2 ^ (q + 2) * (4 * q) ^ (r + 1) * paperColourCount q (r + 1) M : ℕ) : ℝ) ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) / 10) :=
    (by exact_mod_cast hc :
      ((2 ^ (q + 2) * (4 * q) ^ (r + 1) * paperColourCount q (r + 1) M : ℕ) : ℝ) ≤
        (4 * q : ℝ) ^ (6 * q + 5)).trans hgrowth
  calc
    _ ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 10) *
        (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)) :=
      mul_le_mul_of_nonneg_right hcR (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

/-- Corrected finite flattening for the full printed input coefficient.
The multiplicity bound is 16 and the iteration threshold is explicit. -/
theorem exists_flattened_paper_input_explicit {q r n M : ℕ} (hqr : r + 1 < q)
    (hn : finiteFlatteningThreshold q r ≤ n)
    (hM : M ≤ absorberExchangeEdges q (r + 1)) (D : Finset (Block (Fin n) q))
    (hD : IsCliqueFamilyBounded r D
      (((2 ^ (q + 2) * (4 * q) ^ (r + 1) * paperColourCount q (r + 1) M : ℕ) : ℝ) *
        (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)))) :
    ∃ F : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r F ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))) ∧
      (∀ J : Block (Fin n) (r + 1) → ℤ, GeneratedBy D J → GeneratedBy F J) ∧
      ∀ e : Block (Fin n) (r + 1), (F.filter fun Q => e.val ⊆ Q.val).card ≤ 16 :=
  exists_sparse_flattening_explicit hqr hn D
    (hD.mono (paper_flattening_input_normalization hqr ((le_max_left _ _).trans hn) hM))

/-- The corrected threshold cannot be silently identified with the printed
one: it is strictly larger already for the triangle case. -/
theorem triangle_threshold_lt_finiteFlatteningThreshold :
    paperSizeThreshold 3 2 < finiteFlatteningThreshold 3 1 := by
  by_contra h
  have hn : finiteFlatteningThreshold 3 1 ≤ paperSizeThreshold 3 2 := by omega
  have hcost : flatteningCostThreshold (flatteningRoundConstant 3 1)
      (paperAlpha 3 2 / 10) ≤ paperSizeThreshold 3 2 := (le_max_right _ _).trans hn
  have hC : (1 : ℝ) ≤ flatteningRoundConstant 3 1 := by
    exact_mod_cast flatteningRoundConstant_pos 3 1
  have hε : 0 < paperAlpha 3 2 / 10 :=
    div_pos (paperAlpha_pos (by decide : 2 < 3)) (by norm_num)
  obtain ⟨k, hstop, hbudget⟩ := exists_flattening_iterations_explicit hC hε hcost
  have hlarge : (8109 : ℝ) ≤ flatteningRoundConstant 3 1 := by
    norm_num [flatteningRoundConstant, absorberExchangeEdges]
  exact (not_lt_of_ge hbudget) (flattening_iteration_cost_exceeds_triangle_threshold hlarge hstop)

end Arxiv2411_18291
