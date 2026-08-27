import Arxiv.Arxiv2411_18291.RegularCliqueFamily

/-!
# Regularity boosting with the paper's binomial count and error scale

Convert the sampled power-scale clique count to the binomial normalization.
For every fixed polynomially sparse complement, all sufficiently large
graphs have a clique family with edge degrees `(1 ± n^(-1/3))*choose(n,q-r)/2`.
The construction supplies the boost needed in the eventual design theorem.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem regular_count_change_scale {x t b c η : ℝ} (hc : 0 ≤ c) (hcsmall : c ≤ 1 / 2)
    (hb : 0 ≤ b) (hcount : |x - t / 2| ≤ c * (t / 2))
    (hlo : (1 - c) * t ≤ b) (hhi : b ≤ t) (hη : 2 * c ≤ η) :
    |x - b / 2| ≤ η * b := by
  have ht := hb.trans hhi
  have hct := mul_le_mul_of_nonneg_right hcsmall ht
  have htb : t ≤ 2 * b := by nlinarith only [hct, hlo]
  have hcost : c * t ≤ η * b := by
    have hh := mul_le_mul_of_nonneg_left htb hc
    have he := mul_le_mul_of_nonneg_right hη hb
    nlinarith only [hh, he]
  have hnonneg := mul_nonneg hc ht
  obtain ⟨hleft, hright⟩ := abs_le.mp hcount
  rw [abs_le]
  constructor <;> nlinarith only [hleft, hright, hlo, hhi, hcost, hnonneg]

theorem eventually_exists_regularity_boost (q r : ℕ) (hqr : r + 1 < q)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ G : Hypergraph (Fin n) (r + 1),
      IsGraphBounded (complete (Fin n) (r + 1) \ G) ((n : ℝ) ^ (-δ)) →
      ∃ H : Finset (Block (Fin n) q), H ⊆ cliqueFamily G q ∧ ∀ e ∈ G,
        |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - (n.choose (q - (r + 1)) : ℝ) / 2| ≤
          (n : ℝ) ^ (-(1 / 3 : ℝ)) * ((n.choose (q - (r + 1)) : ℝ) / 2) := by
  have hlim := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_exists_regular_clique_family_power_scale q r hqr hδ hδ1
      (κ := 2 / 5) (by norm_num) (by norm_num),
    eventually_uniform_shifted_choose_lower q (κ := 2 / 5) (by norm_num),
    eventually_const_mul_rpow_le 4 (show (1 / 3 : ℝ) < 2 / 5 by norm_num),
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with n hfamily hchoose hscale hsmall
  intro G hG
  obtain ⟨H, hH, hcounts⟩ := hfamily G hG
  refine ⟨H, hH, fun e he => ?_⟩
  have hlo := hchoose.2 0 (by omega) (q - (r + 1)) (Nat.sub_le _ _)
  simp only [Nat.sub_zero] at hlo
  have hlo' : (1 - (n : ℝ) ^ (-(2 / 5 : ℝ))) *
      ((n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial) ≤
        (n.choose (q - (r + 1)) : ℝ) := by
    simpa only [mul_div_assoc] using hlo
  have hη : 2 * (n : ℝ) ^ (-(2 / 5 : ℝ)) ≤ (n : ℝ) ^ (-(1 / 3 : ℝ)) / 2 := by
    linarith only [hscale]
  have hh := regular_count_change_scale (Real.rpow_nonneg (Nat.cast_nonneg n) _) hsmall.le
    (Nat.cast_nonneg _) (hcounts e he) hlo'
    (by simpa only [Nat.sub_zero] using shifted_choose_upper n 0 (q - (r + 1))) hη
  convert hh using 1
  ring

end Arxiv2411_18291
