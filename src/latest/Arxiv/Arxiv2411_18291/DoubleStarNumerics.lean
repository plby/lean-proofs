import Arxiv.Arxiv2411_18291.DoubleStarPattern
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Numerical hypotheses for the rank-two greedy counterexample -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem greedyDoubleStar256_vertices : Fintype.card (Option (ZMod 256)) = 257 := by
  rw [Fintype.card_option, ZMod.card]

theorem greedyDoubleStar256_carrier :
    Fintype.card (Block (Option (ZMod 256)) 2) = 32896 := by
  simp only [Block, Fintype.card_finset_len, greedyDoubleStar256_vertices,
    Nat.choose_two_right]

theorem greedyDoubleStar256_indices (L : ℕ) :
    Fintype.card (Option (ZMod 256) × ZMod 256 × Fin L) = 65792 * L := by
  rw [Fintype.card_prod, Fintype.card_prod, greedyDoubleStar256_vertices,
    ZMod.card, Fintype.card_fin]
  ring

theorem greedyDoubleStar256_smallness :
    (1 / 16385 : ℝ) <
      (8 * ((2 : ℕ).factorial : ℝ) ^ 2 * (greedyDoubleStar (ZMod 256)).card)⁻¹ := by
  have hcard : (greedyDoubleStar (ZMod 256)).card ≤ 512 := by
    simpa only [ZMod.card] using greedyDoubleStar_card_le (ZMod 256)
  have hpos : (0 : ℝ) < (greedyDoubleStar (ZMod 256)).card := by
    exact_mod_cast card_pos.mpr (greedyDoubleStar_nonempty (ZMod 256))
  have hbound : ((greedyDoubleStar (ZMod 256)).card : ℝ) ≤ 512 := by
    exact_mod_cast hcard
  have hden : (0 : ℝ) < 32 * (greedyDoubleStar (ZMod 256)).card :=
    mul_pos (by norm_num) hpos
  have hlt : (32 : ℝ) *
      (greedyDoubleStar (ZMod 256)).card < 16385 := by
    linarith only [hbound]
  norm_num only [show (2 : ℕ).factorial = 2 from rfl, Nat.cast_ofNat]
  simpa only [one_div] using (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 16385) hden).2 hlt

theorem greedyDoubleStar256_degree {L : ℕ} (hL : 0 < L) :
    (4 * L : ℝ) < (1 / 16385 : ℝ) * (65600 * L : ℕ) := by
  have hp : (0 : ℝ) < L := by exact_mod_cast hL
  push_cast
  linarith only [hp]

theorem greedyDoubleStar256_lower_density {L : ℕ} (hL : 4096 ≤ L) :
    ((65600 * L : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) < 1 / 16385 := by
  have hN : (268697600 : ℝ) ≤ (65600 * L : ℕ) := by
    exact_mod_cast (show 268697600 ≤ 65600 * L by omega)
  have hs : (16385 : ℝ) < Real.sqrt (65600 * L : ℕ) := by
    have hsq := Real.sq_sqrt (Nat.cast_nonneg (65600 * L))
    have hpos := Real.sqrt_nonneg ((65600 * L : ℕ) : ℝ)
    nlinarith only [hN, hsq, hpos]
  rw [Real.rpow_neg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow]
  simpa only [one_div] using
    (inv_lt_inv₀ (by linarith only [hs]) (by norm_num : (0 : ℝ) < 16385)).2 hs

end Arxiv2411_18291
