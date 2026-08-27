import Arxiv.Arxiv2411_18291.NibbleComparisonParameters
import Arxiv.Arxiv2411_18291.ColourProbabilityNumerics

/-!
# Eventual construction of the scalar comparison parameters

Polynomial lower bounds for the graph size and clique degree imply all
comparison conditions when their exponents satisfy the displayed gaps.
-/

open Filter
open scoped Topology

namespace Arxiv2411_18291

theorem eventually_scaled_rpow_le (C : ℝ) {c u v : ℝ} (hc : 0 < c) (huv : u < v) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ u ≤ c * (n : ℝ) ^ v := by
  have h := eventually_const_mul_rpow_le (C / c) (β := -u) (κ := -v) (by linarith)
  filter_upwards [h] with n hn
  simp only [neg_neg] at hn
  calc
    _ = c * ((C / c) * (n : ℝ) ^ u) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hn hc.le

theorem rpow_square_decay_mul {x : ℝ} (hx : 0 < x) (α β c : ℝ) :
    (x ^ (-α)) ^ 2 * (c * x ^ β) = c * x ^ (β - 2 * α) := by
  calc
    _ = c * ((x ^ (-α)) ^ 2 * x ^ β) := by ring
    _ = _ := by
      rw [← Real.rpow_mul_natCast hx.le, ← Real.rpow_add hx]
      congr 2
      ring

theorem eventually_nibble_comparison_parameters (k : ℕ) (hk : 3 ≤ k)
    {α β γ δ ℓ cg cD : ℝ} (hβ : 0 < β) (hαβ : 2 * β < α)
    (hkβ : (k : ℝ) * β ≤ α) (hγ : 2 * α < γ) (hδ : ℓ + 2 * α < δ)
    (hcg : 0 < cg) (hcD : 0 < cD) :
    ∀ᶠ n : ℕ in atTop, ∀ g D : ℝ,
      cg * (n : ℝ) ^ γ ≤ g → cD * (n : ℝ) ^ δ ≤ D →
      NibbleComparisonParameters k ((n : ℝ) ^ (-α)) g D ((n : ℝ) ^ (-β))
        ((n : ℝ) ^ ℓ) := by
  have hα : 0 < α := by linarith only [hβ, hαβ]
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_const_mul_rpow_le 2 (β := α) (κ := 0) hα,
    eventually_const_mul_rpow_le ((16 * (k : ℝ)) ^ 2) (β := α) (κ := 0) hα,
    eventually_const_mul_rpow_le (16 * (k : ℝ) ^ 3) hαβ,
    eventually_scaled_rpow_le (16 * (k : ℝ) ^ 3) hcg
      (show (0 : ℝ) < γ - 2 * α by linarith only [hγ]),
    eventually_scaled_rpow_le ((k : ℝ) ^ 2 + k) hcD
      (show ℓ < δ - 2 * α by linarith only [hδ])]
    with n hn hhalf hsmall hden hmany hcode
  intro g D hg hD
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hgp : 0 < g := (mul_pos hcg (Real.rpow_pos_of_pos hn0 γ)).trans_le hg
  have hDp : 0 < D := (mul_pos hcD (Real.rpow_pos_of_pos hn0 δ)).trans_le hD
  simp only [neg_zero, Real.rpow_zero, mul_one] at hhalf hsmall hmany
  have hpow : (n : ℝ) ^ (-α) ≤ ((n : ℝ) ^ (-β)) ^ k := by
    rw [← Real.rpow_mul_natCast hn0.le]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith only [hkβ])
  refine ⟨hk, Real.rpow_pos_of_pos hn0 _, by linarith only [hhalf], hgp, hDp,
    Real.rpow_pos_of_pos hn0 _, ?_, hpow, hsmall, ?_, ?_, Real.rpow_nonneg hn0.le _, ?_⟩
  · exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr hβ.le)
  · rw [← Real.rpow_mul_natCast hn0.le]
    simp only [Nat.cast_ofNat]
    rw [show (-β) * (2 : ℝ) = -(2 * β) by ring]
    exact hden
  · calc
      _ ≤ cg * (n : ℝ) ^ (γ - 2 * α) := hmany
      _ = ((n : ℝ) ^ (-α)) ^ 2 * (cg * (n : ℝ) ^ γ) :=
        (rpow_square_decay_mul hn0 α γ cg).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hg (sq_nonneg _)
  · calc
      _ ≤ cD * (n : ℝ) ^ (δ - 2 * α) := hcode
      _ = ((n : ℝ) ^ (-α)) ^ 2 * (cD * (n : ℝ) ^ δ) :=
        (rpow_square_decay_mul hn0 α δ cD).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hD (sq_nonneg _)

end Arxiv2411_18291
