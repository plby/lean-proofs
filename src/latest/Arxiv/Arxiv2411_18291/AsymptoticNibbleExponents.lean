import Arxiv.Arxiv2411_18291.NibbleExponentConditions
import Arxiv.Arxiv2411_18291.AsymptoticNibbleParameters

/-! # Eventual polynomial margins for a common nibble concentration exponent -/

open Filter
open scoped Topology

namespace Arxiv2411_18291

theorem rpow_nat_decay_mul {x : ℝ} (hx : 0 < x) (m : ℕ) (α β c : ℝ) :
    (x ^ (-α)) ^ m * (c * x ^ β) = c * x ^ (β - (m : ℝ) * α) := by
  calc
    _ = c * ((x ^ (-α)) ^ m * x ^ β) := by ring
    _ = _ := by
      rw [← Real.rpow_mul_natCast hx.le, ← Real.rpow_add hx]
      congr 2
      ring

theorem eventually_nibble_exponent_conditions (k d : ℕ) {α η γ δ ℓ cg cD : ℝ}
    (hγ1 : 1 ≤ γ) (hcount : η + 6 * α < γ) (hcode : η + ℓ + 4 * α < δ)
    (hgraph : η + 4 * α < γ) (hface : η + 2 * α < 1) (hcg : 0 < cg) (hcD : 0 < cD) :
    ∀ᶠ n : ℕ in atTop, ∀ g D : ℝ, cg * (n : ℝ) ^ γ ≤ g → cD * (n : ℝ) ^ δ ≤ D →
      NibbleExponentConditions k d ((n : ℝ) ^ (-α)) g D n ((n : ℝ) ^ ℓ)
        ((n : ℝ) ^ η) cg := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_scaled_rpow_le (16 * (132 * (k : ℝ) ^ 3) ^ 2) hcg
      (show η < γ - 6 * α by linarith only [hcount]),
    eventually_scaled_rpow_le (176 * (k : ℝ) ^ 3) hcD
      (show η + ℓ < δ - 4 * α by linarith only [hcode]),
    eventually_scaled_rpow_le (352 * (k : ℝ) ^ 4) hcg
      (show η < γ - 4 * α by linarith only [hgraph]),
    eventually_scaled_rpow_le
      (8 * (4 * (d : ℝ) * (1 + 128 * (k : ℝ)) * k + ((d : ℝ) + k / cg)))
      (by norm_num : (0 : ℝ) < 1) (show η < 1 - 2 * α by linarith only [hface])]
    with n hn hcount' hcode' hgraph' hface'
  intro g D hg hD
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [one_mul] at hface'
  refine ⟨hcg, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ cg * (n : ℝ) ^ (γ - 6 * α) := hcount'
      _ = ((n : ℝ) ^ (-α)) ^ 6 * (cg * (n : ℝ) ^ γ) :=
        (rpow_nat_decay_mul hn0 6 α γ cg).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hg (by positivity)
  · calc
      _ = (176 * (k : ℝ) ^ 3) * (n : ℝ) ^ (η + ℓ) := by
        rw [Real.rpow_add hn0]
        ring
      _ ≤ cD * (n : ℝ) ^ (δ - 4 * α) := hcode'
      _ = ((n : ℝ) ^ (-α)) ^ 4 * (cD * (n : ℝ) ^ δ) :=
        (rpow_nat_decay_mul hn0 4 α δ cD).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hD (by positivity)
  · calc
      _ ≤ cg * (n : ℝ) ^ (γ - 4 * α) := hgraph'
      _ = ((n : ℝ) ^ (-α)) ^ 4 * (cg * (n : ℝ) ^ γ) :=
        (rpow_nat_decay_mul hn0 4 α γ cg).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hg (by positivity)
  · have heq : (n : ℝ) ^ (1 - 2 * α) = ((n : ℝ) ^ (-α)) ^ 2 * n := by
      simpa only [one_mul, Real.rpow_one, Nat.cast_ofNat] using
        (rpow_nat_decay_mul hn0 2 α 1 1).symm
    exact hface'.trans_eq heq
  · have hp : (n : ℝ) ≤ (n : ℝ) ^ γ := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 hγ1
    exact (mul_le_mul_of_nonneg_left hp hcg.le).trans hg

end Arxiv2411_18291
