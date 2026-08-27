import Arxiv.Arxiv2411_18291.NibbleCountConditions
import Arxiv.Arxiv2411_18291.AsymptoticNibbleParameters

/-! # Eventual construction of the additional clique-count conditions -/

open Filter
open scoped Topology

namespace Arxiv2411_18291

theorem rpow_cube_decay_mul {x : ℝ} (hx : 0 < x) (α β c : ℝ) :
    (x ^ (-α)) ^ 3 * (c * x ^ β) = c * x ^ (β - 3 * α) := by
  calc
    _ = c * ((x ^ (-α)) ^ 3 * x ^ β) := by ring
    _ = _ := by
      rw [← Real.rpow_mul_natCast hx.le, ← Real.rpow_add hx]
      congr 2
      ring

theorem eventually_nibble_count_conditions (k : ℕ) (hk : 3 ≤ k)
    {α β γ δ ℓ cg cD : ℝ} (hβ : 0 < β) (hkβ : (k : ℝ) * β ≤ α)
    (hγ : 3 * α < γ) (hδ : ℓ + 3 * α < δ) (hcg : 0 < cg) (hcD : 0 < cD) :
    ∀ᶠ n : ℕ in atTop, ∀ g D : ℝ,
      cg * (n : ℝ) ^ γ ≤ g → cD * (n : ℝ) ^ δ ≤ D →
      NibbleCountConditions k ((n : ℝ) ^ (-α)) g D ((n : ℝ) ^ (-β)) ((n : ℝ) ^ ℓ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hκ : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
    rw [Nat.cast_sub (show 2 ≤ k by omega), Nat.cast_ofNat]
  have hgap : -α < (-β) * ((k - 2 : ℕ) : ℝ) := by
    rw [hκ]
    nlinarith only [hkβ, hβ]
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_scaled_rpow_le 128 hk0 hgap,
    eventually_scaled_rpow_le 1 hcg (show (0 : ℝ) < γ - 3 * α by linarith only [hγ]),
    eventually_scaled_rpow_le 1 hcD (show ℓ < δ - 3 * α by linarith only [hδ])]
    with n hn hvar hsteps hcode
  intro g D hg hD
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Real.rpow_zero, mul_one, one_mul] at hsteps hcode
  refine ⟨?_, ?_, ?_⟩
  · rw [← Real.rpow_mul_natCast hn0.le]
    exact hvar
  · calc
      _ ≤ cg * (n : ℝ) ^ (γ - 3 * α) := hsteps
      _ = ((n : ℝ) ^ (-α)) ^ 3 * (cg * (n : ℝ) ^ γ) :=
        (rpow_cube_decay_mul hn0 α γ cg).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hg (by positivity)
  · calc
      _ ≤ cD * (n : ℝ) ^ (δ - 3 * α) := hcode
      _ = ((n : ℝ) ^ (-α)) ^ 3 * (cD * (n : ℝ) ^ δ) :=
        (rpow_cube_decay_mul hn0 α δ cD).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hD (by positivity)

end Arxiv2411_18291
