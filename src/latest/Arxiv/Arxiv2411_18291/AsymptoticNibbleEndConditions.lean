import Arxiv.Arxiv2411_18291.NibbleEndConditions
import Arxiv.Arxiv2411_18291.AsymptoticNibbleCountConditions

/-! # Eventual end conditions from polynomial graph density -/

open Filter
open scoped Topology

namespace Arxiv2411_18291

theorem eventually_nibble_end_conditions (k d : ℕ) {α β γ cg : ℝ}
    (hα : α < 1) (hβα : β < α) (hγ : 3 * α < γ) (hcg : 0 < cg) :
    ∀ᶠ n : ℕ in atTop, ∀ g : ℝ, cg * (n : ℝ) ^ γ ≤ g →
      NibbleEndConditions k ((n : ℝ) ^ (-α)) g n ((n : ℝ) ^ (-β)) d := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_scaled_rpow_le (264 * (k : ℝ) ^ 3) hcg
      (show (0 : ℝ) < γ - 3 * α by linarith only [hγ]),
    eventually_scaled_rpow_le (4 * (d : ℝ)) (by norm_num : (0 : ℝ) < 1)
      (show (0 : ℝ) < 1 - α by linarith only [hα]),
    eventually_scaled_rpow_le (128 * (k : ℝ)) (by norm_num : (0 : ℝ) < 1)
      (show -α < -β by linarith only [hβα])]
    with n hn hcount hface herror
  intro g hg
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Real.rpow_zero, mul_one, one_mul] at hcount hface herror
  refine ⟨?_, ?_, herror⟩
  · calc
      _ ≤ cg * (n : ℝ) ^ (γ - 3 * α) := hcount
      _ = ((n : ℝ) ^ (-α)) ^ 3 * (cg * (n : ℝ) ^ γ) :=
        (rpow_cube_decay_mul hn0 α γ cg).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hg (by positivity)
  · have heq : (n : ℝ) ^ (1 - α) = (n : ℝ) ^ (-α) * n := by
      rw [show 1 - α = -α + 1 by ring, Real.rpow_add hn0, Real.rpow_one]
    exact hface.trans_eq heq

end Arxiv2411_18291
