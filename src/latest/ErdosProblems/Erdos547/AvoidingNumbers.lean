import ErdosProblems.Erdos547.ReverseRegionNumbers

/-!
# The deficit bound is smaller than the remaining allocation budget
-/

namespace Erdos547.DPRS

theorem deficit_lt_remaining (γ B t r : ℝ) (hγ : 0 ≤ γ) (ht : t < B)
    (hr : r < γ * B / (1 + γ)) :
    r - γ * t / (1 + γ) < B - t := by
  have hd : 0 < 1 + γ := by linarith
  have hratio : γ / (1 + γ) < 1 := (div_lt_one hd).mpr (by linarith)
  calc
    _ < γ * B / (1 + γ) - γ * t / (1 + γ) := sub_lt_sub_right hr _
    _ = γ / (1 + γ) * (B - t) := by ring
    _ < 1 * (B - t) := mul_lt_mul_of_pos_right hratio (sub_pos.mpr ht)
    _ = _ := one_mul _

theorem reverse_tail_identity (γ s q f : ℝ) (hγ : 0 < γ)
    (hq : q = (1 + γ) / γ * f) :
    γ * s / (1 + γ) + f = γ * (s + q) / (1 + γ) := by
  rw [hq]
  have hd : 0 < 1 + γ := by linarith
  field_simp [hγ.ne', hd.ne']

end Erdos547.DPRS

#print axioms Erdos547.DPRS.deficit_lt_remaining
