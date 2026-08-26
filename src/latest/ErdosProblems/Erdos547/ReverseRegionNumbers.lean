import ErdosProblems.Erdos547.BudgetIdentities

/-!
# The size gain obtained by orienting a covered region in the reverse direction
-/

namespace Erdos547.DPRS

theorem reverse_region_mass_bound (F t s b₁ b₂ k D : ℝ)
    (ht : 0 ≤ t) (hb₁ : 0 < b₁) (hb₂ : b₁ ≤ b₂)
    (hs : F + t / (1 + b₂ / b₁) = s)
    (hsize : b₂ / 2 ≤ s) (hbound : D + k / 2 - b₁ / 2 < s) :
    D + k / 2 < ((1 + b₂ / b₁) / (b₂ / b₁)) * F + t := by
  let γ := b₂ / b₁
  have hγ : 1 ≤ γ := (one_le_div hb₁).mpr hb₂
  have hgp : 0 < γ := zero_lt_one.trans_le hγ
  have hden : 0 < 1 + γ := by linarith
  have hr : (1 + γ) / γ ≤ 1 + γ := by
    apply (div_le_iff₀ hgp).mpr
    nlinarith
  have hz : 0 ≤ t / (1 + γ) := div_nonneg ht hden.le
  have he : (1 + γ) * (t / (1 + γ)) = t := by field_simp
  have hmass : ((1 + γ) / γ) * s ≤ ((1 + γ) / γ) * F + t := by
    have hh := mul_le_mul_of_nonneg_right hr hz
    have hs' : F + t / (1 + γ) = s := hs
    rw [← hs', mul_add]
    linarith
  have hpart : b₁ / 2 ≤ s / γ := by
    calc
      _ = (b₂ / 2) / γ := by
        dsimp [γ]
        have hb₂p := hb₁.trans_le hb₂
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hsize hgp.le
  have hid : ((1 + γ) / γ) * s = s + s / γ := by field_simp; ring
  rw [hid] at hmass
  change D + k / 2 < ((1 + γ) / γ) * F + t
  linarith

theorem remaining_budget_gt_badset (b₁ b₂ t r x : ℝ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hx : 0 ≤ x)
    (hsmall : r + x < b₂)
    (hload : (b₂ / b₁) * t / (1 + b₂ / b₁) ≤ r) :
    x < b₁ + b₂ - t := by
  let γ := b₂ / b₁
  have hγ : 0 < γ := div_pos hb₂ hb₁
  have hden : 0 < 1 + γ := by linarith
  have ht : γ * t ≤ r * (1 + γ) := (div_le_iff₀ hden).mp hload
  have hs := mul_lt_mul_of_pos_right hsmall hden
  have he : b₂ * (1 + γ) = γ * (b₁ + b₂) := by dsimp [γ]; field_simp
  rw [he] at hs
  nlinarith

end Erdos547.DPRS

#print axioms Erdos547.DPRS.reverse_region_mass_bound
#print axioms Erdos547.DPRS.remaining_budget_gt_badset
