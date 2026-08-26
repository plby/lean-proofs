import ErdosProblems.Erdos547.ResidualBudgets

/-!
# The exact conversion rate from fractional mass to an oriented skew budget
-/

namespace Erdos547.DPRS

noncomputable def orientationRate (γ : ℝ) : ℝ := (1 + γ) / max 1 γ

theorem orientationRate_pos {γ : ℝ} (hγ : 0 ≤ γ) : 0 < orientationRate γ :=
  div_pos (by linarith) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

theorem one_le_orientationRate {γ : ℝ} (hγ : 0 ≤ γ) : 1 ≤ orientationRate γ := by
  apply (le_div_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) γ))).mpr
  rw [one_mul]
  exact max_le (by linarith) (by linarith)

theorem max_skew_parts_eq_div_rate (γ r : ℝ) (hγ : 0 ≤ γ) (hr : 0 ≤ r) :
    max (r / (1 + γ)) (γ * (r / (1 + γ))) = r / orientationRate γ := by
  have hden : 0 < 1 + γ := by linarith
  have he := max_mul_of_nonneg (1 : ℝ) γ (div_nonneg hr hden.le)
  rw [one_mul] at he
  rw [← he, orientationRate]
  have hM : 0 < max 1 γ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  field_simp [ne_of_gt hden, ne_of_gt hM]

theorem private_residual_budget (γ A p : ℝ) (hγ : 0 ≤ γ) (hA : 0 ≤ A) (hp : 0 ≤ p) :
    let q := min (A / orientationRate γ) p
    let r := A - orientationRate γ * q
    0 ≤ q ∧ q ≤ p ∧ 0 ≤ r ∧ q ≤ orientationRate γ * q ∧
      max (r / (1 + γ)) (γ * (r / (1 + γ))) =
        max (A / (1 + γ)) (γ * (A / (1 + γ))) - q ∧ (0 < r → q = p) := by
  dsimp only
  have hf := orientationRate_pos hγ
  have hf1 := one_le_orientationRate hγ
  let q := min (A / orientationRate γ) p
  have hq : 0 ≤ q := le_min (div_nonneg hA hf.le) hp
  have hqA : orientationRate γ * q ≤ A := by
    have hh := (le_div_iff₀ hf).mp (min_le_left (A / orientationRate γ) p)
    dsimp [q]
    nlinarith
  have hr : 0 ≤ A - orientationRate γ * q := by linarith
  refine ⟨hq, min_le_right _ _, hr, ?_, ?_, ?_⟩
  · exact le_mul_of_one_le_left hq hf1
  · rw [max_skew_parts_eq_div_rate γ _ hγ hr, max_skew_parts_eq_div_rate γ A hγ hA]
    field_simp [ne_of_gt hf]
    rfl
  · intro hrpos
    apply min_eq_right
    by_contra hn
    have hpeq : q = A / orientationRate γ := min_eq_left (le_of_not_ge hn)
    change 0 < A - orientationRate γ * q at hrpos
    rw [hpeq, mul_div_cancel₀ _ (ne_of_gt hf), sub_self] at hrpos
    exact lt_irrefl 0 hrpos

end Erdos547.DPRS

#print axioms Erdos547.DPRS.private_residual_budget
