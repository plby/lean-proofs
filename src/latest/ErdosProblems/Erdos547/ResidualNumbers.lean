import ErdosProblems.Erdos547.BalancedNumbers
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Solving the residual two-endpoint allocation equations

These scalar identities give a direct completion construction, including
the case of skew one where the usual division by the skew difference is
not available.
-/

namespace Erdos547.DPRS

theorem exists_residual_orientations (u v M γ : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huM : u ≤ M) (hvM : v ≤ M) (hγ : 0 ≤ γ)
    (hlow : γ ≤ 1 → γ * u ≤ v ∧ γ * v ≤ u)
    (hhigh : 1 ≤ γ → u ≤ γ * v ∧ v ≤ γ * u) :
    ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧
      x + γ * y = u ∧ γ * x + y = v ∧ γ * z ≤ u ∧ z ≤ v ∧
      u + v - M ≤ (1 + γ) * z ∧ (γ ≤ 1 → z = v) := by
  rcases lt_trichotomy γ 1 with hlt | heq | hgt
  · obtain ⟨h₁, h₂⟩ := hlow hlt.le
    have hD : 0 < 1 - γ ^ 2 := by nlinarith
    refine ⟨(u - γ * v) / (1 - γ ^ 2), (v - γ * u) / (1 - γ ^ 2), v,
      div_nonneg (sub_nonneg.mpr h₂) hD.le,
      div_nonneg (sub_nonneg.mpr h₁) hD.le, hv, ?_, ?_, h₂, le_rfl, ?_, fun _ ↦ rfl⟩
    · field_simp [ne_of_gt hD]
      ring
    · field_simp [ne_of_gt hD]
      ring
    · nlinarith [mul_nonneg hγ hv]
  · subst γ
    obtain ⟨h₁, h₂⟩ := hlow le_rfl
    have huv : u = v := by linarith
    refine ⟨0, v, v, le_rfl, hv, hv, ?_, ?_, ?_, le_rfl, ?_, fun _ ↦ rfl⟩ <;>
      simp only [one_mul, one_add_one_eq_two, zero_add, mul_zero, huv] <;> linarith
  · obtain ⟨h₁, h₂⟩ := hhigh hgt.le
    have hD : 0 < γ ^ 2 - 1 := by nlinarith
    have hγpos : 0 < γ := by linarith
    have hz : γ * (u / γ) = u := mul_div_cancel₀ u (ne_of_gt hγpos)
    refine ⟨(γ * v - u) / (γ ^ 2 - 1), (γ * u - v) / (γ ^ 2 - 1), u / γ,
      div_nonneg (sub_nonneg.mpr h₁) hD.le,
      div_nonneg (sub_nonneg.mpr h₂) hD.le, div_nonneg hu hγpos.le,
      ?_, ?_, hz.le, (div_le_iff₀ hγpos).mpr (by linarith), ?_, ?_⟩
    · field_simp [ne_of_gt hD]
      ring
    · field_simp [ne_of_gt hD]
      ring
    · have hn : 0 ≤ u / γ := div_nonneg hu hγpos.le
      nlinarith only [hz, hn, hvM]
    · intro hn
      exact (not_le_of_gt hgt hn).elim

theorem residual_ratio_bounds (a₁ a₂ b₁ b₂ M : ℝ)
    (hb₁ : 0 < b₁) (hb₂ : 0 ≤ b₂)
    (hlo : max a₁ a₂ + min b₁ b₂ ≤ M)
    (hhi : M ≤ min a₁ a₂ + max b₁ b₂) :
    0 ≤ M - a₁ ∧ 0 ≤ M - a₂ ∧
      (b₂ / b₁ ≤ 1 → (b₂ / b₁) * (M - a₁) ≤ M - a₂ ∧
        (b₂ / b₁) * (M - a₂) ≤ M - a₁) ∧
      (1 ≤ b₂ / b₁ → M - a₁ ≤ (b₂ / b₁) * (M - a₂) ∧
        M - a₂ ≤ (b₂ / b₁) * (M - a₁)) := by
  have hm : 0 ≤ min b₁ b₂ := le_min hb₁.le hb₂
  have hu : 0 ≤ M - a₁ := by linarith [le_max_left a₁ a₂]
  have hv : 0 ≤ M - a₂ := by linarith [le_max_right a₁ a₂]
  refine ⟨hu, hv, ?_, ?_⟩
  · intro hr
    have hb : b₂ ≤ b₁ := (div_le_one hb₁).mp hr
    rw [min_eq_right hb] at hlo
    rw [max_eq_left hb] at hhi
    have h₁ : b₂ ≤ M - a₁ := by linarith [le_max_left a₁ a₂]
    have h₂ : b₂ ≤ M - a₂ := by linarith [le_max_right a₁ a₂]
    have h₃ : M - a₁ ≤ b₁ := by linarith [min_le_left a₁ a₂]
    have h₄ : M - a₂ ≤ b₁ := by linarith [min_le_right a₁ a₂]
    constructor
    · rw [div_mul_eq_mul_div, div_le_iff₀ hb₁]
      nlinarith [mul_le_mul h₃ h₂ hb₂ hb₁.le]
    · rw [div_mul_eq_mul_div, div_le_iff₀ hb₁]
      nlinarith [mul_le_mul h₄ h₁ hb₂ hb₁.le]
  · intro hr
    have hb : b₁ ≤ b₂ := (one_le_div hb₁).mp hr
    rw [min_eq_left hb] at hlo
    rw [max_eq_right hb] at hhi
    have h₁ : b₁ ≤ M - a₁ := by linarith [le_max_left a₁ a₂]
    have h₂ : b₁ ≤ M - a₂ := by linarith [le_max_right a₁ a₂]
    have h₃ : M - a₁ ≤ b₂ := by linarith [min_le_left a₁ a₂]
    have h₄ : M - a₂ ≤ b₂ := by linarith [min_le_right a₁ a₂]
    constructor
    · rw [div_mul_eq_mul_div, le_div_iff₀ hb₁]
      nlinarith [mul_le_mul h₃ h₂ hb₁.le hb₂]
    · rw [div_mul_eq_mul_div, le_div_iff₀ hb₁]
      nlinarith [mul_le_mul h₄ h₁ hb₁.le hb₂]

theorem exists_completion_coefficients (a₁ a₂ b₁ b₂ M : ℝ)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb₁ : 0 < b₁) (hb₂ : 0 ≤ b₂)
    (hlo : max a₁ a₂ + min b₁ b₂ ≤ M)
    (hhi : M ≤ min a₁ a₂ + max b₁ b₂) :
    ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧
      x + (b₂ / b₁) * y = M - a₁ ∧ (b₂ / b₁) * x + y = M - a₂ ∧
      (b₂ / b₁) * z ≤ M - a₁ ∧ z ≤ M - a₂ ∧
      M - (a₁ + a₂) ≤ (1 + b₂ / b₁) * z ∧ (b₂ / b₁ ≤ 1 → z = M - a₂) := by
  obtain ⟨hu, hv, hl, hh⟩ := residual_ratio_bounds a₁ a₂ b₁ b₂ M hb₁ hb₂ hlo hhi
  obtain ⟨x, y, z, hx, hy, hz, h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
    exists_residual_orientations (M - a₁) (M - a₂) M (b₂ / b₁) hu hv
      (by linarith) (by linarith) (div_nonneg hb₂ hb₁.le) hl hh
  exact ⟨x, y, z, hx, hy, hz, h₁, h₂, h₃, h₄, by linarith, h₆⟩

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_completion_coefficients
