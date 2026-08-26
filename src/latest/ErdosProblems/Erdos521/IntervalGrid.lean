/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A finite grid for the root-repulsion union bound.
Formal proof: Codex.
-/
import Mathlib

namespace Erdos521

noncomputable def intervalGrid (a b : ℝ) (M : ℕ) (i : Fin (M + 1)) : ℝ :=
  min b (a + (i : ℕ) / (M : ℝ))

theorem intervalGrid_mem {a b : ℝ} (hab : a ≤ b) (M : ℕ) (i : Fin (M + 1)) :
    intervalGrid a b M i ∈ Set.Icc a b := by
  refine ⟨le_min hab ?_, min_le_left _ _⟩
  exact le_add_of_nonneg_right (by positivity)

theorem intervalGrid_covers {a b : ℝ} (hab : b - a ≤ 1) (M : ℕ) (hM : 0 < M)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    ∃ i : Fin (M + 1), |intervalGrid a b M i - x| ≤ (M : ℝ)⁻¹ := by
  have hM₀ : (0 : ℝ) < M := by exact_mod_cast hM
  let q := (M : ℝ) * (x - a)
  have hq₀ : 0 ≤ q := mul_nonneg hM₀.le (sub_nonneg.mpr hx.1)
  have hqM : q ≤ M := by
    have hxa : x - a ≤ 1 := (sub_le_sub_right hx.2 a).trans hab
    exact (mul_le_mul_of_nonneg_left hxa hM₀.le).trans_eq (mul_one _)
  have hkM : ⌈q⌉₊ ≤ M := Nat.ceil_le.mpr hqM
  let i : Fin (M + 1) := ⟨⌈q⌉₊, by omega⟩
  have hlow : x ≤ a + (i : ℕ) / (M : ℝ) := by
    have hceil : q ≤ ((i : ℕ) : ℝ) := Nat.le_ceil _
    have hdiv := (le_div_iff₀ hM₀).mpr
      (show (x - a) * M ≤ ((i : ℕ) : ℝ) by simpa only [q, mul_comm] using hceil)
    linarith
  have hhigh : ((i : ℕ) : ℝ) ≤ (M : ℝ) * (x - a) + 1 :=
    (Nat.ceil_lt_add_one hq₀).le
  have hdist : a + (i : ℕ) / (M : ℝ) - x ≤ (M : ℝ)⁻¹ := by
    have hdiv := div_le_div_of_nonneg_right hhigh hM₀.le
    have hid : ((M : ℝ) * (x - a) + 1) / M = x - a + (M : ℝ)⁻¹ := by field_simp
    rw [hid] at hdiv
    linarith
  refine ⟨i, ?_⟩
  have hyx : x ≤ intervalGrid a b M i := le_min hx.2 hlow
  rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
  exact (sub_le_sub_right (min_le_right _ _) x).trans hdist

end Erdos521
