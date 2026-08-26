/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite sums of asymptotic upper bounds.
Formal proof: Codex.
-/
import Mathlib

namespace Erdos521

open Filter
open scoped BigOperators Topology

theorem eventually_finset_sum_le_add {ι : Type*} (S : Finset ι) (f : ι → ℕ → ℝ) (c : ι → ℝ)
    (h : ∀ i ∈ S, ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, f i n ≤ c i + η)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, (∑ i ∈ S, f i n) ≤ (∑ i ∈ S, c i) + η := by
  let e := η / ((S.card : ℝ) + 1)
  have he : 0 < e := by dsimp [e]; positivity
  have hall := S.eventually_all.mpr (fun i hi ↦ h i hi e he)
  filter_upwards [hall] with n hn
  have hsum := Finset.sum_le_sum hn
  have hcancel : e * ((S.card : ℝ) + 1) = η := by
    dsimp [e]
    field_simp
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  nlinarith

theorem eventually_add_le_add_of_bounds {f g : ℕ → ℝ} {a b : ℝ}
    (hf : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, f n ≤ a + η)
    (hg : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, g n ≤ b + η)
    {η : ℝ} (hη : 0 < η) : ∀ᶠ n : ℕ in atTop, f n + g n ≤ a + b + η := by
  filter_upwards [hf (η / 2) (by linarith), hg (η / 2) (by linarith)] with n hn₁ hn₂
  linarith

end Erdos521
