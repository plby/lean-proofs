/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Projected weights and variances for two-dimensional sign arrays.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.GaussianPair

namespace Erdos521

open Filter
open scoped BigOperators Topology InnerProductSpace

theorem pair_weight_inner (a b : ℝ) (t : EuclideanSpace ℝ (Fin 2)) :
    ⟪!₂[a, b], t⟫_ℝ = a * t 0 + b * t 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

theorem pair_projected_variance (S : Finset ℕ) (a b : ℕ → ℝ) (t : EuclideanSpace ℝ (Fin 2)) :
    (∑ i ∈ S, ⟪!₂[a i, b i], t⟫_ℝ ^ 2) =
      t 0 ^ 2 * (∑ i ∈ S, a i ^ 2) + 2 * t 0 * t 1 * (∑ i ∈ S, a i * b i) +
        t 1 ^ 2 * (∑ i ∈ S, b i ^ 2) := by
  simp_rw [pair_weight_inner, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem abs_linear_pair_lt {a b u v r : ℝ} (hr : 0 < r)
    (ha : |a| < r / (|u| + |v| + 1)) (hb : |b| < r / (|u| + |v| + 1)) :
    |a * u + b * v| < r := by
  have hden : 0 < |u| + |v| + 1 := by positivity
  have hcut : 0 < r / (|u| + |v| + 1) := div_pos hr hden
  have hcancel : (r / (|u| + |v| + 1)) * (|u| + |v| + 1) = r :=
    div_mul_cancel₀ _ hden.ne'
  calc
    |a * u + b * v| ≤ |a| * |u| + |b| * |v| := by simpa only [abs_mul] using abs_add_le (a * u) (b * v)
    _ ≤ (r / (|u| + |v| + 1)) * (|u| + |v|) := by
      have h₁ := mul_le_mul_of_nonneg_right ha.le (abs_nonneg u)
      have h₂ := mul_le_mul_of_nonneg_right hb.le (abs_nonneg v)
      nlinarith
    _ < r := by nlinarith

theorem pair_projected_weights_small (S : ℕ → Finset ℕ) (a b : ℕ → ℕ → ℝ)
    (ha : ∀ r : ℝ, 0 < r → ∀ᶠ n : ℕ in atTop, ∀ i ∈ S n, |a n i| < r)
    (hb : ∀ r : ℝ, 0 < r → ∀ᶠ n : ℕ in atTop, ∀ i ∈ S n, |b n i| < r)
    (t : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, ∀ i ∈ S n, |⟪!₂[a n i, b n i], t⟫_ℝ| < r := by
  have hcut : 0 < r / (|t 0| + |t 1| + 1) := by positivity
  filter_upwards [ha _ hcut, hb _ hcut] with n hna hnb
  intro i hi
  rw [pair_weight_inner]
  exact abs_linear_pair_lt hr (hna i hi) (hnb i hi)

end Erdos521
