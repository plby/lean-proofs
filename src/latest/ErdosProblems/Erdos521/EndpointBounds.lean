/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Almost-sure control of all roots in a logarithmic endpoint interval.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.EndpointCover

namespace Erdos521

open MeasureTheory Filter
open scoped BigOperators

theorem ae_endpoint_dyadic_bound (C : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᵐ ε ∂sequenceLaw, ∀ᶠ j : ℕ in atTop, ∀ m : ℕ, 2 ^ j ≤ m → m ≤ 2 * 2 ^ j →
      (intervalRootCount ε m (endpointCenter C (2 ^ j)) 1 : ℝ) ≤
        η * Real.log (2 ^ j : ℕ) := by
  classical
  have hlog₄ : 0 < Real.log 4 := Real.log_pos (by norm_num)
  let a := η * Real.log 4 / 48
  have ha : 0 < a := by dsimp [a]; positivity
  have hfinalGeometry : 4 * max (4 * a - a) 0 < (η / 2) * Real.log 4 := by
    rw [max_eq_left (by linarith : 0 ≤ 4 * a - a)]
    dsimp [a]
    nlinarith [mul_pos hη hlog₄]
  obtain ⟨T, hT⟩ := exists_positive_interval_cover ha C
  let τ := η / (2 * ((T.card : ℝ) + 1))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hlocal : ∀ᵐ ε ∂sequenceLaw, ∀ t ∈ T, ∀ᶠ j : ℕ in atTop,
      ∀ m : ℕ, 2 ^ j ≤ m → m ≤ 2 * 2 ^ j →
        (localRootCount ε m (endpointCenter (t : ℝ) (2 ^ j))
          (endpointRadius ((t : ℝ) / 8) (2 ^ j)) : ℝ) < τ * Real.log (2 ^ j : ℕ) := by
    apply T.eventually_all.mpr
    intro t _
    apply ae_endpoint_local_dyadic_bound t.2 (div_pos t.2 (by norm_num))
    rw [max_eq_right (by linarith [t.2] : 4 * ((t : ℝ) / 8) - (t : ℝ) ≤ 0), mul_zero]
    exact mul_pos hτ hlog₄
  have hbudget : (T.card : ℝ) * τ ≤ η / 2 := by
    have hid : ((T.card : ℝ) + 1) * τ = η / 2 := by dsimp [τ]; field_simp
    nlinarith
  filter_upwards [ae_endpoint_local_dyadic_bound ha ha hfinalGeometry, hlocal]
    with ε hfinal hlocals
  filter_upwards [hfinal, T.eventually_all.mpr hlocals, eventually_ge_atTop 1]
    with j hjfinal hjlocals hj
  intro m hm hm'
  have hN : 1 < (2 : ℕ) ^ j := one_lt_pow₀ (by norm_num) (by omega)
  have hlogN : 0 ≤ Real.log (2 ^ j : ℕ) := Real.log_nonneg
    (by exact_mod_cast hN.le)
  have hcount : (intervalRootCount ε m (endpointCenter C (2 ^ j)) 1 : ℝ) ≤
      (localRootCount ε m (endpointCenter a (2 ^ j)) (endpointRadius a (2 ^ j)) : ℝ) +
        ∑ t ∈ T, (localRootCount ε m (endpointCenter (t : ℝ) (2 ^ j))
          (endpointRadius ((t : ℝ) / 8) (2 ^ j)) : ℝ) := by
    exact_mod_cast endpoint_interval_rootCount_le ha T hT hN ε m
  have hsum := Finset.sum_le_sum (fun t ht ↦ (hjlocals t ht m hm hm').le)
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hfinalBound := (hjfinal m hm hm').le
  have hbudget' := mul_le_mul_of_nonneg_right hbudget hlogN
  nlinarith

end Erdos521
