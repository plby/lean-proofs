/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Passing from fixed approximations to a limit by refining the approximation.
Formal proof: Codex.
-/
import Mathlib

namespace Erdos521

open Filter
open scoped Topology

theorem eventually_approximation_bounds {f g M P : ℕ → ℝ} {v B D R : ℝ} (hR : 0 < R)
    (herror : ∀ᶠ j : ℕ in atTop, 0 ≤ f j - g j ∧ f j - g j ≤ R * P j + M j / R ^ 7)
    (hM : ∀ᶠ j : ℕ in atTop, M j ≤ B)
    (hP : ∀ η : ℝ, 0 < η → ∀ᶠ j : ℕ in atTop, P j ≤ D + η)
    (hg : Tendsto g atTop (𝓝 v)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ j : ℕ in atTop, v - η ≤ f j ∧ f j ≤ v + (R * D + B / R ^ 7) + η := by
  have he : 0 < η / (2 * R) := by positivity
  have hcancel : R * (η / (2 * R)) = η / 2 := by field_simp
  filter_upwards [herror, hM, hP _ he,
    hg.eventually (lt_mem_nhds (by linarith : v - η / 2 < v)),
    hg.eventually (gt_mem_nhds (by linarith : v < v + η / 2))] with j hjerr hjM hjP hjlo hjhi
  have hMdiv := div_le_div_of_nonneg_right hjM (pow_nonneg hR.le 7)
  have hPmul := mul_le_mul_of_nonneg_left hjP hR.le
  constructor <;> nlinarith [hjerr.1, hjerr.2]

theorem tendsto_of_refined_approximations {f v e : ℕ → ℝ} {c : ℝ}
    (hv : Tendsto v atTop (𝓝 c)) (he : Tendsto e atTop (𝓝 0))
    (happrox : ∀ N : ℕ, 1 ≤ N → ∀ η : ℝ, 0 < η →
      ∀ᶠ j : ℕ in atTop, v N - η ≤ f j ∧ f j ≤ v N + e N + η) :
    Tendsto f atTop (𝓝 c) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨N, hN₁, hNv⟩ := ((eventually_ge_atTop 1).and (hv.eventually (lt_mem_nhds ha))).exists
    have hη : 0 < (v N - a) / 2 := by linarith
    filter_upwards [happrox N hN₁ _ hη] with j hj
    linarith [hj.1]
  · intro b hb
    have hsum : Tendsto (fun N ↦ v N + e N) atTop (𝓝 c) := by
      simpa only [add_zero] using hv.add he
    obtain ⟨N, hN₁, hNv⟩ := ((eventually_ge_atTop 1).and (hsum.eventually (gt_mem_nhds hb))).exists
    have hη : 0 < (b - (v N + e N)) / 2 := by linarith
    filter_upwards [happrox N hN₁ _ hη] with j hj
    linarith [hj.2]

end Erdos521
