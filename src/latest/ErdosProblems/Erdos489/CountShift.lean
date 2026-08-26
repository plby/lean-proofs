import ErdosProblems.Erdos489.CountLinear

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open Filter
open scoped Topology

/-- A square-root-little-o counting function remains negligible after any
fixed additive shift when divided by the original variable. -/
theorem tendsto_count_add_div
    (p : ℕ → Prop) [DecidablePred p]
    (h : (fun n : ℕ => (Nat.count p n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ)))
    (c : ℕ) :
    Tendsto (fun x : ℕ => (Nat.count p (x + c) : ℝ) / (x : ℝ))
      atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun x => by
      have hnonneg : (0 : ℝ) ≤ (Nat.count p (x + c) : ℝ) / (x : ℝ) := by positivity
      linarith
  · intro b hb
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / b)
    have hNpos : 0 < N := by
      have htwo : (0 : ℝ) < 2 / b := by positivity
      exact_mod_cast (lt_trans htwo hN)
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp
      (eventually_mul_count_le_of_isLittleO_sqrt p h N hNpos)
    filter_upwards [eventually_ge_atTop (max N0 (max c 1))] with x hx
    have hxN0 : N0 ≤ x + c := le_trans (le_trans (le_max_left _ _) hx) (Nat.le_add_right x c)
    have hlin := hN0 (x + c) hxN0
    have hxc : x + c ≤ 2 * x := by
      have hcx : c ≤ x := le_trans (le_max_left c 1) (le_trans (le_max_right N0 _) hx)
      omega
    have hlinR : (N : ℝ) * (Nat.count p (x + c) : ℝ) ≤ 2 * (x : ℝ) := by
      exact_mod_cast hlin.trans hxc
    have hxpos : (0 : ℝ) < x := by
      have : 1 ≤ x := le_trans (le_max_right c 1) (le_trans (le_max_right N0 _) hx)
      exact_mod_cast this
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hNb : (2 : ℝ) < b * N := by
      have := hN
      rw [div_lt_iff₀ hb] at this
      nlinarith
    rw [div_lt_iff₀ hxpos]
    nlinarith

end Erdos489
