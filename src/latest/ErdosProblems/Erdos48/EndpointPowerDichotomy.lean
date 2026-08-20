/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.EndpointPowerScale

/-!
# The endpoint-good / exceptional-conductor dichotomy

The Page-excluded power-scale estimate has a particularly simple finite
consequence.  Either the omitted conductor is itself endpoint-good, in which
case every conductor in the range is good, or it is a genuine exceptional
conductor and the total mass of all other conductors is small.
-/

namespace Erdos48

open Filter
open scoped Topology BigOperators

noncomputable section

/-- Along one fixed power scale, eventually either all conductors through the
base are endpoint-good, or one conductor is endpoint-bad and the sum over its
complement is at most `x / 20`. -/
theorem eventually_endpointPowerScale_good_or_exceptional_above (Lmin : ℕ) :
    ∃ L : ℕ, 64 ≤ L ∧ Lmin ≤ L ∧
      ∀ᶠ n : ℕ in atTop,
        (∀ q ∈ Finset.Ioc 1 n,
            primitiveEndpointMass (n ^ L) q ≤
              (((n ^ L : ℕ) : ℝ) / 10)) ∨
          ∃ m₀ ∈ Finset.Ioc 1 n,
            (((n ^ L : ℕ) : ℝ) / 10) <
                primitiveEndpointMass (n ^ L) m₀ ∧
              (∑ q ∈ (Finset.Ioc 1 n).filter (fun q ↦ q ≠ m₀),
                  primitiveEndpointMass (n ^ L) q) ≤
                (((n ^ L : ℕ) : ℝ) / 20) := by
  obtain ⟨L, hL, hLmin, hscale⟩ :=
    eventually_exists_pageExcludedEndpointMass_le_mul_above
      (1 / 20 : ℝ) (by norm_num) Lmin
  refine ⟨L, hL, hLmin, ?_⟩
  filter_upwards [hscale] with n hn
  obtain ⟨m₀, hm₀n, hsum⟩ := hn
  have hsum' :
      (∑ q ∈ (Finset.Ioc 1 n).filter (fun q ↦ q ≠ m₀),
          primitiveEndpointMass (n ^ L) q) ≤
        (((n ^ L : ℕ) : ℝ) / 20) := by
    simpa only [one_div, inv_mul_eq_div] using hsum
  by_cases hm₀ : m₀ ∈ Finset.Ioc 1 n
  · by_cases hm₀Good :
        primitiveEndpointMass (n ^ L) m₀ ≤
          (((n ^ L : ℕ) : ℝ) / 10)
    · left
      intro q hq
      by_cases hqm₀ : q = m₀
      · simpa only [hqm₀] using hm₀Good
      · have hqFilter :
            q ∈ (Finset.Ioc 1 n).filter (fun d ↦ d ≠ m₀) := by
          simp only [Finset.mem_filter]
          exact ⟨hq, hqm₀⟩
        have hqSum : primitiveEndpointMass (n ^ L) q ≤
            ∑ d ∈ (Finset.Ioc 1 n).filter (fun d ↦ d ≠ m₀),
              primitiveEndpointMass (n ^ L) d :=
          Finset.single_le_sum
            (fun d _ ↦ primitiveEndpointMass_nonneg (n ^ L) d) hqFilter
        exact hqSum.trans (hsum'.trans (by
          have hx : (0 : ℝ) ≤ ((n ^ L : ℕ) : ℝ) := by positivity
          linarith))
    · right
      exact ⟨m₀, hm₀, lt_of_not_ge hm₀Good, hsum'⟩
  · left
    intro q hq
    have hqm₀ : q ≠ m₀ := fun h ↦ hm₀ (h ▸ hq)
    have hqFilter :
        q ∈ (Finset.Ioc 1 n).filter (fun d ↦ d ≠ m₀) := by
      simp only [Finset.mem_filter]
      exact ⟨hq, hqm₀⟩
    have hqSum : primitiveEndpointMass (n ^ L) q ≤
        ∑ d ∈ (Finset.Ioc 1 n).filter (fun d ↦ d ≠ m₀),
          primitiveEndpointMass (n ^ L) d :=
      Finset.single_le_sum
        (fun d _ ↦ primitiveEndpointMass_nonneg (n ^ L) d) hqFilter
    exact hqSum.trans (hsum'.trans (by
      have hx : (0 : ℝ) ≤ ((n ^ L : ℕ) : ℝ) := by positivity
      linarith))

/-- Backwards-compatible form with the default lower exponent `64`. -/
theorem eventually_endpointPowerScale_good_or_exceptional :
    ∃ L : ℕ, 64 ≤ L ∧
      ∀ᶠ n : ℕ in atTop,
        (∀ q ∈ Finset.Ioc 1 n,
            primitiveEndpointMass (n ^ L) q ≤
              (((n ^ L : ℕ) : ℝ) / 10)) ∨
          ∃ m₀ ∈ Finset.Ioc 1 n,
            (((n ^ L : ℕ) : ℝ) / 10) <
                primitiveEndpointMass (n ^ L) m₀ ∧
              (∑ q ∈ (Finset.Ioc 1 n).filter (fun q ↦ q ≠ m₀),
                  primitiveEndpointMass (n ^ L) q) ≤
                (((n ^ L : ℕ) : ℝ) / 20) := by
  obtain ⟨L, hL64, _hLmin, hL⟩ :=
    eventually_endpointPowerScale_good_or_exceptional_above 0
  exact ⟨L, hL64, hL⟩

end

end Erdos48
