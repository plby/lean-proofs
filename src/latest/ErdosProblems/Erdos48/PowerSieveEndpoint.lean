/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.EndpointPowerDichotomy
import ErdosProblems.Erdos48.PowerSieveParameters

/-!
# Page's endpoint dichotomy in the integer-power sieve variables

The Page-scale theorem has endpoint `N^L` and controls all conductors through
`N`.  Substituting `N = n^240` makes the endpoint exactly `powerSieveX n L`.
This controls the small-conductor end of the power sieve; the remaining
conductors are handled by Vaughan's mean estimate.
-/

namespace Erdos48

open Filter
open scoped Topology BigOperators

noncomputable section

theorem tendsto_nat_pow_fixed_atTop (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ ↦ n ^ k) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (max 1 b)] with n hn
  exact (le_max_right 1 b).trans hn |>.trans
    (Nat.le_pow hk)

/-- The endpoint-good / exceptional-conductor dichotomy after substituting
the base `n^240`, with an arbitrary prescribed lower bound on the exponent. -/
theorem eventually_powerSieveEndpoint_good_or_exceptional_above (Lmin : ℕ) :
    ∃ L : ℕ, 64 ≤ L ∧ Lmin ≤ L ∧
      ∀ᶠ n : ℕ in atTop,
        (∀ q ∈ Finset.Ioc 1 (n ^ 240),
            primitiveEndpointMass (powerSieveX n L) q ≤
              ((powerSieveX n L : ℕ) : ℝ) / 10) ∨
          ∃ m₀ ∈ Finset.Ioc 1 (n ^ 240),
            ((powerSieveX n L : ℕ) : ℝ) / 10 <
                primitiveEndpointMass (powerSieveX n L) m₀ ∧
              (∑ q ∈ (Finset.Ioc 1 (n ^ 240)).filter (fun q ↦ q ≠ m₀),
                  primitiveEndpointMass (powerSieveX n L) q) ≤
                ((powerSieveX n L : ℕ) : ℝ) / 20 := by
  obtain ⟨L, hL, hLmin, hscale⟩ :=
    eventually_endpointPowerScale_good_or_exceptional_above Lmin
  refine ⟨L, hL, hLmin, ?_⟩
  have hpow : Tendsto (fun n : ℕ ↦ n ^ 240) atTop atTop :=
    tendsto_nat_pow_fixed_atTop 240 (by norm_num)
  filter_upwards [hpow.eventually hscale] with n hn
  simpa only [Set.mem_ofPred_eq, powerSieveX, pow_mul] using hn

/-- Backwards-compatible form with the default exponent lower bound. -/
theorem eventually_powerSieveEndpoint_good_or_exceptional :
    ∃ L : ℕ, 64 ≤ L ∧
      ∀ᶠ n : ℕ in atTop,
        (∀ q ∈ Finset.Ioc 1 (n ^ 240),
            primitiveEndpointMass (powerSieveX n L) q ≤
              ((powerSieveX n L : ℕ) : ℝ) / 10) ∨
          ∃ m₀ ∈ Finset.Ioc 1 (n ^ 240),
            ((powerSieveX n L : ℕ) : ℝ) / 10 <
                primitiveEndpointMass (powerSieveX n L) m₀ ∧
              (∑ q ∈ (Finset.Ioc 1 (n ^ 240)).filter (fun q ↦ q ≠ m₀),
                  primitiveEndpointMass (powerSieveX n L) q) ≤
                ((powerSieveX n L : ℕ) : ℝ) / 20 := by
  obtain ⟨L, hL, _hLmin, hscale⟩ :=
    eventually_powerSieveEndpoint_good_or_exceptional_above 0
  exact ⟨L, hL, hscale⟩

/-- Any nontrivial conductor below the Page base inherits the endpoint bound
from the all-good side of the dichotomy. -/
theorem primitiveEndpointMass_le_of_powerSieveEndpoint_allGood
    {n L d : ℕ}
    (hall : ∀ q ∈ Finset.Ioc 1 (n ^ 240),
      primitiveEndpointMass (powerSieveX n L) q ≤
        ((powerSieveX n L : ℕ) : ℝ) / 10)
    (hd : 1 < d) (hdBase : d ≤ n ^ 240) :
    primitiveEndpointMass (powerSieveX n L) d ≤
      ((powerSieveX n L : ℕ) : ℝ) / 10 := by
  exact hall d (Finset.mem_Ioc.mpr ⟨hd, hdBase⟩)

end

end Erdos48
