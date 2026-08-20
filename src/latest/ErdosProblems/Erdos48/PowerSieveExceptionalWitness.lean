/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.EndpointPowerScale
import ErdosProblems.Erdos48.PowerSieveParameters

/-!
# Witness-preserving Page endpoint dichotomies

The finite argument turning a Page-excluded endpoint-mass estimate into an
all-good/exceptional dichotomy is independent of the analytic estimate.
This module records that argument while retaining an actual primitive real
zero at the exceptional conductor.

The analytic Page-exclusion and endpoint-scale constructions now preserve
the witness, while their original public interfaces remain available as
backwards-compatible projections.
-/

namespace Erdos48

open Filter
open scoped Topology BigOperators

noncomputable section

/-- The finite witness-preserving dichotomy.  If the omitted conductor is
good (or is outside the conductor interval), the small complementary sum
makes every conductor good.  If it is bad, membership in `Ioc 1 Q` rules
out the empty-window value `m₀ = 0`, leaving the actual Page zero. -/
theorem endpoint_good_or_exceptional_with_pageWitness
    {Q x m₀ : ℕ} {c : ℝ}
    (_hm₀Q : m₀ ≤ Q)
    (hsum :
      (∑ q ∈ (Finset.Ioc 1 Q).filter (fun q ↦ q ≠ m₀),
          primitiveEndpointMass x q) ≤ ((x : ℝ) / 20))
    (hwitness : m₀ = 0 ∨ PageExceptionalWitness Q m₀ c) :
    (∀ q ∈ Finset.Ioc 1 Q,
        primitiveEndpointMass x q ≤ (x : ℝ) / 10) ∨
      ∃ m ∈ Finset.Ioc 1 Q,
        (x : ℝ) / 10 < primitiveEndpointMass x m ∧
          (∑ q ∈ (Finset.Ioc 1 Q).filter (fun q ↦ q ≠ m),
              primitiveEndpointMass x q) ≤ ((x : ℝ) / 20) ∧
          PageExceptionalWitness Q m c := by
  by_cases hm₀ : m₀ ∈ Finset.Ioc 1 Q
  · by_cases hm₀Good :
        primitiveEndpointMass x m₀ ≤ (x : ℝ) / 10
    · left
      intro q hq
      by_cases hqm₀ : q = m₀
      · simpa only [hqm₀] using hm₀Good
      · have hqFilter :
            q ∈ (Finset.Ioc 1 Q).filter (fun d ↦ d ≠ m₀) := by
          simp only [Finset.mem_filter]
          exact ⟨hq, hqm₀⟩
        have hqSum : primitiveEndpointMass x q ≤
            ∑ d ∈ (Finset.Ioc 1 Q).filter (fun d ↦ d ≠ m₀),
              primitiveEndpointMass x d :=
          Finset.single_le_sum
            (fun d _ ↦ primitiveEndpointMass_nonneg x d) hqFilter
        exact hqSum.trans (hsum.trans (by
          have hx : (0 : ℝ) ≤ (x : ℝ) := by positivity
          linarith))
    · right
      have hw : PageExceptionalWitness Q m₀ c := by
        rcases hwitness with hzero | hw
        · have hm₀gt := (Finset.mem_Ioc.mp hm₀).1
          omega
        · exact hw
      exact ⟨m₀, hm₀, lt_of_not_ge hm₀Good, hsum, hw⟩
  · left
    intro q hq
    have hqm₀ : q ≠ m₀ := fun h ↦ hm₀ (h ▸ hq)
    have hqFilter :
        q ∈ (Finset.Ioc 1 Q).filter (fun d ↦ d ≠ m₀) := by
      simp only [Finset.mem_filter]
      exact ⟨hq, hqm₀⟩
    have hqSum : primitiveEndpointMass x q ≤
        ∑ d ∈ (Finset.Ioc 1 Q).filter (fun d ↦ d ≠ m₀),
          primitiveEndpointMass x d :=
      Finset.single_le_sum
        (fun d _ ↦ primitiveEndpointMass_nonneg x d) hqFilter
    exact hqSum.trans (hsum.trans (by
      have hx : (0 : ℝ) ≤ (x : ℝ) := by positivity
      linarith))

/-- Unconditional witness-preserving endpoint dichotomy on a power scale,
with an arbitrary prescribed lower bound on the exponent. -/
theorem eventually_endpointPowerScale_good_or_exceptional_with_pageWitness_above
    (Lmin : ℕ) :
    ∃ cPage : ℝ, 0 < cPage ∧
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
                  (((n ^ L : ℕ) : ℝ) / 20) ∧
                PageExceptionalWitness n m₀ cPage := by
  obtain ⟨cPage, hcPage, L, hL64, hLmin, hscale⟩ :=
    eventually_exists_pageExcludedEndpointMass_le_mul_above_with_witness
      (1 / 20 : ℝ) (by norm_num) Lmin
  refine ⟨cPage, hcPage, L, hL64, hLmin, ?_⟩
  filter_upwards [hscale] with n hn
  obtain ⟨m₀, hm₀, hsum, hwitness⟩ := hn
  have hsum' :
      (∑ q ∈ (Finset.Ioc 1 n).filter (fun q ↦ q ≠ m₀),
          primitiveEndpointMass (n ^ L) q) ≤
        (((n ^ L : ℕ) : ℝ) / 20) := by
    simpa only [one_div, inv_mul_eq_div] using hsum
  exact endpoint_good_or_exceptional_with_pageWitness hm₀ hsum' hwitness

/-- The unconditional witness-preserving dichotomy after the substitution
`N = n^240` used by the power sieve. -/
theorem eventually_powerSieveEndpoint_good_or_exceptional_with_pageWitness_above
    (Lmin : ℕ) :
    ∃ cPage : ℝ, 0 < cPage ∧
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
                  ((powerSieveX n L : ℕ) : ℝ) / 20 ∧
                PageExceptionalWitness (n ^ 240) m₀ cPage := by
  obtain ⟨cPage, hcPage, L, hL64, hLmin, hendpoint⟩ :=
    eventually_endpointPowerScale_good_or_exceptional_with_pageWitness_above Lmin
  refine ⟨cPage, hcPage, L, hL64, hLmin, ?_⟩
  have hpow : Tendsto (fun n : ℕ ↦ n ^ 240) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (max 1 b)] with n hn
    exact (le_max_right 1 b).trans hn |>.trans
      (Nat.le_pow (by norm_num : 0 < (240 : ℕ)))
  filter_upwards [hpow.eventually hendpoint] with n hn
  simpa only [Set.mem_ofPred_eq, powerSieveX, pow_mul] using hn

/-- Default lower-bound specialization of the witness-preserving power-sieve
endpoint dichotomy. -/
theorem eventually_powerSieveEndpoint_good_or_exceptional_with_pageWitness :
    ∃ cPage : ℝ, 0 < cPage ∧
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
                  ((powerSieveX n L : ℕ) : ℝ) / 20 ∧
                PageExceptionalWitness (n ^ 240) m₀ cPage := by
  obtain ⟨cPage, hcPage, L, hL64, _hLmin, hmain⟩ :=
    eventually_powerSieveEndpoint_good_or_exceptional_with_pageWitness_above 0
  exact ⟨cPage, hcPage, L, hL64, hmain⟩

end

end Erdos48
