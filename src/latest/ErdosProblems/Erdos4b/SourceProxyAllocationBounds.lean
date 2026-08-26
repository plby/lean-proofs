/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceIntervalAllocation
import ErdosProblems.Erdos4b.ResidualPrimeFiberMertens

/-!
# Rounded allocation lengths and exact proxy cancellation

The common slack guarantees the analytic minimum interval length. Its
cost and the rounding cost are retained in the total length estimate.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def sourceRequestedIntervalLength (ρ T L R slack : ℝ) : ℕ :=
  ⌈ρ * T / (L * R) + slack⌉₊

theorem sourceRequestedIntervalLength_ge_proxy {ρ T L R slack : ℝ} (hslack : 0 ≤ slack) :
    ρ * T / (L * R) ≤ sourceRequestedIntervalLength ρ T L R slack :=
  (le_add_of_nonneg_right hslack).trans (Nat.le_ceil _)

theorem sourceRequestedIntervalLength_ge_slack {ρ T L R slack : ℝ}
    (hρ : 0 ≤ ρ) (hT : 0 ≤ T) (hL : 0 ≤ L) (hR : 0 ≤ R) :
    slack ≤ sourceRequestedIntervalLength ρ T L R slack :=
  (le_add_of_nonneg_left (div_nonneg (mul_nonneg hρ hT) (mul_nonneg hL hR))).trans
    (Nat.le_ceil _)

theorem sourceRequestedIntervalLength_le {ρ T L R slack : ℝ}
    (hρ : 0 ≤ ρ) (hT : 0 ≤ T) (hL : 0 ≤ L) (hR : 0 ≤ R) (hslack : 0 ≤ slack) :
    (sourceRequestedIntervalLength ρ T L R slack : ℝ) ≤ ρ * T / (L * R) + slack + 1 := by
  exact (Nat.ceil_lt_add_one (add_nonneg (div_nonneg (mul_nonneg hρ hT)
    (mul_nonneg hL hR)) hslack)).le

theorem sum_sourceRequestedIntervalLength_le
    (E : Finset ℕ) (T R : ℕ → ℝ) {ρ L slack : ℝ}
    (hρ : 0 ≤ ρ) (hL : 0 ≤ L) (hslack : 0 ≤ slack)
    (hT : ∀ m ∈ E, 0 ≤ T m) (hR : ∀ m ∈ E, 0 ≤ R m) :
    (∑ m ∈ E, (sourceRequestedIntervalLength ρ (T m) L (R m) slack : ℝ)) ≤
      ρ / L * (∑ m ∈ E, T m / R m) + E.card * (slack + 1) := by
  calc
    _ ≤ ∑ m ∈ E, (ρ * T m / (L * R m) + slack + 1) :=
      Finset.sum_le_sum fun m hm ↦ sourceRequestedIntervalLength_le hρ (hT m hm) hL (hR m hm) hslack
    _ = ∑ m ∈ E, (ρ / L * (T m / R m) + (slack + 1)) := by
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]

theorem proxy_interval_coverage_lower
    {V L R T I length count M coverage ρ : ℝ}
    (hV : 0 < V) (hL : 0 < L) (hR : 0 < R) (hT : 0 < T) (hI : 0 < I)
    (hM : 0 ≤ M) (hlength : ρ * T / (L * R) ≤ length)
    (hcount : length / (2 * V) ≤ count)
    (hcoverage : V * L * R * count / (8 * I * T) * M ≤ coverage) :
    ρ * M / (16 * I) ≤ coverage := by
  have hc := (div_le_div_of_nonneg_right hlength (by positivity : 0 ≤ 2 * V)).trans hcount
  calc
    _ = (V * L * R / (8 * I * T)) * ((ρ * T / (L * R)) / (2 * V)) * M := by
      field_simp
      ring
    _ ≤ (V * L * R / (8 * I * T)) * count * M :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by positivity)) hM
    _ = V * L * R * count / (8 * I * T) * M := by ring
    _ ≤ _ := hcoverage

end

end Erdos4b
