/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos182.Asymptotics
import ErdosProblems.Erdos182.ExactOrder
import ErdosProblems.Erdos182.Lower
import ErdosProblems.Erdos182.UpperPackaging

/-!
# Erdős Problem 182

For `k ≥ 3`, let `regularExtremalNumber n k` be the maximum number of
edges in a simple graph on `n` labelled vertices which has no nonempty
`k`-regular subgraph.  The resolution of Erdős Problem 182 says that, for
each fixed `k`, this extremal number has order `n * log (log n)`.  In
particular it is eventually at most `n ^ (1 + ε)` for every `ε > 0`.

The exact finite definitions are in `Erdos182.Foundations`; the analytic
translations between two-sided estimates, `Theta` notation, and the
normalized-log formulation `n^(1+o(1))` are in `Erdos182.Asymptotics`.
-/

namespace Erdos182

/-- The exact two-sided estimate resolving Erdős Problem 182.  The constants
may depend on the fixed target degree `k`, while the vertex number tends to
infinity. -/
theorem erdos_182_extremal_bounds (k : ℕ) (hk : 3 ≤ k) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        c * ((n : ℝ) * logLog2 n) ≤ (regularExtremalNumber n k : ℝ) ∧
          (regularExtremalNumber n k : ℝ) ≤
            C * ((n : ℝ) * logLog2 n) := by
  obtain ⟨c, hc, hlower⟩ := prs_extremal_lower
  obtain ⟨C, hC, hupper⟩ := regularExtremalNumber_upper_of_nVertex_forcing
    k (by omega)
    (exists_nVertex_forcing_of_exists_maxDegree_forcing
      (janzer_sudakov_maxDegree_logLog_forcing k hk))
  exact ⟨c, C, hc, hC, (hlower k hk).and hupper⟩

/-- **Erdős Problem 182.**  For every fixed `k ≥ 3`, the maximum number
of edges in an `n`-vertex graph with no nonempty `k`-regular subgraph is
Theta of `n log log n`. -/
theorem erdos_182 (k : ℕ) (hk : 3 ≤ k) :
    (fun n : ℕ ↦ (regularExtremalNumber n k : ℝ))
      =Θ[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) * logLog n) := by
  obtain ⟨c, C, hc, hC, hbounds⟩ := erdos_182_extremal_bounds k hk
  exact regularExtremalNumber_isTheta_logLog_of_bounds k hc hC hbounds

/-- The normalized-log formulation of the answer: the extremal number is
`n^(1+o(1))`. -/
theorem erdos_182_n_pow_one_add_o (k : ℕ) (hk : 3 ≤ k) :
    Filter.Tendsto
      (fun n : ℕ ↦
        Real.log (regularExtremalNumber n k : ℝ) / Real.log (n : ℝ))
      Filter.atTop (nhds 1) := by
  obtain ⟨c, C, hc, hC, hbounds⟩ := erdos_182_extremal_bounds k hk
  exact regularExtremalNumber_normalizedLog_tendsto_one_of_bounds
    k hc hC hbounds

/-- In particular, every positive power saving over a quadratic bound is
eventually available: the extremal number is at most `n^(1+ε)`. -/
theorem erdos_182_eventually_le_n_pow_one_add
    (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (regularExtremalNumber n k : ℝ) ≤ (n : ℝ) ^ (1 + ε) := by
  obtain ⟨c, C, hc, hC, hbounds⟩ := erdos_182_extremal_bounds k hk
  exact regularExtremalNumber_eventually_le_rpow_one_add_of_bounds
    k hc hC hbounds ε hε

end Erdos182

#print axioms Erdos182.erdos_182
#print axioms Erdos182.erdos_182_n_pow_one_add_o
#print axioms Erdos182.erdos_182_eventually_le_n_pow_one_add
