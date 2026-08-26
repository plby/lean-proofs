/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Released under Apache 2.0 license as described in the file LICENSE.
Formalization of Stijn Cambie and Andrea Freschi,
"A general bound on R(C_k,H)", arXiv:2606.11174v1 (9 June 2026).
The formal proofs adapt and extend the graph infrastructure in this repository.
-/
import ErdosProblems.Erdos569.Cycles
import ErdosProblems.Erdos569.C4

/-!
# Erdős Problem 569: the sharp odd-cycle coefficient

For every `r ≥ 1`, the least coefficient in
`R(C_(2r+1),H) ≤ c * e(H)` is `2r+1`, attained by `H = K₂`.
All graph copies are ordinary, non-induced copies, using `Erdos79.GraphCode`
and its usual least Ramsey number. The stronger manuscript bound
`R(C_k,H) ≤ (k-1)m+1` holds for every `k ≥ 3`. The empty graph is included;
the comparison `(k-1)m+1 ≤ km` requires `m ≥ 1`, and its linear Ramsey bound
is proved separately when `m = 0`.

Source: https://arxiv.org/abs/2606.11174
Problem: https://www.erdosproblems.com/569
-/

namespace Erdos569

open Erdos79 Erdos570

/-- The manuscript's bound, including every short-cycle case. -/
theorem cycle_bound {k : ℕ} (hk : 3 ≤ k)
    (H : GraphCode) (hH : NoIsolated H) :
    graphRamseyNumber (cycleCode k) H ≤ (k - 1) * H.edgeCount + 1 := by
  apply graphRamseyNumber_le_of_ramseyAt
  by_cases hk3 : k = 3
  · subst k
    exact ramseyAt_triangle H hH
  by_cases hk4 : k = 4
  · subst k
    exact ramseyAt_c4 H hH
  exact ramseyAt_cycle_ge_five (by omega) H hH

/-- The two upper bounds in the manuscript, with the necessary nonempty
edge hypothesis for the second numerical comparison. -/
theorem cycle_bound_chain {k : ℕ} (hk : 3 ≤ k)
    (H : GraphCode) (hH : NoIsolated H) (hm : 1 ≤ H.edgeCount) :
    graphRamseyNumber (cycleCode k) H ≤ (k - 1) * H.edgeCount + 1 ∧
      (k - 1) * H.edgeCount + 1 ≤ k * H.edgeCount := by
  refine ⟨cycle_bound hk H hH, ?_⟩
  have hk' : k = k - 1 + 1 := by omega
  conv_rhs => rw [hk', Nat.add_mul, one_mul]
  omega

/-- The linear bound includes the empty target, for which the Ramsey number
is zero. The auxiliary inequality with `+1` needs a positive edge count. -/
theorem cycle_linear_bound {k : ℕ} (hk : 3 ≤ k)
    (H : GraphCode) (hH : NoIsolated H) :
    graphRamseyNumber (cycleCode k) H ≤ k * H.edgeCount := by
  by_cases hm : H.edgeCount = 0
  · apply graphRamseyNumber_le_of_ramseyAt
    intro C
    right
    have hn : H.vertexCount = 0 := by
      have := hH.vertexCount_le_twice_edgeCount
      omega
    let : IsEmpty (Fin H.vertexCount) := by rw [hn]; infer_instance
    exact SimpleGraph.IsContained.of_isEmpty
  · exact (cycle_bound hk H hH).trans (cycle_bound_chain hk H hH (by omega)).2

/-- No smaller real coefficient works uniformly, for any cycle length. -/
theorem odd_cycle_coefficient_lower_bound {r : ℕ} {c : ℝ}
    (h : ∀ H : GraphCode, NoIsolated H →
      (graphRamseyNumber (cycleCode (2 * r + 1)) H : ℝ) ≤ c * H.edgeCount) :
    ((2 * r + 1 : ℕ) : ℝ) ≤ c :=
  coefficient_lower_bound h

/-- The original odd-cycle upper bound, including lengths three and five. -/
theorem odd_cycle_bound {r : ℕ} (hr : 1 ≤ r)
    (H : GraphCode) (hH : NoIsolated H) :
    graphRamseyNumber (cycleCode (2 * r + 1)) H ≤ (2 * r + 1) * H.edgeCount :=
  cycle_linear_bound (by omega) H hH

/-- Erdős Problem 569: the least real coefficient is the odd cycle length.
The upper bound is unconditional; the lower bound uses the one-edge graph. -/
theorem erdos569 (r : ℕ) (hr : 1 ≤ r) :
    IsLeast {c : ℝ | ∀ H : GraphCode, NoIsolated H →
      (graphRamseyNumber (cycleCode (2 * r + 1)) H : ℝ) ≤ c * H.edgeCount}
      ((2 * r + 1 : ℕ) : ℝ) := by
  constructor
  · intro H hH
    exact_mod_cast odd_cycle_bound hr H hH
  · intro c hc
    exact odd_cycle_coefficient_lower_bound hc

/-- The sharp odd-cycle Ramsey coefficient from Erdős problem 569. -/
theorem erdos_569 (r : ℕ) (hr : 1 ≤ r) :
    IsLeast {c : ℝ | ∀ H : GraphCode, NoIsolated H →
      (graphRamseyNumber (cycleCode (2 * r + 1)) H : ℝ) ≤ c * H.edgeCount}
      ((2 * r + 1 : ℕ) : ℝ) :=
  erdos569 r hr

end Erdos569

#print axioms Erdos569.cycle_bound
-- [propext, Classical.choice, Quot.sound]
#print axioms Erdos569.cycle_linear_bound
-- [propext, Classical.choice, Quot.sound]
#print axioms Erdos569.odd_cycle_coefficient_lower_bound
-- [propext, Classical.choice, Quot.sound]
#print axioms Erdos569.erdos569
-- [propext, Classical.choice, Quot.sound]
