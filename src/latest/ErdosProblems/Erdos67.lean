/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos67.MRRealPrefixCompleteStability
import ErdosProblems.Erdos67.SignSequence
import ErdosProblems.Erdos67.CommonEndpointCounterexample

/-!
# Erdős Problem 67: unbounded homogeneous discrepancy

The stationary proof constructs a joint sign-and-residue law from a hypothetical
bounded-discrepancy sequence. Conditional dilation and finite entropy give a
uniform harmonic prime correlation budget. The correlation spectrum has finite
energy and no atoms. Wiener averaging and the proved prime-pair sieve then force
every nonzero correlation to vanish, contradicting the uniform block moment bound.

The earlier multiplicative-function development and the common-endpoint
counterexample are preserved. The latter allows its coloring to depend on the
endpoint and is not a counterexample to the theorem below.
-/

open scoped BigOperators

/-- Every sign sequence has arbitrarily large homogeneous progression sums. -/
theorem erdos_67 (f : ℕ → ℤ) (hf : ∀ n, f n = -1 ∨ f n = 1)
    (C : ℝ) (hC : 0 < C) :
    ∃ d m : ℕ, 1 ≤ d ∧ 1 ≤ m ∧
      C < |((∑ k ∈ Finset.Icc 1 m, f (k * d) : ℤ) : ℝ)| := by
  obtain ⟨d, m, hd, hm, hgt⟩ := Erdos67.int_sign_unbounded_discrepancy f hf C hC.le
  refine ⟨d, m, hd, hm, ?_⟩
  have he : (∑ k ∈ Finset.range m, f ((k + 1) * d)) =
      ∑ k ∈ Finset.Icc 1 m, f (k * d) := by
    apply Finset.sum_bij (fun k _ ↦ k + 1)
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Icc]
      omega
    · intro a _ b _ hab
      omega
    · intro b hb
      simp only [Finset.mem_Icc] at hb
      refine ⟨b - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro _ _
      rfl
  rwa [he] at hgt

#print axioms erdos_67
