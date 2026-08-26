import Mathlib
import ErdosProblems.Erdos267.Solution

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Erdos267 — Lean scaffold

Formal statement and kernel-checked proof of the problem in `problem.md`
(snapshot root).
-/

namespace Erdos267

/-- The real number represented by the reciprocal-Fibonacci series along
an index sequence `n`.  The zeroth function value represents the problem's
`n₁`.  Mathlib's `Nat.fib` has values `0, 1, 1, 2, ...`, so it agrees with the
problem's Fibonacci indexing at every positive index. -/
noncomputable def reciprocalFibSeries (n : ℕ → ℕ) : ℝ :=
  ∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹

/-- The problem's uniform ratio-gap condition. -/
def HasRatioGap (n : ℕ → ℕ) : Prop :=
  ∃ c : ℝ, 1 < c ∧
    ∀ k : ℕ, c ≤ (n (k + 1) : ℝ) / (n k : ℝ)

/-- A faithful formalization of Erdős Problem 267. -/
theorem erdos_problem_267
    (n : ℕ → ℕ)
    (hpos : ∀ k : ℕ, 0 < n k)
    (hmono : StrictMono n)
    (hgap : HasRatioGap n) :
    Irrational (reciprocalFibSeries n) := by
  obtain ⟨c, hc, hratioDiv⟩ := hgap
  have hratio : ∀ k : ℕ, c * (n k : ℝ) ≤ n (k + 1) := by
    intro k
    have hnk : (0 : ℝ) < n k := by exact_mod_cast hpos k
    exact (le_div_iff₀ hnk).mp (hratioDiv k)
  simpa [reciprocalFibSeries] using
    irrational_reciprocal_fib_of_ratio_gap n hpos hmono c hc hratio

end Erdos267
