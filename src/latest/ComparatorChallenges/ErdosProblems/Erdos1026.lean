/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1026

set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
set_option linter.style.whitespace false
set_option linter.style.cdot false
set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.deprecated false
set_option linter.flexible false
set_option linter.unusedVariables false

set_option aesop.warn.nonterminal false
set_option maxHeartbeats 50000000
noncomputable section AristotleLemmas

end AristotleLemmas

noncomputable section AristotleLemmas

end AristotleLemmas

noncomputable section AristotleLemmas

end AristotleLemmas

noncomputable def IsMonotoneSubseq {n : ℕ} (x : Fin n → ℝ) (m : ℕ) (s : Fin (m + 1) → Fin n) : Prop :=
  StrictMono s ∧
    (Monotone (fun i => x (s i)) ∨ Antitone (fun i => x (s i)))

noncomputable def monoSubseqSumSet {n : ℕ} (x : Fin n → ℝ) : Set ℝ :=
  { r | ∃ (m : ℕ) (s : Fin (m + 1) → Fin n),
      IsMonotoneSubseq x m s ∧ r = ∑ i, x (s i) }

noncomputable def maxMonoSubseqSum {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  sSup (monoSubseqSumSet x)

noncomputable def score {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  maxMonoSubseqSum x / (∑ i, x i)

noncomputable def c_opt (n : ℕ) : ℝ :=
  sInf { r : ℝ |
    ∃ (x : Fin n → ℝ),
      (∀ i, 0 < x i) ∧
      Function.Injective x ∧
      r = score x }
end Erdos1026

namespace Erdos1026

open scoped Classical in
theorem c_opt_eq_k_div_sq_add_a
    (k n : ℕ) (a : ℤ)
    (hk : 1 < k)
    (ha_low : -k < a)
    (ha_high : a ≤ k)
    (hn : (n : ℤ) = k^2 + 1 + 2 * a) :
    c_opt n = (k : ℝ) / (k^2 + a) := by
  sorry

end Erdos1026
