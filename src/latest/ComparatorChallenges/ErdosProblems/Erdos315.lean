/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos315

def sylvester (i : ℕ) : ℕ :=
  Nat.rec 2 (fun _ previous ↦ previous ^ 2 - previous + 1) i
noncomputable def usual_sylvester_seq_pow (i : ℕ) : ℝ :=
  (sylvester i : ℝ) ^ ((1 / ((2 : ℕ) : ℝ) : ℝ) ^ (i + 1))
noncomputable def vardi_constant : ℝ :=
  Filter.atTop.limUnder usual_sylvester_seq_pow

theorem erdos_315 (a : ℕ → ℕ)
  (h_pos : ∀ i, 0 < a i)
  (h_mono : Monotone a)
  (h_sum : ∑' i, (1 : ℝ) / a i = 1)
  (h_neq : ∃ i, a i ≠ sylvester i) :
  Filter.liminf (fun i => (a i : ℝ) ^ ((1 / ((2 : ℕ) : ℝ) : ℝ) ^ (i + 1))) Filter.atTop < vardi_constant := by
  sorry

end Erdos315
