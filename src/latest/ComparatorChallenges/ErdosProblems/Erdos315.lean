/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos315

def generalized_sylvester (n : ℕ) : ℕ → ℕ
| 0 => n + 1
| (i + 1) => (generalized_sylvester n i)^2 - (generalized_sylvester n i) + 1
noncomputable def sylvester_seq_pow (n : ℕ) (i : ℕ) : ℝ :=
  (generalized_sylvester n i : ℝ) ^ ((1 / 2 : ℝ) ^ (i + 1))
def sylvester : ℕ → ℕ
| 0 => 2
| (i + 1) => (sylvester i)^2 - (sylvester i) + 1
noncomputable def usual_sylvester_seq_pow (i : ℕ) : ℝ :=
  (sylvester i : ℝ) ^ ((1 / 2 : ℝ) ^ (i + 1))
noncomputable def vardi_constant : ℝ :=
  Filter.atTop.limUnder usual_sylvester_seq_pow
end Erdos315

namespace Erdos315

open scoped Classical in
theorem erdos_315 (a : ℕ → ℕ)
  (h_pos : ∀ i, 0 < a i)
  (h_mono : Monotone a)
  (h_sum : ∑' i, (1 : ℝ) / a i = 1)
  (h_neq : ∃ i, a i ≠ sylvester i) :
  Filter.liminf (fun i => (a i : ℝ) ^ ((1 / 2 : ℝ) ^ (i + 1))) Filter.atTop < vardi_constant := by
  sorry

end Erdos315
