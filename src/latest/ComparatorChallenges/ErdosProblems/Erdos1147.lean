/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Set
open scoped Pointwise Topology

noncomputable section


namespace Set

variable {M : Type*} [AddCommMonoid M]

open scoped Classical in
def IsAsymptoticAddBasisOfOrder (A : Set M) (o : ℕ) : Prop :=
  ∀ᶠ m in cofinite, m ∈ o • A

end Set

namespace Erdos1147

open scoped Classical in
abbrev IsBasis2 (A : Set ℕ) : Prop := A.IsAsymptoticAddBasisOfOrder 2

/-! ## An odd Pell sequence for `√2` -/

end Erdos1147

namespace Erdos1147

open scoped Classical in
noncomputable def circleDist (x : ℝ) : ℝ :=
  ‖(x : AddCircle (1 : ℝ))‖

end Erdos1147

namespace Erdos1147

open scoped Classical in
noncomputable def problemSet (α : ℝ) : Set ℕ :=
  {n | 1 ≤ n ∧ circleDist (α * (n : ℝ) ^ 2) < 1 / Real.log n}

end Erdos1147

namespace Erdos1147

open scoped Classical in
theorem erdos_1147 :
    ¬ ∀ α : ℝ, 0 < α → Irrational α → IsBasis2 (problemSet α) := by
  sorry

end Erdos1147

end
