import Mathlib

open Filter Set
open scoped Pointwise Topology

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Set

variable {M : Type*} [AddCommMonoid M]

def IsAsymptoticAddBasisOfOrder (A : Set M) (o : ℕ) : Prop :=
  ∀ᶠ m in cofinite, m ∈ o • A

end Set

namespace Erdos1147

abbrev IsBasis2 (A : Set ℕ) : Prop := A.IsAsymptoticAddBasisOfOrder 2

/-! ## An odd Pell sequence for `√2` -/

end Erdos1147

namespace Erdos1147

noncomputable def circleDist (x : ℝ) : ℝ :=
  ‖(x : AddCircle (1 : ℝ))‖

end Erdos1147

namespace Erdos1147

noncomputable def problemSet (α : ℝ) : Set ℕ :=
  {n | 1 ≤ n ∧ circleDist (α * (n : ℝ) ^ 2) < 1 / Real.log n}

end Erdos1147

namespace Erdos1147

theorem erdos_1147 :
    ¬ ∀ α : ℝ, 0 < α → Irrational α → IsBasis2 (problemSet α) := by
  sorry

end Erdos1147

end
