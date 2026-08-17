import Mathlib

open Filter Real
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace UnitFractions

def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n

end UnitFractions

namespace Erdos305

def HasBoundedExpansion (a b B : ℕ) : Prop :=
  ∃ E : Finset ℕ,
    0 ∉ E ∧
    (∀ n ∈ E, n ≤ B) ∧
    UnitFractions.rec_sum E = (a : ℚ) / b

end Erdos305

namespace Erdos305

def D (a b : ℕ) : ℕ :=
  sInf {B : ℕ | HasBoundedExpansion a b B}

end Erdos305

namespace Erdos305

def Dmax (b : ℕ) : ℕ :=
  (Finset.Ico 1 b).sup fun a ↦ D a b

end Erdos305

namespace Erdos305

def Erdos305Answer : Prop :=
  ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ b : ℕ in atTop,
        (Dmax b : ℝ) ≤ C * b * (log b) ^ (1 + δ b)

end Erdos305

namespace Erdos305

theorem erdos305 : Erdos305Answer := by
  sorry

end Erdos305

end
