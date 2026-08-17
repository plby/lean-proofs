import Mathlib

open Filter Real
open scoped ArithmeticFunction.omega BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

namespace UnitFractions

def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n

end UnitFractions

namespace Erdos300

open UnitFractions

def AvoidsOne (A : Finset ℕ) : Prop :=
  ∀ B : Finset ℕ, B ⊆ A → rec_sum B ≠ 1

end Erdos300

namespace Erdos300

noncomputable def candidateSets (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 N).powerset.filter AvoidsOne

end Erdos300

namespace Erdos300

noncomputable def erdos300Max (N : ℕ) : ℕ :=
  (candidateSets N).sup Finset.card

end Erdos300

namespace Erdos300

theorem erdos300 :
    Tendsto (fun N : ℕ => (erdos300Max N : ℝ) / (N : ℝ)) atTop
      (𝓝 (1 - 1 / Real.exp 1)) := by
  sorry

end Erdos300

end
