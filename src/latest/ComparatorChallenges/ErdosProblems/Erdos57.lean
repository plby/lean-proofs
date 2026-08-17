import Mathlib

open scoped BigOperators
open Set Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos57

def HasCycleLength {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ v, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = n

end Erdos57

namespace Erdos57

def IsOddCycleLength {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  Odd n ∧ HasCycleLength G n

end Erdos57

namespace Erdos57

noncomputable def oddCycleReciprocal {V : Type*} (G : SimpleGraph V) (n : ℕ) : ℝ :=
  by
    classical
    exact if IsOddCycleLength G n then (n : ℝ)⁻¹ else 0

end Erdos57

namespace Erdos57

theorem erdos_57 {V : Type*} (G : SimpleGraph V)
    (hχ : G.chromaticNumber = ⊤) :
    ¬Summable (oddCycleReciprocal G) := by
  sorry

end Erdos57

end
