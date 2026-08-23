import Mathlib

open Set SimpleGraph
open scoped SimpleGraph

noncomputable section


universe u

namespace Erdos63

variable {V : Type u}

open scoped Classical in
def HasCycleLength (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ x : V, ∃ p : G.Walk x x, p.IsCycle ∧ p.length = n

end Erdos63

namespace Erdos63

open scoped Classical in
theorem erdos_63 {V : Type u} (G : SimpleGraph V)
    (hG : G.chromaticNumber = ⊤) :
    Set.Infinite {n : ℕ | HasCycleLength G (2 ^ n)} := by
  sorry

end Erdos63

end
