/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos751

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace BV

structure Cycle where
  base : V
  walk : G.Walk base base
  isCycle : walk.IsCycle
  len_ge_three : 3 ≤ walk.length

namespace Cycle

def length (C : Cycle (G := G)) : ℕ := C.walk.length

end Cycle

end BV

namespace Main

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem erdos_751_strong [Finite V]
    (hχ : (4 : ℕ∞) ≤ G.chromaticNumber) :
    ∃ C1 C2 : BV.Cycle (G := G),
      Nat.dist (BV.Cycle.length (G := G) C1) (BV.Cycle.length (G := G) C2) = 1 ∨
      Nat.dist (BV.Cycle.length (G := G) C1) (BV.Cycle.length (G := G) C2) = 2 := by
  sorry

end Main

end Erdos751
