/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

noncomputable section

namespace Erdos921

variable {V : Type u} [Fintype V] [DecidableEq V]

open scoped Classical in
def HasOddCycleAtMost (G : SimpleGraph V) (L : ℕ) : Prop :=
  ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ Odd w.length ∧ w.length ≤ L

end Erdos921

namespace Erdos921

open scoped Classical in
def Admissible (k n m : ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin n),
    G.chromaticNumber = (k : ℕ∞) ∧ ¬ HasOddCycleAtMost G m

end Erdos921

namespace Erdos921

open scoped Classical in
def f (k n : ℕ) : ℕ :=
  Nat.findGreatest (Admissible k n) n

end Erdos921

namespace Erdos921

open scoped Classical in
theorem erdos_921 (k : ℕ) (hk : 4 ≤ k) :
    (fun n : ℕ ↦ (f k n : ℝ)) =Θ[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (1 / (((k - 2 : ℕ) : ℝ)))) := by
  sorry

end Erdos921

end
