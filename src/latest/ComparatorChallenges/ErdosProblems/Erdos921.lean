/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos921

variable {V : Type u} [Fintype V] [DecidableEq V]

def HasOddCycleAtMost (G : SimpleGraph V) (L : ℕ) : Prop :=
  ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ Odd w.length ∧ w.length ≤ L

def Admissible (k n m : ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin n),
    G.chromaticNumber = (k : ℕ∞) ∧ ¬ HasOddCycleAtMost G m

open scoped Classical in
noncomputable def f (k n : ℕ) : ℕ :=
  Nat.findGreatest (Admissible k n) n

theorem erdos_921 (k : ℕ) (hk : 4 ≤ k) :
    (fun n : ℕ ↦ (f k n : ℝ)) =Θ[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (1 / (((k - 2 : ℕ) : ℝ)))) := by
  sorry

end Erdos921
