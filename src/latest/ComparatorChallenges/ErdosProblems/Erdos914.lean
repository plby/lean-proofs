/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos914

namespace HajnalSzemeredi

section

variable {V : Type*} [Fintype V] [DecidableEq V]

def HasDisjointCliques (G : SimpleGraph V) (r m : ℕ) : Prop :=
  ∃ f : Fin m → Finset V,
    (∀ i, (f i).card = r) ∧
    (∀ i, ∀ v ∈ f i, ∀ w ∈ f i, v ≠ w → G.Adj v w) ∧
    (∀ i j, i ≠ j → Disjoint (f i) (f j))
end

theorem erdos_914 {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r m : ℕ) (hr : 1 ≤ r) (hcard : Fintype.card V = r * m)
    (hmin : m * (r - 1) ≤ G.minDegree) :
    HasDisjointCliques G r m := by
  sorry

end HajnalSzemeredi

end Erdos914
