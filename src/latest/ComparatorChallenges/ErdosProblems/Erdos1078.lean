/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1078

def IsPartite {I : Type u} {V : Type v} (G : SimpleGraph V) (color : V → I) : Prop :=
  ∀ ⦃x y⦄, G.Adj x y → color x ≠ color y

noncomputable def neighbors {V : Type v} [Fintype V]
    (G : SimpleGraph V) (x : V) : Finset V := by
  classical
  exact Finset.univ.filter fun y ↦ G.Adj x y

noncomputable def graphDegree {V : Type v} [Fintype V]
    (G : SimpleGraph V) (x : V) : ℕ := (neighbors G x).card

def IsCliqueTransversal {r n : ℕ} (G : SimpleGraph (Fin r × Fin n))
    (f : Fin r → Fin r × Fin n) : Prop :=
  (∀ i, (f i).1 = i) ∧ ∀ i j, i ≠ j → G.Adj (f i) (f j)

def HasTransversalKr {r n : ℕ} (G : SimpleGraph (Fin r × Fin n)) : Prop :=
  ∃ f : Fin r → Fin r × Fin n, IsCliqueTransversal G f

theorem erdos_1078 {r n : ℕ} (hr : 2 ≤ r) (hn : 0 < n)
    (G : SimpleGraph (Fin r × Fin n))
    (hpart : IsPartite G Prod.fst)
    (hdegree : ∀ x,
      2 * (r - 1) * ((r - 1) * n - graphDegree G x) < r * n) :
    HasTransversalKr G := by
  sorry

end Erdos1078
