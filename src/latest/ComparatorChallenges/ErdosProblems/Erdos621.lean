/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos621

variable {V : Type*} [Fintype V]

namespace TriangleIndep

open scoped Classical in
def IsTriangleIndependent (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Sym2 V)) : Prop :=
  T ⊆ G.edgeFinset ∧
  ∀ u v w : V, G.Adj u v → G.Adj v w → G.Adj u w →
    ({s(u, v), s(v, w), s(u, w)} ∩ T).card ≤ 1

open scoped Classical in
noncomputable def alpha1 (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.edgeFinset.powerset.filter (IsTriangleIndependent G)).sup Finset.card

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsTriangleFree (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ u v w : V, G.Adj u v → G.Adj v w → G.Adj u w → False

noncomputable def tau1 (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf ((fun F => F.card) ''
    {F : Finset (Sym2 V) | F ⊆ G.edgeFinset ∧
      IsTriangleFree (G.deleteEdges (F : Set (Sym2 V)))})

theorem erdos_621 (G : SimpleGraph V) [DecidableRel G.Adj] :
    4 * (alpha1 G + tau1 G) ≤ (Fintype.card V) ^ 2 := by
  sorry

end TriangleIndep

end Erdos621
