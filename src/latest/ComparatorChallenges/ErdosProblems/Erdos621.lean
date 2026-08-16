import Mathlib

namespace Erdos621

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Finset SimpleGraph BigOperators

attribute [local instance] Classical.propDecidable

namespace Trigraph

variable {V : Type*} [Fintype V]

end Trigraph

variable {V : Type*} [Fintype V]

namespace TriangleIndep

def IsTriangleIndependent (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Sym2 V)) : Prop :=
  T ⊆ G.edgeFinset ∧
  ∀ u v w : V, G.Adj u v → G.Adj v w → G.Adj u w →
    ({s(u, v), s(v, w), s(u, w)} ∩ T).card ≤ 1

noncomputable def alpha1 (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.edgeFinset.powerset.filter (IsTriangleIndependent G)).sup Finset.card
end TriangleIndep

namespace Trigraph

variable {V : Type*} [Fintype V]

set_option maxHeartbeats 1600000
end Trigraph

namespace Trigraph

variable {V : Type*} [Fintype V]

set_option maxHeartbeats 800000
end Trigraph

namespace Trigraph

variable {V : Type*} [Fintype V]

set_option maxHeartbeats 1600000
end Trigraph

namespace Trigraph

variable {V : Type*} [Fintype V]

set_option maxHeartbeats 1600000
end Trigraph

namespace Trigraph

variable {V : Type*} [Fintype V]

set_option maxHeartbeats 1600000
end Trigraph

namespace Trigraph

variable {V : Type*} [Fintype V]

end Trigraph

namespace TriangleIndep

variable {V : Type*} [Fintype V] [DecidableEq V]

end TriangleIndep

namespace TriangleIndep

variable {V : Type*} [Fintype V] [DecidableEq V]

end TriangleIndep

namespace TriangleIndep

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsTriangleFree (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ u v w : V, G.Adj u v → G.Adj v w → G.Adj u w → False

noncomputable def tau1 (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf ((fun F => F.card) ''
    {F : Finset (Sym2 V) | F ⊆ G.edgeFinset ∧
      IsTriangleFree (G.deleteEdges (F : Set (Sym2 V)))})

theorem erdos_conjecture (G : SimpleGraph V) [DecidableRel G.Adj] :
    4 * (alpha1 G + tau1 G) ≤ (Fintype.card V) ^ 2 := by
  sorry

end TriangleIndep

end Erdos621
