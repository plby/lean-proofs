import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Order.Lattice.Nat

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
end TriangleIndep

end Erdos621

attribute [local instance] Classical.propDecidable

universe u_1 u_2

theorem Erdos621.TriangleIndep.erdos_conjecture :
    ∀ {V : Type u_2} [inst : Fintype.{u_2} V] [inst_1 : DecidableEq.{u_2 + 1} V]
      (G : SimpleGraph.{u_2} V)
      [inst_2 : @DecidableRel.{u_2 + 1, u_2 + 1} V V (@SimpleGraph.Adj.{u_2} V G)],
      @LE.le.{0} Nat instLENat
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Erdos621.TriangleIndep.alpha1.{u_2} V inst G inst_2)
            (@Erdos621.TriangleIndep.tau1.{u_2} V inst inst_1 G inst_2)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@Fintype.card.{u_2} V inst) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  := by
  let _ := ULift.{u_2, 0} PUnit
  sorry
