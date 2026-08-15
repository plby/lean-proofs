import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Finite
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos1007

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

attribute [local instance] Classical.propDecidable

open SimpleGraph

def IsUnitDistanceEmbedding {V : Type*} (G : SimpleGraph V) (d : ℕ) (f : V → EuclideanSpace ℝ (Fin d)) : Prop :=
  Function.Injective f ∧ ∀ {u v}, G.Adj u v → dist (f u) (f v) = 1
def HasUnitDistanceEmbedding {V : Type*} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ f : V → EuclideanSpace ℝ (Fin d), IsUnitDistanceEmbedding G d f
noncomputable def GraphDimension {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf { d | HasUnitDistanceEmbedding G d }
end Erdos1007

attribute [local instance] Classical.propDecidable

universe u_1

theorem Erdos1007.erdos_1007 :
    @IsLeast.{0} Nat instLENat
      (@Set.ofPred.{0} Nat fun (n : Nat) ↦
        @Exists.{2} Type fun (V : Type) ↦
          @Exists.{1} (Fintype.{0} V) fun (x : Fintype.{0} V) ↦
            @Exists.{1} (DecidableEq.{1} V) fun (x_1 : DecidableEq.{1} V) ↦
              @Exists.{1} (SimpleGraph.{0} V) fun (G : SimpleGraph.{0} V) ↦
                And
                  (@Eq.{1} Nat (@Erdos1007.GraphDimension.{0} V G)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@Eq.{1} Nat
                    (@Finset.card.{0} (Sym2.{0} V)
                      (@SimpleGraph.edgeFinset.{0} V G
                        (@SimpleGraph.fintypeEdgeSet.{0} V G (@Sym2.instFintype.{0} V x) fun (a b : V) ↦
                          Classical.propDecidable (@SimpleGraph.Adj.{0} V G a b))))
                    n))
      (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
  := by
  sorry
