import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Erdos905

open SimpleGraph

namespace ErdosProblems.P905

variable {V : Type*} [Fintype V]

noncomputable def triangleDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V) : ℕ :=
  Sym2.lift
    ⟨fun u v => Fintype.card (G.commonNeighbors u v),
     fun u v => by simp [G.commonNeighbors_symm]⟩ e
end ErdosProblems.P905

end Erdos905

attribute [local instance] Classical.propDecidable

universe u_1

theorem Erdos905.ErdosProblems.P905.erdos_905 :
    ∀ {V : Type u_1} [inst : Fintype.{u_1} V] (G : SimpleGraph.{u_1} V)
      [inst_1 : @DecidableRel.{u_1 + 1, u_1 + 1} V V (@SimpleGraph.Adj.{u_1} V G)],
      @LT.lt.{0} Nat instLTNat
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@Fintype.card.{u_1} V inst)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (@Finset.card.{u_1} (Sym2.{u_1} V)
            (@SimpleGraph.edgeFinset.{u_1} V G
              (@SimpleGraph.fintypeEdgeSet.{u_1} V G (@Sym2.instFintype.{u_1} V inst) inst_1))) →
        @Exists.{u_1 + 1} (Sym2.{u_1} V) fun (e : Sym2.{u_1} V) ↦
          And
            (@Membership.mem.{u_1, u_1} (Sym2.{u_1} V) (Finset.{u_1} (Sym2.{u_1} V))
              (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (Sym2.{u_1} V)) (Sym2.{u_1} V)
                (@Finset.instSetLike.{u_1} (Sym2.{u_1} V)))
              (@SimpleGraph.edgeFinset.{u_1} V G
                (@SimpleGraph.fintypeEdgeSet.{u_1} V G (@Sym2.instFintype.{u_1} V inst) inst_1))
              e)
            (@LE.le.{0} Nat instLENat
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                (@Fintype.card.{u_1} V inst)
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
              (@Erdos905.ErdosProblems.P905.triangleDegree.{u_1} V inst G inst_1 e))
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry
