import Mathlib.Combinatorics.SimpleGraph.Basic

attribute [local instance] Classical.propDecidable

universe u_1 u_2

noncomputable def Erdos621.TriangleIndep.alpha1 :
    {V : Type u_1} →
      [Fintype.{u_1} V] →
        (G : SimpleGraph.{u_1} V) →
          [@DecidableRel.{u_1 + 1, u_1 + 1} V V (@SimpleGraph.Adj.{u_1} V G)] → Nat
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

noncomputable def Erdos621.TriangleIndep.tau1 :
    {V : Type u_2} →
      [Fintype.{u_2} V] →
        [DecidableEq.{u_2 + 1} V] →
          (G : SimpleGraph.{u_2} V) →
            [@DecidableRel.{u_2 + 1, u_2 + 1} V V (@SimpleGraph.Adj.{u_2} V G)] → Nat
  := by
  let _ := ULift.{u_2, 0} PUnit
  sorry

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
