import Mathlib.Combinatorics.SimpleGraph.Finite

attribute [local instance] Classical.propDecidable

universe u_1

noncomputable def Erdos914.HajnalSzemeredi.HasDisjointCliques :
    {V : Type u_1} → SimpleGraph.{u_1} V → Nat → Nat → Prop
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

theorem Erdos914.HajnalSzemeredi.hajnal_szemeredi_clique_cover :
    ∀ {V : Type u_1} [inst : Fintype.{u_1} V] (G : SimpleGraph.{u_1} V)
      [inst_1 : @DecidableRel.{u_1 + 1, u_1 + 1} V V (@SimpleGraph.Adj.{u_1} V G)] (r m : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) r →
        @Eq.{1} Nat (@Fintype.card.{u_1} V inst)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) r m) →
          @LE.le.{0} Nat instLENat
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) m
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) r
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@SimpleGraph.minDegree.{u_1} V G inst inst_1) →
            @Erdos914.HajnalSzemeredi.HasDisjointCliques.{u_1} V G r m
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry
