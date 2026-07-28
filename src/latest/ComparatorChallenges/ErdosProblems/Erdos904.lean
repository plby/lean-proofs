import Mathlib.Combinatorics.SimpleGraph.Clique

attribute [local instance] Classical.propDecidable

universe u_1

noncomputable abbrev Erdos904.SimpleGraph.n :
    (V : Type u_1) → [Fintype.{u_1} V] → Nat
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

noncomputable abbrev Erdos904.SimpleGraph.turanNumber :
    Nat → Nat → Nat
  := by
  sorry

theorem Erdos904.SimpleGraph.erdos904 :
    ∀ {V : Type u_1} [inst : Fintype.{u_1} V] {G : SimpleGraph.{u_1} V}
      [inst_1 : @DecidableRel.{u_1 + 1, u_1 + 1} V V (@SimpleGraph.Adj.{u_1} V G)] {r : Nat},
      @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
          (@Set.Icc.{0} Nat Nat.instPreorder
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Erdos904.SimpleGraph.n.{u_1} V inst))
          r →
        @LE.le.{0} Nat instLENat
            (Erdos904.SimpleGraph.turanNumber (@Erdos904.SimpleGraph.n.{u_1} V inst) r)
            (@Finset.card.{u_1} (Sym2.{u_1} V)
              (@SimpleGraph.edgeFinset.{u_1} V G
                (@SimpleGraph.fintypeEdgeSet.{u_1} V G (@Sym2.instFintype.{u_1} V inst) inst_1))) →
          @Exists.{u_1 + 1} (Finset.{u_1} V) fun (s : Finset.{u_1} V) ↦
            And (@SimpleGraph.IsNClique.{u_1} V G r s)
              (@LE.le.{0} Nat instLENat
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                  (@Finset.card.{u_1} (Sym2.{u_1} V)
                    (@SimpleGraph.edgeFinset.{u_1} V G
                      (@SimpleGraph.fintypeEdgeSet.{u_1} V G (@Sym2.instFintype.{u_1} V inst) inst_1))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@Erdos904.SimpleGraph.n.{u_1} V inst)
                  (@Finset.sum.{u_1, 0} V Nat Nat.instAddCommMonoid s fun (v : V) ↦
                    @SimpleGraph.degree.{u_1} V G v
                      (@Subtype.fintype.{u_1} V
                        (@Membership.mem.{u_1, u_1} V (Set.{u_1} V) (@Set.instMembership.{u_1} V)
                          (@SimpleGraph.neighborSet.{u_1} V G v))
                        (fun (a : V) ↦ @SimpleGraph.neighborSet.memDecidable.{u_1} V G v inst_1 a)
                        inst))))
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry
