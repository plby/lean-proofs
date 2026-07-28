import Mathlib.Combinatorics.SimpleGraph.Finite

attribute [local instance] Classical.propDecidable

universe u_1

noncomputable def Erdos1007.GraphDimension :
    {V : Type u_1} → SimpleGraph.{u_1} V → Nat
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

theorem Erdos1007.erdos_1007 :
    @IsLeast.{0} Nat instLENat
      (@setOf.{0} Nat fun (n : Nat) ↦
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
