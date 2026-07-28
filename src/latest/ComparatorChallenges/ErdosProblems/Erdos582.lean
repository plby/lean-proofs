import Mathlib.Combinatorics.SimpleGraph.Clique

attribute [local instance] Classical.propDecidable

universe u_3

noncomputable def Erdos582.EdgeRamseyTriangle :
    {V : Type u_3} → SimpleGraph.{u_3} V → Prop
  := by
  let _ := ULift.{u_3, 0} PUnit
  sorry

theorem Erdos582.erdos_582 :
    @Exists.{2} Type fun (V : Type) ↦
      @Exists.{1} (Fintype.{0} V) fun (x : Fintype.{0} V) ↦
        @Exists.{1} (DecidableEq.{1} V) fun (x : DecidableEq.{1} V) ↦
          @Exists.{1} (SimpleGraph.{0} V) fun (G : SimpleGraph.{0} V) ↦
            And
              (@Eq.{1} Nat (@SimpleGraph.cliqueNum.{0} V G)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@Erdos582.EdgeRamseyTriangle.{0} V G)
  := by
  sorry
