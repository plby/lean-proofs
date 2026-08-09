import Mathlib.Data.Nat.Log
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

namespace Erdos760

set_option linter.style.setOption false
set_option linter.flexible false

open scoped ENat

namespace SimpleGraph

open _root_.SimpleGraph

def CochromPartable {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ f : V → Fin n, ∀ i : Fin n, G.IsClique (f ⁻¹' {i}) ∨ G.IsIndepSet (f ⁻¹' {i})

noncomputable def cochromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ∞ :=
  ⨅ n ∈ {n : ℕ | CochromPartable G n}, (n : ℕ∞)
end SimpleGraph

end Erdos760

attribute [local instance] Classical.propDecidable

universe u_1

theorem Erdos760.SimpleGraph.erdos_760 :
    @Exists.{1} Nat fun (C : Nat) ↦
      And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) C)
        (∀ (V : Type u_1) [Finite.{u_1 + 1} V] (G : SimpleGraph.{u_1} V) (m : Nat),
          @Eq.{1} ENat (@SimpleGraph.chromaticNumber.{u_1} V G)
              (@Nat.cast.{0} ENat ENat.instNatCast m) →
            @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m →
              @Exists.{u_1 + 1} (Set.{u_1} V) fun (S : Set.{u_1} V) ↦
                @Exists.{u_1 + 1} (SimpleGraph.{u_1} (@Set.Elem.{u_1} V S))
                  fun (H : SimpleGraph.{u_1} (@Set.Elem.{u_1} V S)) ↦
                  And
                    (∀ (u v : @Set.Elem.{u_1} V S),
                      @SimpleGraph.Adj.{u_1} (@Set.Elem.{u_1} V S) H u v →
                        @SimpleGraph.Adj.{u_1} V G
                          (@Subtype.val.{u_1 + 1} V
                            (fun (x : V) ↦
                              @Membership.mem.{u_1, u_1} V (Set.{u_1} V) (@Set.instMembership.{u_1} V) S
                                x)
                            u)
                          (@Subtype.val.{u_1 + 1} V
                            (fun (x : V) ↦
                              @Membership.mem.{u_1, u_1} V (Set.{u_1} V) (@Set.instMembership.{u_1} V) S
                                x)
                            v))
                    (@LE.le.{0} ENat instLEENat (@Nat.cast.{0} ENat ENat.instNatCast m)
                      (@HMul.hMul.{0, 0, 0} ENat ENat ENat
                        (@instHMul.{0} ENat
                          (@Distrib.toMul.{0} ENat
                            (@instDistribOfSemiring.{0} ENat
                              (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat))))
                        (@HMul.hMul.{0, 0, 0} ENat ENat ENat
                          (@instHMul.{0} ENat
                            (@Distrib.toMul.{0} ENat
                              (@instDistribOfSemiring.{0} ENat
                                (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat))))
                          (@Nat.cast.{0} ENat ENat.instNatCast C)
                          (@Nat.cast.{0} ENat ENat.instNatCast
                            (Nat.log (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                        (@Erdos760.SimpleGraph.cochromaticNumber.{u_1} (@Set.Elem.{u_1} V S) H))))
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry
