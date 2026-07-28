import Mathlib.Data.Nat.Dist
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

attribute [local instance] Classical.propDecidable

universe u

namespace Erdos751

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace BV

structure Cycle where
  base : V
  walk : G.Walk base base
  isCycle : walk.IsCycle
  len_ge_three : 3 ≤ walk.length

end BV

end Erdos751

noncomputable def Erdos751.BV.Cycle.length :
    {V : Type u} → (G : SimpleGraph.{u} V) → @Erdos751.BV.Cycle.{u} V G → Nat
  := by
  let _ := ULift.{u, 0} PUnit
  sorry

theorem Erdos751.Main.erdos_751_strong :
    ∀ {V : Type u} (G : SimpleGraph.{u} V) [Finite.{u + 1} V],
      @LE.le.{0} ENat instLEENat
          (@OfNat.ofNat.{0} ENat (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} ENat (nat_lit 4) ENat.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
          (@SimpleGraph.chromaticNumber.{u} V G) →
        @Exists.{u + 1} (@Erdos751.BV.Cycle.{u} V G) fun (C1 : @Erdos751.BV.Cycle.{u} V G) ↦
          @Exists.{u + 1} (@Erdos751.BV.Cycle.{u} V G) fun (C2 : @Erdos751.BV.Cycle.{u} V G) ↦
            Or
              (@Eq.{1} Nat
                ((@Erdos751.BV.Cycle.length.{u} V G C1).dist (@Erdos751.BV.Cycle.length.{u} V G C2))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Eq.{1} Nat
                ((@Erdos751.BV.Cycle.length.{u} V G C1).dist (@Erdos751.BV.Cycle.length.{u} V G C2))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  := by
  let _ := ULift.{u, 0} PUnit
  sorry
