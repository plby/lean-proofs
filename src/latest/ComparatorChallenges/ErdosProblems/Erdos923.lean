import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

attribute [local instance] Classical.propDecidable

universe u_1

theorem Erdos923.erdos923 :
    ∀ {V : Type u_1} (n : Nat),
      @Exists.{1} Nat fun (k : Nat) ↦
        ∀ (G : SimpleGraph.{u_1} V),
          @LE.le.{0} ENat instLEENat (@Nat.cast.{0} ENat ENat.instNatCast k)
              (@SimpleGraph.chromaticNumber.{u_1} V G) →
            @Exists.{u_1 + 1} (SimpleGraph.{u_1} V) fun (H : SimpleGraph.{u_1} V) ↦
              And (@LE.le.{u_1} (SimpleGraph.{u_1} V) (@SimpleGraph.instLE.{u_1} V) H G)
                (And
                  (@LE.le.{0} ENat instLEENat (@Nat.cast.{0} ENat ENat.instNatCast n)
                    (@SimpleGraph.chromaticNumber.{u_1} V H))
                  (@SimpleGraph.CliqueFree.{u_1} V H
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry
