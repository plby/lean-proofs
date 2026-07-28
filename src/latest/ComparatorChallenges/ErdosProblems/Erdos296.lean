import Mathlib.Analysis.SpecialFunctions.Log.Basic

attribute [local instance] Classical.propDecidable

noncomputable def Erdos296.HasDisjointUnitDecomps :
    Nat → Nat → Prop
  := by
  sorry

theorem Erdos296.erdos296 :
    @Exists.{1} Real fun (c : Real) ↦
      And
        (@GT.gt.{0} Real Real.instLT c
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
        (@Filter.Eventually.{0} Nat
          (fun (N : Nat) ↦
            Erdos296.HasDisjointUnitDecomps N
              (@Nat.floor.{0} Real Real.semiring Real.partialOrder
                (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c
                  (Real.log (@Nat.cast.{0} Real Real.instNatCast N)))))
          (@Filter.atTop.{0} Nat Nat.instPreorder))
  := by
  sorry
