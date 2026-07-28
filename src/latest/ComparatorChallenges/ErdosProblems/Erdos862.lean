import Mathlib.Analysis.SpecialFunctions.Log.Basic

attribute [local instance] Classical.propDecidable

noncomputable def Erdos862.A1 :
    Nat → Nat
  := by
  sorry

noncomputable def Erdos862.eta :
    Real
  := by
  sorry

theorem Erdos862.erdos_862 :
    ∀ (c : Real),
      @LT.lt.{0} Real Real.instLT c Erdos862.eta →
        @Filter.Eventually.{0} Nat
          (fun (N : Nat) ↦
            @GE.ge.{0} Real Real.instLE
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (Real.log (@Nat.cast.{0} Real Real.instNatCast (Erdos862.A1 N)))
                (@Nat.cast.{0} Real Real.instNatCast N).sqrt)
              c)
          (@Filter.atTop.{0} Nat Nat.instPreorder)
  := by
  sorry
