import Mathlib.Analysis.SpecialFunctions.Log.Basic

attribute [local instance] Classical.propDecidable

noncomputable def Erdos648.g :
    Nat → Nat
  := by
  sorry

theorem Erdos648.erdos_648 :
    @Asymptotics.IsTheta.{0, 0, 0} Nat Real Real Real.norm Real.norm
      (@Filter.atTop.{0} Nat Nat.instPreorder)
      (fun (n : Nat) ↦ @Nat.cast.{0} Real Real.instNatCast (Erdos648.g n)) fun (n : Nat) ↦
      (@HDiv.hDiv.{0, 0, 0} Real Real Real
          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@Nat.cast.{0} Real Real.instNatCast n)
          (Real.log (@Nat.cast.{0} Real Real.instNatCast n))).sqrt
  := by
  sorry
