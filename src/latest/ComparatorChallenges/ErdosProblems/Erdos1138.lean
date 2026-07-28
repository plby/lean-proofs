import Mathlib.Data.Real.Basic

attribute [local instance] Classical.propDecidable

noncomputable def Erdos1138.AsymptoticA :
    Real → Prop
  := by
  sorry

theorem Erdos1138.erdos1138_corollary :
    Not
      (∀ (C : Real),
        @LT.lt.{0} Real Real.instLT
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) C →
          Erdos1138.AsymptoticA C)
  := by
  sorry
