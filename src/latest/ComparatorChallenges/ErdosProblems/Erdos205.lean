import Mathlib.Data.Finite.Defs
import Mathlib.Data.Real.Basic

attribute [local instance] Classical.propDecidable

noncomputable def Erdos205.is_counterexample :
    Real → Nat → Prop
  := by
  sorry

theorem Erdos205.infinitely_many_counterexamples :
    @Exists.{1} Real fun (c : Real) ↦
      And
        (@LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c)
        (@Set.Infinite.{0} Nat (@setOf.{0} Nat fun (n : Nat) ↦ Erdos205.is_counterexample c n))
  := by
  sorry
