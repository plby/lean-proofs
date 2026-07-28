import Mathlib.Analysis.Asymptotics.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos728p.bad_set_thm_1_1 :
    Real → Finset.{0} Nat
  := by
  sorry

theorem Erdos728p.theorem_1_1 :
    @Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.norm Real.norm
      (@Filter.atTop.{0} Real Real.instPreorder)
      (fun (x : Real) ↦
        @Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Nat (Erdos728p.bad_set_thm_1_1 x)))
      fun (x : Real) ↦ x
  := by
  sorry

noncomputable def Erdos728p.bad_set_intrinsic_1_2 :
    Real → Finset.{0} Nat
  := by
  sorry

theorem Erdos728p.theorem_1_2 :
    @Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.norm Real.norm
      (@Filter.atTop.{0} Real Real.instPreorder)
      (fun (x : Real) ↦
        @Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Nat (Erdos728p.bad_set_intrinsic_1_2 x)))
      fun (x : Real) ↦ x
  := by
  sorry
