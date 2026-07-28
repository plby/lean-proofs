import Mathlib.Data.Real.Basic

attribute [local instance] Classical.propDecidable

noncomputable def Erdos990b.SparseErdosTuranBound :
    Real → Prop
  := by
  sorry

theorem Erdos990b.erdos990_no_absolute_constant_sparseErdosTuran :
    Not
      (@Exists.{1} Real fun (C : Real) ↦
        And
          (@LT.lt.{0} Real Real.instLT
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C)
          (Erdos990b.SparseErdosTuranBound C))
  := by
  sorry
