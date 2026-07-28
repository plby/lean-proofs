import Mathlib.Analysis.InnerProductSpace.PiL2

attribute [local instance] Classical.propDecidable

noncomputable def Erdos846.NonTrilinearFor :
    Set.{0}
        (EuclideanSpace.{0, 0} Real
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
      Real → Prop
  := by
  sorry

noncomputable def Erdos846.WeaklyNonTrilinear :
    Set.{0}
        (EuclideanSpace.{0, 0} Real
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
      Prop
  := by
  sorry

theorem Erdos846.erdos_846 :
    Iff False
      (∀
        (A :
          Set.{0}
            (EuclideanSpace.{0, 0} Real
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (ε : Real),
        @GT.gt.{0} Real Real.instLT ε
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
          @Set.Infinite.{0}
              (EuclideanSpace.{0, 0} Real
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              A →
            Erdos846.NonTrilinearFor A ε → Erdos846.WeaklyNonTrilinear A)
  := by
  sorry
