import Mathlib.Analysis.SpecialFunctions.Log.Basic

attribute [local instance] Classical.propDecidable

noncomputable def Erdos280.isCoveredBy :
    (Nat → Nat) → (Nat → Nat) → Nat → Nat → Prop
  := by
  sorry

noncomputable instance Erdos280.isCoveredBy_decidable :
    (n a : Nat → Nat) → (m k : Nat) → Decidable (Erdos280.isCoveredBy n a m k)
  := by
  sorry

theorem Erdos280.erdos_280_counterexample :
    @Exists.{1} (Nat → Nat) fun (n : Nat → Nat) ↦
      @Exists.{1} (Nat → Nat) fun (a : Nat → Nat) ↦
        @Exists.{1} Real fun (ε : Real) ↦
          And
            (@LT.lt.{0} Real Real.instLT
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
            (And (@StrictMono.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder n)
              (And
                (∀ (i : Nat),
                  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      i →
                    @LT.lt.{0} Nat instLTNat (a i) (n i))
                (And
                  (∀ (k : Nat),
                    @LE.le.{0} Nat instLENat
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k →
                      @GT.gt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (n k))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                              ε)
                            (@Nat.cast.{0} Real Real.instNatCast k))
                          (Real.log (@Nat.cast.{0} Real Real.instNatCast k))))
                  (And
                    (∀ (k : Nat),
                      @LE.le.{0} Nat instLENat
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k →
                        @Eq.{1} Nat
                          (@Finset.card.{0} Nat
                            (@Finset.filter.{0} Nat (fun (m : Nat) ↦ Not (Erdos280.isCoveredBy n a m k))
                              (fun (a_2 : Nat) ↦
                                @instDecidableNot (Erdos280.isCoveredBy n a a_2 k)
                                  (Erdos280.isCoveredBy_decidable n a a_2 k))
                              (Finset.range (n k))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@Filter.Tendsto.{0, 0} Nat Real
                      (fun (k : Nat) ↦
                        @HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@Nat.cast.{0} Real Real.instNatCast
                            (@Finset.card.{0} Nat
                              (@Finset.filter.{0} Nat
                                (fun (m : Nat) ↦ Not (Erdos280.isCoveredBy n a m k))
                                (fun (a_1 : Nat) ↦
                                  @instDecidableNot (Erdos280.isCoveredBy n a a_1 k)
                                    (Erdos280.isCoveredBy_decidable n a a_1 k))
                                (Finset.range (n k)))))
                          (@Nat.cast.{0} Real Real.instNatCast k))
                      (@Filter.atTop.{0} Nat Nat.instPreorder)
                      (@nhds.{0} Real
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@OfNat.ofNat.{0} Real (nat_lit 0)
                          (@Zero.toOfNat0.{0} Real Real.instZero))))))))
  := by
  sorry
