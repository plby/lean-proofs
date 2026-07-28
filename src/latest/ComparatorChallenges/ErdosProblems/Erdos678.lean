import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Interval.Finset.Nat

attribute [local instance] Classical.propDecidable

universe u_1

noncomputable abbrev Erdos678.erdos_678_kmn_infinite.match_1 :
    (motive : Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat) → Sort u_1) →
      (x : Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) →
        ((k m n : Nat) →
            motive (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat Nat) k (@Prod.mk.{0, 0} Nat Nat m n))) →
          motive x
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

noncomputable abbrev Erdos678.not_erdos_678_other.match_1 :
    (motive : Prod.{0, 0} Nat Nat → Sort u_1) →
      (x : Prod.{0, 0} Nat Nat) → ((m n : Nat) → motive (@Prod.mk.{0, 0} Nat Nat m n)) → motive x
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

noncomputable def Erdos678.lcm_real :
    Finset.{0} Nat → Real
  := by
  sorry

noncomputable def Erdos678.lcmInterval :
    Nat → Nat → Nat
  := by
  sorry

theorem Erdos678.not_erdos_678_other :
    Not
      (∀ (k : Nat),
        @GE.ge.{0} Nat instLENat k (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
          @Set.Infinite.{0} (Prod.{0, 0} Nat Nat)
            (@setOf.{0} (Prod.{0, 0} Nat Nat) fun (x : Prod.{0, 0} Nat Nat) ↦
              Erdos678.not_erdos_678_other.match_1.{1} (fun (x : Prod.{0, 0} Nat Nat) ↦ Prop) x
                fun (m n : Nat) ↦
                And
                  (@LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n k) m)
                  (@LT.lt.{0} Nat instLTNat
                    (Erdos678.lcmInterval m
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Erdos678.lcmInterval n k))))
  := by
  sorry

theorem Erdos678.main_theorem_expanded :
    ∀ (C : Real),
      @GE.ge.{0} Real Real.instLE C
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
        @Exists.{1} Nat fun (K : Nat) ↦
          ∀ (k : Nat),
            @GE.ge.{0} Nat instLENat k K →
              @Exists.{1} Nat fun (x : Nat) ↦
                @Exists.{1} Nat fun (y : Nat) ↦
                  And
                    (@LT.lt.{0} Nat instLTNat
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x)
                    (And (@LT.lt.{0} Nat instLTNat x y)
                      (And
                        (@GT.gt.{0} Nat instLTNat y
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) x k))
                        (@GT.gt.{0} Real Real.instLT
                          (Erdos678.lcm_real
                            (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder x
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) x k)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                            (Erdos678.lcm_real
                              (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder y
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) y
                                  k)))))))
  := by
  sorry

theorem Erdos678.erdos_678 :
    @Exists.{1} Nat fun (K : Nat) ↦
      ∀ (k : Nat),
        @GE.ge.{0} Nat instLENat k K →
          @Exists.{1} Nat fun (x : Nat) ↦
            @Exists.{1} Nat fun (y : Nat) ↦
              And
                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  x)
                (And (@LT.lt.{0} Nat instLTNat x y)
                  (And
                    (@GT.gt.{0} Nat instLTNat y
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) x k))
                    (@GT.gt.{0} Real Real.instLT
                      (Erdos678.lcm_real
                        (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder x
                          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) x k)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (Erdos678.lcm_real
                        (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder y
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) y k))))))
  := by
  sorry

theorem Erdos678.not_erdos_678_fc :
    Not
      (@Filter.Eventually.{0} Nat
        (fun (k : Nat) ↦
          @Set.Infinite.{0} (Prod.{0, 0} Nat Nat)
            (@setOf.{0} (Prod.{0, 0} Nat Nat) fun (x : Prod.{0, 0} Nat Nat) ↦
              Erdos678.not_erdos_678_other.match_1.{1} (fun (x : Prod.{0, 0} Nat Nat) ↦ Prop) x
                fun (m n : Nat) ↦
                And
                  (@LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n k) m)
                  (@LT.lt.{0} Nat instLTNat
                    (Erdos678.lcmInterval m
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Erdos678.lcmInterval n k))))
        (@Filter.atTop.{0} Nat Nat.instPreorder))
  := by
  sorry

theorem Erdos678.erdos_678_kmn_infinite :
    @Set.Infinite.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))
      (@setOf.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))
        fun (x : Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) ↦
        Erdos678.erdos_678_kmn_infinite.match_1.{1}
          (fun (x : Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) ↦ Prop) x fun (k m n : Nat) ↦
          And (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) k)
            (And
              (@LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n k) m)
              (@LT.lt.{0} Nat instLTNat
                (Erdos678.lcmInterval m
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (Erdos678.lcmInterval n k))))
  := by
  sorry
