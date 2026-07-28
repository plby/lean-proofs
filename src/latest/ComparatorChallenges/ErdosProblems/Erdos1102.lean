import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

attribute [local instance] Classical.propDecidable

noncomputable def Erdos1102.HasPropertyP :
    Set.{0} Nat → Prop
  := by
  sorry

theorem Erdos1102.erdos_1102.exists_sequence_with_P :
    ∀ (f : Nat → Nat),
      @Filter.Tendsto.{0, 0} Nat Nat f (@Filter.atTop.{0} Nat Nat.instPreorder)
          (@Filter.atTop.{0} Nat Nat.instPreorder) →
        (∀ (n : Nat), @Ne.{1} Nat (f n) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
          @Exists.{1} (Nat → Nat) fun (A : Nat → Nat) ↦
            And (@StrictMono.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder A)
              (And (Erdos1102.HasPropertyP (@Set.range.{0, 1} Nat Nat A))
                (∀ (j : Nat),
                  @LE.le.{0} Real Real.instLE
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@Nat.cast.{0} Real Real.instNatCast (A j))
                      (@Nat.cast.{0} Real Real.instNatCast j))
                    (@Nat.cast.{0} Real Real.instNatCast (f j))))
  := by
  sorry

noncomputable def Erdos1102b.SF :
    Set.{0} Nat
  := by
  sorry

noncomputable def Erdos1102b.PropertyQ :
    Set.{0} Nat → Prop
  := by
  sorry

noncomputable def Erdos1102b.HasNaturalDensity :
    Set.{0} Nat → Real → Prop
  := by
  sorry

noncomputable def Erdos1102b.upperDensity :
    Set.{0} Nat → Real
  := by
  sorry

theorem Erdos1102b.TheoremQ_upper :
    ∀ (A : Set.{0} Nat),
      Erdos1102b.PropertyQ A →
        @LE.le.{0} Real Real.instLE (Erdos1102b.upperDensity A)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real
            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 6)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat
                  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat
                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              Real.pi (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  := by
  sorry

theorem Erdos1102b.TheoremQ_lower :
    @Exists.{1} (Set.{0} Nat) fun (A : Set.{0} Nat) ↦
      And (@LE.le.{0} (Set.{0} Nat) (@Set.instLE.{0} Nat) A Erdos1102b.SF)
        (And (Erdos1102b.PropertyQ A)
          (Erdos1102b.HasNaturalDensity A
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 6)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat
                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                    (@Nat.instNeZeroSucc
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat
                  (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                Real.pi (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
  := by
  sorry

noncomputable def Erdos1102b.HasPropertyQ :
    Set.{0} Nat → Prop
  := by
  sorry

theorem Erdos1102b.erdos_1102.upper_density_Q :
    ∀ (A : Nat → Nat),
      @StrictMono.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder A →
        Erdos1102b.HasPropertyQ (@Set.range.{0, 1} Nat Nat A) →
          @LE.le.{0} Real Real.instLE
            (@Filter.limsup.{0, 0} Real Nat
              (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Real
                Real.instConditionallyCompleteLinearOrder)
              (fun (j : Nat) ↦
                @HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@Nat.cast.{0} Real Real.instNatCast j) (@Nat.cast.{0} Real Real.instNatCast (A j)))
              (@Filter.atTop.{0} Nat Nat.instPreorder))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 6)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat
                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                    (@Nat.instNeZeroSucc
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat
                  (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                Real.pi (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  := by
  sorry

theorem Erdos1102b.erdos_1102.lower_density_Q_exists :
    @Exists.{1} (Nat → Nat) fun (A : Nat → Nat) ↦
      And (@StrictMono.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder A)
        (And (∀ (j : Nat), @Squarefree.{0} Nat Nat.instMonoid (A j))
          (And (Erdos1102b.HasPropertyQ (@Set.range.{0, 1} Nat Nat A))
            (@Filter.Tendsto.{0, 0} Nat Real
              (fun (j : Nat) ↦
                @HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@Nat.cast.{0} Real Real.instNatCast j) (@Nat.cast.{0} Real Real.instNatCast (A j)))
              (@Filter.atTop.{0} Nat Nat.instPreorder)
              (@nhds.{0} Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 6)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat
                        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                        (@Nat.instNeZeroSucc
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat
                      (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                    Real.pi (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
  := by
  sorry

noncomputable def Erdos1102c.PropertyP_bar :
    Set.{0} Nat → Prop
  := by
  sorry

noncomputable def Erdos1102c.PropertyP_bar_infty :
    Set.{0} Nat → Prop
  := by
  sorry

noncomputable def Erdos1102c.upperDensity :
    Set.{0} Nat → Real
  := by
  sorry

noncomputable def Erdos1102c.lowerDensity :
    Set.{0} Nat → Real
  := by
  sorry

theorem Erdos1102c.theorem_overp_i :
    ∀ (A : Set.{0} Nat),
      Erdos1102c.PropertyP_bar_infty A →
        @LT.lt.{0} Real Real.instLT (Erdos1102c.upperDensity A)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real
            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 6)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat
                  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat
                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              Real.pi (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  := by
  sorry

theorem Erdos1102c.theorem_overp_ii :
    ∀ (ε : Real),
      @GT.gt.{0} Real Real.instLT ε
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @Exists.{1} (Set.{0} Nat) fun (A : Set.{0} Nat) ↦
          And (Erdos1102c.PropertyP_bar A)
            (@GE.ge.{0} Real Real.instLE (Erdos1102c.lowerDensity A)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 6)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat
                        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                        (@Nat.instNeZeroSucc
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat
                      (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                    Real.pi (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                ε))
  := by
  sorry

noncomputable def Erdos1102d.PropertyQ :
    Set.{0} Nat → Prop
  := by
  sorry

noncomputable def Erdos1102d.Admissible :
    Set.{0} Nat → Prop
  := by
  sorry

noncomputable def Erdos1102d.A1 :
    Set.{0} Nat
  := by
  sorry

noncomputable def Erdos1102d.A2 :
    Set.{0} Nat
  := by
  sorry

noncomputable def Erdos1102d.A3 :
    Set.{0} Nat
  := by
  sorry

noncomputable def Erdos1102d.A4 :
    Set.{0} Nat
  := by
  sorry

noncomputable def Erdos1102d.GrowthCondition :
    Set.{0} Nat → Real → Prop
  := by
  sorry

theorem Erdos1102d.Theorem_suff :
    @Exists.{1} Real fun (C : Real) ↦
      And
        (@GT.gt.{0} Real Real.instLT C
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
        (∀ (A : Set.{0} Nat),
          Erdos1102d.Admissible A →
            @Set.Infinite.{0} Nat A → Erdos1102d.GrowthCondition A C → Erdos1102d.PropertyQ A)
  := by
  sorry

theorem Erdos1102d.All_Sequences_PropertyQ :
    And (Erdos1102d.PropertyQ Erdos1102d.A1)
      (And (Erdos1102d.PropertyQ Erdos1102d.A2)
        (And (Erdos1102d.PropertyQ Erdos1102d.A3) (Erdos1102d.PropertyQ Erdos1102d.A4)))
  := by
  sorry
