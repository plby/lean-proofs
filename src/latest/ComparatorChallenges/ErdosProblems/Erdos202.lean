import Mathlib.Analysis.SpecialFunctions.Log.Basic

attribute [local instance] Classical.propDecidable

universe u_1 u_2

noncomputable abbrev Erdos202.ResidueAssignment :
    Finset.{0} Nat → Type
  := by
  sorry

noncomputable def Erdos202.PairwiseDisjointResidues :
    (Q : Finset.{0} Nat) → Erdos202.ResidueAssignment Q → Prop
  := by
  sorry

noncomputable def Erdos202.Admissible :
    Nat → Finset.{0} Nat → Prop
  := by
  sorry

noncomputable def Erdos202.f :
    Nat → Nat
  := by
  sorry

noncomputable def Erdos202.Zscale :
    Nat → Real
  := by
  sorry

noncomputable def Erdos202.Lscale :
    Real → Nat → Real
  := by
  sorry

noncomputable def Erdos202.Mscale :
    Nat → Real
  := by
  sorry

noncomputable def Erdos202.Erdos202Statement :
    Prop
  := by
  sorry

noncomputable def Erdos202.omega :
    Nat → Nat
  := by
  sorry

noncomputable def Erdos202.rad :
    Nat → Nat
  := by
  sorry

noncomputable def Erdos202.hExp :
    Nat → Nat
  := by
  sorry

noncomputable def Erdos202.UniformFamily :
    {α : Type u_1} → [DecidableEq.{u_1 + 1} α] → Finset.{u_1} (Finset.{u_1} α) → Nat → Prop
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

noncomputable def Erdos202.SpreadFamily :
    {α : Type u_1} → [DecidableEq.{u_1 + 1} α] → Finset.{u_1} (Finset.{u_1} α) → Real → Prop
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

noncomputable def Erdos202.PairwiseDisjointMembers :
    {α : Type u_1} → [DecidableEq.{u_1 + 1} α] → Finset.{u_1} (Finset.{u_1} α) → Prop
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

noncomputable def Erdos202.ParkPham.IncreasingIn :
    {α : Type u_1} → Finset.{u_1} α → Finset.{u_1} (Finset.{u_1} α) → Prop
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

noncomputable def Erdos202.ParkPham.ell :
    {α : Type u_1} → [DecidableEq.{u_1 + 1} α] → Finset.{u_1} α → Finset.{u_1} (Finset.{u_1} α) → Nat
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

noncomputable def Erdos202.ParkPham.muP :
    {α : Type u_1} →
      [DecidableEq.{u_1 + 1} α] → Finset.{u_1} α → Finset.{u_1} (Finset.{u_1} α) → Real → Real
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

noncomputable def Erdos202.ParkPham.pSmall :
    {α : Type u_1} → Finset.{u_1} α → Finset.{u_1} (Finset.{u_1} α) → Real → Prop
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

theorem Erdos202.ParkPham.park_pham_threshold_not_small_lt_exists :
    @Exists.{1} Real fun (CKK : Real) ↦
      And
        (@LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) CKK)
        (∀ {α : Type u_1} [inst : DecidableEq.{u_1 + 1} α] (X : Finset.{u_1} α)
          (U : Finset.{u_1} (Finset.{u_1} α)) (q : Real),
          @LT.lt.{0} Real Real.instLT
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) q →
            @LE.le.{0} Real Real.instLE q
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
              @LT.lt.{0} Real Real.instLT
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) CKK q)
                    (Real.log
                      (@Nat.cast.{0} Real Real.instNatCast (@Erdos202.ParkPham.ell.{u_1} α inst X U))))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                (∀ (S : Finset.{u_1} α),
                    @Membership.mem.{u_1, u_1} (Finset.{u_1} α) (Finset.{u_1} (Finset.{u_1} α))
                        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (Finset.{u_1} α))
                          (Finset.{u_1} α) (@Finset.instSetLike.{u_1} (Finset.{u_1} α)))
                        U S →
                      @LE.le.{u_1} (Finset.{u_1} α)
                        (@Preorder.toLE.{u_1} (Finset.{u_1} α)
                          (@PartialOrder.toPreorder.{u_1} (Finset.{u_1} α)
                            (@Finset.instPartialOrder.{u_1} α)))
                        S X) →
                  @Erdos202.ParkPham.IncreasingIn.{u_1} α X U →
                    Not (@Erdos202.ParkPham.pSmall.{u_1} α X U q) →
                      @GE.ge.{0} Real Real.instLE
                        (@Erdos202.ParkPham.muP.{u_1} α inst X U
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) CKK
                              q)
                            (Real.log
                              (@Nat.cast.{0} Real Real.instNatCast
                                (@Erdos202.ParkPham.ell.{u_1} α inst X U)))))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

theorem Erdos202.ParkPham.spread_disjointness_theorem :
    @Exists.{1} Real fun (Csp : Real) ↦
      And
        (@LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Csp)
        (∀ {α : Type u_2} [inst : DecidableEq.{u_2 + 1} α] (A : Finset.{u_2} (Finset.{u_2} α))
          (r k : Nat) (κ : Real),
          @Finset.Nonempty.{u_2} (Finset.{u_2} α) A →
            @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r →
              @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k →
                @Erdos202.UniformFamily.{u_2} α inst A k →
                  @Erdos202.SpreadFamily.{u_2} α inst A κ →
                    @LE.le.{0} Real Real.instLE
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Csp
                            (@Nat.cast.{0} Real Real.instNatCast r))
                          (Real.log
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (Real.exp
                                (@OfNat.ofNat.{0} Real (nat_lit 1)
                                  (@One.toOfNat1.{0} Real Real.instOne)))
                              (@Nat.cast.{0} Real Real.instNatCast k))))
                        κ →
                      @Exists.{u_2 + 1} (Finset.{u_2} (Finset.{u_2} α))
                        fun (B : Finset.{u_2} (Finset.{u_2} α)) ↦
                        And
                          (@LE.le.{u_2} (Finset.{u_2} (Finset.{u_2} α))
                            (@Preorder.toLE.{u_2} (Finset.{u_2} (Finset.{u_2} α))
                              (@PartialOrder.toPreorder.{u_2} (Finset.{u_2} (Finset.{u_2} α))
                                (@Finset.instPartialOrder.{u_2} (Finset.{u_2} α))))
                            B A)
                          (And (@Eq.{1} Nat (@Finset.card.{u_2} (Finset.{u_2} α) B) r)
                            (@Erdos202.PairwiseDisjointMembers.{u_2} α inst B)))
  := by
  let _ := ULift.{u_2, 0} PUnit
  sorry

theorem Erdos202.bfv_omega_count_theorem :
    ∀ (ε : Real),
      @LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
        @Filter.Eventually.{0} Nat
          (fun (N : Nat) ↦
            ∀ (y K W : Nat),
              @LE.le.{0} Nat instLENat y N →
                @LE.le.{0} Nat instLENat W K →
                  @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast K)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@OfNat.ofNat.{0} Real (nat_lit 3)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@Nat.instNeZeroSucc
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                        (Erdos202.Mscale N)) →
                    have d :=
                      @HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@Nat.cast.{0} Real Real.instNatCast K) (Erdos202.Mscale N);
                    @LE.le.{0} Nat instLENat
                      (@Finset.card.{0} Nat
                        (@Finset.filter.{0} Nat
                          (fun (n : Nat) ↦
                            @Eq.{1} Nat (Erdos202.omega n)
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) K W))
                          (fun (a : Nat) ↦
                            instDecidableEqNat (Erdos202.omega a)
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) K W))
                          (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) y)))
                      (@Nat.floor.{0} Real Real.semiring Real.partialOrder
                        (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder
                          Real.instFloorRing)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@Nat.cast.{0} Real Real.instNatCast y)
                            (Real.exp
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                    (@instHDiv.{0} Real
                                      (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                    (@Neg.neg.{0} Real Real.instNeg d)
                                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                              (instOfNatNat (nat_lit 0))))))))
                                  ε)
                                (Erdos202.Zscale N))))
                          (Real.exp
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real
                                  (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@Nat.cast.{0} Real Real.instNatCast W)
                                (@OfNat.ofNat.{0} Real (nat_lit 2)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                          (instOfNatNat (nat_lit 0))))))))
                              (Real.log (Real.log (@Nat.cast.{0} Real Real.instNatCast N))))))))
          (@Filter.atTop.{0} Nat Nat.instPreorder)
  := by
  sorry

theorem Erdos202.bfv_lower_bound_theorem :
    ∀ (ε : Real),
      @LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
        @Filter.Eventually.{0} Nat
          (fun (N : Nat) ↦
            @LE.le.{0} Real Real.instLE
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Nat.cast.{0} Real Real.instNatCast N)
                (Erdos202.Lscale
                  (@Neg.neg.{0} Real Real.instNeg
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ε))
                  N))
              (@Nat.cast.{0} Real Real.instNatCast (Erdos202.f N)))
          (@Filter.atTop.{0} Nat Nat.instPreorder)
  := by
  sorry

namespace Erdos202

structure PrunedData (N : ℕ) where
  Q : Finset ℕ
  Q_nonempty : Q.Nonempty
  a : ResidueAssignment Q
  admissible : Admissible N Q
  pairwise_disjoint : PairwiseDisjointResidues Q a
  K : ℕ
  K_pos : 1 ≤ K
  modulus_lower : ∀ q ∈ Q, (N : ℝ) * Lscale (-2) N ≤ (q : ℝ)
  modulus_upper : ∀ q ∈ Q, q ≤ N
  hExp_bound : ∀ q ∈ Q, (hExp q : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ)))
  omega_eq : ∀ q ∈ Q, omega q = K
  K_bound : (K : ℝ) ≤ 3 * Mscale N
  rad_injective : ∀ q ∈ Q, ∀ r ∈ Q, rad q = rad r → q = r

end Erdos202

theorem Erdos202.bfv_pruning_theorem :
    ∀ (ε : Real),
      @LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
        @Filter.Eventually.{0} Nat
          (fun (N : Nat) ↦
            ∀ (Q : Finset.{0} Nat) (a : Erdos202.ResidueAssignment Q),
              (∀ (q : Nat),
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                        (@Finset.instSetLike.{0} Nat))
                      Q q →
                    And
                      (@LE.le.{0} Nat instLENat
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) q)
                      (@LE.le.{0} Nat instLENat q N)) →
                Erdos202.PairwiseDisjointResidues Q a →
                  @GE.ge.{0} Real Real.instLE
                      (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Nat Q))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Nat.cast.{0} Real Real.instNatCast (Erdos202.f N))
                        (Erdos202.Lscale (@Neg.neg.{0} Real Real.instNeg ε) N)) →
                    @Exists.{1} (Erdos202.PrunedData N) fun (D : Erdos202.PrunedData N) ↦
                      @GE.ge.{0} Real Real.instLE
                        (@Nat.cast.{0} Real Real.instNatCast
                          (@Finset.card.{0} Nat (@Erdos202.PrunedData.Q N D)))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Nat Q))
                          (Erdos202.Lscale (@Neg.neg.{0} Real Real.instNeg ε) N)))
          (@Filter.atTop.{0} Nat Nat.instPreorder)
  := by
  sorry

theorem Erdos202.erdos202_main :
    Erdos202.Erdos202Statement
  := by
  sorry
