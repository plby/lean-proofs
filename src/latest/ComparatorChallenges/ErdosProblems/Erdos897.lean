import Mathlib.Analysis.SpecialFunctions.Log.Basic

attribute [local instance] Classical.propDecidable

universe u_1

noncomputable abbrev Erdos897.f_hypothesis.match_1 :
    (motive : Prod.{0, 0} Nat Nat → Sort u_1) →
      (x : Prod.{0, 0} Nat Nat) → ((p _k : Nat) → motive (@Prod.mk.{0, 0} Nat Nat p _k)) → motive x
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

theorem Erdos897.erdos_897.parts.i :
    Iff
      (∀ (f : Nat → Real),
        (∀ (a : Nat),
            @GT.gt.{0} Nat instLTNat a (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              ∀ (b : Nat),
                @GT.gt.{0} Nat instLTNat b
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                  a.Coprime b →
                    @Eq.{1} Real
                      (f (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) a b))
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (f a)
                        (f b))) →
          @Eq.{1} EReal
              (@Filter.limsup.{0, 0} EReal (Prod.{0, 0} Nat Nat)
                (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} EReal
                  (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} EReal
                    (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} EReal
                      instCompleteLinearOrderEReal)))
                (fun (x : Prod.{0, 0} Nat Nat) ↦
                  Erdos897.f_hypothesis.match_1.{1} (fun (x : Prod.{0, 0} Nat Nat) ↦ EReal) x
                    fun (p k : Nat) ↦
                    @HDiv.hDiv.{0, 0, 0} EReal EReal EReal
                      (@instHDiv.{0} EReal (@DivInvMonoid.toDiv.{0} EReal EReal.instDivInvMonoid))
                      ↑(f
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat
                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                            p k))
                      ↑(Real.log
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat
                              (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            (@Nat.cast.{0} Real Real.instNatCast p) k)))
                (@Min.min.{0} (Filter.{0} (Prod.{0, 0} Nat Nat))
                  (@Filter.instInf.{0} (Prod.{0, 0} Nat Nat))
                  (@Filter.atTop.{0} (Prod.{0, 0} Nat Nat)
                    (@Prod.instPreorder.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder))
                  (@Filter.principal.{0} (Prod.{0, 0} Nat Nat)
                    (@setOf.{0} (Prod.{0, 0} Nat Nat) fun (x : Prod.{0, 0} Nat Nat) ↦
                      Erdos897.f_hypothesis.match_1.{1} (fun (x : Prod.{0, 0} Nat Nat) ↦ Prop) x
                        fun (p _k : Nat) ↦ Nat.Prime p))))
              (@Top.top.{0} EReal instTopEReal) →
            @Eq.{1} EReal
              (@Filter.limsup.{0, 0} EReal Nat
                (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} EReal
                  (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} EReal
                    (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} EReal
                      instCompleteLinearOrderEReal)))
                (fun (n : Nat) ↦
                  @HDiv.hDiv.{0, 0, 0} EReal EReal EReal
                    (@instHDiv.{0} EReal (@DivInvMonoid.toDiv.{0} EReal EReal.instDivInvMonoid))
                    (@HSub.hSub.{0, 0, 0} EReal EReal EReal
                      (@instHSub.{0} EReal
                        (@SubNegMonoid.toSub.{0} EReal
                          (@SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.instSubNegZeroMonoid)))
                      ↑(f
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      ↑(f n))
                    ↑(Real.log (@Nat.cast.{0} Real Real.instNatCast n)))
                (@Filter.atTop.{0} Nat Nat.instPreorder))
              (@Top.top.{0} EReal instTopEReal))
      (@Eq.{1} Bool Bool.false Bool.true)
  := by
  sorry

theorem Erdos897.erdos_897.parts.ii :
    Iff
      (∀ (f : Nat → Real),
        (∀ (a : Nat),
            @GT.gt.{0} Nat instLTNat a (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              ∀ (b : Nat),
                @GT.gt.{0} Nat instLTNat b
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                  a.Coprime b →
                    @Eq.{1} Real
                      (f (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) a b))
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (f a)
                        (f b))) →
          @Eq.{1} EReal
              (@Filter.limsup.{0, 0} EReal (Prod.{0, 0} Nat Nat)
                (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} EReal
                  (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} EReal
                    (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} EReal
                      instCompleteLinearOrderEReal)))
                (fun (x : Prod.{0, 0} Nat Nat) ↦
                  Erdos897.f_hypothesis.match_1.{1} (fun (x : Prod.{0, 0} Nat Nat) ↦ EReal) x
                    fun (p k : Nat) ↦
                    @HDiv.hDiv.{0, 0, 0} EReal EReal EReal
                      (@instHDiv.{0} EReal (@DivInvMonoid.toDiv.{0} EReal EReal.instDivInvMonoid))
                      ↑(f
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat
                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                            p k))
                      ↑(Real.log
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat
                              (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            (@Nat.cast.{0} Real Real.instNatCast p) k)))
                (@Min.min.{0} (Filter.{0} (Prod.{0, 0} Nat Nat))
                  (@Filter.instInf.{0} (Prod.{0, 0} Nat Nat))
                  (@Filter.atTop.{0} (Prod.{0, 0} Nat Nat)
                    (@Prod.instPreorder.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder))
                  (@Filter.principal.{0} (Prod.{0, 0} Nat Nat)
                    (@setOf.{0} (Prod.{0, 0} Nat Nat) fun (x : Prod.{0, 0} Nat Nat) ↦
                      Erdos897.f_hypothesis.match_1.{1} (fun (x : Prod.{0, 0} Nat Nat) ↦ Prop) x
                        fun (p _k : Nat) ↦ Nat.Prime p))))
              (@Top.top.{0} EReal instTopEReal) →
            @Eq.{1} EReal
              (@Filter.limsup.{0, 0} EReal Nat
                (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} EReal
                  (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} EReal
                    (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} EReal
                      instCompleteLinearOrderEReal)))
                (fun (n : Nat) ↦
                  @HDiv.hDiv.{0, 0, 0} EReal EReal EReal
                    (@instHDiv.{0} EReal (@DivInvMonoid.toDiv.{0} EReal EReal.instDivInvMonoid))
                    ↑(f
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    ↑(f n))
                (@Filter.atTop.{0} Nat Nat.instPreorder))
              (@Top.top.{0} EReal instTopEReal))
      (@Eq.{1} Bool Bool.false Bool.true)
  := by
  sorry
