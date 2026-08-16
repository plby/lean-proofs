import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Std.Tactic.BVDecide.LRAT.Internal.Clause

open Nat Finset Real Filter Asymptotics Topology
open scoped Pointwise

namespace BinQuadForm

end BinQuadForm

axiom mertens_product :
    Tendsto
      (fun y : ℝ =>
        (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊y⌋₊), ((p : ℝ) / (p - 1))) /
          (Real.exp Real.eulerMascheroniConstant * Real.log y))
      atTop (𝓝 1)

axiom linnik_dvd :
  ∃ C : ℝ, ∃ L : ℕ, 1 ≤ C ∧ 1 ≤ L ∧
    ∀ M : ℕ, 1 ≤ M →
      ∃ ℓ : ℕ, Nat.Prime ℓ ∧ M ∣ ℓ - 1 ∧ (ℓ : ℝ) ≤ C * (M : ℝ) ^ L

namespace Erdos694

open Filter Asymptotics Topology
open scoped BigOperators Nat

noncomputable def R (x : ℕ) : ℝ :=
  ⨆ n ∈ {n | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n},
    let mmax := sSup {m | Nat.totient m = n}
    let mmin := sInf {m | Nat.totient m = n}
    (mmax : ℝ) / mmin
namespace LowerConstruction

open Filter
open scoped BigOperators Nat

noncomputable def smallPrimes (Y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Y).filter Nat.Prime

noncomputable def P (Y : ℕ) : ℕ :=
  ∏ p ∈ smallPrimes Y, p

noncomputable def A (Y : ℕ) : ℕ :=
  ∏ p ∈ smallPrimes Y, (p - 1)

noncomputable def largeFactors (Y U : ℕ) : Finset ℕ :=
  U.primeFactors.filter fun q => Y < q

noncomputable def Q (Y U : ℕ) : ℕ :=
  ∏ q ∈ largeFactors Y U, q
end LowerConstruction

end Erdos694

attribute [local instance] Classical.propDecidable

theorem Erdos694.totient_sq_ge_half :
    ∀ (m : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m →
        @LE.le.{0} Nat instLENat m
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              m.totient (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  := by
  sorry
theorem Erdos694.landau_max_ratio :
    @Filter.Tendsto.{0, 0} Real Real
      (fun (T : Real) ↦
        @HDiv.hDiv.{0, 0, 0} Real Real Real
          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@iSup.{0, 1} Real Nat Real.instSupSet fun (m : Nat) ↦
            @iSup.{0, 0} Real
              (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
                (@Set.Icc.{0} Nat Nat.instPreorder
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.floor.{0} Real Real.semiring Real.partialOrder
                    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder
                      Real.instFloorRing)
                    T))
                m)
              Real.instSupSet
              fun
                (h :
                  @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
                    (@Set.Icc.{0} Nat Nat.instPreorder
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.floor.{0} Real Real.semiring Real.partialOrder
                        (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder
                          Real.instFloorRing)
                        T))
                    m) ↦
              @HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@Nat.cast.{0} Real Real.instNatCast m) (@Nat.cast.{0} Real Real.instNatCast m.totient))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Real.exp Real.eulerMascheroniConstant) (Real.log (Real.log T))))
      (@Filter.atTop.{0} Real Real.instPreorder)
      (@nhds.{0} Real
        (@UniformSpace.toTopologicalSpace.{0} Real
          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  := by
  sorry
theorem Erdos694.R_upper_bound :
    ∀ (ε : Real),
      @GT.gt.{0} Real Real.instLT ε
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @Filter.Eventually.{0} Nat
          (fun (x : Nat) ↦
            @LE.le.{0} Real Real.instLE (Erdos694.R x)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (Real.exp Real.eulerMascheroniConstant) ε)
                (Real.log (Real.log (@Nat.cast.{0} Real Real.instNatCast x)))))
          (@Filter.atTop.{0} Nat Nat.instPreorder)
  := by
  sorry
theorem Erdos694.LowerConstruction.totient_a_eq_totient_b :
    ∀ (Y U ℓ : Nat),
      Nat.Prime ℓ →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) U →
          @LT.lt.{0} Nat instLTNat U ℓ →
            @Eq.{1} Nat
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (Erdos694.LowerConstruction.A Y) U)
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) ℓ
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
              @Eq.{1} Nat
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) ℓ
                    (Erdos694.LowerConstruction.Q Y U)).totient
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (Erdos694.LowerConstruction.P Y) U)
                    (Erdos694.LowerConstruction.Q Y U)).totient
  := by
  sorry
theorem Erdos694.collision_at_height :
    ∀ (C : Real) (L : Nat),
      @LE.le.{0} Real Real.instLE
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) C →
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) L →
          (∀ (M : Nat),
              @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M →
                @Exists.{1} Nat fun (ℓ : Nat) ↦
                  And (Nat.Prime ℓ)
                    (And
                      (@Dvd.dvd.{0} Nat Nat.instDvd M
                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) ℓ
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast ℓ)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat
                              (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            (@Nat.cast.{0} Real Real.instNatCast M) L))))) →
            ∀ (ε : Real),
              @LT.lt.{0} Real Real.instLT
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
                @Exists.{1} Real fun (K : Real) ↦
                  And
                    (@LT.lt.{0} Real Real.instLT
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K)
                    (@Filter.Eventually.{0} Nat
                      (fun (Y : Nat) ↦
                        @Exists.{1} Nat fun (a : Nat) ↦
                          @Exists.{1} Nat fun (b : Nat) ↦
                            @Exists.{1} Nat fun (n : Nat) ↦
                              And
                                (@LE.le.{0} Nat instLENat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a)
                                (And
                                  (@LE.le.{0} Nat instLENat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) b)
                                  (And
                                    (@LE.le.{0} Nat instLENat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n)
                                    (And (@Eq.{1} Nat a.totient n)
                                      (And (@Eq.{1} Nat b.totient n)
                                        (And
                                          (@GE.ge.{0} Real Real.instLE
                                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                              (@instHDiv.{0} Real
                                                (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                              (@Nat.cast.{0} Real Real.instNatCast b)
                                              (@Nat.cast.{0} Real Real.instNatCast a))
                                            (@HMul.hMul.{0, 0, 0} Real Real Real
                                              (@instHMul.{0} Real Real.instMul)
                                              (@HSub.hSub.{0, 0, 0} Real Real Real
                                                (@instHSub.{0} Real Real.instSub)
                                                (Real.exp Real.eulerMascheroniConstant) ε)
                                              (Real.log (@Nat.cast.{0} Real Real.instNatCast Y))))
                                          (@LE.le.{0} Real Real.instLE
                                            (@Nat.cast.{0} Real Real.instNatCast n)
                                            (Real.exp
                                              (@HMul.hMul.{0, 0, 0} Real Real Real
                                                (@instHMul.{0} Real Real.instMul) K
                                                (@Nat.cast.{0} Real Real.instNatCast Y))))))))))
                      (@Filter.atTop.{0} Nat Nat.instPreorder))
  := by
  sorry
theorem Erdos694.totient_collision_construction :
    ∀ (ε : Real),
      @GT.gt.{0} Real Real.instLT ε
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @Filter.Eventually.{0} Nat
          (fun (x : Nat) ↦
            @Exists.{1} Nat fun (a : Nat) ↦
              @Exists.{1} Nat fun (b : Nat) ↦
                @Exists.{1} Nat fun (n : Nat) ↦
                  And
                    (@LE.le.{0} Nat instLENat
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a)
                    (And
                      (@LE.le.{0} Nat instLENat
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) b)
                      (And
                        (@LE.le.{0} Nat instLENat
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n)
                        (And (@LE.le.{0} Nat instLENat n x)
                          (And (@Eq.{1} Nat a.totient n)
                            (And (@Eq.{1} Nat b.totient n)
                              (@GE.ge.{0} Real Real.instLE
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real
                                    (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                  (@Nat.cast.{0} Real Real.instNatCast b)
                                  (@Nat.cast.{0} Real Real.instNatCast a))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                    (Real.exp Real.eulerMascheroniConstant) ε)
                                  (Real.log (Real.log (@Nat.cast.{0} Real Real.instNatCast x)))))))))))
          (@Filter.atTop.{0} Nat Nat.instPreorder)
  := by
  sorry
theorem Erdos694.R_lower_bound :
    ∀ (ε : Real),
      @GT.gt.{0} Real Real.instLT ε
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @Filter.Eventually.{0} Nat
          (fun (x : Nat) ↦
            @GE.ge.{0} Real Real.instLE (Erdos694.R x)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (Real.exp Real.eulerMascheroniConstant) ε)
                (Real.log (Real.log (@Nat.cast.{0} Real Real.instNatCast x)))))
          (@Filter.atTop.{0} Nat Nat.instPreorder)
  := by
  sorry
theorem Erdos694.totient_fibre_extremes :
    @Filter.Tendsto.{0, 0} Nat Real
      (fun (x : Nat) ↦
        @HDiv.hDiv.{0, 0, 0} Real Real Real
          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) (Erdos694.R x)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Real.exp Real.eulerMascheroniConstant)
            (Real.log (Real.log (@Nat.cast.{0} Real Real.instNatCast x)))))
      (@Filter.atTop.{0} Nat Nat.instPreorder)
      (@nhds.{0} Real
        (@UniformSpace.toTopologicalSpace.{0} Real
          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  := by
  sorry
theorem Erdos694.permanence_step :
    ∀ (a b r : Nat),
      @Eq.{1} Nat a.totient b.totient →
        Nat.Prime r →
          Not (@Dvd.dvd.{0} Nat Nat.instDvd r a) →
            Not (@Dvd.dvd.{0} Nat Nat.instDvd r b) →
              @Eq.{1} Nat (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) r a).totient
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) r b).totient
  := by
  sorry
theorem Erdos694.infinitely_many_collisions :
    ∀ (a b : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) b →
        @LT.lt.{0} Nat instLTNat b a →
          @Eq.{1} Nat a.totient b.totient →
            @Set.Infinite.{0} Nat
              (@Set.ofPred.{0} Nat fun (N : Nat) ↦
                @Exists.{1} Nat fun (x : Nat) ↦
                  @Exists.{1} Nat fun (y : Nat) ↦
                    And (@Eq.{1} Nat x.totient N)
                      (And (@Eq.{1} Nat y.totient N)
                        (And (@LT.lt.{0} Nat instLTNat y x)
                          (@GE.ge.{0} Nat instLENat
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) b x)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) a y)))))
  := by
  sorry
theorem Erdos694.erdos_694_asymptotic :
    @Filter.Tendsto.{0, 0} Nat Real
      (fun (x : Nat) ↦
        @HDiv.hDiv.{0, 0, 0} Real Real Real
          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) (Erdos694.R x)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Real.exp Real.eulerMascheroniConstant)
            (Real.log (Real.log (@Nat.cast.{0} Real Real.instNatCast x)))))
      (@Filter.atTop.{0} Nat Nat.instPreorder)
      (@nhds.{0} Real
        (@UniformSpace.toTopologicalSpace.{0} Real
          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  := by
  sorry
