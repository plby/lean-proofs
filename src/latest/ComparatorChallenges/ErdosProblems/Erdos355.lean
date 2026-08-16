import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Std.Tactic.BVDecide.LRAT.Internal.Clause

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.multiGoal false
set_option linter.style.cases false
set_option linter.style.whitespace false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 50000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

noncomputable section

namespace Erdos355

open Set Filter Topology
open scoped BigOperators

def IsLambdaLacunary (lambda : ℝ) (seq : ℕ → ℝ) : Prop :=
  ∀ i, seq (i + 1) / seq i ≥ lambda
def IsLacunary (a : ℕ → ℕ) : Prop :=
  ∃ lambda_val > 1, ∀ i ≥ 1, (a (i + 1) : ℝ) / a i ≥ lambda_val
def SubsetSums (seq : ℕ → ℝ) : Set ℝ :=
  { s | ∃ t : Finset ℕ, s = ∑ i ∈ t, seq i }
def FillsInterval (lambda : ℝ) (alpha beta : ℝ) : Prop :=
  ∃ n : ℕ → ℕ,
    (∀ i, 0 < n i) ∧
    IsLambdaLacunary lambda (fun i => n i) ∧
    Set.Ioo alpha beta ∩ {x | ∃ q : ℚ, x = q} ⊆ SubsetSums (fun i => (1 : ℝ) / n i)
noncomputable def R_lambda (lambda : ℝ) : ℝ :=
  sSup {len | ∃ alpha beta, beta - alpha = len ∧ FillsInterval lambda alpha beta}
def S_cond (S : Set ℕ) : Prop :=
  (∀ s ∈ S, s > 0) ∧ (∀ s ∈ S, 2 * s ∈ S) ∧ (∀ k, Odd k → ∃ s ∈ S, k ∣ s)
noncomputable def TargetInterval (f : ℕ → ℝ) : Set ℝ :=
  if Summable f then Set.Ico 0 (∑' i, f i) else Set.Ici 0
noncomputable def a_seq (lambda : ℝ) : ℕ → ℕ
| 0 => 1
| (n + 1) => Nat.ceil (lambda * (a_seq lambda n))
end Erdos355

attribute [local instance] Classical.propDecidable

theorem Erdos355.Theorem_1 :
    ∀ (lambda : Real),
      And
          (@LT.lt.{0} Real Real.instLT
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) lambda)
          (@LT.lt.{0} Real Real.instLT lambda
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) →
        @Exists.{1} (Nat → Nat) fun (n : Nat → Nat) ↦
          And
            (∀ (i : Nat),
              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (n i))
            (And
              (Erdos355.IsLambdaLacunary lambda fun (i : Nat) ↦
                @Nat.cast.{0} Real Real.instNatCast (n i))
              (And
                (@Filter.Tendsto.{0, 0} Nat Real
                  (fun (i : Nat) ↦
                    @HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@Nat.cast.{0} Real Real.instNatCast
                        (n
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (@Nat.cast.{0} Real Real.instNatCast (n i)))
                  (@Filter.atTop.{0} Nat Nat.instPreorder)
                  (@nhds.{0} Real
                    (@UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
                (@LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real)
                  (@Inter.inter.{0} (Set.{0} Real) (@Set.instInter.{0} Real)
                    (@Set.Icc.{0} Real Real.instPreorder
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                    (@Set.ofPred.{0} Real fun (x : Real) ↦
                      @Exists.{1} Rat fun (q : Rat) ↦
                        @Eq.{1} Real x (@Rat.cast.{0} Real Real.instRatCast q)))
                  (Erdos355.SubsetSums fun (i : Nat) ↦
                    @HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@Nat.cast.{0} Real Real.instNatCast (n i))))))
  := by
  sorry
theorem Erdos355.Theorem_2 :
    ∀ (lambda : Real),
      And
          (@LT.lt.{0} Real Real.instLT
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) lambda)
          (@LT.lt.{0} Real Real.instLT lambda
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) →
        @Eq.{1} Real (Erdos355.R_lambda lambda)
          (@tsum.{0, 0} Real Nat Real.instAddCommMonoid
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (fun (i : Nat) ↦
              @HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@Nat.cast.{0} Real Real.instNatCast (Erdos355.a_seq lambda i)))
            (SummationFilter.unconditional.{0} Nat))
  := by
  sorry
theorem Erdos355.Theorem_3 :
    ∀ (Lambda lambda : Real),
      @GE.ge.{0} Real Real.instLE Lambda
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) →
        And
            (@LT.lt.{0} Real Real.instLT
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) lambda)
            (@LT.lt.{0} Real Real.instLT lambda
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Lambda
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) Lambda
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))) →
          @Exists.{1} (Nat → Nat) fun (n : Nat → Nat) ↦
            And
              (Erdos355.IsLambdaLacunary lambda fun (i : Nat) ↦
                @Nat.cast.{0} Real Real.instNatCast (n i))
              (And
                (∀ (i : Nat),
                  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (n i))
                (And
                  (@Set.Infinite.{0} Nat
                    (@Set.ofPred.{0} Nat fun (i : Nat) ↦
                      @GT.gt.{0} Real Real.instLT
                        (@Nat.cast.{0} Real Real.instNatCast
                          (n
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Lambda
                          (@Nat.cast.{0} Real Real.instNatCast (n i)))))
                  (@GE.ge.{0} (Set.{0} Real) (@Set.instLE.{0} Real)
                    (Erdos355.SubsetSums fun (i : Nat) ↦
                      @HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@Nat.cast.{0} Real Real.instNatCast (n i)))
                    (@Inter.inter.{0} (Set.{0} Real) (@Set.instInter.{0} Real)
                      (Erdos355.TargetInterval fun (i : Nat) ↦
                        @HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@Nat.cast.{0} Real Real.instNatCast (n i)))
                      (@Set.ofPred.{0} Real fun (x : Real) ↦
                        @Exists.{1} Rat fun (q : Rat) ↦
                          @Eq.{1} Real x (@Rat.cast.{0} Real Real.instRatCast q))))))
  := by
  sorry
theorem Erdos355.Theorem_4 :
    ∀ (S : Set.{0} Nat),
      Erdos355.S_cond S →
        @Eq.{1} (Set.{0} Real)
          (Erdos355.SubsetSums fun (i : Nat) ↦
            @HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@Nat.cast.{0} Real Real.instNatCast
                (Nat.nth
                  (fun (x : Nat) ↦
                    @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) S x)
                  i)))
          (@Inter.inter.{0} (Set.{0} Real) (@Set.instInter.{0} Real)
            (Erdos355.TargetInterval fun (i : Nat) ↦
              @HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@Nat.cast.{0} Real Real.instNatCast
                  (Nat.nth
                    (fun (x : Nat) ↦
                      @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) S x)
                    i)))
            (@Set.ofPred.{0} Real fun (x : Real) ↦
              @Exists.{1} Rat fun (q : Rat) ↦ @Eq.{1} Real x (@Rat.cast.{0} Real Real.instRatCast q)))
  := by
  sorry
theorem Erdos355.erdos_355 :
    @Exists.{1} (Nat → Nat) fun (A : Nat → Nat) ↦
      And (Erdos355.IsLacunary A)
        (@Exists.{1} Real fun (u : Real) ↦
          @Exists.{1} Real fun (v : Real) ↦
            And (@LT.lt.{0} Real Real.instLT u v)
              (∀ (q : Rat),
                @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                    (@Set.Ioo.{0} Real Real.instPreorder u v) (@Rat.cast.{0} Real Real.instRatCast q) →
                  @Membership.mem.{0, 0} Rat (Set.{0} Rat) (@Set.instMembership.{0} Rat)
                    (@Set.ofPred.{0} Rat fun (x : Rat) ↦
                      @Exists.{1} (Finset.{0} Nat) fun (A' : Finset.{0} Nat) ↦
                        @Exists.{0}
                          (@LE.le.{0} (Set.{0} Nat) (@Set.instLE.{0} Nat)
                            (@SetLike.coe.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat) A')
                            (@Set.range.{0, 1} Nat Nat A))
                          fun
                            (x_1 :
                              @LE.le.{0} (Set.{0} Nat) (@Set.instLE.{0} Nat)
                                (@SetLike.coe.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)
                                  A')
                                (@Set.range.{0, 1} Nat Nat A)) ↦
                          @Eq.{1} Rat
                            (@Finset.sum.{0, 0} Nat Rat Rat.addCommMonoid A' fun (a : Nat) ↦
                              @HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                                (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                (@Nat.cast.{0} Rat Rat.instNatCast a))
                            x)
                    q))
  := by
  sorry
