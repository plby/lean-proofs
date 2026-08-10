import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos1197

open MeasureTheory Set
open scoped ENNReal

def Phi (A : Set ℝ) : Set ℝ :=
  Ico (1/2 : ℝ) 1 ∩ {x | ∃ m : ℕ, 0 < m ∧ ((m : ℝ) * x) ∈ A}

def I_inf : Set ℝ := Icc (16/25 : ℝ) (2/3)

axiom bm_approx_data :
    ∃ K₀ : ℕ, ∀ k, K₀ ≤ k →
      ∃ N_k : ℕ, ∀ ν, N_k ≤ ν →
        ∃ q : ℕ, 0 < q ∧
          (∀ y ∈ I_inf, ∃ m : ℕ, 0 < m ∧
            (m : ℝ) * y ∈ Ioo ((8 : ℝ) / 9 * 2 ^ ν) ((2 : ℝ) ^ ν) ∧
            ∃ n : ℤ, |Real.logb 2 ((m : ℝ) * y) - (n : ℝ) / (q : ℝ)| <
              1 / ((q : ℝ) * 2 ^ k)) ∧
          (∀ n : ℕ, (n : ℝ) ∈ Ioo ((7 : ℝ) / 8 * 2 ^ ν) ((9 : ℝ) / 8 * 2 ^ ν) →
            ∃ m : ℤ, |Real.logb 2 (n : ℝ) - (m : ℝ) / (q : ℝ)| <
              1 / (4 * (q : ℝ) * 2 ^ k))
end Erdos1197

open Erdos1197

attribute [local instance] Classical.propDecidable

theorem Erdos1197.negative_answer :
    @Exists.{1} (Set.{0} Real) fun (E : Set.{0} Real) ↦
      And (@MeasurableSet.{0} Real Real.measurableSpace E)
        (And
          (@LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) E
            (@Set.Ioi.{0} Real Real.instPreorder
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
          (And
            (@LT.lt.{0} ENNReal
              (@Preorder.toLT.{0} ENNReal
                (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
              (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))
              (@DFunLike.coe.{1, 1, 1}
                (@MeasureTheory.Measure.{0} Real
                  (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace))
                (Set.{0} Real) (fun (x : Set.{0} Real) ↦ ENNReal)
                (@MeasureTheory.Measure.instFunLike.{0} Real
                  (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace))
                (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) E))
            (∀ (x : Real),
              @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real) Erdos1197.I_inf
                  x →
                @Set.Infinite.{0} Nat
                  (@setOf.{0} Nat fun (n : Nat) ↦
                    And
                      (@LT.lt.{0} Nat instLTNat
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
                      (∀ (r : Nat),
                        @LT.lt.{0} Nat instLTNat
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r →
                          Not
                            (@Exists.{1} Real fun (e : Real) ↦
                              And
                                (@Membership.mem.{0, 0} Real (Set.{0} Real)
                                  (@Set.instMembership.{0} Real) E e)
                                (@Eq.{1} Real x
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                      (@instHDiv.{0} Real
                                        (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                      (@Nat.cast.{0} Real Real.instNatCast r)
                                      (@Nat.cast.{0} Real Real.instNatCast n))
                                    e))))))))
  := by
  sorry
