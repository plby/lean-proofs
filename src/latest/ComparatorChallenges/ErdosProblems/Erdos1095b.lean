import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos1095b

open Filter Real

open scoped Asymptotics Topology

def Good (k n : ℕ) : Prop :=
  k + 1 < n ∧ k < Nat.minFac (Nat.choose n k)
open Classical in
noncomputable def g (k : ℕ) : ℕ :=
  if h : ∃ n : ℕ, Good k n then Nat.find h else 0
end Erdos1095b

attribute [local instance] Classical.propDecidable

theorem Erdos1095b.erdos_1095_weaker_upper_bound :
    @Exists.{1} (Nat → Real) fun (f : Nat → Real) ↦
      And
        (@Filter.Tendsto.{0, 0} Nat Real f (@Filter.atTop.{0} Nat Nat.instPreorder)
          (@nhds.{0} Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
        (∀ (k : Nat),
          @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k →
            @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (Erdos1095b.g k))
              (Real.exp
                (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                  (@Nat.cast.{0} Real Real.instNatCast k)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) (f k)))))
  := by
  sorry
