import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos268

open Set Filter Topology Matrix
open scoped BigOperators

def harmonicSubseriesSet : Set (Fin 3 → ℝ) :=
  { p | ∃ A : Set ℕ, A.Infinite ∧ (∀ n ∈ A, 0 < n) ∧
    Summable (fun (n : A) => (1 : ℝ) / (n : ℕ)) ∧
    ∀ i : Fin 3, p i = ∑' (n : A), 1 / (((n : ℕ) : ℝ) + ((i : ℕ) : ℝ)) }
noncomputable section

end

noncomputable section

end
end Erdos268

attribute [local instance] Classical.propDecidable

theorem Erdos268.harmonicSubseriesSet_interior_nonempty :
    @Set.Nonempty.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real)
      (@interior.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real)
        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) ↦ Real)
          fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) ↦
          @UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        Erdos268.harmonicSubseriesSet)
  := by
  sorry
