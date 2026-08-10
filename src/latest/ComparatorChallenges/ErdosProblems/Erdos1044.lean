import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Std.Tactic.BVDecide.LRAT.Internal.Clause

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.longLine false

open Polynomial MeasureTheory Topology Set Metric

noncomputable section

namespace Erdos1044

def OmegaSet (f : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ < 1}

def componentBoundaryLength (f : Polynomial ℂ) (z : ℂ) : ENNReal :=
  μH[(1 : ℝ)] (frontier (connectedComponentIn (OmegaSet f) z))

def LambdaFn (f : Polynomial ℂ) : ENNReal :=
  ⨆ z ∈ OmegaSet f, componentBoundaryLength f z

def IsAdmissible (f : Polynomial ℂ) : Prop :=
  f.Monic ∧ ∀ z : ℂ, f.IsRoot z → ‖z‖ ≤ 1

def lambdaInf : ENNReal :=
  ⨅ (f : Polynomial ℂ) (_ : IsAdmissible f ∧ f.natDegree ≥ 1), LambdaFn f
end Erdos1044

open Set Metric MeasureTheory Topology

noncomputable section

namespace Erdos1044

end Erdos1044

open Polynomial MeasureTheory Topology Set Metric Complex

noncomputable section

namespace Erdos1044

end Erdos1044

open Set Metric MeasureTheory Topology Complex

noncomputable section

namespace Erdos1044

end Erdos1044

open Polynomial MeasureTheory Topology Set Metric Complex

noncomputable section

namespace Erdos1044

end Erdos1044

open Polynomial MeasureTheory Topology Set Metric Complex

noncomputable section

namespace Erdos1044

end Erdos1044

open MeasureTheory Topology Set Metric Filter

noncomputable section

namespace Erdos1044

end Erdos1044

open Polynomial MeasureTheory Topology Set Metric Complex

noncomputable section

namespace Erdos1044

end Erdos1044

open Polynomial MeasureTheory Topology Set Metric Complex

noncomputable section

namespace Erdos1044

end Erdos1044

open Polynomial MeasureTheory Topology Set Metric Complex MeasureTheory.Measure

noncomputable section

namespace Erdos1044

end Erdos1044

open Polynomial MeasureTheory Topology Set Metric Complex

noncomputable section

namespace Erdos1044

end Erdos1044

open Polynomial MeasureTheory Topology Set Metric Complex

noncomputable section

namespace Erdos1044

end Erdos1044

open Polynomial MeasureTheory Topology Set Metric Complex

noncomputable section

namespace Erdos1044

end Erdos1044

open Polynomial MeasureTheory Topology Set Metric

noncomputable section

namespace Erdos1044

end Erdos1044

attribute [local instance] Classical.propDecidable

theorem Erdos1044.erdos_problem_1044 :
    @Eq.{1} ENNReal Erdos1044.lambdaInf
      (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
          (@AddMonoidWithOne.toNatCast.{0} ENNReal
            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
  := by
  sorry
