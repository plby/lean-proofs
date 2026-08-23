/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

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


open Polynomial MeasureTheory Topology Set Metric
open Set Metric MeasureTheory Topology
open Polynomial MeasureTheory Topology Set Metric Complex
open Set Metric MeasureTheory Topology Complex
open MeasureTheory Topology Set Metric Filter
open Polynomial MeasureTheory Topology Set Metric Complex MeasureTheory.Measure

namespace Erdos1044

open scoped Classical in
theorem erdos_problem_1044 : lambdaInf = 2 := by
  sorry

end Erdos1044
