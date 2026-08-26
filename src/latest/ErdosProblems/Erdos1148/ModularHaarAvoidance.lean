import ErdosProblems.Erdos1148.ErgodicAvoidance
import ErdosProblems.Erdos1148.ModularHaarTimeOneErgodic

/-! # Open-set avoidance has vanishing modular Haar mass -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Filter
open scoped Topology

theorem modularHaar_open_avoidance_tendsto_zero {U : Set ModularOrbitSpace}
    (hU : IsOpen U) (hne : U.Nonempty) :
    Tendsto (fun n : ℕ => normalizedModularHaarMeasure (finiteOrbitAvoidance modularTimeOne U n))
      atTop (𝓝 0) :=
  normalizedModularHaarMeasure_time_one_ergodic.finiteOrbitAvoidance_mass_tendsto_zero
    hU.measurableSet (normalizedModularHaarMeasure_open_pos hU hne)

end Erdos1148.DukeArithmetic
