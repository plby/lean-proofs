import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Homotopy.LocallyContractible

/-!
# Local contractibility of real normed spaces

The positive-radius metric balls form an actual neighborhood basis.  Each
ball is nonempty and convex, so affine contraction makes it contractible.
This gives strong local contractibility and hence classical local
contractibility without finite-dimensionality, completeness, or separation
assumptions.  The results are theorems, not new global instances.
-/

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.LocalContractibility

variable (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every real seminormed vector space has a basis of contractible
neighborhoods, given by its positive-radius open balls. -/
theorem normedSpace_stronglyLocallyContractibleSpace :
    StronglyLocallyContractibleSpace E :=
  StronglyLocallyContractibleSpace.of_bases
    (p := fun (_ : E) (r : ℝ) => 0 < r) (s := fun x r => Metric.ball x r)
    (fun _ => Metric.nhds_basis_ball)
    (fun x r hr => (convex_ball x r).contractibleSpace ⟨x, Metric.mem_ball_self hr⟩)

/-- Classical local contractibility follows from the actual open-ball
contractible neighborhood basis. -/
theorem normedSpace_locallyContractibleSpace : LocallyContractibleSpace E := by
  let := normedSpace_stronglyLocallyContractibleSpace E
  exact StronglyLocallyContractibleSpace.locallyContractible

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.LocalContractibility
