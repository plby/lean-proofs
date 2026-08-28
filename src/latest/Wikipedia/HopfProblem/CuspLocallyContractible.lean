import Wikipedia.HopfProblem.CuspLocallyContractibleCharts
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLocalContractibilityCharts
import Wikipedia.HopfProblem.CuspPositiveRetractionDescent
import Wikipedia.HopfProblem.CuspNormalizationSheafCuspBasic

/-!
# Local contractibility of the original cusp central fibre

The original quotient charts restrict to actual central-fibre charts.
The zero-product affine model has a basis of genuine star-convex small
relative balls.  Locality through the unchanged open chart subspaces
therefore proves strong and classical local contractibility of the
original cusp fibre, in both its existing singular-topology and sheaf
notations.  No replacement homotopy model or cohomology hypothesis is used.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspLocallyContractible

open CuspQuotient ToricSpace
open ConstantSheafSingularComparison.LocalContractibility

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

include hε hε1 hC hR

/-- The literal original quotient central fibre has a basis of contractible neighbourhoods. -/
theorem quotientCentralFibre_stronglyLocallyContractible :
    StronglyLocallyContractibleSpace (CuspRetraction.QuotientCentralFibre C ε) := by
  apply stronglyLocallyContractible_of_open_neighborhoods
  intro x
  obtain ⟨a, s, hx⟩ := centralFibreOpen_cover C ε hε hε1 hC hR x
  exact ⟨centralFibreOpen C ε hε hε1 hC hR a s, hx,
    centralFibreOpen_stronglyLocallyContractible C ε hε hε1 hC hR a s⟩

/-- Actual local contractibility in Mathlib's classical null-homotopic-inclusion sense. -/
theorem quotientCentralFibre_locallyContractible :
    LocallyContractibleSpace (CuspRetraction.QuotientCentralFibre C ε) := by
  have := quotientCentralFibre_stronglyLocallyContractible C ε hε hε1 hC hR
  exact StronglyLocallyContractibleSpace.locallyContractible

/-- The sheaf-resolution base is the same original subspace, with the same contractible basis. -/
theorem centralSpace_stronglyLocallyContractible :
    StronglyLocallyContractibleSpace (CuspNormalization.SheafResolution.CentralSpace C ε) :=
  quotientCentralFibre_stronglyLocallyContractible C ε hε hε1 hC hR

/-- The genuine sheaf-resolution base satisfies the required classical local contractibility. -/
theorem centralSpace_locallyContractible :
    LocallyContractibleSpace (CuspNormalization.SheafResolution.CentralSpace C ε) :=
  quotientCentralFibre_locallyContractible C ε hε hε1 hC hR

end Wikipedia.HopfProblem.CuspLocallyContractible
