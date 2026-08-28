import Wikipedia.HopfProblem.CuspCentralHomologySpecializationCover
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleMayerVietorisNaturality

/-!
# Connecting naturality for the actual cusp specialization covers

The existing product collapse carries each literal source radial region
into the corresponding literal central region. The proved naturality of
the actual singular Mayer–Vietoris sequence therefore gives this exact
connecting square, with the actual restricted overlap map.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction SingularMayerVietoris SpecializationModel

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

/-- Every map in this square is an induced map or connecting map of
the actual source and target open covers. -/
theorem productCollapse_connecting_naturality (a : ℝ) (ha1 : a < 1) (n : ℕ)
    (x : SingularHomology BaseCover.PhaseBase (n + 1)) :
    singularHomologyMap (SpecializationCover.overlapMap C ε hε a) n
        (connectingHomomorphism (BaseCover.phaseOuterRegion a) BaseCover.phaseInnerRegion
          (BaseCover.phaseOuterRegion_isOpen a) BaseCover.phaseInnerRegion_isOpen
          (BaseCover.phaseOuterRegion_union_phaseInnerRegion a ha1) n x) =
      connectingHomomorphism (outerRegion C ε hε a) (innerRegion C ε hε)
        (outerRegion_isOpen C ε hε hε1 hC hR a)
        (innerRegion_isOpen C ε hε hε1 hC hR)
        (outerRegion_union_innerRegion C ε hε a ha1) n
        (singularHomologyMap (productCollapse C ε hε) (n + 1) x) :=
  connectingHomomorphism_naturality_apply (productCollapse C ε hε)
    (BaseCover.phaseOuterRegion a) BaseCover.phaseInnerRegion
    (outerRegion C ε hε a) (innerRegion C ε hε)
    (SpecializationCover.productCollapse_mapsTo_outer C ε hε a)
    (SpecializationCover.productCollapse_mapsTo_inner C ε hε)
    (BaseCover.phaseOuterRegion_isOpen a) BaseCover.phaseInnerRegion_isOpen
    (BaseCover.phaseOuterRegion_union_phaseInnerRegion a ha1)
    (outerRegion_isOpen C ε hε hε1 hC hR a)
    (innerRegion_isOpen C ε hε hε1 hC hR)
    (outerRegion_union_innerRegion C ε hε a ha1) n x

end Wikipedia.HopfProblem.CuspCentralHomology
