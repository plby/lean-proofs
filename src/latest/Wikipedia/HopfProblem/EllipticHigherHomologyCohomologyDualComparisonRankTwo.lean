import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyDualComparisonCore
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyDualAlgebra
import Wikipedia.HopfProblem.EllipticHigherHomologyDeckCoinvariants

/-!
# Actual period-cover dual cokernels in degrees one through three

The input maps are the actual maps induced by the finite period cover
on the actual deck coinvariants.  Their proved triangular formulas,
not additional hypotheses, determine the exact image and cokernel of
their actual integer duals.  The off-diagonal coefficient is retained
as the actual covering-map coordinate in the residue formula.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris CohomologyDualComparison CohomologyDualAlgebra

/-- The actual off-diagonal entry in degree 1, with its chosen homology markings. -/
def periodCoverDeckDualH1Shear (j : Kind) (p : FixedPeriod j) : ℤ :=
  periodCoverCoinvariantH1Map j p ![0, 1] 0

/-- The transposed formula for the dual of the actual degree-1 covering map. -/
theorem periodCoverDeckDual_h1_coordinates (j : Kind) (p : FixedPeriod j)
    (φ : Module.Dual ℤ
      (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 1)) :
    intDualCoordinatesOfEquiv (periodDeckCoinvariantsH1Equiv j p)
        ((periodCoverFromDeckCoinvariants j p 1).dualMap φ) =
      ![intDualCoordinatesOfEquiv (surfaceH1Equiv j p) φ 0,
        periodCoverDeckDualH1Shear j p * intDualCoordinatesOfEquiv (surfaceH1Equiv j p) φ 0 +
          (j.order : ℤ) * intDualCoordinatesOfEquiv (surfaceH1Equiv j p) φ 1] := by
  change intDualCoordinates 2
    ((periodDeckCoinvariantsH1Equiv j p).symm.dualMap
      ((periodCoverFromDeckCoinvariants j p 1).dualMap φ)) = _
  rw [dual_coordinates_commute (periodCoverFromDeckCoinvariants j p 1)
    (periodDeckCoinvariantsH1Equiv j p) (surfaceH1Equiv j p)
    (periodCoverCoinvariantH1Map j p) (fun _ => rfl)]
  rw [dual_coordinates_of_formula (periodCoverCoinvariantH1Map j p)
    (periodCoverDeckDualH1Shear j p) (j.order) (periodCoverCoinvariantH1Map_apply j p)]
  rfl

/-- The actual degree-1 dual cokernel, not a substitute coordinate quotient. -/
def periodCoverDeckDualH1CokernelEquivZMod (j : Kind) (p : FixedPeriod j) :
    (Module.Dual ℤ (PeriodDeckCoinvariants j p 1) ⧸
      LinearMap.range (periodCoverFromDeckCoinvariants j p 1).dualMap) ≃ₗ[ℤ]
        ZMod (j.order) :=
  (dualCokernelEquivOfCoordinates (periodCoverFromDeckCoinvariants j p 1)
    (periodDeckCoinvariantsH1Equiv j p) (surfaceH1Equiv j p) (periodCoverCoinvariantH1Map j p)
    (fun _ => rfl)).trans
      (dualCokernelEquivZModOfFormula (periodCoverCoinvariantH1Map j p)
        (periodCoverDeckDualH1Shear j p) (j.order) (periodCoverCoinvariantH1Map_apply j p))

@[simp] theorem periodCoverDeckDualH1CokernelEquivZMod_apply_mk (j : Kind) (p : FixedPeriod j)
    (φ : Module.Dual ℤ (PeriodDeckCoinvariants j p 1)) :
    periodCoverDeckDualH1CokernelEquivZMod j p (Submodule.Quotient.mk φ) =
      ((intDualCoordinatesOfEquiv (periodDeckCoinvariantsH1Equiv j p) φ 1 -
        periodCoverDeckDualH1Shear j p *
          intDualCoordinatesOfEquiv (periodDeckCoinvariantsH1Equiv j p) φ 0 : ℤ) :
          ZMod (j.order)) := by
  rfl

/-- Exact membership in the actual dual image, in the actual deck-coinvariant markings. -/
theorem periodCoverDeckDual_h1_mem_range (j : Kind) (p : FixedPeriod j)
    (φ : Module.Dual ℤ (PeriodDeckCoinvariants j p 1)) :
    φ ∈ LinearMap.range (periodCoverFromDeckCoinvariants j p 1).dualMap ↔
      (j.order : ℤ) ∣ intDualCoordinatesOfEquiv (periodDeckCoinvariantsH1Equiv j p) φ 1 -
        periodCoverDeckDualH1Shear j p *
          intDualCoordinatesOfEquiv (periodDeckCoinvariantsH1Equiv j p) φ 0 := by
  rw [← Submodule.Quotient.mk_eq_zero,
    ← (periodCoverDeckDualH1CokernelEquivZMod j p).map_eq_zero_iff,
    periodCoverDeckDualH1CokernelEquivZMod_apply_mk, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem periodCoverDeckDual_h1_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (periodCoverFromDeckCoinvariants j p 1).dualMap).toAddSubgroup.index =
      j.order := by
  change Nat.card (Module.Dual ℤ (PeriodDeckCoinvariants j p 1) ⧸
    LinearMap.range (periodCoverFromDeckCoinvariants j p 1).dualMap) = _
  exact (Nat.card_congr (periodCoverDeckDualH1CokernelEquivZMod j p).toEquiv).trans
    (Nat.card_zmod _)

theorem periodCoverDeckDual_h1_range_finiteIndex (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range
      (periodCoverFromDeckCoinvariants j p 1).dualMap).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [periodCoverDeckDual_h1_range_index]
  exact (j.order_pos).ne'

/-- The actual off-diagonal entry in degree 2, with its chosen homology markings. -/
def periodCoverDeckDualH2Shear (j : Kind) (p : FixedPeriod j) : ℤ :=
  periodCoverCoinvariantH2Map j p ![0, 1] 0

/-- The transposed formula for the dual of the actual degree-2 covering map. -/
theorem periodCoverDeckDual_h2_coordinates (j : Kind) (p : FixedPeriod j)
    (φ : Module.Dual ℤ
      (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 2)) :
    intDualCoordinatesOfEquiv (periodDeckCoinvariantsH2Equiv j p)
        ((periodCoverFromDeckCoinvariants j p 2).dualMap φ) =
      ![intDualCoordinatesOfEquiv (surfaceH2Equiv j p) φ 0,
        periodCoverDeckDualH2Shear j p * intDualCoordinatesOfEquiv (surfaceH2Equiv j p) φ 0 +
          (fibreNormIndex j : ℤ) * intDualCoordinatesOfEquiv (surfaceH2Equiv j p) φ 1] := by
  change intDualCoordinates 2
    ((periodDeckCoinvariantsH2Equiv j p).symm.dualMap
      ((periodCoverFromDeckCoinvariants j p 2).dualMap φ)) = _
  rw [dual_coordinates_commute (periodCoverFromDeckCoinvariants j p 2)
    (periodDeckCoinvariantsH2Equiv j p) (surfaceH2Equiv j p)
    (periodCoverCoinvariantH2Map j p) (fun _ => rfl)]
  rw [dual_coordinates_of_formula (periodCoverCoinvariantH2Map j p)
    (periodCoverDeckDualH2Shear j p) (fibreNormIndex j) (periodCoverCoinvariantH2Map_apply j p)]
  rfl

/-- The actual degree-2 dual cokernel, not a substitute coordinate quotient. -/
def periodCoverDeckDualH2CokernelEquivZMod (j : Kind) (p : FixedPeriod j) :
    (Module.Dual ℤ (PeriodDeckCoinvariants j p 2) ⧸
      LinearMap.range (periodCoverFromDeckCoinvariants j p 2).dualMap) ≃ₗ[ℤ]
        ZMod (fibreNormIndex j) :=
  (dualCokernelEquivOfCoordinates (periodCoverFromDeckCoinvariants j p 2)
    (periodDeckCoinvariantsH2Equiv j p) (surfaceH2Equiv j p) (periodCoverCoinvariantH2Map j p)
    (fun _ => rfl)).trans
      (dualCokernelEquivZModOfFormula (periodCoverCoinvariantH2Map j p)
        (periodCoverDeckDualH2Shear j p) (fibreNormIndex j) (periodCoverCoinvariantH2Map_apply j p))

@[simp] theorem periodCoverDeckDualH2CokernelEquivZMod_apply_mk (j : Kind) (p : FixedPeriod j)
    (φ : Module.Dual ℤ (PeriodDeckCoinvariants j p 2)) :
    periodCoverDeckDualH2CokernelEquivZMod j p (Submodule.Quotient.mk φ) =
      ((intDualCoordinatesOfEquiv (periodDeckCoinvariantsH2Equiv j p) φ 1 -
        periodCoverDeckDualH2Shear j p *
          intDualCoordinatesOfEquiv (periodDeckCoinvariantsH2Equiv j p) φ 0 : ℤ) :
          ZMod (fibreNormIndex j)) := by
  rfl

/-- Exact membership in the actual dual image, in the actual deck-coinvariant markings. -/
theorem periodCoverDeckDual_h2_mem_range (j : Kind) (p : FixedPeriod j)
    (φ : Module.Dual ℤ (PeriodDeckCoinvariants j p 2)) :
    φ ∈ LinearMap.range (periodCoverFromDeckCoinvariants j p 2).dualMap ↔
      (fibreNormIndex j : ℤ) ∣ intDualCoordinatesOfEquiv (periodDeckCoinvariantsH2Equiv j p) φ 1 -
        periodCoverDeckDualH2Shear j p *
          intDualCoordinatesOfEquiv (periodDeckCoinvariantsH2Equiv j p) φ 0 := by
  rw [← Submodule.Quotient.mk_eq_zero,
    ← (periodCoverDeckDualH2CokernelEquivZMod j p).map_eq_zero_iff,
    periodCoverDeckDualH2CokernelEquivZMod_apply_mk, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem periodCoverDeckDual_h2_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (periodCoverFromDeckCoinvariants j p 2).dualMap).toAddSubgroup.index =
      fibreNormIndex j := by
  change Nat.card (Module.Dual ℤ (PeriodDeckCoinvariants j p 2) ⧸
    LinearMap.range (periodCoverFromDeckCoinvariants j p 2).dualMap) = _
  exact (Nat.card_congr (periodCoverDeckDualH2CokernelEquivZMod j p).toEquiv).trans
    (Nat.card_zmod _)

theorem periodCoverDeckDual_h2_range_finiteIndex (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range
      (periodCoverFromDeckCoinvariants j p 2).dualMap).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [periodCoverDeckDual_h2_range_index]
  exact (fibreNormIndex_pos j).ne'

/-- The actual off-diagonal entry in degree 3, with its chosen homology markings. -/
def periodCoverDeckDualH3Shear (j : Kind) (p : FixedPeriod j) : ℤ :=
  periodCoverCoinvariantH3Map j p ![0, 1] 0

/-- The transposed formula for the dual of the actual degree-3 covering map. -/
theorem periodCoverDeckDual_h3_coordinates (j : Kind) (p : FixedPeriod j)
    (φ : Module.Dual ℤ
      (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 3)) :
    intDualCoordinatesOfEquiv (periodDeckCoinvariantsH3Equiv j p)
        ((periodCoverFromDeckCoinvariants j p 3).dualMap φ) =
      ![intDualCoordinatesOfEquiv (surfaceH3Equiv j p) φ 0,
        periodCoverDeckDualH3Shear j p * intDualCoordinatesOfEquiv (surfaceH3Equiv j p) φ 0 +
          (fibreNormIndex j : ℤ) * intDualCoordinatesOfEquiv (surfaceH3Equiv j p) φ 1] := by
  change intDualCoordinates 2
    ((periodDeckCoinvariantsH3Equiv j p).symm.dualMap
      ((periodCoverFromDeckCoinvariants j p 3).dualMap φ)) = _
  rw [dual_coordinates_commute (periodCoverFromDeckCoinvariants j p 3)
    (periodDeckCoinvariantsH3Equiv j p) (surfaceH3Equiv j p)
    (periodCoverCoinvariantH3Map j p) (fun _ => rfl)]
  rw [dual_coordinates_of_formula (periodCoverCoinvariantH3Map j p)
    (periodCoverDeckDualH3Shear j p) (fibreNormIndex j) (periodCoverCoinvariantH3Map_apply j p)]
  rfl

/-- The actual degree-3 dual cokernel, not a substitute coordinate quotient. -/
def periodCoverDeckDualH3CokernelEquivZMod (j : Kind) (p : FixedPeriod j) :
    (Module.Dual ℤ (PeriodDeckCoinvariants j p 3) ⧸
      LinearMap.range (periodCoverFromDeckCoinvariants j p 3).dualMap) ≃ₗ[ℤ]
        ZMod (fibreNormIndex j) :=
  (dualCokernelEquivOfCoordinates (periodCoverFromDeckCoinvariants j p 3)
    (periodDeckCoinvariantsH3Equiv j p) (surfaceH3Equiv j p) (periodCoverCoinvariantH3Map j p)
    (fun _ => rfl)).trans
      (dualCokernelEquivZModOfFormula (periodCoverCoinvariantH3Map j p)
        (periodCoverDeckDualH3Shear j p) (fibreNormIndex j) (periodCoverCoinvariantH3Map_apply j p))

@[simp] theorem periodCoverDeckDualH3CokernelEquivZMod_apply_mk (j : Kind) (p : FixedPeriod j)
    (φ : Module.Dual ℤ (PeriodDeckCoinvariants j p 3)) :
    periodCoverDeckDualH3CokernelEquivZMod j p (Submodule.Quotient.mk φ) =
      ((intDualCoordinatesOfEquiv (periodDeckCoinvariantsH3Equiv j p) φ 1 -
        periodCoverDeckDualH3Shear j p *
          intDualCoordinatesOfEquiv (periodDeckCoinvariantsH3Equiv j p) φ 0 : ℤ) :
          ZMod (fibreNormIndex j)) := by
  rfl

/-- Exact membership in the actual dual image, in the actual deck-coinvariant markings. -/
theorem periodCoverDeckDual_h3_mem_range (j : Kind) (p : FixedPeriod j)
    (φ : Module.Dual ℤ (PeriodDeckCoinvariants j p 3)) :
    φ ∈ LinearMap.range (periodCoverFromDeckCoinvariants j p 3).dualMap ↔
      (fibreNormIndex j : ℤ) ∣ intDualCoordinatesOfEquiv (periodDeckCoinvariantsH3Equiv j p) φ 1 -
        periodCoverDeckDualH3Shear j p *
          intDualCoordinatesOfEquiv (periodDeckCoinvariantsH3Equiv j p) φ 0 := by
  rw [← Submodule.Quotient.mk_eq_zero,
    ← (periodCoverDeckDualH3CokernelEquivZMod j p).map_eq_zero_iff,
    periodCoverDeckDualH3CokernelEquivZMod_apply_mk, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem periodCoverDeckDual_h3_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (periodCoverFromDeckCoinvariants j p 3).dualMap).toAddSubgroup.index =
      fibreNormIndex j := by
  change Nat.card (Module.Dual ℤ (PeriodDeckCoinvariants j p 3) ⧸
    LinearMap.range (periodCoverFromDeckCoinvariants j p 3).dualMap) = _
  exact (Nat.card_congr (periodCoverDeckDualH3CokernelEquivZMod j p).toEquiv).trans
    (Nat.card_zmod _)

theorem periodCoverDeckDual_h3_range_finiteIndex (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range
      (periodCoverFromDeckCoinvariants j p 3).dualMap).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [periodCoverDeckDual_h3_range_index]
  exact (fibreNormIndex_pos j).ne'

end Wikipedia.HopfProblem.Elliptic.HigherHomology
