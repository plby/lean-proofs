import Wikipedia.HopfProblem.ConstructionSphereRecognitionGlobalGaugeCombined
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationStandardNeighborhood
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCollarActual

/-!
# The original fixed-curve normal neighborhood is unchanged

The entire native normal-product map factors through the original cusp
inclusion.  Consequently both the individual and simultaneous global
elliptic gauge isotopies fix it pointwise, including the literal standard
open chart, the actual closed disk neighborhood, and its original collar.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge

open Elliptic SpecialPeriods SpecialPeriods.Threefold CuspCircleNormalTrivialization

attribute [local instance] Threefold.chartedSpace

/-- The original cusp quotient point underlying the native normal-product map. -/
def normalCuspPoint (p : smallNormalProduct) : CuspGeometry.LocalSpace :=
  CuspQuotient.quotientMap CuspGeometry.data.correction CuspGeometry.data.radius (toTube p)

@[simp] theorem normalCuspPoint_inclusion (p : smallNormalProduct) :
    CuspGeometry.inclusion (normalCuspPoint p) = globalProductMap p := rfl

/-- The actual original normal-product map remains fixed, before any radius restriction. -/
theorem globalDiffeomorph_globalProductMap (j : Kind) (τ s : ℝ) (p : smallNormalProduct) :
    globalDiffeomorph j τ s (globalProductMap p) = globalProductMap p :=
  globalDiffeomorph_cusp j τ s (normalCuspPoint p)

theorem combinedDiffeomorph_globalProductMap (τ₃ τ₄ s : ℝ) (p : smallNormalProduct) :
    combinedDiffeomorph τ₃ τ₄ s (globalProductMap p) = globalProductMap p :=
  combinedDiffeomorph_cusp τ₃ τ₄ s (normalCuspPoint p)

theorem globalDiffeomorph_roundProductMap (j : Kind) (τ s : ℝ) (p : roundNormalProduct) :
    globalDiffeomorph j τ s (roundProductMap p) = roundProductMap p :=
  globalDiffeomorph_globalProductMap j τ s (roundToSmall p)

theorem combinedDiffeomorph_roundProductMap (τ₃ τ₄ s : ℝ) (p : roundNormalProduct) :
    combinedDiffeomorph τ₃ τ₄ s (roundProductMap p) = roundProductMap p :=
  combinedDiffeomorph_globalProductMap τ₃ τ₄ s (roundToSmall p)

/-- The whole actual open fixed-curve neighborhood is fixed pointwise. -/
theorem globalDiffeomorph_fixedCurveNeighborhood (j : Kind) (τ s : ℝ)
    (x : fixedCurveNeighborhood) : globalDiffeomorph j τ s x.val = x.val := by
  obtain ⟨p, hp⟩ := x.property
  rw [← hp]
  exact globalDiffeomorph_roundProductMap j τ s p

theorem combinedDiffeomorph_fixedCurveNeighborhood (τ₃ τ₄ s : ℝ)
    (x : fixedCurveNeighborhood) : combinedDiffeomorph τ₃ τ₄ s x.val = x.val := by
  obtain ⟨p, hp⟩ := x.property
  rw [← hp]
  exact combinedDiffeomorph_roundProductMap τ₃ τ₄ s p

/-- In particular the previously constructed literal standard open normal chart is unchanged. -/
theorem globalDiffeomorph_standardNeighborhood (j : Kind) (τ s : ℝ)
    (p : StandardOpenNormalProduct) :
    globalDiffeomorph j τ s (standardNeighborhoodDiffeomorph p : Threefold.Space) =
      (standardNeighborhoodDiffeomorph p : Threefold.Space) :=
  globalDiffeomorph_fixedCurveNeighborhood j τ s (standardNeighborhoodDiffeomorph p)

theorem combinedDiffeomorph_standardNeighborhood (τ₃ τ₄ s : ℝ)
    (p : StandardOpenNormalProduct) :
    combinedDiffeomorph τ₃ τ₄ s (standardNeighborhoodDiffeomorph p : Threefold.Space) =
      (standardNeighborhoodDiffeomorph p : Threefold.Space) :=
  combinedDiffeomorph_fixedCurveNeighborhood τ₃ τ₄ s (standardNeighborhoodDiffeomorph p)

/-- The original standard closed normal disk is retained point for point. -/
theorem globalDiffeomorph_standardClosedDisk (j : Kind) (τ s : ℝ)
    (p : StandardClosedNormalProduct) :
    globalDiffeomorph j τ s (standardClosedDiskMap p) = standardClosedDiskMap p := by
  rw [standardClosedDiskMap_eq_open_chart]
  exact globalDiffeomorph_standardNeighborhood j τ s (standardClosedIntoOpen p)

theorem combinedDiffeomorph_standardClosedDisk (τ₃ τ₄ s : ℝ)
    (p : StandardClosedNormalProduct) :
    combinedDiffeomorph τ₃ τ₄ s (standardClosedDiskMap p) = standardClosedDiskMap p := by
  rw [standardClosedDiskMap_eq_open_chart]
  exact combinedDiffeomorph_standardNeighborhood τ₃ τ₄ s (standardClosedIntoOpen p)

/-- Every point of the literal closed neighborhood is fixed, independently of parametrization. -/
theorem combinedDiffeomorph_closedDiskNeighborhood (τ₃ τ₄ s : ℝ) {x : Threefold.Space}
    (hx : x ∈ closedDiskNeighborhood) : combinedDiffeomorph τ₃ τ₄ s x = x := by
  rw [← standardClosedDiskMap_range] at hx
  obtain ⟨p, rfl⟩ := hx
  exact combinedDiffeomorph_standardClosedDisk τ₃ τ₄ s p

/-- The original native radial collar, including its boundary slice, is also unchanged. -/
theorem globalDiffeomorph_normalCollar (j : Kind) (τ s : ℝ) (p : Collar.Domain) :
    globalDiffeomorph j τ s (Collar.actualMap p) = Collar.actualMap p :=
  globalDiffeomorph_standardNeighborhood j τ s (Collar.standardProductMap p)

theorem combinedDiffeomorph_normalCollar (τ₃ τ₄ s : ℝ) (p : Collar.Domain) :
    combinedDiffeomorph τ₃ τ₄ s (Collar.actualMap p) = Collar.actualMap p :=
  combinedDiffeomorph_standardNeighborhood τ₃ τ₄ s (Collar.standardProductMap p)

theorem combinedIsotopy_fixedCurveNeighborhood (τ₃ τ₄ : ℝ) (s : unitInterval)
    (x : fixedCurveNeighborhood) : combinedIsotopy τ₃ τ₄ (s, x.val) = x.val :=
  combinedDiffeomorph_fixedCurveNeighborhood τ₃ τ₄ s x

theorem combinedIsotopy_standardClosedDisk (τ₃ τ₄ : ℝ) (s : unitInterval)
    (p : StandardClosedNormalProduct) :
    combinedIsotopy τ₃ τ₄ (s, standardClosedDiskMap p) = standardClosedDiskMap p :=
  combinedDiffeomorph_standardClosedDisk τ₃ τ₄ s p

theorem combinedIsotopy_normalCollar (τ₃ τ₄ : ℝ) (s : unitInterval) (p : Collar.Domain) :
    combinedIsotopy τ₃ τ₄ (s, Collar.actualMap p) = Collar.actualMap p :=
  combinedDiffeomorph_normalCollar τ₃ τ₄ s p

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge
