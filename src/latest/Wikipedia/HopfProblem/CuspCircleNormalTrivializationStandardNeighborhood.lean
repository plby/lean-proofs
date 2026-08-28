import Wikipedia.HopfProblem.CuspCircleNormalTrivialization
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationStandardOpenProduct
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationStandardClosedDisk

/-!
# The actual fixed-curve neighborhood in standard sphere-and-disk coordinates

The open neighborhood is real-analytically diffeomorphic to the literal
standard `S² × B⁴`, with both native atlases unchanged. The compact
standard `S² × D⁴` embedding lies inside this same analytic chart: its
normal coordinate is precisely half the open unit-ball coordinate.
-/

noncomputable section

open Set Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open SpecialPeriods SpecialPeriods.Threefold

local notation "IS" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, RealFour.Space)
local notation "IX" => 𝓘(ℝ, ℂ × ComplexPlane₂)

attribute [local instance] Threefold.chartedSpace

/-- A genuine native real-analytic standard-product diffeomorphism onto the actual open subset. -/
def standardNeighborhoodDiffeomorph :
    Diffeomorph IS IX StandardOpenNormalProduct fixedCurveNeighborhood ω :=
  standardUnitToNormalDiffeomorph.trans normalNeighborhoodDiffeomorph

@[simp] theorem standardNeighborhoodDiffeomorph_coe (p : StandardOpenNormalProduct) :
    (standardNeighborhoodDiffeomorph p : Threefold.Space) =
      roundProductMap (standardUnitToNormalDiffeomorph p) := rfl

theorem standardNeighborhoodDiffeomorph_zeroSection (p : RealSphere.UnitTwoSphere) :
    (standardNeighborhoodDiffeomorph (p, standardOpenZero) : Threefold.Space) =
      CuspGeometry.doubleCurveParametrization 1 (RealSphere.sphereDiffeomorph.symm p) := by
  rw [standardNeighborhoodDiffeomorph_coe, standardUnitToNormalDiffeomorph_zeroSection,
    roundProductMap_zeroSection]

theorem standardUnitToNormal_fibre_zero_iff (p : StandardOpenNormalProduct) :
    (standardUnitToNormalDiffeomorph p).val.2 = 0 ↔ (p.2 : RealFour.Space) = 0 := by
  rw [standardUnitToNormalDiffeomorph_coe]
  constructor
  · intro h
    have hc := congrArg RealFour.coordinateEquiv h
    rw [RealFour.coordinateEquiv.apply_symm_apply, map_zero] at hc
    exact (smul_eq_zero.mp hc).resolve_left injectiveRadius_pos.ne'
  · intro h
    rw [h, smul_zero, map_zero]

theorem standardNeighborhoodDiffeomorph_mem_doubleCurve_iff (p : StandardOpenNormalProduct) :
    (standardNeighborhoodDiffeomorph p : Threefold.Space) ∈ CuspGeometry.doubleCurve 1 ↔
      (p.2 : RealFour.Space) = 0 := by
  rw [standardNeighborhoodDiffeomorph_coe, roundProductMap_mem_doubleCurve_iff,
    standardUnitToNormal_fibre_zero_iff]

theorem standardNeighborhoodDiffeomorph_inverse_normal_zero_iff (x : fixedCurveNeighborhood) :
    ((standardNeighborhoodDiffeomorph.symm x).2 : RealFour.Space) = 0 ↔
      (x : Threefold.Space) ∈ CuspGeometry.doubleCurve 1 := by
  rw [← standardNeighborhoodDiffeomorph_mem_doubleCurve_iff,
    standardNeighborhoodDiffeomorph.apply_symm_apply]

/-- The standard closed disk lies in the open chart by literal half-scaling of its normal vector. -/
def standardClosedIntoOpen (p : StandardClosedNormalProduct) : StandardOpenNormalProduct :=
  (p.1, ⟨(1 / 2 : ℝ) • (p.2 : RealFour.Space), by
    change (1 / 2 : ℝ) • (p.2 : RealFour.Space) ∈ ball (0 : RealFour.Space) 1
    rw [mem_ball, dist_zero_right, norm_smul]
    have hp : ‖(p.2 : RealFour.Space)‖ ≤ 1 := mem_closedBall_zero_iff.mp p.2.property
    norm_num
    linarith⟩)

@[simp] theorem standardClosedIntoOpen_coe (p : StandardClosedNormalProduct) :
    ((standardClosedIntoOpen p).1, ((standardClosedIntoOpen p).2 : RealFour.Space)) =
      (p.1, (1 / 2 : ℝ) • (p.2 : RealFour.Space)) := rfl

/-- The compact standard disk embedding is a literal restriction of the actual analytic chart. -/
theorem standardClosedDiskMap_eq_open_chart (p : StandardClosedNormalProduct) :
    standardClosedDiskMap p =
      (standardNeighborhoodDiffeomorph (standardClosedIntoOpen p) : Threefold.Space) := by
  change roundProductMap (closedProductIntoRound (standardClosedProductHomeomorph p)) =
    roundProductMap (standardUnitToNormalDiffeomorph (standardClosedIntoOpen p))
  apply congrArg roundProductMap
  apply Subtype.ext
  rw [closedProductIntoRound_coe, standardClosedProductHomeomorph_fst,
    standardClosedProductHomeomorph_snd_coe, standardUnitToNormalDiffeomorph_coe]
  change (RealSphere.sphereDiffeomorph.symm p.1,
    RealFour.coordinateEquiv.symm (closedRadius • (p.2 : RealFour.Space))) =
      (RealSphere.sphereDiffeomorph.symm p.1,
        RealFour.coordinateEquiv.symm
          (injectiveRadius • ((1 / 2 : ℝ) • (p.2 : RealFour.Space))))
  rw [smul_smul]
  congr 3
  simp only [closedRadius, div_eq_mul_inv, one_mul]

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
