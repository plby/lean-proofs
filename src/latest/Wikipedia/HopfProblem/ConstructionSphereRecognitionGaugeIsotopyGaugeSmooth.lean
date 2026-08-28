import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticGaugeLinearizationReal
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticGaugeLinearizationHomotopyCore
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologySmoothCoordinates
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRealMaps

/-!
# Real smoothness of the original logarithmic gauge

The real lift uses the actual inverse varying-period map and the original
holomorphic period vector. Its boundary parameter and root are the unchanged
native logarithm and exponential curves. All manifold statements use the
inherited open-disc charts and ordinary product charts.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy

open Elliptic Elliptic.LogGauge SpecialPeriods SpecialPeriods.EllipticFilling
open SpecialPeriods.Threefold.EllipticGeometry
open TrianglePeriodFamily.Boundary TrianglePeriodFamily.Boundary.EllipticGaugeLinearization

local notation "I₁" => modelWithCornersSelf ℝ ℂ
local notation "I₂" => modelWithCornersSelf ℝ ComplexPlane₂
local notation "IV" => modelWithCornersSelf ℝ RealCoordinates
local notation "IP" => modelWithCornersSelf ℝ (ℂ × ℂ)
local notation "IC" => modelWithCornersSelf ℝ (ℂ × ComplexPlane₂)

local instance logarithmProductChartedSpace : ChartedSpace (ℂ × ℂ) (Disc × ℂ) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ℂ) (Disc × ℂ))

local instance periodProductChartedSpace :
    ChartedSpace (ℂ × ComplexPlane₂) (Disc × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (Disc × ComplexPlane₂))

/-- Restricting the scalar field preserves the original period-vector charts. -/
theorem periodVector_contMDiff {j : Kind} (D : Equivariant.Data j) (v : Lattice) :
    ContMDiff I₁ I₂ ∞ (periodVector D.periods v) :=
  (CuspCircleNormalTrivialization.contMDiff_real_of_complex
    (periodVector_holomorphic D.periods v)).of_le le_top

private theorem logarithm_fst_contMDiff :
    ContMDiff IP I₁ ∞ (Prod.fst : Disc × ℂ → Disc) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_fst

private theorem logarithm_snd_contMDiff :
    ContMDiff IP I₁ ∞ (Prod.snd : Disc × ℂ → ℂ) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_snd

private theorem complexSmul_contDiff :
    ContDiff ℝ ∞ (fun p : ℂ × ComplexPlane₂ => p.1 • p.2) :=
  contDiff_fst.smul contDiff_snd

private theorem scaledPeriodVector_contMDiff {j : Kind} (D : Equivariant.Data j)
    (v : Lattice) :
    ContMDiff IP I₂ ∞ (fun p : Disc × ℂ => p.2 • periodVector D.periods v p.1) := by
  exact complexSmul_contDiff.contMDiff.comp
    (logarithm_snd_contMDiff.prodMk_space
      ((periodVector_contMDiff D v).comp logarithm_fst_contMDiff))

private theorem logarithmPeriodCoordinates_contMDiff {j : Kind} (D : Equivariant.Data j)
    (v : Lattice) :
    ContMDiff IP IC ∞
      (fun p : Disc × ℂ => (p.1, p.2 • periodVector D.periods v p.1)) := by
  rw [modelWithCornersSelf_prod]
  exact logarithm_fst_contMDiff.prodMk (scaledPeriodVector_contMDiff D v)

/-- Joint real smoothness of the literal positive logarithmic translation,
before restricting to any native boundary curve. -/
theorem positiveLogFlat_contMDiff {j : Kind} (D : Equivariant.Data j) (v : Lattice) :
    ContMDiff IP IV ∞ (fun p : Disc × ℂ => positiveLogFlat D v p.1 p.2) := by
  change ContMDiff IP IV ∞
    ((fun x : Disc × ComplexPlane₂ => (D.periods.periodEquiv x.1).symm x.2) ∘
      (fun p : Disc × ℂ => (p.1, p.2 • periodVector D.periods v p.1)))
  exact (PeriodFamilyHolomorphicCohomology.Smooth.inversePeriodCoordinates_native_contMDiff
    (U := unitDisc) D.periods).comp (logarithmPeriodCoordinates_contMDiff D v)

/-- The exact native normalized logarithm is a smooth real affine curve. -/
theorem nativeLogParameter_contDiff (j : Kind) (τ : ℝ) :
    ContDiff ℝ ∞ (nativeLogParameter j τ) := by
  change ContDiff ℝ ∞ (fun t : ℝ =>
    chosenAttachingParameter j - ((-(t + τ) : ℝ) : ℂ) / (j.order : ℂ))
  exact contDiff_const.sub
    ((Complex.ofRealCLM.contDiff.comp (contDiff_id.add contDiff_const).neg).div_const _)

/-- The original exponential root is smooth in the inherited open-disc atlas. -/
theorem nativeLogRoot_contMDiff (j : Kind) (τ : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) I₁ ∞ (nativeLogRoot j τ) := by
  apply (ContMDiff.subtypeVal_comp_iff unitDisc _).mp
  exact (((CuspUniformization.exponential_holomorphic.restrict_scalars ℝ).of_le le_top).comp
    (nativeLogParameter_contDiff j τ)).contMDiff

/-- The full original real gauge lift is smooth, with its native phase and
time convention unchanged. -/
theorem nativeGaugeRealLift_contDiff (j : Kind) (τ : ℝ) :
    ContDiff ℝ ∞ (nativeGaugeRealLift j τ) := by
  have hp : ContMDiff 𝓘(ℝ, ℝ) IP ∞
      (fun t : ℝ => (nativeLogRoot j τ t, nativeLogParameter j τ t)) := by
    rw [modelWithCornersSelf_prod]
    exact (nativeLogRoot_contMDiff j τ).prodMk (nativeLogParameter_contDiff j τ).contMDiff
  exact ((positiveLogFlat_contMDiff (specialLocalData j) j.twist).comp hp).contDiff

/-- The time-linear gauge is smooth for every original lattice vector. -/
theorem linearGauge_contDiff (j : Kind) (v : Lattice) :
    ContDiff ℝ ∞ (linearGauge j v) := by
  change ContDiff ℝ ∞ (fun t : ℝ => (t / (j.order : ℝ)) • realCast v)
  exact (contDiff_id.div_const _).smul contDiff_const

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy
