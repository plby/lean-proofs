import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspGeometry
import Wikipedia.HopfProblem.CuspPuncturedManifold
import Wikipedia.HopfProblem.HolomorphicDifferentialFormsFlat

/-!
# Native global forms on the actual logarithmic cusp cover

The map used here is the original toric exponential, followed by the
actual cusp quotient and the actual inclusion into the glued threefold.
Its pullback is Mathlib's derivative pullback of a genuine holomorphic
alternating tangent-covector section. The logarithmic cover keeps its
original open-subset atlas.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp

open ToricCharts CuspUniformization CuspGeometry
open Wikipedia.HopfProblem.HolomorphicDifferentialForms

local notation "E₃" => CoordinateSpace 3
local notation "I₃" => modelWithCornersSelf ℂ E₃
local notation "EL" => ℂ × ComplexPlane₂
local notation "IL" => modelWithCornersSelf ℂ EL

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace

local instance globalManifold : IsManifold IL ω Threefold.Space := Threefold.space_isManifold

local instance nativeManifold : IsManifold I₃ ω CuspGeometry.LocalSpace :=
  CuspGeometry.native_isManifold

/-- The original logarithmic cusp cover, at the actually chosen filling radius. -/
abbrev LogDomain := LogCover CuspGeometry.data.radius

/-- The literal toric quotient map, with codomain named as the actual full cusp piece. -/
def localLogMap (x : LogDomain) : CuspGeometry.LocalSpace :=
  totalCuspCover CuspGeometry.data.correction CuspGeometry.data.radius x

/-- Holomorphicity is in the original native quotient atlas. -/
theorem localLogMap_holomorphic : ContMDiff IL I₃ ω localLogMap := by
  let := CuspQuotient.chartedSpace data.correction data.radius data.radius_pos
    data.radius_lt_one data.holomorphic data.smallDrift
  have hq : ContMDiff I₃ I₃ ω
      (fun x : ToricSpace.Tube (CuspQuotient.disc data.radius) =>
        (CuspQuotient.quotientMap data.correction data.radius x : CuspGeometry.LocalSpace)) :=
    CuspQuotient.quotientMap_holomorphic data.correction data.radius data.radius_pos
      data.radius_lt_one data.holomorphic data.smallDrift
  exact hq.comp (totalExponentialLift_holomorphic data.radius)

/-- The actual map of the logarithmic cover into the full glued threefold. -/
def globalLogMap (x : LogDomain) : Threefold.Space := CuspGeometry.inclusion (localLogMap x)

/-- Holomorphicity uses the original toric map, quotient atlas, and global patch inclusion. -/
theorem globalLogMap_holomorphic : ContMDiff IL IL ω globalLogMap :=
  CuspGeometry.inclusion_holomorphic.comp localLogMap_holomorphic

/-- The full global cusp coordinate of this map is the original exponential parameter. -/
@[simp] theorem cuspCoordinate_globalLogMap (x : LogDomain) :
    CuspGeometry.cuspCoordinate (globalLogMap x) = exponential x.val.1 := by
  exact (CuspGeometry.cuspCoordinate_inclusion (localLogMap x)).trans
    (projection_totalCuspCover data.correction data.radius x)

/-- The pulled-back form is an actual holomorphic section of the native tangent-covector bundle. -/
def logPullback {p : ℕ} (θ : Form EL Threefold.Space p) : Form EL LogDomain p :=
  pullback globalLogMap globalLogMap_holomorphic θ

theorem logPullback_apply {p : ℕ} (θ : Form EL Threefold.Space p)
    (x : LogDomain) (v : Fin p → EL) :
    logPullback θ x v =
      θ (globalLogMap x) (fun j => mfderiv IL IL globalLogMap x (v j)) := rfl

/-- The native logarithmic covector is the coefficient in the unchanged fixed chart. -/
def logCoefficients {p : ℕ} (θ : Form EL Threefold.Space p) (x : LogDomain) :
    EL [⋀^Fin p]→L[ℂ] ℂ :=
  nativeCoefficients EL LogDomain (logPullback θ) x

@[simp] theorem logCoefficients_apply {p : ℕ} (θ : Form EL Threefold.Space p)
    (x : LogDomain) (v : Fin p → EL) :
    logCoefficients θ x v = logPullback θ x v :=
  nativeCoefficients_apply EL LogDomain (logPullback θ) x v

/-- Native coefficient covectors vary holomorphically on the full logarithmic cover. -/
theorem logCoefficients_holomorphic {p : ℕ} (θ : Form EL Threefold.Space p) :
    ContMDiff IL (modelWithCornersSelf ℂ (EL [⋀^Fin p]→L[ℂ] ℂ)) ω (logCoefficients θ) :=
  nativeCoefficients_holomorphic_of_constant_charts EL LogDomain
    (fun _ _ => rfl) (logPullback θ)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp
