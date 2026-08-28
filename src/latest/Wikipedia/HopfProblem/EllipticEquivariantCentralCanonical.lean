import Wikipedia.HopfProblem.EllipticEquivariantData
import Wikipedia.HopfProblem.EllipticBundleCanonicalFixed

/-!
# The canonical bundle of an arbitrary equivariant central surface

The central period of actual equivariant period data is a fixed period.
Consequently the existing fixed-period canonical construction applies to
its original quotient surface, with its original analytic atlas.  Its
identification with the character bundle is justified by the actual chart
Jacobians and the pullback law for full alternating two-covectors.

This file exposes that construction for `D.centralPeriod`, including the
analytic, base-preserving, fibre-linear identification with the associated
orbit quotient and the exact tensor-power order.  It makes no assertion
about the normal bundle in a varying family.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data.CentralCanonical

open HolomorphicCharacterBundle CanonicalBundle

local notation "IS" => modelWithCornersSelf ℂ Model
local notation "IB" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)
local notation "IA" => modelWithCornersSelf ℂ (Model × ℂ)

variable {j : Kind} (D : Data j) (v : Lattice) (hv : AdmissibleTwist j v)

/-- The actual central surface's character cocycle, without any change of
its base type, topology, or quotient charts. -/
abbrev data := fixedData j D.centralPeriod v hv

/-- The native surface chart derivatives identify this cocycle with the
geometric canonical bundle. -/
abbrev atlas := fixedAtlas j D.centralPeriod v hv

/-- The canonical line bundle, with the native chart-pullback description
given by `coordinateEquiv` and `inCoordinates_change` below. -/
abbrev bundle := (atlas D v hv).core

theorem jacobian_eq_transition (i k x : Surface j D.centralPeriod v hv)
    (hi : x ∈ (chartAt Model i).source) (hk : x ∈ (chartAt Model k).source) :
    LinearMap.det (fderiv ℂ
      ((chartAt Model i).symm.trans (chartAt Model k)) (chartAt Model i x)).toLinearMap =
        ((data D v hv).transition k i x : ℂ) :=
  fixed_jacobian_eq_transition j D.centralPeriod v hv i k x hi hk

theorem holomorphicVectorBundle :
    ContMDiffVectorBundle ω ℂ (bundle D v hv).Fiber IS :=
  (atlas D v hv).holomorphicVectorBundle

theorem fibre_rank_one (x : Surface j D.centralPeriod v hv) :
    Module.finrank ℂ ((bundle D v hv).Fiber x) = 1 :=
  (atlas D v hv).fibre_rank_one x

theorem totalSpace_isManifold : IsManifold IB ω (bundle D v hv).TotalSpace :=
  (atlas D v hv).totalSpace_isManifold

/-- Each canonical fibre is identified with the full space of continuous
alternating two-covectors in any actual surface chart containing the point. -/
def coordinateEquiv (i : Surface j D.centralPeriod v hv)
    {x : Surface j D.centralPeriod v hv} (hx : x ∈ (chartAt Model i).source) :
    (bundle D v hv).Fiber x ≃L[ℂ] TopCovector :=
  (atlas D v hv).coordinateEquiv i hx

/-- These covectors change by pullback through the original surface chart
derivative, not through a newly selected atlas. -/
theorem inCoordinates_change (i k : Surface j D.centralPeriod v hv)
    {x : Surface j D.centralPeriod v hv}
    (hi : x ∈ (chartAt Model i).source) (hk : x ∈ (chartAt Model k).source)
    (z : (bundle D v hv).Fiber x) :
    (atlas D v hv).inCoordinates k x z =
      ((atlas D v hv).inCoordinates i x z).compContinuousLinearMap
        (fderiv ℂ ((chartAt Model k).symm.trans (chartAt Model i)) (chartAt Model k x)) :=
  (atlas D v hv).inCoordinates_change i k hi hk z

/-- Analytic identification of the geometric canonical bundle with the
actual associated orbit quotient for the canonical character. -/
def associatedIdentification :
    letI := affineAction j D.centralPeriod v hv.1
    letI := associatedChartedSpace (E := Model)
      (surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv) (canonicalCharacter j)
    Diffeomorph IB IA (bundle D v hv).TotalSpace
      (AssociatedSpace (A := D.centralPeriod.val.Torus) (canonicalCharacter j)) ω := by
  letI := affineAction j D.centralPeriod v hv.1
  let hq := surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv
  letI := associatedChartedSpace (E := Model) hq (canonicalCharacter j)
  exact AssociatedCore.identification hq (canonicalCharacter j)
    (affineAction_holomorphic j D.centralPeriod v hv.1)

@[simp] theorem associatedIdentification_preserves_base (p : (bundle D v hv).TotalSpace) :
    letI := affineAction j D.centralPeriod v hv.1
    projection (surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv)
      (canonicalCharacter j) (associatedIdentification D v hv p) = p.proj := by
  let := affineAction j D.centralPeriod v hv.1
  exact AssociatedCore.projection_toAssociated
    (surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv) (canonicalCharacter j) p

/-- In every native surface chart the analytic identification uses exactly
the original bundle's scalar coordinate, so it is complex-linear on fibres. -/
theorem associatedIdentification_localTriv (i : Surface j D.centralPeriod v hv)
    (p : (bundle D v hv).TotalSpace) (hp : p.proj ∈ (chartAt Model i).source) :
    letI := affineAction j D.centralPeriod v hv.1
    associatedIdentification D v hv p =
      associatedMap (canonicalCharacter j)
        (AssociatedCore.lift
          (surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv) i p.proj,
          ((bundle D v hv).localTriv i p).2) := by
  let := affineAction j D.centralPeriod v hv.1
  exact AssociatedCore.toAssociated_localTriv
    (surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv) (canonicalCharacter j)
    i p (fixed_chart_source_subset j D.centralPeriod v hv i hp)

/-- The tensor-power cocycle of this geometric canonical bundle. -/
abbrev powerData (n : ℕ) := fixedPowerData j D.centralPeriod v hv n

@[simp] theorem powerData_transition (n : ℕ) (i k x : Surface j D.centralPeriod v hv) :
    (powerData D v hv n).transition i k x = ((data D v hv).transition i k x) ^ n :=
  fixedPowerData_transition j D.centralPeriod v hv n i k x

@[simp] theorem powerData_one : powerData D v hv 1 = data D v hv :=
  fixedPowerData_one j D.centralPeriod v hv

/-- Genuine analytic, base-preserving, fibre-linear product triviality of
a canonical tensor power is equivalent to divisibility by the elliptic order. -/
theorem power_analyticTrivialization_iff (n : ℕ) :
    Nonempty ((powerData D v hv n).AnalyticTrivialization IS) ↔ j.order ∣ n :=
  fixedPower_analyticTrivialization_iff j D.centralPeriod v hv n

theorem order_isLeast :
    IsLeast {n : ℕ | 0 < n ∧
      Nonempty ((powerData D v hv n).AnalyticTrivialization IS)} j.order :=
  fixedPower_order_isLeast j D.centralPeriod v hv

theorem order_power_trivial :
    Nonempty ((powerData D v hv j.order).AnalyticTrivialization IS) :=
  (power_analyticTrivialization_iff D v hv j.order).mpr (dvd_refl _)

/-- In particular the canonical bundle of the actual central surface is
not analytically trivial. -/
theorem not_analytically_trivial : ¬ Nonempty ((data D v hv).AnalyticTrivialization IS) := by
  intro h
  have h1 : Nonempty ((powerData D v hv 1).AnalyticTrivialization IS) := by
    simpa only [powerData_one] using h
  have hd := (power_analyticTrivialization_iff D v hv 1).mp h1
  cases j <;> norm_num [Kind.order] at hd

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data.CentralCanonical
