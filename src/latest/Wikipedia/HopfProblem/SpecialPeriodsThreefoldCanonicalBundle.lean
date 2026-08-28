import Wikipedia.HopfProblem.SpecialPeriodsThreefoldConnected
import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalLocalFrames

/-!
# The native canonical bundle of the actual compact threefold

This is the inverse-Jacobian bundle of the actual glued tangent atlas.
Its fibre at every point is identified with the full space of continuous
alternating three-covectors on that point's actual tangent space.  Its
local frames and their transition factors are derived from the actual
chart derivatives; no canonical divisor formula or global triviality is
an input or a conclusion of this construction.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical

open TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] Threefold.chartedSpace

local instance canonicalManifold : IsManifold IF ω Threefold.Space := Threefold.space_isManifold

/-- The genuine canonical line bundle of the actual glued threefold. -/
abbrev bundle := Atlas.core Threefold.Space

theorem bundle_holomorphic : ContMDiffVectorBundle ω ℂ bundle.Fiber IF :=
  Atlas.holomorphicVectorBundle Threefold.Space

theorem fibre_rank_one (x : Threefold.Space) : Module.finrank ℂ (bundle.Fiber x) = 1 :=
  Atlas.fibre_rank_one Threefold.Space x

/-- Full intrinsic alternating three-covectors on the native tangent space. -/
abbrev IntrinsicTopCovector (x : Threefold.Space) :=
  (TangentSpace IF x) [⋀^(Fin 3)]→L[ℂ] ℂ

def intrinsicEquiv (x : Threefold.Space) : bundle.Fiber x ≃L[ℂ] IntrinsicTopCovector x :=
  Atlas.intrinsicEquiv Threefold.Space x

/-- Representation of a global canonical vector in a selected actual chart. -/
def inCoordinates (i : atlas Model Threefold.Space) (x : Threefold.Space)
    (v : bundle.Fiber x) : TopCovector := Atlas.inCoordinates Threefold.Space i x v

theorem inCoordinates_eq_intrinsic_pullback (i : atlas Model Threefold.Space)
    (x : Threefold.Space) (v : bundle.Fiber x) :
    inCoordinates i x v = (intrinsicEquiv x v).compContinuousLinearMap
      ((tangentBundleCore IF Threefold.Space).coordChange i (achart Model x) x) :=
  Atlas.inCoordinates_eq_intrinsic_pullback Threefold.Space i x v

/-- A chart supplies the full scalar-to-top-covector identification. -/
def coordinateEquiv (i : atlas Model Threefold.Space) {x : Threefold.Space}
    (hx : x ∈ i.val.source) : bundle.Fiber x ≃L[ℂ] TopCovector :=
  Atlas.coordinateEquiv Threefold.Space i hx

theorem inCoordinates_change (i j : atlas Model Threefold.Space) {x : Threefold.Space}
    (hi : x ∈ i.val.source) (hj : x ∈ j.val.source) (v : bundle.Fiber x) :
    inCoordinates j x v = (inCoordinates i x v).compContinuousLinearMap
      (fderiv ℂ (i.val ∘ j.val.symm) (j.val x)) :=
  Atlas.inCoordinates_change Threefold.Space i j hi hj v

/-- The global bundle's transition function is precisely the inverse
determinant of the actual forward tangent-coordinate change. -/
theorem transition_eq_inverse_jacobian (i j : atlas Model Threefold.Space)
    {x : Threefold.Space} (hi : x ∈ i.val.source) (hj : x ∈ j.val.source) :
    bundle.coordChange i j x =
      (LinearMap.det (fderiv ℂ (j.val ∘ i.val.symm) (i.val x)).toLinearMap)⁻¹ •
        ContinuousLinearMap.id ℂ ℂ :=
  Atlas.coordChange_eq_inverse_jacobian Threefold.Space i j hi hj

/-- The source of a preferred chart, with its natural open-submanifold atlas. -/
abbrev chartSource (i : Threefold.Space) : TopologicalSpace.Opens Threefold.Space :=
  Atlas.chartSource Threefold.Space (achart Model i)

def localFrame (i : Threefold.Space) (x : chartSource i) : bundle.Fiber x.val :=
  Atlas.localFrame Threefold.Space (achart Model i) x

theorem localFrame_ne_zero (i : Threefold.Space) (x : chartSource i) : localFrame i x ≠ 0 :=
  Atlas.localFrame_ne_zero Threefold.Space (achart Model i) x

def localFrameSection (i : Threefold.Space) (x : chartSource i) : bundle.TotalSpace :=
  ⟨x.val, localFrame i x⟩

theorem localFrameSection_holomorphic (i : Threefold.Space) :
    ContMDiff IF ((IF).prod I₁) ω (localFrameSection i) :=
  Atlas.localFrameSection_holomorphic Threefold.Space (achart Model i)

@[simp] theorem localFrame_inCoordinates (i : Threefold.Space) (x : chartSource i) :
    inCoordinates (achart Model i) x.val (localFrame i x) = volume :=
  Atlas.localFrame_inCoordinates Threefold.Space (achart Model i) x

theorem localFrame_change (i j : Threefold.Space) (x : chartSource i)
    (hj : x.val ∈ chartSource j) :
    localFrame i x =
      (LinearMap.det (fderiv ℂ (chartAt Model j ∘ (chartAt Model i).symm)
        (chartAt Model i x)).toLinearMap)⁻¹ • localFrame j ⟨x.val, hj⟩ := by
  rw [localFrame, Atlas.localFrame_change Threefold.Space (achart Model i) (achart Model j)
    x hj, Atlas.jacobian_reverse Threefold.Space (achart Model i) (achart Model j)
    x.property hj, Atlas.jacobian_eq_fderiv]
  rfl

theorem localFrames_cover (x : Threefold.Space) : ∃ i, x ∈ chartSource i :=
  ⟨x, mem_chart_source Model x⟩

theorem totalSpace_isManifold : IsManifold ((IF).prod I₁) ω bundle.TotalSpace :=
  Atlas.totalSpace_isManifold Threefold.Space

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical
