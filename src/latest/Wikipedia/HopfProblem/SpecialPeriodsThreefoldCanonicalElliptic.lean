import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalBundle
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticPieces
import Wikipedia.HopfProblem.SpecialPeriodsEllipticFilling

/-!
# The ambient canonical bundles of the genuine elliptic fillings

The full elliptic fillings and their chosen small open pieces are complex
threefolds with the original quotient and open-submanifold atlases.  Their
canonical lines below are built from the inverse Jacobians of those very
atlases.  Each fibre is identified with the full space of continuous
alternating THREE-covectors on the actual ambient tangent space.

These bundles are not the canonical bundles of the central bielliptic
surfaces.  No character description, divisor formula, or global
trivialization is asserted here.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Elliptic

open Wikipedia.HopfProblem.Elliptic EllipticFilling TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace

local instance fullCanonicalManifold (j : Kind) :
    IsManifold IF ω (SpecialFullFilling j) := (specialFullFilling_construction j).2.2.1

local instance pieceCanonicalManifold (j : Kind) :
    IsManifold IF ω (SpecialEllipticPiece j) := specialEllipticPiece_isManifold j

/-- The genuine ambient canonical bundle of the full elliptic filling. -/
abbrev fullBundle (j : Kind) := Atlas.core (SpecialFullFilling j)

theorem fullBundle_holomorphic (j : Kind) :
    ContMDiffVectorBundle ω ℂ (fullBundle j).Fiber IF :=
  Atlas.holomorphicVectorBundle (SpecialFullFilling j)

theorem full_fibre_rank_one (j : Kind) (x : SpecialFullFilling j) :
    Module.finrank ℂ ((fullBundle j).Fiber x) = 1 :=
  Atlas.fibre_rank_one (SpecialFullFilling j) x

/-- Ambient top covectors on the genuine tangent space of the full filling. -/
abbrev FullIntrinsicTopCovector (j : Kind) (x : SpecialFullFilling j) :=
  (TangentSpace IF x) [⋀^(Fin 3)]→L[ℂ] ℂ

def fullIntrinsicEquiv (j : Kind) (x : SpecialFullFilling j) :
    (fullBundle j).Fiber x ≃L[ℂ] FullIntrinsicTopCovector j x :=
  Atlas.intrinsicEquiv (SpecialFullFilling j) x

def fullInCoordinates (j : Kind) (i : atlas Model (SpecialFullFilling j))
    (x : SpecialFullFilling j) (v : (fullBundle j).Fiber x) : TopCovector :=
  Atlas.inCoordinates (SpecialFullFilling j) i x v

theorem fullInCoordinates_eq_intrinsic_pullback (j : Kind)
    (i : atlas Model (SpecialFullFilling j)) (x : SpecialFullFilling j)
    (v : (fullBundle j).Fiber x) :
    fullInCoordinates j i x v = (fullIntrinsicEquiv j x v).compContinuousLinearMap
      ((tangentBundleCore IF (SpecialFullFilling j)).coordChange i (achart Model x) x) :=
  Atlas.inCoordinates_eq_intrinsic_pullback (SpecialFullFilling j) i x v

def fullCoordinateEquiv (j : Kind) (i : atlas Model (SpecialFullFilling j))
    {x : SpecialFullFilling j} (hx : x ∈ i.val.source) :
    (fullBundle j).Fiber x ≃L[ℂ] TopCovector :=
  Atlas.coordinateEquiv (SpecialFullFilling j) i hx

/-- The full filling's transition is the inverse determinant of its
actual forward tangent-coordinate map. -/
theorem full_transition_eq_inverse_jacobian (j : Kind)
    (i k : atlas Model (SpecialFullFilling j)) {x : SpecialFullFilling j}
    (hi : x ∈ i.val.source) (hk : x ∈ k.val.source) :
    (fullBundle j).coordChange i k x =
      (LinearMap.det (fderiv ℂ (k.val ∘ i.val.symm) (i.val x)).toLinearMap)⁻¹ •
        ContinuousLinearMap.id ℂ ℂ :=
  Atlas.coordChange_eq_inverse_jacobian (SpecialFullFilling j) i k hi hk

theorem fullInCoordinates_change (j : Kind)
    (i k : atlas Model (SpecialFullFilling j)) {x : SpecialFullFilling j}
    (hi : x ∈ i.val.source) (hk : x ∈ k.val.source) (v : (fullBundle j).Fiber x) :
    fullInCoordinates j k x v = (fullInCoordinates j i x v).compContinuousLinearMap
      (fderiv ℂ (i.val ∘ k.val.symm) (k.val x)) :=
  Atlas.inCoordinates_change (SpecialFullFilling j) i k hi hk v

abbrev fullChartSource (j : Kind) (i : SpecialFullFilling j) :
    TopologicalSpace.Opens (SpecialFullFilling j) :=
  Atlas.chartSource (SpecialFullFilling j) (achart Model i)

def fullLocalFrame (j : Kind) (i : SpecialFullFilling j) (x : fullChartSource j i) :
    (fullBundle j).Fiber x.val :=
  Atlas.localFrame (SpecialFullFilling j) (achart Model i) x

theorem fullLocalFrame_ne_zero (j : Kind) (i : SpecialFullFilling j)
    (x : fullChartSource j i) : fullLocalFrame j i x ≠ 0 :=
  Atlas.localFrame_ne_zero (SpecialFullFilling j) (achart Model i) x

def fullLocalFrameSection (j : Kind) (i : SpecialFullFilling j)
    (x : fullChartSource j i) : (fullBundle j).TotalSpace :=
  ⟨x.val, fullLocalFrame j i x⟩

theorem fullLocalFrameSection_holomorphic (j : Kind) (i : SpecialFullFilling j) :
    ContMDiff IF ((IF).prod I₁) ω (fullLocalFrameSection j i) :=
  Atlas.localFrameSection_holomorphic (SpecialFullFilling j) (achart Model i)

@[simp] theorem fullLocalFrame_inCoordinates (j : Kind) (i : SpecialFullFilling j)
    (x : fullChartSource j i) :
    fullInCoordinates j (achart Model i) x.val (fullLocalFrame j i x) = volume :=
  Atlas.localFrame_inCoordinates (SpecialFullFilling j) (achart Model i) x

/-- Native local volume frames have exactly the inverse-Jacobian factor. -/
theorem fullLocalFrame_change (j : Kind) (i k : SpecialFullFilling j)
    (x : fullChartSource j i) (hk : x.val ∈ fullChartSource j k) :
    fullLocalFrame j i x =
      (LinearMap.det (fderiv ℂ (chartAt Model k ∘ (chartAt Model i).symm)
        (chartAt Model i x)).toLinearMap)⁻¹ • fullLocalFrame j k ⟨x.val, hk⟩ := by
  rw [fullLocalFrame, Atlas.localFrame_change (SpecialFullFilling j)
    (achart Model i) (achart Model k) x hk,
    Atlas.jacobian_reverse (SpecialFullFilling j) (achart Model i) (achart Model k)
      x.property hk, Atlas.jacobian_eq_fderiv]
  rfl

theorem fullLocalFrames_cover (j : Kind) (x : SpecialFullFilling j) :
    ∃ i, x ∈ fullChartSource j i := ⟨x, mem_chart_source Model x⟩

theorem fullTotalSpace_isManifold (j : Kind) :
    IsManifold ((IF).prod I₁) ω (fullBundle j).TotalSpace :=
  Atlas.totalSpace_isManifold (SpecialFullFilling j)

/-- The genuine ambient canonical bundle of the original small open piece. -/
abbrev bundle (j : Kind) := Atlas.core (SpecialEllipticPiece j)

theorem bundle_holomorphic (j : Kind) : ContMDiffVectorBundle ω ℂ (bundle j).Fiber IF :=
  Atlas.holomorphicVectorBundle (SpecialEllipticPiece j)

theorem fibre_rank_one (j : Kind) (x : SpecialEllipticPiece j) :
    Module.finrank ℂ ((bundle j).Fiber x) = 1 :=
  Atlas.fibre_rank_one (SpecialEllipticPiece j) x

/-- These are three-covectors on the ambient tangent, including at the
central surface; they are not two-covectors on that surface's tangent. -/
abbrev IntrinsicTopCovector (j : Kind) (x : SpecialEllipticPiece j) :=
  (TangentSpace IF x) [⋀^(Fin 3)]→L[ℂ] ℂ

def intrinsicEquiv (j : Kind) (x : SpecialEllipticPiece j) :
    (bundle j).Fiber x ≃L[ℂ] IntrinsicTopCovector j x :=
  Atlas.intrinsicEquiv (SpecialEllipticPiece j) x

def inCoordinates (j : Kind) (i : atlas Model (SpecialEllipticPiece j))
    (x : SpecialEllipticPiece j) (v : (bundle j).Fiber x) : TopCovector :=
  Atlas.inCoordinates (SpecialEllipticPiece j) i x v

theorem inCoordinates_eq_intrinsic_pullback (j : Kind)
    (i : atlas Model (SpecialEllipticPiece j)) (x : SpecialEllipticPiece j)
    (v : (bundle j).Fiber x) :
    inCoordinates j i x v = (intrinsicEquiv j x v).compContinuousLinearMap
      ((tangentBundleCore IF (SpecialEllipticPiece j)).coordChange i (achart Model x) x) :=
  Atlas.inCoordinates_eq_intrinsic_pullback (SpecialEllipticPiece j) i x v

def coordinateEquiv (j : Kind) (i : atlas Model (SpecialEllipticPiece j))
    {x : SpecialEllipticPiece j} (hx : x ∈ i.val.source) :
    (bundle j).Fiber x ≃L[ℂ] TopCovector :=
  Atlas.coordinateEquiv (SpecialEllipticPiece j) i hx

theorem transition_eq_inverse_jacobian (j : Kind)
    (i k : atlas Model (SpecialEllipticPiece j)) {x : SpecialEllipticPiece j}
    (hi : x ∈ i.val.source) (hk : x ∈ k.val.source) :
    (bundle j).coordChange i k x =
      (LinearMap.det (fderiv ℂ (k.val ∘ i.val.symm) (i.val x)).toLinearMap)⁻¹ •
        ContinuousLinearMap.id ℂ ℂ :=
  Atlas.coordChange_eq_inverse_jacobian (SpecialEllipticPiece j) i k hi hk

theorem inCoordinates_change (j : Kind)
    (i k : atlas Model (SpecialEllipticPiece j)) {x : SpecialEllipticPiece j}
    (hi : x ∈ i.val.source) (hk : x ∈ k.val.source) (v : (bundle j).Fiber x) :
    inCoordinates j k x v = (inCoordinates j i x v).compContinuousLinearMap
      (fderiv ℂ (i.val ∘ k.val.symm) (k.val x)) :=
  Atlas.inCoordinates_change (SpecialEllipticPiece j) i k hi hk v

abbrev chartSource (j : Kind) (i : SpecialEllipticPiece j) :
    TopologicalSpace.Opens (SpecialEllipticPiece j) :=
  Atlas.chartSource (SpecialEllipticPiece j) (achart Model i)

def localFrame (j : Kind) (i : SpecialEllipticPiece j) (x : chartSource j i) :
    (bundle j).Fiber x.val :=
  Atlas.localFrame (SpecialEllipticPiece j) (achart Model i) x

theorem localFrame_ne_zero (j : Kind) (i : SpecialEllipticPiece j)
    (x : chartSource j i) : localFrame j i x ≠ 0 :=
  Atlas.localFrame_ne_zero (SpecialEllipticPiece j) (achart Model i) x

def localFrameSection (j : Kind) (i : SpecialEllipticPiece j)
    (x : chartSource j i) : (bundle j).TotalSpace := ⟨x.val, localFrame j i x⟩

theorem localFrameSection_holomorphic (j : Kind) (i : SpecialEllipticPiece j) :
    ContMDiff IF ((IF).prod I₁) ω (localFrameSection j i) :=
  Atlas.localFrameSection_holomorphic (SpecialEllipticPiece j) (achart Model i)

@[simp] theorem localFrame_inCoordinates (j : Kind) (i : SpecialEllipticPiece j)
    (x : chartSource j i) :
    inCoordinates j (achart Model i) x.val (localFrame j i x) = volume :=
  Atlas.localFrame_inCoordinates (SpecialEllipticPiece j) (achart Model i) x

theorem localFrame_change (j : Kind) (i k : SpecialEllipticPiece j)
    (x : chartSource j i) (hk : x.val ∈ chartSource j k) :
    localFrame j i x =
      (LinearMap.det (fderiv ℂ (chartAt Model k ∘ (chartAt Model i).symm)
        (chartAt Model i x)).toLinearMap)⁻¹ • localFrame j k ⟨x.val, hk⟩ := by
  rw [localFrame, Atlas.localFrame_change (SpecialEllipticPiece j)
    (achart Model i) (achart Model k) x hk,
    Atlas.jacobian_reverse (SpecialEllipticPiece j) (achart Model i) (achart Model k)
      x.property hk, Atlas.jacobian_eq_fderiv]
  rfl

theorem localFrames_cover (j : Kind) (x : SpecialEllipticPiece j) :
    ∃ i, x ∈ chartSource j i := ⟨x, mem_chart_source Model x⟩

theorem totalSpace_isManifold (j : Kind) :
    IsManifold ((IF).prod I₁) ω (bundle j).TotalSpace :=
  Atlas.totalSpace_isManifold (SpecialEllipticPiece j)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Elliptic
