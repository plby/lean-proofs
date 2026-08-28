import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionGluingHolomorphic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionCuspOverlap
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionElliptic

/-!
# The actual global vertical complex flow

The original regular translations, the toric cusp cocharacter, and the
two actual logarithmic-filling translations agree on all three full
overlaps.  They therefore construct a jointly holomorphic fibre-preserving
flow on the genuine compact threefold.  Its exact kernel is proved using
the already established actual regular-family kernel.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] chartedSpace localPieceChartedSpace

/-- The four original local flows, including the actual central fibres. -/
def localFlow : (i : Index) → ℂ → localPiece i → localPiece i
  | none => Regular.flow
  | some none => Cusp.specialFlow
  | some (some j) => Elliptic.specialFlow j

theorem localFlow_projection (i : Index) (s : ℂ) (x : localPiece i) :
    localProjectionToBase i (localFlow i s x) = localProjectionToBase i x := by
  cases i with
  | none => exact Regular.flow_projection s x
  | some i =>
      cases i with
      | none => exact Cusp.specialCuspPieceProjectionToBase_specialFlow s x
      | some j => exact Elliptic.specialFlow_projectionToBase j s x

/-- Agreement is proved for the actual unmodified gluing maps. -/
theorem localFlow_overlap (i : Puncture) (s : ℂ) (x : localPiece (some i))
    (hx : x ∈ (localOverlap i).source) :
    localOverlap i (localFlow (some i) s x) = localFlow none s (localOverlap i x) := by
  cases i with
  | none => exact Cusp.specialCuspOverlap_specialFlow s x hx
  | some j => exact Elliptic.specialEllipticOverlap_specialFlow j s x hx

theorem localFlow_zero (i : Index) (x : localPiece i) : localFlow i 0 x = x := by
  cases i with
  | none => exact Regular.flow_zero x
  | some i =>
      cases i with
      | none => exact Cusp.specialFlow_zero x
      | some j => exact Elliptic.specialFlow_zero j x

theorem localFlow_add (i : Index) (s t : ℂ) (x : localPiece i) :
    localFlow i (s + t) x = localFlow i s (localFlow i t x) := by
  cases i with
  | none => exact Regular.flow_add s t x
  | some i =>
      cases i with
      | none => exact Cusp.specialFlow_add s t x
      | some j => exact Elliptic.specialFlow_add j s t x

theorem localFlow_int_cast (i : Index) (n : ℤ) (x : localPiece i) :
    localFlow i (n : ℂ) x = x := by
  cases i with
  | none => exact Regular.flow_int_cast n x
  | some i =>
      cases i with
      | none => exact Cusp.specialFlow_int_cast n x
      | some j => exact Elliptic.specialFlow_int_cast j n x

theorem localFlow_joint_holomorphic (i : Index) :
    ContMDiff ((IF).prod I₁) IF ω
      (fun p : localPiece i × ℂ => localFlow i p.2 p.1) := by
  cases i with
  | none => exact Regular.jointFlow_holomorphic
  | some i =>
      cases i with
      | none => exact Cusp.specialFlow_joint_common_holomorphic
      | some j => exact Elliptic.specialFlow_joint_holomorphic j

/-- The globally constructed vertical flow on the actual threefold. -/
def flow (s : ℂ) : Space → Space :=
  Gluing.glue localFlow localFlow_projection localFlow_overlap s

@[simp] theorem flow_inclusion (s : ℂ) (i : Index) (x : localPiece i) :
    flow s (inclusion i x) = inclusion i (localFlow i s x) :=
  Gluing.glue_inclusion localFlow localFlow_projection localFlow_overlap s i x

@[simp] theorem flow_regular (s : ℂ) (x : SpecialRegularFamily) :
    flow s (regularFamilyInclusion x) = regularFamilyInclusion (Regular.flow s x) :=
  flow_inclusion s none x

@[simp] theorem flow_cusp (s : ℂ) (x : CuspGeometry.LocalSpace) :
    flow s (CuspGeometry.inclusion x) = CuspGeometry.inclusion (Cusp.specialFlow s x) :=
  flow_inclusion s (some none) x

@[simp] theorem flow_elliptic (j : Wikipedia.HopfProblem.Elliptic.Kind)
    (s : ℂ) (x : EllipticGeometry.LocalSpace j) :
    flow s (EllipticGeometry.inclusion j x) =
      EllipticGeometry.inclusion j (Elliptic.specialFlow j s x) :=
  flow_inclusion s (some (some j)) x

@[simp] theorem flow_zero (x : Space) : flow 0 x = x :=
  Gluing.glue_zero localFlow localFlow_projection localFlow_overlap localFlow_zero x

theorem flow_add (s t : ℂ) (x : Space) : flow (s + t) x = flow s (flow t x) :=
  Gluing.glue_add localFlow localFlow_projection localFlow_overlap localFlow_add s t x

@[simp] theorem flow_int_cast (n : ℤ) (x : Space) : flow (n : ℂ) x = x :=
  Gluing.glue_int_cast localFlow localFlow_projection localFlow_overlap localFlow_int_cast n x

@[simp] theorem projection_flow (s : ℂ) (x : Space) : projection (flow s x) = projection x :=
  Gluing.glue_projection localFlow localFlow_projection localFlow_overlap s x

@[simp] theorem projectionSphere_flow (s : ℂ) (x : Space) :
    projectionSphere (flow s x) = projectionSphere x := by
  simp only [projectionSphere, Function.comp_def, projection_flow]

theorem jointFlow_holomorphic :
    ContMDiff ((IF).prod I₁) IF ω (fun p : Space × ℂ => flow p.2 p.1) :=
  Gluing.glue_joint_holomorphic localFlow localFlow_projection localFlow_overlap
    localFlow_joint_holomorphic

theorem flow_holomorphic (s : ℂ) : ContMDiff IF IF ω (flow s) :=
  Gluing.glue_holomorphic localFlow localFlow_projection localFlow_overlap
    localFlow_joint_holomorphic s

def flowBiholomorph (s : ℂ) : Diffeomorph IF IF Space Space ω :=
  Gluing.glueBiholomorph localFlow localFlow_projection localFlow_overlap
    localFlow_joint_holomorphic localFlow_zero localFlow_add s

@[simp] theorem flowBiholomorph_apply (s : ℂ) (x : Space) :
    flowBiholomorph s x = flow s x := rfl

/-- No nonintegral complex time acts trivially on the actual threefold. -/
theorem flow_eq_id_iff (s : ℂ) : flow s = id ↔ ∃ n : ℤ, s = (n : ℂ) := by
  constructor
  · intro h
    apply (Regular.flow_eq_id_iff s).mp
    funext x
    apply regularFamilyInclusion_isOpenEmbedding.injective
    calc
      regularFamilyInclusion (Regular.flow s x) = flow s (regularFamilyInclusion x) :=
        (flow_regular s x).symm
      _ = regularFamilyInclusion x := congrFun h (regularFamilyInclusion x)
  · rintro ⟨n, rfl⟩
    funext x
    exact flow_int_cast n x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction
