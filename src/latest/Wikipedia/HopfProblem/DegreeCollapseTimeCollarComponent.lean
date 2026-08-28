import Wikipedia.HopfProblem.DegreeCollapseTimeCollarOverlap
import Wikipedia.SmoothSixDPoincare.FundamentalGroupMapTools
import Mathlib.Topology.Connected.LocallyPathConnected

/-!

# The actual component containing a connected collar boundary

The entire time band is path connected when the specified boundary is.
It lies in the path component of a boundary basepoint. This component is
open and closed in a locally path-connected ambient space, hence compact
when the ambient space is compact. Restricting the original time and collar
to it preserves every original zero point. All maps are literal subtype
inclusions or their inverses; no replacement topology is introduced.
-/

noncomputable section

open Set Topology ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

open Wikipedia.SmoothSixDPoincare

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  [LocallyPathConnectedSpace M] {t : M → ℝ} (C : TimeCollar t B) (b : B)

def boundaryComponent : TopologicalSpace.Opens M :=
  ⟨pathComponent (C.zeroPoint b).val, (IsClopen.pathComponent _).isOpen⟩

theorem boundaryComponent_isClosed : IsClosed (C.boundaryComponent b : Set M) :=
  (IsClopen.pathComponent _).isClosed

theorem boundaryComponent_pathConnected : PathConnectedSpace (C.boundaryComponent b) :=
  isPathConnected_iff_pathConnectedSpace.mp isPathConnected_pathComponent

theorem boundaryComponent_compact [CompactSpace M] : CompactSpace (C.boundaryComponent b) :=
  isCompact_iff_compactSpace.mp (C.boundaryComponent_isClosed b).isCompact

variable [PathConnectedSpace B]

theorem band_subset_boundaryComponent :
    {p : M | t p ∈ Ioo (-C.width) C.width} ⊆ C.boundaryComponent b := by
  let : PathConnectedSpace (TimeBand t C.width) :=
    FundamentalGroupTools.pathConnected_of_homotopyEquiv C.bandHomotopyEquiv
  have hBand : IsPathConnected {p : M | t p ∈ Ioo (-C.width) C.width} :=
    isPathConnected_iff_pathConnectedSpace.mpr
      (inferInstanceAs (PathConnectedSpace (TimeBand t C.width)))
  exact hBand.subset_pathComponent (C.zeroPoint b).property

theorem zero_mem_boundaryComponent {p : M} (hp : t p = 0) : p ∈ C.boundaryComponent b := by
  apply C.band_subset_boundaryComponent b
  change t p ∈ Ioo (-C.width) C.width
  rw [hp]
  exact ⟨neg_lt_zero.mpr C.width_pos, C.width_pos⟩

def componentBandHomeomorph :
    TimeBand (fun p : C.boundaryComponent b ↦ t p.val) C.width ≃ₜ TimeBand t C.width where
  toFun p := ⟨p.val.val, p.property⟩
  invFun p := ⟨⟨p.val, C.band_subset_boundaryComponent b p.property⟩, p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

def restrictToBoundaryComponent : TimeCollar (fun p : C.boundaryComponent b ↦ t p.val) B where
  width := C.width
  width_pos := C.width_pos
  continuous_time := C.continuous_time.comp continuous_subtype_val
  coordinates := (C.componentBandHomeomorph b).trans C.coordinates
  coordinate_time p := C.coordinate_time (C.componentBandHomeomorph b p)

def componentZeroHomeomorph :
    {p : C.boundaryComponent b // t p.val = 0} ≃ₜ {p : M // t p = 0} where
  toFun p := ⟨p.val.val, p.property⟩
  invFun p := ⟨⟨p.val, C.zero_mem_boundaryComponent b p.property⟩, p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem componentZeroHomeomorph_point (p : {p : C.boundaryComponent b // t p.val = 0}) :
    (C.componentZeroHomeomorph b p).val = p.val.val := rfl

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
