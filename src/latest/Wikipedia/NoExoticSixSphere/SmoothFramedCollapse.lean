import Wikipedia.NoExoticSixSphere.FramedCollapseDifferential
import Wikipedia.NoExoticSixSphere.FramedTubeData

/-!
# Collapse data with smooth finite coordinates and the actual normal frame

The collapse map is continuous on the one-point compactification. On an
open neighborhood of the embedded manifold it has smooth finite coordinates,
with surjective differential. That differential identifies the positively
rescaled given normal frame with the normal model. No global smoothness at
the collapsed complement or bordism correspondence is asserted here.

The canonical construction retains its chosen `FramedTubeData` certificate.
Its map is exactly the collapse of that actual tube, not an opaque choice
among data records whose fields describe only the local geometry.
-/

open scoped Manifold ContDiff
open Set Topology

namespace NoExoticSixSphere.EuclideanEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (e : EuclideanEmbedding n M)
  (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel)

structure FramedCollapseData where
  radius : ℝ
  radius_pos : 0 < radius
  neighborhood : Set (EuclideanSpace ℝ (Fin e.ambientDimension))
  open_neighborhood : IsOpen neighborhood
  range_subset : range e.toFun ⊆ neighborhood
  coordinates : EuclideanSpace ℝ (Fin e.ambientDimension) → e.NormalModel
  smooth_coordinates : ContDiffOn ℝ ∞ coordinates neighborhood
  surjective_differential : ∀ y ∈ neighborhood, Function.Surjective (fderiv ℝ coordinates y)
  differential_frame : ∀ x v, fderiv ℝ coordinates (e.toFun x) (radius • a.ambient x v) = v
  map : C(OnePoint (EuclideanSpace ℝ (Fin e.ambientDimension)), OnePoint e.NormalModel)
  map_infty : map OnePoint.infty = OnePoint.infty
  zero_fiber : ∀ y, map y = (↑(0 : e.NormalModel)) ↔
    ∃ x, (e.toFun x : OnePoint (EuclideanSpace ℝ (Fin e.ambientDimension))) = y
  local_formula : ∀ y ∈ neighborhood, map (y : OnePoint _) = (↑(coordinates y) : OnePoint _)

variable [IsManifold (𝓡 n) ∞ M] [CompactSpace M]
variable {e a}

noncomputable def FramedTubeData.collapseData (d : e.FramedTubeData a) :
    e.FramedCollapseData a := by
  refine {
    radius := d.radius
    radius_pos := d.radius_pos
    neighborhood := d.tube.target
    open_neighborhood := d.tube.open_target
    range_subset := d.range_subset_target
    coordinates := SmoothCollapseCoordinates.coordinate d.tube
    smooth_coordinates := (SmoothCollapseCoordinates.contMDiffOn_coordinate d.tube).contDiffOn
    surjective_differential := ?_
    differential_frame := e.fderiv_collapseCoordinate_frame a d.radius d.radius_pos
      d.tube d.source_univ d.formula
    map := ⟨OpenFiberCollapse.collapseOnePoint d.tube,
      OpenFiberCollapse.continuous_collapseOnePoint d.tube d.isOpenEmbedding⟩
    map_infty := OpenFiberCollapse.collapseOnePoint_infty d.tube
    zero_fiber := ?_
    local_formula := fun _ hy ↦
      SmoothCollapseCoordinates.collapseOnePoint_eq_coordinate d.tube d.source_univ hy }
  · intro y hy
    have hd := (SmoothCollapseCoordinates.contMDiffAt_coordinate d.tube hy).contDiffAt
      |>.differentiableAt (by simp)
    have hsurj := SmoothCollapseCoordinates.mfderiv_coordinate_surjective d.tube hy
    rw [hd.hasFDerivAt.hasMFDerivAt.mfderiv] at hsurj
    exact hsurj
  · intro y
    change OpenFiberCollapse.collapseOnePoint d.tube y = (↑(0 : e.NormalModel)) ↔ _
    rw [OpenFiberCollapse.collapseOnePoint_eq_coe_iff d.tube d.isOpenEmbedding.injective]
    simp only [d.tube_zero]

theorem FramedTubeData.collapseData_map (d : e.FramedTubeData a)
    (z : OnePoint (EuclideanSpace ℝ (Fin e.ambientDimension))) :
    d.collapseData.map z = OpenFiberCollapse.collapseOnePoint d.tube z := rfl

variable (e a) [Nonempty M]

theorem nonempty_framedCollapseData : Nonempty (e.FramedCollapseData a) :=
  ⟨(e.framedTubeData a).collapseData⟩

noncomputable def framedCollapseData : e.FramedCollapseData a :=
  (e.framedTubeData a).collapseData

theorem framedCollapseData_map (z : OnePoint (EuclideanSpace ℝ (Fin e.ambientDimension))) :
    (e.framedCollapseData a).map z =
      OpenFiberCollapse.collapseOnePoint (e.framedTubeData a).tube z := rfl

theorem framedCollapseData_radius :
    (e.framedCollapseData a).radius = (e.framedTubeData a).radius := rfl

end NoExoticSixSphere.EuclideanEmbedding
