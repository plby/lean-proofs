import Wikipedia.NoExoticSixSphere.QuaternionCommutatorCubeCoordinates

/-!
# An exact source-chart comparison for the original native seven-sphere map

This includes the reversed native time coordinate, both actual sphere
block charts, and the original sphere/cube quotient. The comparison
holds on a genuine open chart containing the unique antipodal preimage.
-/

noncomputable section

open scoped unitInterval commutatorElement

namespace NoExoticSixSphere.QuaternionCommutatorNativeCharts

open Wikipedia.HomotopyGroupsOfSpheres
open QuaternionicFibration QuaternionCommutatorSourceChart
open QuaternionCommutatorBlockChart QuaternionCommutatorCubeCoordinates
open QuaternionCommutatorNativeSphere QuaternionCommutatorBoundaryLift CubeFirstCoordinate

local notation "south" => QuaternionCommutatorAntipodal.antipode

def productChart : OpenPartialHomeomorph (ℝ × (GLOrthonormalization.Vector 3 ×
    GLOrthonormalization.Vector 3)) Parameters :=
  timeCoordinates.toOpenPartialHomeomorph.prod (blockChart.prod blockChart)

def nativeChart : OpenPartialHomeomorph (Sphere 7) Parameters :=
  ((SmoothCube.sphereChart 7).toOpenPartialHomeomorph.transHomeomorph blocks.toHomeomorph).trans
    productChart

theorem nativeChart_source_subset : nativeChart.source ⊆ {spherePole 7}ᶜ :=
  fun _ hx ↦ hx.1

theorem nativeChart_source_cube (u : Fin 7 → I) (hu : u ∉ Cube.boundary (Fin 7)) :
    SmoothCube.quotient 7 u ∈ nativeChart.source := by
  have hx := (SmoothCube.vectorOfCube_mem_openCube 7 u).mpr hu
  refine ⟨?_, ?_⟩
  · exact fun h ↦ hu ((SmoothCube.quotient_eq_pole_iff 7 u).mp h)
  · change blocks (SmoothCube.sphereChart 7 (SmoothCube.quotient 7 u)) ∈
      timeCoordinates.toOpenPartialHomeomorph.source ×ˢ (blockChart.source ×ˢ blockChart.source)
    rw [SmoothCube.sphereChart_quotient 7 u hu]
    exact ⟨Set.mem_univ _, blocks_left_open hx, blocks_right_open hx⟩

theorem nativeChart_quotient (u : Fin 7 → I) (hu : u ∉ Cube.boundary (Fin 7)) :
    nativeChart (SmoothCube.quotient 7 u) = (timeCoordinates (split 6 u).1.val,
      (blockChart (SmoothCube.vectorOfCube 3
        (fun i ↦ (split 6 u).2 (blockCoordinates (Sum.inl i)))),
       blockChart (SmoothCube.vectorOfCube 3
        (fun i ↦ (split 6 u).2 (blockCoordinates (Sum.inr i)))))) := by
  change productChart (blocks (SmoothCube.sphereChart 7 (SmoothCube.quotient 7 u))) = _
  rw [SmoothCube.sphereChart_quotient 7 u hu, blocks_cube]
  rfl

theorem south_ne_north : south ≠ north := by
  intro h
  have hh := congrArg (fun v : BaseSphere ↦ v.val.fst.re) h
  change (-1 : ℝ) = 1 at hh
  norm_num at hh

theorem antipodalSevenCube_not_boundary : antipodalSevenCube ∉ Cube.boundary (Fin 7) := by
  intro h
  exact south_ne_north (antipodalSevenCube_value.symm.trans (sevenLoop.property _ h))

def sourcePoint : Sphere 7 := SmoothCube.quotient 7 antipodalSevenCube

theorem sourcePoint_map : sphereMap sourcePoint = south :=
  (sphereMap_quotient _).trans antipodalSevenCube_value

theorem sourcePoint_mem_nativeChart : sourcePoint ∈ nativeChart.source :=
  nativeChart_source_cube _ antipodalSevenCube_not_boundary

theorem nativeChart_sourcePoint : nativeChart sourcePoint = 0 := by
  change productChart (blocks (SmoothCube.sphereChart 7
    (SmoothCube.quotient 7 antipodalSevenCube))) = 0
  rw [SmoothCube.sphereChart_quotient 7 _ antipodalSevenCube_not_boundary, blocks_antipodal]
  change (timeCoordinates (1 / 2),
    (blockChart (SmoothCube.vectorOfCube 3 antipodalCube),
      blockChart (SmoothCube.vectorOfCube 3 antipodalCube))) = (0, 0, 0)
  rw [timeCoordinates_half, blockChart_antipodalCube]

theorem zero_mem_nativeChart_target : (0 : Parameters) ∈ nativeChart.target := by
  have h := nativeChart.map_source sourcePoint_mem_nativeChart
  rwa [nativeChart_sourcePoint] at h

theorem projectionMap_nativeChart_cube (u : Fin 7 → I) (hu : u ∉ Cube.boundary (Fin 7)) :
    QuaternionCommutatorSourceChart.projectionMap (nativeChart (SmoothCube.quotient 7 u)) =
      sphereMap (SmoothCube.quotient 7 u) := by
  let l : Fin 3 → I := fun i ↦ (split 6 u).2 (blockCoordinates (Sum.inl i))
  let r : Fin 3 → I := fun i ↦ (split 6 u).2 (blockCoordinates (Sum.inr i))
  have hx := (SmoothCube.vectorOfCube_mem_openCube 7 u).mpr hu
  have hl : l ∉ Cube.boundary (Fin 3) :=
    (SmoothCube.vectorOfCube_mem_openCube 3 l).mp (blocks_left_open hx)
  have hr : r ∉ Cube.boundary (Fin 3) :=
    (SmoothCube.vectorOfCube_mem_openCube 3 r).mp (blocks_right_open hx)
  rw [nativeChart_quotient u hu, sphereMap_quotient]
  change projection ⁅fiberInclusion (quaternionChart (blockChart (SmoothCube.vectorOfCube 3 l))),
    QuaternionCommutatorRotation.conjugatedFiber (Real.pi / 4 + timeCoordinates (split 6 u).1.val)
      (quaternionChart (blockChart (SmoothCube.vectorOfCube 3 r)))⁆ =
    projection (QuaternionCommutatorRotation.contraction (unitInterval.symm (split 6 u).1)
      (quaternionCube l) (quaternionCube r))
  rw [quaternionCube_chart l hl, quaternionCube_chart r hr, angle_timeCoordinates]
  rfl

theorem projectionMap_nativeChart (x : Sphere 7) (hx : x ∈ nativeChart.source) :
    QuaternionCommutatorSourceChart.projectionMap (nativeChart x) = sphereMap x := by
  obtain ⟨u, rfl⟩ := SmoothCube.quotient_surjective (by decide : 0 < 7) x
  apply projectionMap_nativeChart_cube u
  intro h
  exact nativeChart_source_subset hx (SmoothCube.quotient_boundary 7 u h)

end NoExoticSixSphere.QuaternionCommutatorNativeCharts
