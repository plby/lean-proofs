import Wikipedia.HopfProblem.DegreeCollapseNativeMiddleCoreDisks
import Wikipedia.HopfProblem.DegreeCollapseStandardDiskCoordinates

/-!
# Actual closed middle sphere maps in the original manifold

Both native core disks are glued to their constructed controlled caps.
The domain is the literal standard three-sphere. Exact hemisphere formulas,
the critical center and membership in the original capped basins are retained.
These maps are continuous; relative smoothing is a subsequent step.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality.SeparatedSystem

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] (D : SeparatedSystem E M)

def negativeLinear (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) :
    Hemisphere.Ambient 3 ≃ₗᵢ[ℝ] (D.windows.data p).chart.NegativeCoordinates :=
  StandardDiskCoordinates.coordinates
    ((nativeMorseIndex_eq_chart (D.windows.data p).chart).symm.trans hp)

def positiveLinear (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) :
    Hemisphere.Ambient 3 ≃ₗᵢ[ℝ] (D.windows.data p).chart.PositiveCoordinates := by
  apply StandardDiskCoordinates.coordinates
  have hn := (nativeMorseIndex_eq_chart (D.windows.data p).chart).symm.trans hp
  have hs := (D.windows.data p).chart.finrank_negative_add_positive
  have hd := D.dimension
  omega

def attachingCap (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) :
    C(closedBall (0 : (D.windows.data p).chart.NegativeCoordinates) 1, M) :=
  (D.exists_attaching_cap p hp).choose

def beltCap (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) :
    C(closedBall (0 : (D.windows.data p).chart.PositiveCoordinates) 1, M) :=
  (D.exists_belt_cap p hp).choose

theorem attachingCap_boundary (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3)
    (z : sphere (0 : (D.windows.data p).chart.NegativeCoordinates) 1) :
    D.attachingCap p hp ⟨z.val, sphere_subset_closedBall z.property⟩ = D.attachingMap p z :=
  (D.exists_attaching_cap p hp).choose_spec.1 z

theorem beltCap_boundary (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3)
    (z : sphere (0 : (D.windows.data p).chart.PositiveCoordinates) 1) :
    D.beltCap p hp ⟨z.val, sphere_subset_closedBall z.property⟩ = D.beltMap p z :=
  (D.exists_belt_cap p hp).choose_spec.1 z

theorem attachingCap_image (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3)
    (z : closedBall (0 : (D.windows.data p).chart.NegativeCoordinates) 1) :
    D.attachingCap p hp z ∈ orbitSaturation D.windows.flow (D.attachingMap p) ∪
      {x | D.function x ≤ D.lowerCut} :=
  (D.exists_attaching_cap p hp).choose_spec.2 z

theorem beltCap_image (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3)
    (z : closedBall (0 : (D.windows.data p).chart.PositiveCoordinates) 1) :
    D.beltCap p hp z ∈ orbitSaturation D.windows.flow (D.beltMap p) ∪
      {x | D.upperCut ≤ D.function x} :=
  (D.exists_belt_cap p hp).choose_spec.2 z

theorem negative_boundary_agrees (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3)
    (z : DiskDouble.Boundary (Hemisphere.Ambient 3)) :
    StandardDiskCoordinates.reparametrize (D.negativeLinear p hp)
      (CoreDisks.negativeDisk (D.windows.data p)) (DiskDouble.boundary _ z) =
    StandardDiskCoordinates.reparametrize (D.negativeLinear p hp)
      (D.attachingCap p hp) (DiskDouble.boundary _ z) := by
  apply StandardDiskCoordinates.boundary_agrees
  intro u
  rw [CoreDisks.negative_boundary, D.attachingCap_boundary]
  rfl

theorem positive_boundary_agrees (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3)
    (z : DiskDouble.Boundary (Hemisphere.Ambient 3)) :
    StandardDiskCoordinates.reparametrize (D.positiveLinear p hp)
      (CoreDisks.positiveDisk (D.windows.data p)) (DiskDouble.boundary _ z) =
    StandardDiskCoordinates.reparametrize (D.positiveLinear p hp)
      (D.beltCap p hp) (DiskDouble.boundary _ z) := by
  apply StandardDiskCoordinates.boundary_agrees
  intro u
  rw [CoreDisks.positive_boundary, D.beltCap_boundary]
  rfl

def descendingSphere (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) : C(Hemisphere.Sphere 3, M) :=
  SphereDiskGluing.map
    (StandardDiskCoordinates.reparametrize (D.negativeLinear p hp)
      (CoreDisks.negativeDisk (D.windows.data p)))
    (StandardDiskCoordinates.reparametrize (D.negativeLinear p hp) (D.attachingCap p hp))
    (D.negative_boundary_agrees p hp)

def ascendingSphere (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) : C(Hemisphere.Sphere 3, M) :=
  SphereDiskGluing.map
    (StandardDiskCoordinates.reparametrize (D.positiveLinear p hp)
      (CoreDisks.positiveDisk (D.windows.data p)))
    (StandardDiskCoordinates.reparametrize (D.positiveLinear p hp) (D.beltCap p hp))
    (D.positive_boundary_agrees p hp)

theorem descendingSphere_false (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) (u : Hemisphere.Ball 3) :
    D.descendingSphere p hp (Hemisphere.point false u) =
      CoreDisks.negativeFun (D.windows.data p) (D.negativeLinear p hp u.val) :=
  SphereDiskGluing.map_false _ _ _ u

theorem ascendingSphere_false (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) (u : Hemisphere.Ball 3) :
    D.ascendingSphere p hp (Hemisphere.point false u) =
      CoreDisks.positiveFun (D.windows.data p) (D.positiveLinear p hp u.val) :=
  SphereDiskGluing.map_false _ _ _ u

theorem descendingSphere_true (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) (u : Hemisphere.Ball 3) :
    D.descendingSphere p hp (Hemisphere.point true u) =
      D.attachingCap p hp (StandardDiskCoordinates.disk (D.negativeLinear p hp) u) :=
  SphereDiskGluing.map_true _ _ _ u

theorem ascendingSphere_true (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) (u : Hemisphere.Ball 3) :
    D.ascendingSphere p hp (Hemisphere.point true u) =
      D.beltCap p hp (StandardDiskCoordinates.disk (D.positiveLinear p hp) u) :=
  SphereDiskGluing.map_true _ _ _ u

theorem descendingSphere_mem (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) (x : Hemisphere.Sphere 3) :
    D.descendingSphere p hp x ∈ D.descendingCarrier p := by
  obtain ⟨b, u, rfl⟩ := Hemisphere.point_jointly_surjective x
  cases b
  · rw [D.descendingSphere_false]
    exact Or.inl (D.negativeDisk_descending p
      (StandardDiskCoordinates.disk (D.negativeLinear p hp) u))
  · rw [D.descendingSphere_true]
    rcases D.attachingCap_image p hp _ with h | h
    · exact Or.inl (D.attaching_orbit_descending p h)
    · exact Or.inr h

theorem ascendingSphere_mem (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) (x : Hemisphere.Sphere 3) :
    D.ascendingSphere p hp x ∈ D.ascendingCarrier p := by
  obtain ⟨b, u, rfl⟩ := Hemisphere.point_jointly_surjective x
  cases b
  · rw [D.ascendingSphere_false]
    exact Or.inl (D.positiveDisk_ascending p
      (StandardDiskCoordinates.disk (D.positiveLinear p hp) u))
  · rw [D.ascendingSphere_true]
    rcases D.beltCap_image p hp _ with h | h
    · exact Or.inl (D.belt_orbit_ascending p h)
    · exact Or.inr h

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality.SeparatedSystem
