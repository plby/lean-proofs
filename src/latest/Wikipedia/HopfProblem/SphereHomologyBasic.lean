import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Homotopy.Contractible

/-!
# The original Euclidean spheres used in singular homology

These are the literal unit spheres in real Euclidean space, with the
inherited topology. No homology or recognition property is part of their
definition.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SphereHomology

/-- The standard unit `n`-sphere in real Euclidean `(n+1)`-space. -/
abbrev UnitSphere (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

@[simp] theorem unitSphere_norm {n : ℕ} (x : UnitSphere n) : ‖x.val‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using x.property

/-- An actual unit coordinate vector gives a point in every sphere here. -/
def basePoint (n : ℕ) : UnitSphere n :=
  ⟨PiLp.single 2 (0 : Fin (n + 1)) (1 : ℝ), by simp⟩

instance unitSphere_nonempty (n : ℕ) : Nonempty (UnitSphere n) := ⟨basePoint n⟩

instance unitSphere_compactSpace (n : ℕ) : CompactSpace (UnitSphere n) := inferInstance

end Wikipedia.HopfProblem.SphereHomology
