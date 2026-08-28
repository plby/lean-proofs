import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The statement that there are no exotic six-spheres

The standard sphere below has mathlib's stereographic smooth structure. A candidate
manifold has its own, independently supplied charted-space structure. In particular,
a homeomorphism is not assumed to be smooth.

`SixSphereRigidity` is the proposition to be proved, not a theorem asserting it.
The results in this file only establish elementary reformulations and topological
prerequisites. They do not establish the classification of smooth six-spheres.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere

universe u v

/-- The unit `n`-sphere in Euclidean `(n + 1)`-space, with its standard smooth structure. -/
abbrev Sphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- A charted space is exotic if it is homeomorphic, but not diffeomorphic, to the
standard sphere. Smoothness of the atlas is imposed separately in `SixSphereRigidity`. -/
def IsExoticSphere (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] : Prop :=
  Nonempty (M ≃ₜ Sphere n) ∧ IsEmpty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ Sphere n)

/-- The requested classification statement, with no classification hypothesis.
This definition does not supply a proof of the proposition. -/
def SixSphereRigidity : Prop :=
  ∀ (M : Type u) (_ : TopologicalSpace M)
    (_ : ChartedSpace (EuclideanSpace ℝ (Fin 6)) M)
    (_ : IsManifold (𝓡 6) ∞ M),
    Nonempty (M ≃ₜ Sphere 6) → Nonempty (M ≃ₘ⟮𝓡 6, 𝓡 6⟯ Sphere 6)

section Elementary

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {N : Type v} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]

/-- Once a homeomorphism is given, not being exotic means that a diffeomorphism exists. -/
theorem not_isExoticSphere_iff (h : Nonempty (M ≃ₜ Sphere n)) :
    ¬ IsExoticSphere n M ↔ Nonempty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ Sphere n) := by
  classical
  simp only [IsExoticSphere, h, true_and, not_isEmpty_iff]

/-- Diffeomorphism, not just homeomorphism, preserves exoticity. -/
theorem isExoticSphere_iff_of_diffeomorph (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) :
    IsExoticSphere n M ↔ IsExoticSphere n N := by
  constructor
  · rintro ⟨⟨h⟩, hd⟩
    exact ⟨⟨e.symm.toHomeomorph.trans h⟩, ⟨fun d ↦ hd.false (e.trans d)⟩⟩
  · rintro ⟨⟨h⟩, hd⟩
    exact ⟨⟨e.toHomeomorph.trans h⟩, ⟨fun d ↦ hd.false (e.symm.trans d)⟩⟩

/-- The standard smooth sphere itself is not exotic. This is not a uniqueness theorem
for other smooth structures on its underlying topological space. -/
theorem standardSphere_not_exotic (n : ℕ) : ¬ IsExoticSphere n (Sphere n) := by
  intro h
  exact h.2.false (Diffeomorph.refl (𝓡 n) (Sphere n) ∞)

end Elementary

/-- A precise equivalence between the classification statement and nonexistence of
exotic six-spheres. Neither side is assumed or asserted unconditionally here. -/
theorem sixSphereRigidity_iff_no_exotic :
    SixSphereRigidity.{u} ↔
      ∀ (M : Type u) (_ : TopologicalSpace M)
        (_ : ChartedSpace (EuclideanSpace ℝ (Fin 6)) M)
        (_ : IsManifold (𝓡 6) ∞ M), ¬ IsExoticSphere 6 M := by
  constructor
  · intro h M _ _ _ he
    obtain ⟨d⟩ := h M inferInstance inferInstance inferInstance he.1
    exact he.2.false d
  · intro h M _ _ _ he
    exact (not_isExoticSphere_iff he).mp (h M inferInstance inferInstance inferInstance)

section Topology

variable {n : ℕ} {M : Type u} [TopologicalSpace M]

/-- Compactness need not be an additional hypothesis in the requested theorem. -/
theorem compactSpace_of_homeomorph (h : M ≃ₜ Sphere n) : CompactSpace M :=
  h.symm.compactSpace

/-- The Hausdorff assumption also follows from the given homeomorphism. -/
theorem t2Space_of_homeomorph (h : M ≃ₜ Sphere n) : T2Space M :=
  h.symm.t2Space

/-- The given homeomorphism supplies the usual countability assumption for a manifold. -/
theorem secondCountableTopology_of_homeomorph (h : M ≃ₜ Sphere n) :
    SecondCountableTopology M :=
  h.secondCountableTopology

/-- A candidate exotic sphere is a homotopy sphere at the level of topological spaces. -/
theorem homotopyEquiv_of_homeomorph (h : Nonempty (M ≃ₜ Sphere n)) :
    Nonempty (ContinuousMap.HomotopyEquiv M (Sphere n)) := by
  obtain ⟨e⟩ := h
  exact ⟨e.toHomotopyEquiv⟩

end Topology

end NoExoticSixSphere
