import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.ContinuousMap.Basic

/-!
# An exact whole-body homeomorphism with a native smooth boundary restriction

The commuting point identity is retained under inverse and composition.
The whole body is only required to be topological; smoothness refers to
the actual native boundary manifolds.
-/

noncomputable section

open ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {G H X X' Y Y' : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H}
  [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace X'] [ChartedSpace H X']
  [TopologicalSpace Y] [TopologicalSpace Y']

structure SmoothBoundaryBodyEquiv (i : C(X, Y)) (i' : C(X', Y')) where
  body : Y ≃ₜ Y'
  boundary : Diffeomorph J J X X' ∞
  boundary_point : ∀ x, body (i x) = i' (boundary x)

namespace SmoothBoundaryBodyEquiv

def refl (i : C(X, Y)) : SmoothBoundaryBodyEquiv (J := J) i i where
  body := Homeomorph.refl Y
  boundary := Diffeomorph.refl J X ∞
  boundary_point _ := rfl

variable {i : C(X, Y)} {i' : C(X', Y')} (e : SmoothBoundaryBodyEquiv (J := J) i i')

def symm : SmoothBoundaryBodyEquiv (J := J) i' i where
  body := e.body.symm
  boundary := e.boundary.symm
  boundary_point y := by
    apply e.body.injective
    have h := e.boundary_point (e.boundary.symm y)
    rw [Diffeomorph.apply_symm_apply] at h
    exact (e.body.apply_symm_apply _).trans h.symm

variable {X'' Y'' : Type*}
  [TopologicalSpace X''] [ChartedSpace H X''] [TopologicalSpace Y'']
  {i'' : C(X'', Y'')} (f : SmoothBoundaryBodyEquiv (J := J) i' i'')

def trans : SmoothBoundaryBodyEquiv (J := J) i i'' where
  body := e.body.trans f.body
  boundary := e.boundary.trans f.boundary
  boundary_point x :=
    (congrArg f.body (e.boundary_point x)).trans (f.boundary_point (e.boundary x))

end SmoothBoundaryBodyEquiv

end Wikipedia.SmoothSixDPoincare
