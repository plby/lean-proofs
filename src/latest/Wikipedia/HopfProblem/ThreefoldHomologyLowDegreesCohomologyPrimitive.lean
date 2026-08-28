import Wikipedia.HopfProblem.ThreefoldHomologyLowDegreesCohomologyPath
import Wikipedia.HopfProblem.SingularCohomologyFreeComplexSingular
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluation
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Actual degree-one singular cocycles have path primitives

A closed integral one-cochain on a simply connected space has a literal
zero-cochain primitive: evaluate it on a chosen path from a basepoint to
each point.  Path-homotopy invariance and concatenation show that its
coboundary is the original cochain on every singular edge.  This uses
neither freeness nor projectivity of any singular homology group.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThreefoldCohomologyPath

open FirstHurewicz SingularCohomologyFree

variable {X : Type} [TopologicalSpace X] {b : X}

/-- A literal zero-cochain obtained by integrating along chosen paths
from one basepoint. -/
def pathPrimitive (r : ∀ x : X, Path b x) (φ : Chains X 1 →ₗ[ℤ] ℤ) :
    Chains X 0 →ₗ[ℤ] ℤ :=
  chainLift X 0 (fun σ =>
    φ (pathChain (r (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 1))))))

@[simp] theorem pathPrimitive_simplex (r : ∀ x : X, Path b x)
    (φ : Chains X 1 →ₗ[ℤ] ℤ) (σ : SingularSimplex X 0) :
    pathPrimitive r φ (simplexChain X 0 σ) =
      φ (pathChain (r (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 1))))) :=
  chainLift_simplex X 0 _ σ

/-- On the boundary of an actual edge, the primitive gives the difference
of its endpoint path values. -/
theorem pathPrimitive_boundaryOne_simplex (r : ∀ x : X, Path b x)
    (φ : Chains X 1 →ₗ[ℤ] ℤ) (σ : SingularSimplex X 1) :
    pathPrimitive r φ (boundaryOne X (simplexChain X 1 σ)) =
      φ (pathChain (r (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 2))))) -
        φ (pathChain (r (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 2))))) := by
  have h₀ : σ.comp (simplexFace 0 0) = ContinuousMap.const (Simplex 0)
      (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 2))) := by
    apply ContinuousMap.ext
    intro s
    exact congrArg σ (simplexFace_zero_zero s)
  have h₁ : σ.comp (simplexFace 0 1) = ContinuousMap.const (Simplex 0)
      (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 2))) := by
    apply ContinuousMap.ext
    intro s
    exact congrArg σ (simplexFace_zero_one s)
  rw [boundaryOne_simplex, map_sub, h₀, h₁,
    pathPrimitive_simplex, pathPrimitive_simplex]
  rfl

/-- Simple connectedness makes the path primitive a genuine primitive of
every closed integral one-cochain. -/
theorem pathPrimitive_comp_boundaryOne [SimplyConnectedSpace X]
    (r : ∀ x : X, Path b x) (φ : Chains X 1 →ₗ[ℤ] ℤ)
    (hφ : IsClosedFunctional (singularComplex X) 1 φ) :
    (pathPrimitive r φ).comp (boundaryOne X) = φ := by
  apply chainMap_ext X 1
  intro σ
  have hp := closed_path_homotopic φ hφ
    (SimplyConnectedSpace.paths_homotopic
      ((r (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 2)))).trans (simplexPath σ))
      (r (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 2)))))
  rw [closed_path_trans φ hφ] at hp
  have he : pathChain (simplexPath σ) = simplexChain X 1 σ := by
    rw [pathChain, pathSimplex_simplexPath]
  rw [he] at hp
  change pathPrimitive r φ (boundaryOne X (simplexChain X 1 σ)) = _
  rw [pathPrimitive_boundaryOne_simplex]
  linarith

/-- Existence of a literal zero-cochain whose coboundary is the given
closed one-cochain, without hypotheses on any higher homology. -/
theorem closed_is_coboundary [SimplyConnectedSpace X]
    (φ : Chains X 1 →ₗ[ℤ] ℤ)
    (hφ : IsClosedFunctional (singularComplex X) 1 φ) :
    ∃ ψ : Chains X 0 →ₗ[ℤ] ℤ, ψ.comp (boundaryOne X) = φ := by
  let b : X := Classical.choice (inferInstance : Nonempty X)
  exact ⟨pathPrimitive (PathConnectedSpace.somePath b) φ,
    pathPrimitive_comp_boundaryOne (PathConnectedSpace.somePath b) φ hφ⟩

/-- The actual integral first singular cohomology of a simply connected
space is zero. -/
theorem singularH1Cohomology_eq_zero_of_simplyConnected (X : Type)
    [TopologicalSpace X] [SimplyConnectedSpace X] (a : SingularCohomology X 1) :
    a = 0 := by
  obtain ⟨c, rfl⟩ := cocycleClass_surjective (singularCochainComplex X) 1 a
  apply (cocycleClass_eq_zero_iff (singularCochainComplex X) 1 c).mpr
  obtain ⟨ψ, hψ⟩ := closed_is_coboundary c.val
    (cocycle_isClosedFunctional (singularComplex X) 1 c)
  exact ⟨ψ, hψ⟩

theorem singularH1Cohomology_subsingleton_of_simplyConnected (X : Type)
    [TopologicalSpace X] [SimplyConnectedSpace X] :
    Subsingleton (SingularCohomology X 1) :=
  ⟨fun a c => (singularH1Cohomology_eq_zero_of_simplyConnected X a).trans
    (singularH1Cohomology_eq_zero_of_simplyConnected X c).symm⟩

end Wikipedia.HopfProblem.ThreefoldCohomologyPath
