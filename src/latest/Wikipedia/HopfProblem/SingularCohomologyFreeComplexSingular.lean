import Wikipedia.HopfProblem.SingularCohomologyFreeComplex
import Wikipedia.HopfProblem.FirstHurewiczChainNaturality

/-!
# The actual integral singular cochain functor

The singular cochain complex is the integral linear dual of Mathlib's
actual singular chain complex.  A continuous map acts by precomposition
with the native singular chain map.  On singular simplices this is literal
composition, and the coboundary is the alternating face formula.

The induced cohomology maps are maps on the actual categorical homology
of these cochain complexes, not maps on a replacement presentation.
-/

noncomputable section

open CategoryTheory Opposite

namespace Wikipedia.HopfProblem.SingularCohomologyFree

open FirstHurewicz

/-- The actual integral singular cochain complex of a topological space. -/
abbrev singularCochainComplex (X : Type) [TopologicalSpace X] :
    CochainComplex (ModuleCat.{0} ℤ) ℕ :=
  dualComplex (FirstHurewicz.singularComplex X)

@[simp] theorem singularCochainComplex_X (X : Type) [TopologicalSpace X] (n : ℕ) :
    (singularCochainComplex X).X n = ModuleCat.of ℤ (Chains X n →ₗ[ℤ] ℤ) := rfl

/-- The actual coboundary is precomposition with the singular boundary. -/
@[simp] theorem singularCochainComplex_d_apply (X : Type) [TopologicalSpace X]
    (i j : ℕ) (φ : Chains X i →ₗ[ℤ] ℤ) :
    ((singularCochainComplex X).d i j).hom φ =
      φ.comp ((FirstHurewicz.singularComplex X).d j i).hom := rfl

theorem singularCochainComplex_d_apply_apply (X : Type) [TopologicalSpace X]
    (i j : ℕ) (φ : Chains X i →ₗ[ℤ] ℤ) (c : Chains X j) :
    ((singularCochainComplex X).d i j).hom φ c =
      φ (((FirstHurewicz.singularComplex X).d j i).hom c) := rfl

/-- The alternating singular-face formula for the literal cochain differential. -/
theorem singularCochainComplex_d_simplex (X : Type) [TopologicalSpace X]
    (n : ℕ) (φ : Chains X n →ₗ[ℤ] ℤ) (σ : SingularSimplex X (n + 1)) :
    ((singularCochainComplex X).d n (n + 1)).hom φ (simplexChain X (n + 1) σ) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val *
        φ (simplexChain X n (σ.comp (simplexFace n i))) := by
  rw [singularCochainComplex_d_apply_apply, FirstHurewicz.boundary_simplex]
  simp only [map_sum, map_zsmul, zsmul_eq_mul, Int.cast_id]

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Pullback by the actual singular chain map induced by a continuous map. -/
def singularPullback (f : C(X, Y)) :
    singularCochainComplex Y ⟶ singularCochainComplex X :=
  dualMap (FirstHurewicz.singularChainMap f)

@[simp] theorem singularPullback_f_apply (f : C(X, Y)) (n : ℕ)
    (φ : Chains Y n →ₗ[ℤ] ℤ) :
    ((singularPullback f).f n).hom φ = φ.comp (FirstHurewicz.inducedChain f n) := rfl

theorem singularPullback_f_apply_apply (f : C(X, Y)) (n : ℕ)
    (φ : Chains Y n →ₗ[ℤ] ℤ) (c : Chains X n) :
    ((singularPullback f).f n).hom φ c = φ (FirstHurewicz.inducedChain f n c) := rfl

/-- Pulling back a cochain evaluates it on the composite singular simplex. -/
@[simp] theorem singularPullback_simplex (f : C(X, Y)) (n : ℕ)
    (φ : Chains Y n →ₗ[ℤ] ℤ) (σ : SingularSimplex X n) :
    ((singularPullback f).f n).hom φ (simplexChain X n σ) =
      φ (simplexChain Y n (f.comp σ)) := by
  rw [singularPullback_f_apply_apply, FirstHurewicz.inducedChain_simplex]

/-- The native singular-chain functor followed contravariantly by the
actual integral cochain-dual functor. -/
def singularCochainFunctor : TopCat.{0}ᵒᵖ ⥤ CochainComplex (ModuleCat.{0} ℤ) ℕ :=
  (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).op) ⋙ dualFunctor

@[simp] theorem singularCochainFunctor_obj (X : Type) [TopologicalSpace X] :
    singularCochainFunctor.obj (op (TopCat.of X)) = singularCochainComplex X := rfl

@[simp] theorem singularCochainFunctor_map (f : C(X, Y)) :
    singularCochainFunctor.map (TopCat.ofHom f).op = singularPullback f := rfl

@[simp] theorem singularPullback_id (X : Type) [TopologicalSpace X] :
    singularPullback (ContinuousMap.id X) = 𝟙 (singularCochainComplex X) :=
  singularCochainFunctor.map_id (op (TopCat.of X))

/-- Pullback reverses the order of composition. -/
@[simp] theorem singularPullback_comp (f : C(X, Y)) (g : C(Y, Z)) :
    singularPullback (g.comp f) = singularPullback g ≫ singularPullback f :=
  singularCochainFunctor.map_comp (TopCat.ofHom g).op (TopCat.ofHom f).op

/-- Integral singular cohomology is the actual homology object of the
constructed singular cochain complex. -/
abbrev SingularCohomology (X : Type) [TopologicalSpace X] (n : ℕ) :=
  (singularCochainComplex X).homology n

/-- The actual induced map on integral singular cohomology. -/
def singularCohomologyPullback (f : C(X, Y)) (n : ℕ) :
    SingularCohomology Y n →ₗ[ℤ] SingularCohomology X n :=
  (HomologicalComplex.homologyMap (singularPullback f) n).hom

@[simp] theorem singularCohomologyPullback_id (X : Type) [TopologicalSpace X] (n : ℕ) :
    singularCohomologyPullback (ContinuousMap.id X) n = LinearMap.id := by
  simp only [singularCohomologyPullback, singularPullback_id,
    HomologicalComplex.homologyMap_id, ModuleCat.hom_id]

@[simp] theorem singularCohomologyPullback_comp (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) :
    singularCohomologyPullback (g.comp f) n =
      (singularCohomologyPullback f n).comp (singularCohomologyPullback g n) := by
  simp only [singularCohomologyPullback, singularPullback_comp,
    HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp]

/-- The contravariant integral singular-cohomology functor in every degree. -/
def singularCohomologyFunctor (n : ℕ) : TopCat.{0}ᵒᵖ ⥤ ModuleCat.{0} ℤ :=
  singularCochainFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) n

@[simp] theorem singularCohomologyFunctor_obj (X : Type) [TopologicalSpace X] (n : ℕ) :
    (singularCohomologyFunctor n).obj (op (TopCat.of X)) = SingularCohomology X n := rfl

@[simp] theorem singularCohomologyFunctor_map (f : C(X, Y)) (n : ℕ) :
    ((singularCohomologyFunctor n).map (TopCat.ofHom f).op).hom =
      singularCohomologyPullback f n := rfl

end Wikipedia.HopfProblem.SingularCohomologyFree
