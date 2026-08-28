import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCocycleBasic
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCocycleFaces
import Wikipedia.HopfProblem.SingularCohomologyFreeComplexSingular

/-!
# Actual singular cochains from group cocycles and edge labels

On each genuine singular triangle the cochain has value
`k(label 01, label 12)`. Its outgoing differential vanishes by the
actual tetrahedron face identities and the inhomogeneous group cocycle
law. Group coboundaries become literal singular coboundaries with the
orientation `12 - 02 + 01`.

These constructions do not identify the resulting class with a Chern
class or invoke a comparison with another cohomology theory.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernCocycle

open FirstHurewicz SingularCohomologyFree

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable {A B : Type*} [AddGroup A] [AddGroup B]

/-- A literal integral linear functional on the actual singular two-chains. -/
def twoCochain (ℓ : EdgeCocycle X A) (k : IntegralTwoCocycle A) :
    Chains X 2 →ₗ[ℤ] ℤ :=
  chainLift X 2 (fun σ => k (ℓ (σ.comp (simplexFace 1 2)))
    (ℓ (σ.comp (simplexFace 1 0))))

@[simp] theorem twoCochain_simplex (ℓ : EdgeCocycle X A) (k : IntegralTwoCocycle A)
    (σ : SingularSimplex X 2) :
    twoCochain ℓ k (simplexChain X 2 σ) =
      k (ℓ (σ.comp (simplexFace 1 2))) (ℓ (σ.comp (simplexFace 1 0))) :=
  chainLift_simplex X 2 _ σ

/-- The native singular coboundary vanishes, proved on the actual tetrahedron generators. -/
theorem twoCochain_closed (ℓ : EdgeCocycle X A) (k : IntegralTwoCocycle A) :
    ((singularCochainComplex X).d 2 3).hom (twoCochain ℓ k) = 0 := by
  apply chainMap_ext X 3
  intro σ
  rw [singularCochainComplex_d_simplex X 2]
  change (∑ i : Fin 4, (-1 : ℤ) ^ i.val *
    twoCochain ℓ k (simplexChain X 2 (σ.comp (simplexFace 2 i)))) = 0
  rw [Fin.sum_univ_four]
  simp only [twoCochain_simplex]
  change (1 : ℤ) * _ + (-1) * _ + 1 * _ + (-1) * _ = 0
  rw [tetrahedron_edge12 σ, tetrahedron_edge02 σ, ← tetrahedron_edge23 σ,
    tetrahedron_edge01 σ, tetrahedron_edge13 σ]
  rw [ℓ.triangle (σ.comp (simplexFace 2 3)), ℓ.triangle (σ.comp (simplexFace 2 0)),
    tetrahedron_edge12 σ]
  have hk := k.cocycle
    (ℓ ((σ.comp (simplexFace 2 3)).comp (simplexFace 1 2)))
    (ℓ ((σ.comp (simplexFace 2 3)).comp (simplexFace 1 0)))
    (ℓ ((σ.comp (simplexFace 2 0)).comp (simplexFace 1 0)))
  omega

@[simp] theorem twoCochain_zero (ℓ : EdgeCocycle X A) : twoCochain ℓ 0 = 0 := by
  apply chainMap_ext X 2
  intro σ
  simp only [twoCochain_simplex, IntegralTwoCocycle.zero_apply, LinearMap.zero_apply]

@[simp] theorem twoCochain_add (ℓ : EdgeCocycle X A) (k l : IntegralTwoCocycle A) :
    twoCochain ℓ (k + l) = twoCochain ℓ k + twoCochain ℓ l := by
  apply chainMap_ext X 2
  intro σ
  simp only [twoCochain_simplex, IntegralTwoCocycle.add_apply, LinearMap.add_apply]

@[simp] theorem twoCochain_neg (ℓ : EdgeCocycle X A) (k : IntegralTwoCocycle A) :
    twoCochain ℓ (-k) = -twoCochain ℓ k := by
  apply chainMap_ext X 2
  intro σ
  simp only [twoCochain_simplex, IntegralTwoCocycle.neg_apply, LinearMap.neg_apply]

/-- Actual singular pullback agrees with pullback of the genuine edge labels. -/
theorem twoCochain_pullback (ℓ : EdgeCocycle Y A) (k : IntegralTwoCocycle A)
    (f : C(X, Y)) :
    ((singularPullback f).f 2).hom (twoCochain ℓ k) = twoCochain (ℓ.pullback f) k := by
  apply chainMap_ext X 2
  intro σ
  rw [singularPullback_simplex f 2 (twoCochain ℓ k) σ]
  simp only [twoCochain_simplex, EdgeCocycle.pullback_apply, ContinuousMap.comp_assoc]

/-- Additive changes of the actual edge labels agree with pullback of the group cocycle. -/
theorem twoCochain_comap (ℓ : EdgeCocycle X A) (k : IntegralTwoCocycle B)
    (f : A →+ B) : twoCochain ℓ (k.comap f) = twoCochain (ℓ.map f) k := by
  apply chainMap_ext X 2
  intro σ
  simp only [twoCochain_simplex, IntegralTwoCocycle.comap_apply, EdgeCocycle.map_apply]

/-- A function on edge labels gives a literal integral singular one-cochain. -/
def oneCochain (ℓ : EdgeCocycle X A) (b : A → ℤ) : Chains X 1 →ₗ[ℤ] ℤ :=
  chainLift X 1 (fun σ => b (ℓ σ))

@[simp] theorem oneCochain_simplex (ℓ : EdgeCocycle X A) (b : A → ℤ)
    (σ : SingularSimplex X 1) :
    oneCochain ℓ b (simplexChain X 1 σ) = b (ℓ σ) :=
  chainLift_simplex X 1 _ σ

/-- Standard group coboundaries become actual incoming singular coboundaries. -/
theorem twoCochain_coboundary (ℓ : EdgeCocycle X A) (b : A → ℤ) :
    twoCochain ℓ (IntegralTwoCocycle.coboundary b) =
      ((singularCochainComplex X).d 1 2).hom (oneCochain ℓ b) := by
  apply chainMap_ext X 2
  intro σ
  rw [twoCochain_simplex, IntegralTwoCocycle.coboundary_apply,
    singularCochainComplex_d_apply_apply]
  change _ = oneCochain ℓ b (boundaryTwo X (simplexChain X 2 σ))
  rw [boundaryTwo_simplex, map_add, map_sub]
  simp only [oneCochain_simplex]
  rw [ℓ.triangle σ]
  ring

end Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernCocycle
