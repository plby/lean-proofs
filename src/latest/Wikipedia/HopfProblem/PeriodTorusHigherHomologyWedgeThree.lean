import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeTwo
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductAssociativityHomology

/-!
# The actual exterior-cube map into singular homology

The proved singular associator and mixed swap boundaries give cyclic symmetry
of the actual triple Pontryagin product. The square-zero identity in degree two
then kills every repeated argument. Thus the actual triple product factors
through the exterior cube, naturally for continuous additive maps.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryagin

open SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
  PeriodTorusHigherHomology.integerTensorModule

variable (G : Type) [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]

/-- Cyclic symmetry follows from the actual singular associator and mixed swap cones. -/
theorem tripleProduct_cyclic (a b c : SingularHomology G 1) :
    tripleProduct G a b c = tripleProduct G b c a := by
  rw [tripleProduct_eq_cross G a b c, tripleProduct_eq_cross G b c a,
    crossProductHomology_cyclic]
  have he : crossProductCyclicMap G G G = cyclicMap G G G := by
    apply ContinuousMap.ext
    intro p
    rfl
  rw [he]
  exact LinearMap.congr_fun (rightAddition_homology_cyclic G 3)
    (crossProductHomology G (G × G) 2 b (crossProductHomology G G 1 c a))

/-- The actual mixed Pontryagin product in bidegree `(2,1)`. -/
def product21 :
    SingularHomology G 2 →ₗ[ℤ] SingularHomology G 1 →ₗ[ℤ] SingularHomology G 3 :=
  integerBilinearPostcompose (crossProductHomologyTwoOne G G)
    (singularHomologyMap (additionMap G) 3)

@[simp] theorem product21_apply (a : SingularHomology G 2) (b : SingularHomology G 1) :
    product21 G a b = singularHomologyMap (additionMap G) 3
      (crossProductHomologyTwoOne G G a b) := rfl

theorem product21_commutes (a : SingularHomology G 2) (b : SingularHomology G 1) :
    product21 G a b = product12 G b a := by
  rw [product21_apply, crossProductHomologyTwoOne_apply]
  exact LinearMap.congr_fun (addition_homology_swap G 3) (crossProductHomology G G 2 b a)

/-- The two actual associations of three degree-one classes give the same product. -/
theorem product11_product21_associative (a b c : SingularHomology G 1) :
    product21 G (product11 G a b) c = product12 G a (product11 G b c) := by
  rw [product21_commutes]
  exact tripleProduct_cyclic G c a b

variable [Module.IsTorsionFree ℤ (SingularHomology G 2)]

theorem tripleProduct_self12 (a b : SingularHomology G 1) :
    tripleProduct G a b b = 0 := by
  rw [tripleProduct_apply, product11_self, map_zero]

theorem tripleProduct_self02 (a b : SingularHomology G 1) :
    tripleProduct G a b a = 0 :=
  (tripleProduct_cyclic G a b a).trans (tripleProduct_self12 G b a)

theorem tripleProduct_self01 (a b : SingularHomology G 1) :
    tripleProduct G a a b = 0 :=
  (tripleProduct_cyclic G a a b).trans (tripleProduct_self02 G a b)

/-- The actual alternating triple operation on first singular homology. -/
def homologyAlternatingThree :
    AlternatingMap ℤ (SingularHomology G 1) (SingularHomology G 3) (Fin 3) :=
  alternatingOfTrilinear (tripleProduct G) (tripleProduct_self01 G)
    (tripleProduct_self02 G) (tripleProduct_self12 G)

@[simp] theorem homologyAlternatingThree_apply (v : Fin 3 → SingularHomology G 1) :
    homologyAlternatingThree G v = tripleProduct G (v 0) (v 1) (v 2) := rfl

/-- The actual triple product factored through the exterior cube. -/
def homologyWedgeThree : (⋀[ℤ]^3 (SingularHomology G 1)) →ₗ[ℤ] SingularHomology G 3 :=
  exteriorPower.alternatingMapLinearEquiv (homologyAlternatingThree G)

@[simp] theorem homologyWedgeThree_apply_ιMulti (v : Fin 3 → SingularHomology G 1) :
    homologyWedgeThree G (exteriorPower.ιMulti ℤ 3 v) =
      tripleProduct G (v 0) (v 1) (v 2) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

/-- The degree-three map for any actual linear lattice marking of first homology. -/
def latticeWedgeThree (c : Lattice →ₗ[ℤ] SingularHomology G 1) :
    (⋀[ℤ]^3 Lattice) →ₗ[ℤ] SingularHomology G 3 :=
  (homologyWedgeThree G).comp (exteriorPower.map 3 c)

@[simp] theorem latticeWedgeThree_apply_ιMulti
    (c : Lattice →ₗ[ℤ] SingularHomology G 1) (v : Fin 3 → Lattice) :
    latticeWedgeThree G c (exteriorPower.ιMulti ℤ 3 v) =
      tripleProduct G (c (v 0)) (c (v 1)) (c (v 2)) := by
  change homologyWedgeThree G (exteriorPower.map 3 c (exteriorPower.ιMulti ℤ 3 v)) = _
  rw [exteriorPower.map_apply_ιMulti, homologyWedgeThree_apply_ιMulti]
  rfl

variable {G} {H : Type} [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H]
  [Module.IsTorsionFree ℤ (SingularHomology H 2)]

theorem homologyWedgeThree_natural (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y) :
    (singularHomologyMap f 3).comp (homologyWedgeThree G) =
      (homologyWedgeThree H).comp (exteriorPower.map 3 (singularHomologyMap f 1)) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change singularHomologyMap f 3 (homologyWedgeThree G (exteriorPower.ιMulti ℤ 3 v)) =
    homologyWedgeThree H (exteriorPower.map 3 (singularHomologyMap f 1)
      (exteriorPower.ιMulti ℤ 3 v))
  rw [exteriorPower.map_apply_ιMulti, homologyWedgeThree_apply_ιMulti,
    homologyWedgeThree_apply_ιMulti]
  exact tripleProduct_natural f hf (v 0) (v 1) (v 2)

theorem latticeWedgeThree_natural (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y)
    (c : Lattice →ₗ[ℤ] SingularHomology G 1)
    (d : Lattice →ₗ[ℤ] SingularHomology H 1) (A : Lattice →ₗ[ℤ] Lattice)
    (hmark : ∀ v, singularHomologyMap f 1 (c v) = d (A v)) :
    (singularHomologyMap f 3).comp (latticeWedgeThree G c) =
      (latticeWedgeThree H d).comp (exteriorPower.map 3 A) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change singularHomologyMap f 3 (latticeWedgeThree G c (exteriorPower.ιMulti ℤ 3 v)) =
    latticeWedgeThree H d (exteriorPower.map 3 A (exteriorPower.ιMulti ℤ 3 v))
  rw [exteriorPower.map_apply_ιMulti, latticeWedgeThree_apply_ιMulti,
    latticeWedgeThree_apply_ιMulti]
  rw [tripleProduct_natural f hf, hmark, hmark, hmark]
  rfl

end Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryagin
