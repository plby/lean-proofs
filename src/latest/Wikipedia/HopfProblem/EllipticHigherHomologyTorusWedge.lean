import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeSurjectiveTopClass
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeSurjectiveMaps

/-!
# Exterior-product maps for arbitrary integral first-homology markings

The actual Pontryagin exterior maps can be precomposed with a marking by
any integral module, not only the rank-four period lattice. The proved
coordinate-subtorus basis shows that these maps are surjective for an
additive topological torus whenever the first-homology marking is onto.
These generic helpers are used below with the proved rank-three marking.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomologyPontryagin

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
  PeriodTorusHigherHomology.integerTensorModule

section MarkedMaps

variable (G : Type) [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [Module.IsTorsionFree ℤ (SingularHomology G 2)]
  {M : Type*} [AddCommGroup M] [Module ℤ M]

/-- The exterior square of a genuine first-homology marking, evaluated by
the actual Pontryagin product. -/
def markedWedgeTwo (c : M →ₗ[ℤ] SingularHomology G 1) :
    (⋀[ℤ]^2 M) →ₗ[ℤ] SingularHomology G 2 :=
  (homologyWedgeTwo G).comp (exteriorPower.map 2 c)

/-- The exterior cube of a genuine first-homology marking, evaluated by
the actual ordered triple Pontryagin product. -/
def markedWedgeThree (c : M →ₗ[ℤ] SingularHomology G 1) :
    (⋀[ℤ]^3 M) →ₗ[ℤ] SingularHomology G 3 :=
  (homologyWedgeThree G).comp (exteriorPower.map 3 c)

@[simp] theorem markedWedgeTwo_apply_ιMulti
    (c : M →ₗ[ℤ] SingularHomology G 1) (v : Fin 2 → M) :
    markedWedgeTwo G c (exteriorPower.ιMulti ℤ 2 v) =
      product11 G (c (v 0)) (c (v 1)) := by
  change homologyWedgeTwo G (exteriorPower.map 2 c (exteriorPower.ιMulti ℤ 2 v)) = _
  rw [exteriorPower.map_apply_ιMulti, homologyWedgeTwo_apply_ιMulti]
  rfl

@[simp] theorem markedWedgeThree_apply_ιMulti
    (c : M →ₗ[ℤ] SingularHomology G 1) (v : Fin 3 → M) :
    markedWedgeThree G c (exteriorPower.ιMulti ℤ 3 v) =
      tripleProduct G (c (v 0)) (c (v 1)) (c (v 2)) := by
  change homologyWedgeThree G (exteriorPower.map 3 c (exteriorPower.ιMulti ℤ 3 v)) = _
  rw [exteriorPower.map_apply_ιMulti, homologyWedgeThree_apply_ιMulti]
  rfl

/-- Every degree-one product has a decomposable preimage under an onto marking. -/
theorem product11_mem_range_markedWedgeTwo
    (c : M →ₗ[ℤ] SingularHomology G 1) (hc : Function.Surjective c)
    (a b : SingularHomology G 1) :
    product11 G a b ∈ LinearMap.range (markedWedgeTwo G c) := by
  obtain ⟨v, rfl⟩ := hc a
  obtain ⟨w, rfl⟩ := hc b
  refine ⟨exteriorPower.ιMulti ℤ 2 ![v, w], ?_⟩
  simp

/-- Every triple degree-one product has a decomposable preimage under an onto marking. -/
theorem tripleProduct_mem_range_markedWedgeThree
    (c : M →ₗ[ℤ] SingularHomology G 1) (hc : Function.Surjective c)
    (a b d : SingularHomology G 1) :
    tripleProduct G a b d ∈ LinearMap.range (markedWedgeThree G c) := by
  obtain ⟨v, rfl⟩ := hc a
  obtain ⟨w, rfl⟩ := hc b
  obtain ⟨u, rfl⟩ := hc d
  refine ⟨exteriorPower.ιMulti ℤ 3 ![v, w, u], ?_⟩
  simp

end MarkedMaps

section Naturality

variable {G H : Type}
  [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H]
  [Module.IsTorsionFree ℤ (SingularHomology G 2)]
  [Module.IsTorsionFree ℤ (SingularHomology H 2)]
  {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]

/-- The actual exterior-square product respects additive continuous maps
and any compatible pair of integral markings. -/
theorem markedWedgeTwo_natural (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y)
    (c : M →ₗ[ℤ] SingularHomology G 1) (d : N →ₗ[ℤ] SingularHomology H 1)
    (A : M →ₗ[ℤ] N)
    (hmark : ∀ v, singularHomologyMap f 1 (c v) = d (A v)) :
    (singularHomologyMap f 2).comp (markedWedgeTwo G c) =
      (markedWedgeTwo H d).comp (exteriorPower.map 2 A) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change singularHomologyMap f 2 (markedWedgeTwo G c (exteriorPower.ιMulti ℤ 2 v)) =
    markedWedgeTwo H d (exteriorPower.map 2 A (exteriorPower.ιMulti ℤ 2 v))
  rw [exteriorPower.map_apply_ιMulti, markedWedgeTwo_apply_ιMulti,
    markedWedgeTwo_apply_ιMulti, product_natural f hf 1, hmark, hmark]
  rfl

/-- The actual exterior-cube product respects additive continuous maps
and any compatible pair of integral markings. -/
theorem markedWedgeThree_natural (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y)
    (c : M →ₗ[ℤ] SingularHomology G 1) (d : N →ₗ[ℤ] SingularHomology H 1)
    (A : M →ₗ[ℤ] N)
    (hmark : ∀ v, singularHomologyMap f 1 (c v) = d (A v)) :
    (singularHomologyMap f 3).comp (markedWedgeThree G c) =
      (markedWedgeThree H d).comp (exteriorPower.map 3 A) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change singularHomologyMap f 3 (markedWedgeThree G c (exteriorPower.ιMulti ℤ 3 v)) =
    markedWedgeThree H d (exteriorPower.map 3 A (exteriorPower.ιMulti ℤ 3 v))
  rw [exteriorPower.map_apply_ιMulti, markedWedgeThree_apply_ιMulti,
    markedWedgeThree_apply_ιMulti, tripleProduct_natural f hf, hmark, hmark, hmark]
  rfl

end Naturality

section Surjectivity

variable {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [Module.IsTorsionFree ℤ (SingularHomology G 2)]
  {M : Type*} [AddCommGroup M] [Module ℤ M] {r : ℕ}

/-- The image of the actual two-torus top class has an exterior-square preimage. -/
theorem map_topClass_two_mem_range_markedWedgeTwo
    (c : M →ₗ[ℤ] SingularHomology G 1) (hc : Function.Surjective c)
    (f : C(ProductTorus 2, G)) (hf : ∀ x y, f (x + y) = f x + f y) :
    singularHomologyMap f 2 (productTorusTopClass 2) ∈
      LinearMap.range (markedWedgeTwo G c) := by
  obtain ⟨a, b, hab⟩ := productTorusTopClass_two_is_product
  rw [hab, product_natural f hf 1]
  exact product11_mem_range_markedWedgeTwo G c hc _ _

/-- The image of the actual three-torus top class has an exterior-cube preimage. -/
theorem map_topClass_three_mem_range_markedWedgeThree
    (c : M →ₗ[ℤ] SingularHomology G 1) (hc : Function.Surjective c)
    (f : C(ProductTorus 3, G)) (hf : ∀ x y, f (x + y) = f x + f y) :
    singularHomologyMap f 3 (productTorusTopClass 3) ∈
      LinearMap.range (markedWedgeThree G c) := by
  obtain ⟨a, b, d, habd⟩ := productTorusTopClass_three_is_tripleProduct
  rw [habd, tripleProduct_natural f hf]
  exact tripleProduct_mem_range_markedWedgeThree G c hc _ _ _

/-- Every coordinate two-subtorus class has a marked exterior-square preimage. -/
theorem coordinateTorusClassAlong_mem_range_markedWedgeTwo
    (e : G ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y)
    (c : M →ₗ[ℤ] SingularHomology G 1) (hc : Function.Surjective c)
    (i : Fin (r.choose 2)) :
    coordinateTorusClassAlong e 2 i ∈ LinearMap.range (markedWedgeTwo G c) :=
  map_topClass_two_mem_range_markedWedgeTwo c hc (coordinateTorusMapAlong e 2 i)
    (coordinateTorusMapAlong_add e he 2 i)

/-- Every coordinate three-subtorus class has a marked exterior-cube preimage. -/
theorem coordinateTorusClassAlong_mem_range_markedWedgeThree
    (e : G ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y)
    (c : M →ₗ[ℤ] SingularHomology G 1) (hc : Function.Surjective c)
    (i : Fin (r.choose 3)) :
    coordinateTorusClassAlong e 3 i ∈ LinearMap.range (markedWedgeThree G c) :=
  map_topClass_three_mem_range_markedWedgeThree c hc (coordinateTorusMapAlong e 3 i)
    (coordinateTorusMapAlong_add e he 3 i)

/-- The proved actual coordinate-subtorus basis gives exterior-square surjectivity. -/
theorem markedWedgeTwo_surjective_of_torusHomeomorph
    (e : G ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y)
    (c : M →ₗ[ℤ] SingularHomology G 1) (hc : Function.Surjective c) :
    Function.Surjective (markedWedgeTwo G c) :=
  surjective_of_coordinateTorusClassAlong_mem_range e 2 (markedWedgeTwo G c)
    (coordinateTorusClassAlong_mem_range_markedWedgeTwo e he c hc)

/-- The proved actual coordinate-subtorus basis gives exterior-cube surjectivity. -/
theorem markedWedgeThree_surjective_of_torusHomeomorph
    (e : G ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y)
    (c : M →ₗ[ℤ] SingularHomology G 1) (hc : Function.Surjective c) :
    Function.Surjective (markedWedgeThree G c) :=
  surjective_of_coordinateTorusClassAlong_mem_range e 3 (markedWedgeThree G c)
    (coordinateTorusClassAlong_mem_range_markedWedgeThree e he c hc)

end Surjectivity

end Wikipedia.HopfProblem.Elliptic.HigherHomology
