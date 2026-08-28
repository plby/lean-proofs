import Wikipedia.HopfProblem.Lattice
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryaginAlgebra
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryaginNaturality
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductSymmetryHomology

/-!
# The actual exterior-square map into singular homology

The signed singular swap boundary proves skew symmetry of the Pontryagin
product. Torsion freeness of the actual degree-two homology group kills its
diagonal. The resulting actual alternating map factors through Mathlib's
exterior square, and is natural for continuous additive maps.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryagin

open SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
  PeriodTorusHigherHomology.integerTensorModule

variable (G : Type) [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]

/-- Skew symmetry is proved from the actual singular swap boundary. -/
theorem product11_skew (a b : SingularHomology G 1) :
    product11 G a b = -product11 G b a :=
  crossProductHomology_pushforward_anticommute (additionMap G)
    (by ext p; exact add_comm p.2 p.1) a b

variable [Module.IsTorsionFree ℤ (SingularHomology G 2)]

theorem product11_self (a : SingularHomology G 1) : product11 G a a = 0 :=
  skewBilinear_diagonal_zero (product11 G) (product11_skew G) a

/-- The alternating operation on the actual first singular homology group. -/
def homologyAlternatingTwo :
    AlternatingMap ℤ (SingularHomology G 1) (SingularHomology G 2) (Fin 2) :=
  alternatingOfBilinear (product11 G) (product11_self G)

@[simp] theorem homologyAlternatingTwo_apply (v : Fin 2 → SingularHomology G 1) :
    homologyAlternatingTwo G v = product11 G (v 0) (v 1) := rfl

/-- The actual Pontryagin product factored through the exterior square. -/
def homologyWedgeTwo : (⋀[ℤ]^2 (SingularHomology G 1)) →ₗ[ℤ] SingularHomology G 2 :=
  exteriorPower.alternatingMapLinearEquiv (homologyAlternatingTwo G)

@[simp] theorem homologyWedgeTwo_apply_ιMulti (v : Fin 2 → SingularHomology G 1) :
    homologyWedgeTwo G (exteriorPower.ιMulti ℤ 2 v) = product11 G (v 0) (v 1) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

/-- Any genuine linear lattice marking of first homology gives the marked exterior-square map. -/
def latticeWedgeTwo (c : Lattice →ₗ[ℤ] SingularHomology G 1) :
    (⋀[ℤ]^2 Lattice) →ₗ[ℤ] SingularHomology G 2 :=
  (homologyWedgeTwo G).comp (exteriorPower.map 2 c)

@[simp] theorem latticeWedgeTwo_apply_ιMulti
    (c : Lattice →ₗ[ℤ] SingularHomology G 1) (v : Fin 2 → Lattice) :
    latticeWedgeTwo G c (exteriorPower.ιMulti ℤ 2 v) = product11 G (c (v 0)) (c (v 1)) := by
  change homologyWedgeTwo G (exteriorPower.map 2 c (exteriorPower.ιMulti ℤ 2 v)) = _
  rw [exteriorPower.map_apply_ιMulti, homologyWedgeTwo_apply_ιMulti]
  rfl

variable {G} {H : Type} [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H]
  [Module.IsTorsionFree ℤ (SingularHomology H 2)]

/-- Naturality uses the actual induced singular-homology maps. -/
theorem homologyWedgeTwo_natural (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y) :
    (singularHomologyMap f 2).comp (homologyWedgeTwo G) =
      (homologyWedgeTwo H).comp (exteriorPower.map 2 (singularHomologyMap f 1)) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change singularHomologyMap f 2 (homologyWedgeTwo G (exteriorPower.ιMulti ℤ 2 v)) =
    homologyWedgeTwo H (exteriorPower.map 2 (singularHomologyMap f 1)
      (exteriorPower.ιMulti ℤ 2 v))
  rw [exteriorPower.map_apply_ιMulti, homologyWedgeTwo_apply_ιMulti,
    homologyWedgeTwo_apply_ιMulti]
  exact product_natural f hf 1 (v 0) (v 1)

/-- Marked naturality for an arbitrary proved degree-one lattice transformation. -/
theorem latticeWedgeTwo_natural (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y)
    (c : Lattice →ₗ[ℤ] SingularHomology G 1)
    (d : Lattice →ₗ[ℤ] SingularHomology H 1) (A : Lattice →ₗ[ℤ] Lattice)
    (hmark : ∀ v, singularHomologyMap f 1 (c v) = d (A v)) :
    (singularHomologyMap f 2).comp (latticeWedgeTwo G c) =
      (latticeWedgeTwo H d).comp (exteriorPower.map 2 A) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change singularHomologyMap f 2 (latticeWedgeTwo G c (exteriorPower.ιMulti ℤ 2 v)) =
    latticeWedgeTwo H d (exteriorPower.map 2 A (exteriorPower.ιMulti ℤ 2 v))
  rw [exteriorPower.map_apply_ιMulti, latticeWedgeTwo_apply_ιMulti,
    latticeWedgeTwo_apply_ιMulti]
  rw [product_natural f hf 1, hmark, hmark]
  rfl

end Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryagin
