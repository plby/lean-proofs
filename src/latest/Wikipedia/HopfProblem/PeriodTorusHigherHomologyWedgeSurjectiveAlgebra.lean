import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeThree

/-!
# Decomposable Pontryagin classes in the range of the exterior maps

Every product of two or three actual degree-one homology classes is the
image of a decomposable exterior vector. When a lattice marking surjects
onto first homology, the same products are in the range of its marked
exterior maps, by choosing lattice preimages of the factors.

These range statements do not assert that such products generate all of
second or third homology.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryagin

open SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
  PeriodTorusHigherHomology.integerTensorModule

variable (G : Type) [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [Module.IsTorsionFree ℤ (SingularHomology G 2)]

/-- Every actual product of two degree-one classes is in the range of the
actual exterior-square map. -/
theorem product11_mem_range_homologyWedgeTwo (a b : SingularHomology G 1) :
    product11 G a b ∈ LinearMap.range (homologyWedgeTwo G) := by
  refine ⟨exteriorPower.ιMulti ℤ 2 ![a, b], ?_⟩
  simp

/-- Every actual product of three degree-one classes is in the range of the
actual exterior-cube map. -/
theorem tripleProduct_mem_range_homologyWedgeThree (a b d : SingularHomology G 1) :
    tripleProduct G a b d ∈ LinearMap.range (homologyWedgeThree G) := by
  refine ⟨exteriorPower.ιMulti ℤ 3 ![a, b, d], ?_⟩
  simp

/-- A surjective first-homology lattice marking lifts every actual product
of two degree-one classes through its marked exterior-square map. -/
theorem product11_mem_range_latticeWedgeTwo
    (c : Lattice →ₗ[ℤ] SingularHomology G 1) (hc : Function.Surjective c)
    (a b : SingularHomology G 1) :
    product11 G a b ∈ LinearMap.range (latticeWedgeTwo G c) := by
  obtain ⟨v, rfl⟩ := hc a
  obtain ⟨w, rfl⟩ := hc b
  refine ⟨exteriorPower.ιMulti ℤ 2 ![v, w], ?_⟩
  simp

/-- A surjective first-homology lattice marking lifts every actual product
of three degree-one classes through its marked exterior-cube map. -/
theorem tripleProduct_mem_range_latticeWedgeThree
    (c : Lattice →ₗ[ℤ] SingularHomology G 1) (hc : Function.Surjective c)
    (a b d : SingularHomology G 1) :
    tripleProduct G a b d ∈ LinearMap.range (latticeWedgeThree G c) := by
  obtain ⟨v, rfl⟩ := hc a
  obtain ⟨w, rfl⟩ := hc b
  obtain ⟨u, rfl⟩ := hc d
  refine ⟨exteriorPower.ιMulti ℤ 3 ![v, w, u], ?_⟩
  simp

end Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryagin
