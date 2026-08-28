import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeSurjectiveTopClass
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeSurjectiveMaps
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgePeriodThree

/-!
# Surjectivity of the actual marked exterior-product maps

The coordinate-subtorus classes form a proved basis of actual singular
homology. Each class is an additive image of a genuine torus top class,
which is a product of degree-one classes. Consequently a surjective
first-homology marking gives surjective degree-two and degree-three
exterior-product maps. For the actual period tori all hypotheses are
discharged by the proved homeomorphism and first-homology equivalence.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open Elliptic SingularMayerVietoris PeriodTorusHigherHomologyPontryagin

variable {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [Module.IsTorsionFree ℤ (SingularHomology G 2)] {r : ℕ}

/-- Each actual coordinate two-subtorus class lies in the marked wedge range. -/
theorem coordinateTorusClassAlong_mem_range_latticeWedgeTwo
    (e : G ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y)
    (c : Lattice →ₗ[ℤ] SingularHomology G 1) (hc : Function.Surjective c)
    (i : Fin (r.choose 2)) :
    coordinateTorusClassAlong e 2 i ∈ LinearMap.range (latticeWedgeTwo G c) :=
  map_topClass_two_mem_range_latticeWedgeTwo c hc (coordinateTorusMapAlong e 2 i)
    (coordinateTorusMapAlong_add e he 2 i)

/-- Each actual coordinate three-subtorus class lies in the marked wedge range. -/
theorem coordinateTorusClassAlong_mem_range_latticeWedgeThree
    (e : G ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y)
    (c : Lattice →ₗ[ℤ] SingularHomology G 1) (hc : Function.Surjective c)
    (i : Fin (r.choose 3)) :
    coordinateTorusClassAlong e 3 i ∈ LinearMap.range (latticeWedgeThree G c) :=
  map_topClass_three_mem_range_latticeWedgeThree c hc (coordinateTorusMapAlong e 3 i)
    (coordinateTorusMapAlong_add e he 3 i)

/-- Actual exterior-square surjectivity follows from the genuine coordinate-subtorus basis. -/
theorem latticeWedgeTwo_surjective_of_torusHomeomorph
    (e : G ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y)
    (c : Lattice →ₗ[ℤ] SingularHomology G 1) (hc : Function.Surjective c) :
    Function.Surjective (latticeWedgeTwo G c) :=
  surjective_of_coordinateTorusClassAlong_mem_range e 2 (latticeWedgeTwo G c)
    (coordinateTorusClassAlong_mem_range_latticeWedgeTwo e he c hc)

/-- Actual exterior-cube surjectivity follows from the genuine coordinate-subtorus basis. -/
theorem latticeWedgeThree_surjective_of_torusHomeomorph
    (e : G ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y)
    (c : Lattice →ₗ[ℤ] SingularHomology G 1) (hc : Function.Surjective c) :
    Function.Surjective (latticeWedgeThree G c) :=
  surjective_of_coordinateTorusClassAlong_mem_range e 3 (latticeWedgeThree G c)
    (coordinateTorusClassAlong_mem_range_latticeWedgeThree e he c hc)

/-- Every actual coordinate two-subtorus class is in the actual marked wedge image. -/
theorem periodTorusCoordinateClass_mem_range_wedgeTwo (p : PeriodDomain)
    (i : Fin (Nat.choose 4 2)) :
    periodTorusCoordinateClass p 2 i ∈ LinearMap.range (periodTorusWedgeTwo p) := by
  let := periodTorus_homology_torsionFree p 2
  exact coordinateTorusClassAlong_mem_range_latticeWedgeTwo
    (periodTorusCircleHomeomorph p) (periodTorusCircleHomeomorph_add p)
    p.singularH1Equiv.symm.toLinearMap p.singularH1Equiv.symm.surjective i

/-- Every actual coordinate three-subtorus class is in the actual marked wedge image. -/
theorem periodTorusCoordinateClass_mem_range_wedgeThree (p : PeriodDomain)
    (i : Fin (Nat.choose 4 3)) :
    periodTorusCoordinateClass p 3 i ∈ LinearMap.range (periodTorusWedgeThree p) := by
  let := periodTorus_homology_torsionFree p 2
  exact coordinateTorusClassAlong_mem_range_latticeWedgeThree
    (periodTorusCircleHomeomorph p) (periodTorusCircleHomeomorph_add p)
    p.singularH1Equiv.symm.toLinearMap p.singularH1Equiv.symm.surjective i

/-- The actual period-loop exterior-square map is unconditionally surjective. -/
theorem periodTorusWedgeTwo_surjective (p : PeriodDomain) :
    Function.Surjective (periodTorusWedgeTwo p) :=
  surjective_of_periodTorusCoordinateClass_mem_range p 2 (periodTorusWedgeTwo p)
    (periodTorusCoordinateClass_mem_range_wedgeTwo p)

/-- The actual period-loop exterior-cube map is unconditionally surjective. -/
theorem periodTorusWedgeThree_surjective (p : PeriodDomain) :
    Function.Surjective (periodTorusWedgeThree p) :=
  surjective_of_periodTorusCoordinateClass_mem_range p 3 (periodTorusWedgeThree p)
    (periodTorusCoordinateClass_mem_range_wedgeThree p)

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
