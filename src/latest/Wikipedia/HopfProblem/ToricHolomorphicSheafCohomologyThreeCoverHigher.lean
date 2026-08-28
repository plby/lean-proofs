import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyThreeCoverBasic

/-!
# Higher-degree vanishing from three actual opens

Two applications of the genuine Mayer--Vietoris sequence show that a
three-open cover with acyclic nonempty intersections has no cohomology
above degree two. No Čech comparison is assumed.
-/

noncomputable section

open TopologicalSpace CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ThreeCover

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
  (U : Fin 3 → Opens X)

theorem firstUnion_higher_subsingleton (n : ℕ)
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 2) (U 0))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 2) (U 1))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 1) (U 0 ⊓ U 1))] :
    Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 2) (firstUnion U)) :=
  MayerVietoris.union_successor_subsingleton F (U 0) (U 1) (n + 1)

theorem overlapUnion_higher_subsingleton (n : ℕ)
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 2) (U 0 ⊓ U 2))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 2) (U 1 ⊓ U 2))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 1) (tripleOpen U))] :
    Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 2) (overlapUnion U)) := by
  have h : Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 1)
      ((U 0 ⊓ U 2) ⊓ (U 1 ⊓ U 2))) :=
    (pairIntersection_eq U).symm ▸ inferInstance
  exact MayerVietoris.union_successor_subsingleton F (U 0 ⊓ U 2) (U 1 ⊓ U 2) (n + 1)

/-- The relevant actual intersection vanishings force actual degree
`n+3` cohomology on the union to vanish. -/
theorem cover_above_two_subsingleton (n : ℕ)
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 3) (U 0))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 3) (U 1))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 3) (U 2))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 2) (U 0 ⊓ U 1))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 2) (U 0 ⊓ U 2))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 2) (U 1 ⊓ U 2))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 1) (tripleOpen U))] :
    Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 3) (coverOpen U)) := by
  have := firstUnion_higher_subsingleton F U (n + 1)
  have hI := overlapUnion_higher_subsingleton F U n
  have : Subsingleton
      (CategoryTheory.Sheaf.H'.{0} F (n + 2) (firstUnion U ⊓ U 2)) :=
    (firstUnion_inf U).symm ▸ hI
  exact MayerVietoris.union_successor_subsingleton F (firstUnion U) (U 2) (n + 2)

/-- For a genuine three-open cover this is vanishing of the original
global Ext-defined cohomology, using the proved top-open comparison. -/
theorem sheaf_above_two_subsingleton (hcover : coverOpen U = ⊤) (n : ℕ)
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 3) (U 0))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 3) (U 1))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 3) (U 2))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 2) (U 0 ⊓ U 1))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 2) (U 0 ⊓ U 2))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 2) (U 1 ⊓ U 2))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 1) (tripleOpen U))] :
    Subsingleton (CategoryTheory.Sheaf.H.{0} F (n + 3)) :=
  MayerVietoris.sheaf_subsingleton_of_union F (firstUnion U) (U 2) hcover (n + 3)
    (cover_above_two_subsingleton F U n)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ThreeCover
