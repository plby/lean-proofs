import Wikipedia.HopfProblem.PeriodFamily
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Actual local-lift cover for additive period cocycles

The indices are the original upstairs points. Each cover member is the
source of the original quotient-cover local inverse at that point.
Surjectivity proves that these sources cover. On every overlap the two
literal lifts differ locally by one fixed original period-lattice deck
translation, by uniqueness of continuous local lifts.
-/

noncomputable section

open Set Topology TopologicalSpace

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Cocycle

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- The original local quotient-cover inverse, indexed by its actual upstairs point. -/
def lift (P : HolomorphicPeriodMap V B) (i : B × ComplexPlane₂) :
    OpenPartialHomeomorph P.TotalSpace (B × ComplexPlane₂) := by
  letI := P.coveringAction
  exact CoveringQuotient.localInverse P.quotientCoveringMap i

/-- Its actual open source in the unchanged total-space topology. -/
def coverOpen (P : HolomorphicPeriodMap V B) (i : B × ComplexPlane₂) : Opens P.TotalSpace :=
  ⟨(lift P i).source, (lift P i).open_source⟩

/-- The chosen lift is defined at the projection of its actual upstairs index. -/
theorem quotientMap_mem_coverOpen (P : HolomorphicPeriodMap V B) (i : B × ComplexPlane₂) :
    P.quotientMap i ∈ coverOpen P i := by
  let := P.coveringAction
  exact P.quotientCoveringMap.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source

/-- The original quotient surjection makes these literal sources a cover. -/
theorem coverOpen_covers (P : HolomorphicPeriodMap V B) (x : P.TotalSpace) :
    ∃ i : B × ComplexPlane₂, x ∈ coverOpen P i := by
  obtain ⟨i, rfl⟩ := P.quotientMap_surjective x
  exact ⟨i, quotientMap_mem_coverOpen P i⟩

/-- The actual local lift projects to its original total-space point. -/
theorem project_lift (P : HolomorphicPeriodMap V B) (i : B × ComplexPlane₂)
    {x : P.TotalSpace} (hx : x ∈ coverOpen P i) : P.quotientMap (lift P i x) = x := by
  let := P.coveringAction
  exact CoveringQuotient.project_localInverse P.quotientCoveringMap i hx

/-- A local lift retains the literal original base coordinate. -/
theorem lift_base (P : HolomorphicPeriodMap V B) (i : B × ComplexPlane₂)
    {x : P.TotalSpace} (hx : x ∈ coverOpen P i) : (lift P i x).1 = P.projection x :=
  congrArg Prod.fst (project_lift P i hx)

/-- On an actual overlap, the two lifts differ by an original lattice deck transformation. -/
theorem exists_deck (P : HolomorphicPeriodMap V B) (i j : B × ComplexPlane₂)
    {x : P.TotalSpace} (hx : x ∈ coverOpen P i ⊓ coverOpen P j) :
    letI := P.coveringAction
    ∃ g : Multiplicative standardLattice, g • lift P j x = lift P i x := by
  let := P.coveringAction
  exact P.quotientCoveringMap.apply_eq_iff_mem_orbit.mp
    ((project_lift P i hx.1).trans (project_lift P j hx.2).symm)

/-- Uniqueness of local lifts fixes that same actual deck transformation
throughout a neighborhood of the original overlap point. -/
theorem lift_deck_eventuallyEq (P : HolomorphicPeriodMap V B) (i j : B × ComplexPlane₂)
    {x : P.TotalSpace} (hx : x ∈ coverOpen P i ⊓ coverOpen P j) :
    letI := P.coveringAction
    ∃ g : Multiplicative standardLattice,
      (lift P i : P.TotalSpace → B × ComplexPlane₂) =ᶠ[𝓝 x]
        fun y => g • lift P j y := by
  let := P.coveringAction
  obtain ⟨g, hg⟩ := exists_deck P i j hx
  have hU : ∀ᶠ y in 𝓝 x, y ∈ coverOpen P i ⊓ coverOpen P j :=
    (coverOpen P i ⊓ coverOpen P j).isOpen.mem_nhds hx
  refine ⟨g, eventuallyEq_of_localHomeomorph_comp_eq P.quotientMap_localHomeomorph
    ((lift P i).continuousAt hx.1)
    ((P.quotientCoveringMap.continuous_const_smul g).continuousAt.comp
      ((lift P j).continuousAt hx.2)) hg.symm ?_⟩
  filter_upwards [hU] with y hy
  exact (project_lift P i hy.1).trans
    ((P.quotientCoveringMap.map_smul g).trans (project_lift P j hy.2)).symm

/-- The same fixed deck element is a literal vector of the original
integer period lattice, added in the original covering coordinates. -/
theorem lift_period_eventuallyEq (P : HolomorphicPeriodMap V B) (i j : B × ComplexPlane₂)
    {x : P.TotalSpace} (hx : x ∈ coverOpen P i ⊓ coverOpen P j) :
    ∃ g : standardLattice,
      (lift P i : P.TotalSpace → B × ComplexPlane₂) =ᶠ[𝓝 x]
        fun y => ((lift P j y).1,
          (lift P j y).2 + P.periodEquiv (lift P j y).1 (g : RealPlane₄)) := by
  let := P.coveringAction
  obtain ⟨g, hg⟩ := lift_deck_eventuallyEq P i j hx
  exact ⟨g.toAdd, hg⟩

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Cocycle
