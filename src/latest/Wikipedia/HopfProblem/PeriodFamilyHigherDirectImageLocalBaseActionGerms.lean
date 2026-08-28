import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageLocalBaseActionStalk

/-!
# Common original neighborhood representatives for local scalars and derived classes

Native derived neighborhood germs respect the original presheaf
restrictions. Intersecting representatives therefore puts an arbitrary
holomorphic local-ring germ and an arbitrary original degree-one derived
stalk class on one actual common base neighborhood.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.LocalBaseAction

open PeriodFamilyHolomorphicCohomology

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- Original derived germs retain every original neighborhood restriction, in every degree. -/
theorem neighborhoodGerm_restrict (P : HolomorphicPeriodMap V B) (b : B) (q : ℕ)
    {U W : Opens B} (h : U ≤ W) (hbU : b ∈ U) (hbW : b ∈ W)
    (x : OpenClasses.neighborhoodCohomology P W q) :
    neighborhoodGerm P b q U hbU (neighborhoodRestriction P h q x) =
      neighborhoodGerm P b q W hbW x := by
  have hg := (FibreNeighborhood.sourceCohomologyPresheaf
    (F := Zero.totalAdditiveSheaf P) (Zero.projectionMap P) q).germ_res_apply
      (homOfLE h) b hbU x
  exact congrArg
    (fun y => (SheafHigherDirectImage.stalkCohomologyPresheafIso
      (Zero.projectionMap P) (Zero.totalAdditiveSheaf P) q b).inv y) hg

/-- An arbitrary scalar germ and original derived class admit representatives
on one actual common open; no global extension of either representative is used. -/
theorem exists_common_neighborhood (P : HolomorphicPeriodMap V B) (b : B)
    (a : BaseLocalRing P b) (x : higherDirectImageStalk P b 1) :
    ∃ (U : Opens B) (hb : b ∈ U) (g : Zero.BaseSection P U)
      (y : OpenClasses.neighborhoodCohomology P U 1),
      (baseFunctionPresheaf P).germ U b hb g = a ∧ neighborhoodGerm P b 1 U hb y = x := by
  obtain ⟨U, hbU, g, hg⟩ := (baseFunctionPresheaf P).exists_germ_eq a
  obtain ⟨W, hbW, y, hy⟩ := exists_neighborhoodGerm P b x
  have hb : b ∈ U ⊓ W := ⟨hbU, hbW⟩
  refine ⟨U ⊓ W, hb, Zero.baseRestriction P inf_le_left g,
    neighborhoodRestriction P inf_le_right 1 y, ?_, ?_⟩
  · exact ((baseFunctionPresheaf P).germ_res_apply (homOfLE inf_le_left) b hb g).trans hg
  · exact (neighborhoodGerm_restrict P b 1 inf_le_right hb hbW y).trans hy

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.LocalBaseAction
