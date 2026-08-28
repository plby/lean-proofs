import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocyclePrimitiveBasic

/-!
# Primitive differences for arbitrary continuous local lifts

Two continuous local lifts of the same map through the original varying-period
quotient differ locally by one fixed deck transformation. Consequently their
literal primitive difference is a fixed lattice character of the common base
projection. Neither lift is required to be holomorphic.
-/

noncomputable section

open Topology

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.PrimitiveDifference

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  {M : Type*} [TopologicalSpace M]

/-- Continuous local lifts of a common map differ near the point by a fixed
element of the original deck group. The projection identities are only local. -/
theorem lift_deck_eventuallyEq (P : HolomorphicPeriodMap V B)
    (f : M → P.TotalSpace) (l₀ l₁ : M → B × ComplexPlane₂) {x : M}
    (h₀ : ContinuousAt l₀ x) (h₁ : ContinuousAt l₁ x)
    (hq₀ : (P.quotientMap ∘ l₀) =ᶠ[𝓝 x] f)
    (hq₁ : (P.quotientMap ∘ l₁) =ᶠ[𝓝 x] f) :
    letI := P.coveringAction
    ∃ g : Multiplicative standardLattice,
      l₀ =ᶠ[𝓝 x] fun y => g • l₁ y := by
  let := P.coveringAction
  have hq : P.quotientMap (l₀ x) = P.quotientMap (l₁ x) :=
    hq₀.eq_of_nhds.trans hq₁.eq_of_nhds.symm
  obtain ⟨g, hg⟩ := P.quotientCoveringMap.apply_eq_iff_mem_orbit.mp hq
  refine ⟨g, eventuallyEq_of_localHomeomorph_comp_eq P.quotientMap_localHomeomorph
    h₀ ((P.quotientCoveringMap.continuous_const_smul g).continuousAt.comp h₁)
    hg.symm ?_⟩
  filter_upwards [hq₀, hq₁] with y h₀y h₁y
  exact h₀y.trans ((P.quotientCoveringMap.map_smul g).trans h₁y).symm

/-- The same actual deck comparison written as addition of a fixed marked
lattice vector through the original period isomorphism. -/
theorem lift_period_eventuallyEq (P : HolomorphicPeriodMap V B)
    (f : M → P.TotalSpace) (l₀ l₁ : M → B × ComplexPlane₂) {x : M}
    (h₀ : ContinuousAt l₀ x) (h₁ : ContinuousAt l₁ x)
    (hq₀ : (P.quotientMap ∘ l₀) =ᶠ[𝓝 x] f)
    (hq₁ : (P.quotientMap ∘ l₁) =ᶠ[𝓝 x] f) :
    ∃ g : standardLattice,
      l₀ =ᶠ[𝓝 x] fun y =>
        ((l₁ y).1, (l₁ y).2 + P.periodEquiv (l₁ y).1 (g : RealPlane₄)) := by
  let := P.coveringAction
  obtain ⟨g, hg⟩ := lift_deck_eventuallyEq P f l₀ l₁ h₀ h₁ hq₀ hq₁
  exact ⟨g.toAdd, hg⟩

/-- First primitive minus second primitive is locally the positive character
of one actual marked lattice vector at the common base projection. -/
theorem difference_eventually_character (P : HolomorphicPeriodMap V B)
    (a : Cocycle.Coefficients V B) (f : M → P.TotalSpace)
    (l₀ l₁ : M → B × ComplexPlane₂) {x : M}
    (h₀ : ContinuousAt l₀ x) (h₁ : ContinuousAt l₁ x)
    (hq₀ : (P.quotientMap ∘ l₀) =ᶠ[𝓝 x] f)
    (hq₁ : (P.quotientMap ∘ l₁) =ᶠ[𝓝 x] f) :
    ∃ g : standardLattice,
      (fun y => Cocycle.primitive P a (l₀ y) - Cocycle.primitive P a (l₁ y)) =ᶠ[𝓝 x]
        fun y => Cocycle.character a (P.projection (f y)) g := by
  obtain ⟨g, hg⟩ := lift_period_eventuallyEq P f l₀ l₁ h₀ h₁ hq₀ hq₁
  refine ⟨g, ?_⟩
  filter_upwards [hg, hq₁] with y hgy hqy
  have hb : (l₁ y).1 = P.projection (f y) := congrArg Prod.fst hqy
  rw [hgy, Cocycle.primitive_add_period, add_sub_cancel_left, hb]

end OpenClassRestriction.PrimitiveDifference
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
