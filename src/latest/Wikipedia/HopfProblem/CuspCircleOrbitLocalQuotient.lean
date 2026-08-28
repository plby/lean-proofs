import Wikipedia.HopfProblem.CuspCircleOrbitLocalProper
import Wikipedia.HopfProblem.CuspCircleOrbitLocalSurjective
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The actual local unit-circle orbit quotient

The relation below is defined by the original opposite-weight action of
norm-one complex units. Its quotient carries the ordinary quotient
topology. The Hopf invariant induces a homeomorphism from this orbit
space onto `ℂ × ℝ`; properness and surjectivity supply the quotient-map
property, including at the fixed origin.
-/

noncomputable section

open Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit

/-- The actual unit-circle orbit relation, not a relation defined by invariant equality. -/
def normalOrbitSetoid : Setoid (ℂ × ℂ) where
  r z w := ∃ u : ℂˣ, ‖(u : ℂ)‖ = 1 ∧ unitNormalAction u z = w
  iseqv := {
    refl := fun z => (hopfMap_eq_iff z z).mp rfl
    symm := fun h => (hopfMap_eq_iff _ _).mp ((hopfMap_eq_iff _ _).mpr h).symm
    trans := fun h₁ h₂ => (hopfMap_eq_iff _ _).mp
      (((hopfMap_eq_iff _ _).mpr h₁).trans ((hopfMap_eq_iff _ _).mpr h₂)) }

/-- The native topological quotient of the normal coordinates by their actual orbits. -/
abbrev NormalOrbitSpace := Quotient normalOrbitSetoid

/-- The original representative projection to the normal orbit space. -/
def normalOrbitProjection (z : ℂ × ℂ) : NormalOrbitSpace :=
  Quotient.mk normalOrbitSetoid z

theorem normalOrbitProjection_surjective : Function.Surjective normalOrbitProjection :=
  Quotient.mk_surjective

theorem normalOrbitProjection_isQuotientMap : IsQuotientMap normalOrbitProjection :=
  isQuotientMap_quotient_mk'

theorem normalOrbitProjection_continuous : Continuous normalOrbitProjection :=
  normalOrbitProjection_isQuotientMap.continuous

/-- Equality in the native quotient is exactly the original norm-one-unit orbit relation. -/
theorem normalOrbitProjection_eq_iff (z w : ℂ × ℂ) :
    normalOrbitProjection z = normalOrbitProjection w ↔
      ∃ u : ℂˣ, ‖(u : ℂ)‖ = 1 ∧ unitNormalAction u z = w := by
  constructor
  · exact Quotient.exact
  · exact @Quotient.sound _ normalOrbitSetoid z w

/-- The original Hopf invariant is a quotient map onto its ordinary target. -/
theorem hopfMap_isQuotientMap : IsQuotientMap hopfMap :=
  hopfMap_isClosedMap.isQuotientMap hopfMap_continuous hopfMap_surjective

/-- The original invariant descended through the literal orbit relation. -/
def normalOrbitMap : NormalOrbitSpace → ℂ × ℝ :=
  Quotient.lift hopfMap (fun z w h => (hopfMap_eq_iff z w).mpr h)

@[simp] theorem normalOrbitMap_projection (z : ℂ × ℂ) :
    normalOrbitMap (normalOrbitProjection z) = hopfMap z := rfl

theorem normalOrbitMap_continuous : Continuous normalOrbitMap :=
  hopfMap_continuous.quotient_lift _

theorem normalOrbitMap_bijective : Function.Bijective normalOrbitMap := by
  constructor
  · intro x y h
    obtain ⟨z, rfl⟩ := normalOrbitProjection_surjective x
    obtain ⟨w, rfl⟩ := normalOrbitProjection_surjective y
    exact Quotient.sound ((hopfMap_eq_iff z w).mp h)
  · intro y
    obtain ⟨z, hz⟩ := hopfMap_surjective y
    exact ⟨normalOrbitProjection z, hz⟩

/-- The bijection induced by the actual invariant on the actual orbit quotient. -/
def normalOrbitSpaceEquiv : NormalOrbitSpace ≃ ℂ × ℝ :=
  Equiv.ofBijective normalOrbitMap normalOrbitMap_bijective

@[simp] theorem normalOrbitSpaceEquiv_projection (z : ℂ × ℂ) :
    normalOrbitSpaceEquiv (normalOrbitProjection z) = hopfMap z := rfl

/-- The continuous inverse sends an invariant to its genuine unit-circle orbit. -/
theorem normalOrbitSpaceEquiv_symm_continuous : Continuous normalOrbitSpaceEquiv.symm := by
  apply hopfMap_isQuotientMap.continuous_iff.mpr
  have he : normalOrbitSpaceEquiv.symm ∘ hopfMap = normalOrbitProjection := by
    funext z
    change normalOrbitSpaceEquiv.symm
      (normalOrbitSpaceEquiv (normalOrbitProjection z)) = normalOrbitProjection z
    exact normalOrbitSpaceEquiv.symm_apply_apply _
  rw [he]
  exact normalOrbitProjection_continuous

/-- The ordinary local orbit quotient is homeomorphic to `ℂ × ℝ`. -/
def normalOrbitSpaceHomeomorph : NormalOrbitSpace ≃ₜ ℂ × ℝ where
  toEquiv := normalOrbitSpaceEquiv
  continuous_toFun := normalOrbitMap_continuous
  continuous_invFun := normalOrbitSpaceEquiv_symm_continuous

/-- The orbit-space homeomorphism keeps the original invariant formula on representatives. -/
@[simp] theorem normalOrbitSpaceHomeomorph_projection (z : ℂ × ℂ) :
    normalOrbitSpaceHomeomorph (normalOrbitProjection z) = hopfMap z := rfl

@[simp] theorem normalOrbitSpaceHomeomorph_symm_hopfMap (z : ℂ × ℂ) :
    normalOrbitSpaceHomeomorph.symm (hopfMap z) = normalOrbitProjection z :=
  normalOrbitSpaceHomeomorph.symm_apply_apply (normalOrbitProjection z)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit
