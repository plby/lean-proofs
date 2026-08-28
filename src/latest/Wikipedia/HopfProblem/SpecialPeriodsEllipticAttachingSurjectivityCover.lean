import Wikipedia.HopfProblem.SpecialPeriodsEllipticFillingPieces
import Wikipedia.HopfProblem.EllipticFillingTopologyUniversalCover

/-!
# The actual vector-space cover of the elliptic filling

The genuine period-lattice covering followed by the genuine finite affine
quotient is a covering of the whole filling.  The finite-cover composition
theorem applies because the outer fibres have the proved order three or
four.  Its base coordinate is the literal positive power of the disc
coordinate, independently of the chosen period-vector coordinates.
-/

noncomputable section

open Set Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingSurjectivity

open EllipticFilling

variable (P : HolomorphicPeriodMap ℂ ℍ)
  (h₁ : ∀ z : ℍ, P.point (Triangle.generatorOneSL • z) = (P.point z).step₁)
  (h₂ : ∀ z : ℍ, P.point (Triangle.generatorTwoSL • z) = (P.point z).step₂)
  (j : Elliptic.Kind)

/-- The actual period-lattice map followed by the actual finite quotient. -/
def fullCover : Disc × ComplexPlane₂ → fillingSpace P h₁ h₂ j :=
  fillingQuotient P h₁ h₂ j ∘ (localPeriods P j).quotientMap

@[simp] theorem fullCover_apply (x : Disc × ComplexPlane₂) :
    fullCover P h₁ h₂ j x =
      fillingQuotient P h₁ h₂ j ((localPeriods P j).quotientMap x) := rfl

@[simp] theorem fullCover_projection (x : Disc × ComplexPlane₂) :
    fillingProjection P h₁ h₂ j (fullCover P h₁ h₂ j x) =
      Elliptic.discPower j.order j.order_pos x.1 := rfl

@[simp] theorem fullCover_projection_coe (x : Disc × ComplexPlane₂) :
    (fillingProjection P h₁ h₂ j (fullCover P h₁ h₂ j x) : ℂ) =
      (x.1 : ℂ) ^ j.order := rfl

theorem fillingQuotient_finite_fibre (y : fillingSpace P h₁ h₂ j) :
    Finite (fillingQuotient P h₁ h₂ j ⁻¹' {y}) := by
  apply Nat.finite_of_card_ne_zero
  have hcard := (localData P h₁ h₂ j).quotient_fibre_card
    j.twist (Elliptic.mainTwist_admissible j) y
  change Nat.card (fillingQuotient P h₁ h₂ j ⁻¹' {y}) = j.order at hcard
  rw [hcard]
  exact j.order_pos.ne'

/-- The composition is a genuine covering map, not merely a local chart. -/
theorem fullCover_isCoveringMap : IsCoveringMap (fullCover P h₁ h₂ j) := by
  let := (localPeriods P j).coveringAction
  exact CoveringComposition.covering_comp_of_finite_fibres
    (localPeriods P j).quotientCoveringMap.isCoveringMap
    (fillingQuotient_isCoveringMap P h₁ h₂ j)
    (fillingQuotient_finite_fibre P h₁ h₂ j)

theorem fullCover_surjective : Function.Surjective (fullCover P h₁ h₂ j) :=
  (fillingQuotient_surjective P h₁ h₂ j).comp (localPeriods P j).quotientMap_surjective

theorem fullCover_continuous : Continuous (fullCover P h₁ h₂ j) :=
  (fullCover_isCoveringMap P h₁ h₂ j).continuous

end Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingSurjectivity
