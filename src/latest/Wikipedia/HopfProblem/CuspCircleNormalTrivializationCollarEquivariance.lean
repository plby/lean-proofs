import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCollarActual
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationStandardEquivariance

/-!
# The original circle action preserves the actual analytic collar

The group rotates only the standard sphere direction and leaves the signed
radial parameter unchanged. Positive real radial scaling commutes with the
literal two-block real rotation. The resulting collar equivariance is for
the original global threefold action, not an action defined by transport.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Collar

open SpecialPeriods SpecialPeriods.Threefold SpecialPeriods.Threefold.Homology

local notation "Circle" => AddCircle (1 : ℝ)

attribute [local instance] Threefold.chartedSpace

/-- The literal boundary rotation, with the actual collar parameter fixed. -/
def circleAction (θ : Circle) (p : Domain) : Domain :=
  (standardBoundaryCircleAction θ p.1, p.2)

@[simp] theorem circleAction_parameter (θ : Circle) (p : Domain) :
    (circleAction θ p).2 = p.2 := rfl

@[simp] theorem circleAction_zero (p : Domain) : circleAction 0 p = p := by
  change (standardBoundaryCircleAction 0 p.1, p.2) = p
  rw [standardBoundaryCircleAction_zero]

theorem circleAction_add (θ φ : Circle) (p : Domain) :
    circleAction (θ + φ) p = circleAction θ (circleAction φ p) := by
  change (standardBoundaryCircleAction (θ + φ) p.1, p.2) =
    (standardBoundaryCircleAction θ (standardBoundaryCircleAction φ p.1), p.2)
  rw [standardBoundaryCircleAction_add]

/-- The given standard collar carries the actual product additive-circle action. -/
@[instance_reducible] def circleAddAction : AddAction Circle Domain where
  vadd := circleAction
  zero_vadd := circleAction_zero
  add_vadd := circleAction_add

theorem circleAction_continuous :
    Continuous (fun q : Circle × Domain => circleAction q.1 q.2) := by
  have h : Continuous (fun q : Circle × Domain => (q.1, q.2.1)) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  exact (standardBoundaryCircleAction_continuous.comp h).prodMk
    (continuous_snd.comp continuous_snd)

/-- Exact equivariance of the literal standard radial collar coordinates. -/
theorem standardProductMap_circleAction (θ : Circle) (p : Domain) :
    standardProductMap (circleAction θ p) = standardCircleAction θ (standardProductMap p) := by
  apply Prod.ext
  · rw [standardProductMap_fst, standardCircleAction_fst, standardProductMap_fst]
    rfl
  · apply Subtype.ext
    rw [standardProductMap_snd_coe, standardCircleAction_snd_coe, standardProductMap_snd_coe]
    change radialScale p.2 • RealFour.circleRotation θ (p.1.2 : Space) =
      RealFour.circleRotation θ (radialScale p.2 • (p.1.2 : Space))
    exact ((RealFour.circleRotation θ).map_smul (radialScale p.2) (p.1.2 : Space)).symm

/-- The actual global circle action intertwines with the unchanged collar rotation. -/
theorem actualMap_circleAction (θ : Circle) (p : Domain) :
    DeltaSweep.actionMap (θ, actualMap p) = actualMap (circleAction θ p) := by
  change DeltaSweep.actionMap (θ,
      (standardNeighborhoodDiffeomorph (standardProductMap p) : Threefold.Space)) =
    (standardNeighborhoodDiffeomorph (standardProductMap (circleAction θ p)) : Threefold.Space)
  rw [standardNeighborhood_circleAction, standardProductMap_circleAction]

/-- The proved annular open subset is invariant under the original global circle. -/
theorem actionMap_mem_actualCollarNeighborhood (θ : Circle) {x : Threefold.Space}
    (hx : x ∈ actualCollarNeighborhood) :
    DeltaSweep.actionMap (θ, x) ∈ actualCollarNeighborhood := by
  obtain ⟨p, rfl⟩ := hx
  exact ⟨circleAction θ p, (actualMap_circleAction θ p).symm⟩

/-- Restriction of the original global action to the actual collar image. -/
def actualCircleAction (θ : Circle) (x : actualCollarNeighborhood) : actualCollarNeighborhood :=
  ⟨DeltaSweep.actionMap (θ, x), actionMap_mem_actualCollarNeighborhood θ x.property⟩

/-- The genuine native analytic collar diffeomorphism is exactly circle equivariant. -/
theorem actualCollarDiffeomorph_circleAction (θ : Circle) (p : Domain) :
    actualCircleAction θ (actualCollarDiffeomorph p) =
      actualCollarDiffeomorph (circleAction θ p) := by
  apply Subtype.ext
  exact actualMap_circleAction θ p

theorem actualCollarDiffeomorph_inverse_circleAction
    (θ : Circle) (x : actualCollarNeighborhood) :
    actualCollarDiffeomorph.symm (actualCircleAction θ x) =
      circleAction θ (actualCollarDiffeomorph.symm x) := by
  apply actualCollarDiffeomorph.injective
  change actualCollarDiffeomorph
      (actualCollarDiffeomorph.symm (actualCircleAction θ x)) =
    actualCollarDiffeomorph (circleAction θ (actualCollarDiffeomorph.symm x))
  rw [actualCollarDiffeomorph.apply_symm_apply,
    ← actualCollarDiffeomorph_circleAction, actualCollarDiffeomorph.apply_symm_apply]

/-- The signed actual collar parameter is invariant under the original circle action. -/
theorem actualCollarDiffeomorph_inverse_parameter_circleAction
    (θ : Circle) (x : actualCollarNeighborhood) :
    (actualCollarDiffeomorph.symm (actualCircleAction θ x)).2 =
      (actualCollarDiffeomorph.symm x).2 := by
  rw [actualCollarDiffeomorph_inverse_circleAction]
  rfl

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Collar
