import Wikipedia.NoExoticSixSphere.GenericOperatorLocalParity
import Wikipedia.NoExoticSixSphere.ResidualLinkGeometry

/-!
# The actual embedded-ball contribution of a generic singularity

The local contribution uses the original operator family on an embedded ball
in its original parameter space. The ball is centered at the given singularity,
has no other singularities, and its original operator boundary has parity one.
-/

noncomputable section

open Set Function Metric Topology
open scoped ContDiff

namespace NoExoticSixSphere.GenericLocalParity

open GLOrthonormalization CorankOne CorankOneCoordinates OperatorRank Stiefel

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

def HasLocalContribution (D : X → Vector 3 →L[ℝ] Vector 6) (hD : Continuous D)
    (x : X) : Prop :=
  ∃ c : RankTwoCoordinates (Vector 3) (Vector 6),
  ∃ d : ResidualCoordinates.Data (inCoordinates c D), x ∈ d.coord.source ∧
  ∃ ε : ℝ, ∃ hε : 0 < ε, ∃ hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target,
    d.ballMap ε 0 = x ∧
    ContDiffOn ℝ ∞ (d.ballMap ε) (closedBall (0 : Vector 4) 1) ∧
    IsClosedEmbedding (fun z : closedBall (0 : Vector 4) 1 ↦ d.ballMap ε z.val) ∧
    (∀ z ∈ closedBall (0 : Vector 4) 1, ¬ Injective (D (d.ballMap ε z)) ↔ z = 0) ∧
    Monomorphism.sphereParity 1 (originalLink c D d hD hε hball) = 1

theorem hasLocalContribution [FiniteDimensional ℝ X]
    (D : X → Vector 3 →L[ℝ] Vector 6) (hD : ContDiff ℝ ∞ D) (hreg : RegularThreeSix D)
    (x : X) (hx : ¬ Injective (D x)) : HasLocalContribution D hD.continuous x := by
  obtain ⟨c, hc, hz, hb⟩ := hreg.residual_regular x hx
  obtain ⟨d, hdx⟩ := ResidualCoordinates.exists_data (inCoordinates c D)
    (contDiff_inCoordinates c D hD) x hc hb
  obtain ⟨ε, hε, hball⟩ := d.exists_radius hdx hz
  refine ⟨c, d, hdx, ε, hε, hball, d.ballMap_zero ε hdx hz,
    d.contDiffOn_ballMap hε hball, d.ballMap_isClosedEmbedding hε hball, ?_,
    originalLink_parity c D d hD.continuous hε hball⟩
  intro z hz
  exact ((injective_operatorEquiv_iff c (D (d.ballMap ε z))).not).symm.trans
    (d.singular_ballMap_iff hε hball hz)

end NoExoticSixSphere.GenericLocalParity
