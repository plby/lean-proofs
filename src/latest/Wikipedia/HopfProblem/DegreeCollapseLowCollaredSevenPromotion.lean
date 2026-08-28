import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenBothHalves
import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenRecognition
import Wikipedia.HopfProblem.SphereHomologySimplyConnectedCover

/-!

# Cleared actual halves construct the existing smooth-recognition input

The genuine collar open cover proves ambient simple connectivity from the
two halves. Its actual Mayer--Vietoris sum proves ambient H2 vanishing from
the two cleared groups. These are constructed properties, not added fields
on the earlier low-surgery state. Promotion keeps every original geometric
field and identifies the two native zero atlases by the actual identity.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState

open NoExoticSixSphere GLOrthonormalization SingularMayerVietoris FundamentalGroupVanKampen

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)

theorem ambient_simplyConnected_of_halves [SimplyConnectedSpace B]
    [SimplyConnectedSpace S.PositiveHalf] [SimplyConnectedSpace S.NegativeHalf] :
    SimplyConnectedSpace S.Space := by
  let : SimplyConnectedSpace S.collar.positiveOpen :=
    S.collar.positiveHalfHomotopyEquiv.simplyConnectedSpace
  let : SimplyConnectedSpace S.collar.reverse.positiveOpen :=
    S.collar.reverse.positiveHalfHomotopyEquiv.simplyConnectedSpace
  let : SimplyConnectedSpace S.collar.overlap :=
    S.collar.overlapHomotopyEquiv.simplyConnectedSpace
  let o : S.collar.overlap := Classical.choice inferInstance
  let D : TwoOpenCover S.Space := {
    U := S.collar.positiveOpen
    V := S.collar.reverse.positiveOpen
    cover := S.collar.open_halves_cover
    pathConnectedU := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
    pathConnectedV := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
    pathConnectedIntersection := isPathConnected_iff_pathConnectedSpace.mpr
      (inferInstanceAs (PathConnectedSpace S.collar.overlap))
    base := o.val
    baseU := o.property.1
    baseV := o.property.2 }
  let : SimplyConnectedSpace D.U :=
    inferInstanceAs (SimplyConnectedSpace S.collar.positiveOpen)
  let : SimplyConnectedSpace D.V :=
    inferInstanceAs (SimplyConnectedSpace S.collar.reverse.positiveOpen)
  exact SphereHomology.twoOpenCover_simplyConnectedSpace D

theorem ambient_h2_zero_of_halves
    [Subsingleton (SingularHomology B 1)] [Subsingleton (SingularHomology B 2)]
    [Subsingleton (SingularHomology S.PositiveHalf 2)]
    [Subsingleton (SingularHomology S.NegativeHalf 2)] :
    Subsingleton (SingularHomology S.Space 2) :=
  (S.collar.halvesHomologySum_bijective 1).2.subsingleton

variable [SimplyConnectedSpace B]
  [Subsingleton (SingularHomology B 1)] [Subsingleton (SingularHomology B 2)]
  [SimplyConnectedSpace S.PositiveHalf] [SimplyConnectedSpace S.NegativeHalf]
  [Subsingleton (SingularHomology S.PositiveHalf 2)]
  [Subsingleton (SingularHomology S.NegativeHalf 2)]

def toCollaredSevenState : CollaredSevenState B := by
  let := S.ambient_simplyConnected_of_halves
  let := S.ambient_h2_zero_of_halves
  exact CollaredSevenState.ofCollar S.embedding S.normalFrame S.time S.time_smooth
    S.time_regular S.collar

def promotionZeroDiffeomorph :
    letI := S.zeroAtlas
    letI := S.toCollaredSevenState.zeroAtlas
    S.Zero ≃ₘ⟮𝓡 6, 𝓡 6⟯ S.toCollaredSevenState.Zero := by
  let := S.zeroAtlas
  let := S.toCollaredSevenState.zeroAtlas
  exact Diffeomorph.refl (𝓡 6) S.Zero ∞

theorem promotionZeroDiffeomorph_point (p : S.Zero) :
    letI := S.zeroAtlas
    letI := S.toCollaredSevenState.zeroAtlas
    (S.promotionZeroDiffeomorph p).val = p.val := rfl

end Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState
