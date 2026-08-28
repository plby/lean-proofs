import Wikipedia.NoExoticSixSphere.StabilizedResidualLink
import Wikipedia.NoExoticSixSphere.GenericFourSevenOperators

/-!
# Parity one for the original four-to-seven operator link

The rank-three coordinate change carries the actual operator link to the
proved one-column-stabilized residual link. Both changes are genuine
continuous linear equivalences. Hence the original linking sphere cannot
extend through injective operators and its actual frame parity is one.
-/

noncomputable section

open Set Function Metric
open scoped ContDiff

namespace NoExoticSixSphere.FourSevenLocalParity

open GLOrthonormalization CorankOne CorankOneCoordinates OperatorRank Stiefel DiskBoundary

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

def inCoordinates (c : RankThreeCoordinates (Vector 4) (Vector 7))
    (D : X → Vector 4 →L[ℝ] Vector 7) : X → BlockMap (Vector 3) (Vector 4) :=
  fun x ↦ operatorEquiv c (D x)

theorem contDiff_inCoordinates (c : RankThreeCoordinates (Vector 4) (Vector 7))
    (D : X → Vector 4 →L[ℝ] Vector 7) (hD : ContDiff ℝ ∞ D) :
    ContDiff ℝ ∞ (inCoordinates c D) := (operatorEquiv c).contDiff.comp hD

def originalLink (c : RankThreeCoordinates (Vector 4) (Vector 7))
    (D : X → Vector 4 →L[ℝ] Vector 7) (d : ResidualCoordinates.Data (inCoordinates c D))
    (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    C(Sphere 3, Monomorphism.Space 7 4) where
  toFun q := ⟨D (d.link ε q),
    (injective_operatorEquiv_iff c (D (d.link ε q))).mp
      (StabilizedResidual.injective_link (k := 1) d hε hball q)⟩
  continuous_toFun := (hD.comp (d.continuous_link hε hball)).subtype_mk _

def targetChange (c : RankThreeCoordinates (Vector 4) (Vector 7)) :
    Vector 7 ≃L[ℝ] Vector 7 := c.2.trans (StabilizedResidual.targetSplit 1).symm

def sourceChange (c : RankThreeCoordinates (Vector 4) (Vector 7)) :
    Vector 4 ≃L[ℝ] Vector 4 := (StabilizedResidual.sourceSplit 1).trans c.1.symm

theorem changed_originalLink (c : RankThreeCoordinates (Vector 4) (Vector 7))
    (D : X → Vector 4 →L[ℝ] Vector 7) (d : ResidualCoordinates.Data (inCoordinates c D))
    (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    ((Monomorphism.linearHomeomorph (targetChange c) (sourceChange c) : C(_, _)).comp
      (originalLink c D d hD hε hball)) =
      StabilizedResidual.linkOperators (k := 1) d ((operatorEquiv c).continuous.comp hD)
        hε hball := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem originalLink_not_extends (c : RankThreeCoordinates (Vector 4) (Vector 7))
    (D : X → Vector 4 →L[ℝ] Vector 7) (d : ResidualCoordinates.Data (inCoordinates c D))
    (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    ¬ Extends (originalLink c D d hD hε hball) := by
  rintro ⟨G, hG⟩
  apply StabilizedResidual.linkOperators_not_extends (k := 1) d
    ((operatorEquiv c).continuous.comp hD) hε hball
  rw [← changed_originalLink c D d hD hε hball]
  let H : C(Monomorphism.Space 7 4, Monomorphism.Space 7 4) :=
    Monomorphism.linearHomeomorph (targetChange c) (sourceChange c)
  exact ⟨H.comp G, fun q ↦ congrArg H (hG q)⟩

theorem originalLink_parity (c : RankThreeCoordinates (Vector 4) (Vector 7))
    (D : X → Vector 4 →L[ℝ] Vector 7) (d : ResidualCoordinates.Data (inCoordinates c D))
    (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    Monomorphism.sphereParity 2 (originalLink c D d hD hε hball) = 1 := by
  have hn : Monomorphism.sphereParity 2 (originalLink c D d hD hε hball) ≠ 0 := by
    intro hz
    exact originalLink_not_extends c D d hD hε hball
      ((Monomorphism.sphereParity_zero_iff_extension 2 _).mp hz)
  exact zmodTwo_eq_of_zero_iff _ _ (by simp [hn])

end NoExoticSixSphere.FourSevenLocalParity
