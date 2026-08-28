import Wikipedia.NoExoticSixSphere.ResidualLinkParity
import Wikipedia.NoExoticSixSphere.GenericThreeSixOperators

/-!
# Local parity one for the original generic operator family

The regularity theorem supplies the rank-adapted coordinates and the actual
regular residual. The residual inverse chart defines a genuine local sphere
in the original parameter space. General linear invariance transfers parity
one back to the original operator family, evaluated on that same sphere.
-/

noncomputable section

open Set Function Metric
open scoped ContDiff

namespace NoExoticSixSphere.GenericLocalParity

open GLOrthonormalization CorankOne CorankOneCoordinates CorankOneEuclidean
open OperatorRank Stiefel

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

def inCoordinates (c : RankTwoCoordinates (Vector 3) (Vector 6))
    (D : X → Vector 3 →L[ℝ] Vector 6) : X → BlockMap (Vector 2) (Vector 4) :=
  fun x ↦ operatorEquiv c (D x)

theorem contDiff_inCoordinates (c : RankTwoCoordinates (Vector 3) (Vector 6))
    (D : X → Vector 3 →L[ℝ] Vector 6) (hD : ContDiff ℝ ∞ D) :
    ContDiff ℝ ∞ (inCoordinates c D) := (operatorEquiv c).contDiff.comp hD

def originalLink (c : RankTwoCoordinates (Vector 3) (Vector 6))
    (D : X → Vector 3 →L[ℝ] Vector 6) (d : ResidualCoordinates.Data (inCoordinates c D))
    (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    C(Sphere 3, Monomorphism.Space 6 3) where
  toFun q := ⟨D (d.link ε q),
    (injective_operatorEquiv_iff c (D (d.link ε q))).mp (d.injective_link hε hball q)⟩
  continuous_toFun := (hD.comp (d.continuous_link hε hball)).subtype_mk _

def targetChange (c : RankTwoCoordinates (Vector 3) (Vector 6)) : Vector 6 ≃L[ℝ] Vector 6 :=
  c.2.trans targetSplit.symm

def sourceChange (c : RankTwoCoordinates (Vector 3) (Vector 6)) : Vector 3 ≃L[ℝ] Vector 3 :=
  sourceSplit.trans c.1.symm

theorem changed_originalLink (c : RankTwoCoordinates (Vector 3) (Vector 6))
    (D : X → Vector 3 →L[ℝ] Vector 6) (d : ResidualCoordinates.Data (inCoordinates c D))
    (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    ((Monomorphism.linearHomeomorph (targetChange c) (sourceChange c) : C(_, _)).comp
      (originalLink c D d hD hε hball)) =
      d.linkOperators ((operatorEquiv c).continuous.comp hD) hε hball := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem originalLink_parity (c : RankTwoCoordinates (Vector 3) (Vector 6))
    (D : X → Vector 3 →L[ℝ] Vector 6) (d : ResidualCoordinates.Data (inCoordinates c D))
    (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    Monomorphism.sphereParity 1 (originalLink c D d hD hε hball) = 1 := by
  have he := Monomorphism.sphereParity_linearCoordinates 1 (targetChange c) (sourceChange c)
    (originalLink c D d hD hε hball)
  rw [changed_originalLink c D d hD hε hball] at he
  exact he.symm.trans (d.link_parity ((operatorEquiv c).continuous.comp hD) hε hball)

theorem exists_local_parity [FiniteDimensional ℝ X]
    (D : X → Vector 3 →L[ℝ] Vector 6) (hD : ContDiff ℝ ∞ D) (hreg : RegularThreeSix D)
    (x : X) (hx : ¬ Injective (D x)) :
    ∃ c : RankTwoCoordinates (Vector 3) (Vector 6),
    ∃ d : ResidualCoordinates.Data (inCoordinates c D), x ∈ d.coord.source ∧
    ∃ ε : ℝ, ∃ hε : 0 < ε, ∃ hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target,
      Monomorphism.sphereParity 1 (originalLink c D d hD.continuous hε hball) = 1 := by
  obtain ⟨c, hc, hz, hb⟩ := hreg.residual_regular x hx
  obtain ⟨d, hdx⟩ := ResidualCoordinates.exists_data (inCoordinates c D)
    (contDiff_inCoordinates c D hD) x hc hb
  obtain ⟨ε, hε, hball⟩ := d.exists_radius hdx hz
  exact ⟨c, d, hdx, ε, hε, hball, originalLink_parity c D d hD.continuous hε hball⟩

end NoExoticSixSphere.GenericLocalParity
