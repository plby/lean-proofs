import Wikipedia.HopfProblem.DegreeCollapseIntegralRelativeCapConnectingSquare
import Wikipedia.HopfProblem.DegreeCollapseIntegralSupportedCohomologyConnecting

/-!
# Transport of the signed integral cap square along actual subset equalities

Only the two named subsets and the total degree are reindexed. This
lets complement identities express the proved relative cap square
on the original union-support and intersection-support groups.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris NoExoticSixSphere

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralRelativeCapMayerVietoris

open IntegralCap (Coefficient)
open RelativeSingularHomology (overlapIn)

variable {X : Type} [TopologicalSpace X] (U A V B : Set X)

/-- The actual connecting-cap square with equal named subsets and an equal total degree. -/
theorem connecting_cap_congr
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hA : IsOpen A) (hB : IsOpen B) (hUA : U ∪ A = Set.univ) (hVB : V ∪ B = Set.univ)
    (P Q : Set X) (hP : P = A ∩ B) (hQ : Q = A ∪ B) (hPQ : P ⊆ Q)
    {p q n : ℕ} (h : p + q + 1 = n) (a : RelativeIntegralCap.Cohomology P p)
    (F : (RelativeCoefficients.complex Coefficient P).homology n)
    (G : (RelativeCoefficients.complex Coefficient (overlapIn (U ∩ V) Q)).homology n)
    (hFG : homologyLinearMap (RelativeCoefficients.subtypePairMap Coefficient (U ∩ V) Q) n G =
      homologyLinearMap (RelativeCoefficients.subsetMap Coefficient hPQ) n F) :
    connectingHomomorphism U V hU hV hcover q
        (RelativeIntegralCap.capProductInDegree P (p := p) (q := q + 1) (n := n) (by omega) a F) =
      -((-1 : ℤ) ^ p) • RelativeIntegralCap.capProductInDegree (overlapIn (U ∩ V) Q)
        (p := p + 1) (q := q) (n := n) (by omega)
        (RelativeIntegralCap.cohomologyPullback (subtypeInclusion (U ∩ V))
          (show Set.MapsTo (subtypeInclusion (U ∩ V)) (overlapIn (U ∩ V) Q) Q
            from fun _ hx => hx) (p + 1)
          ((IntegralRelativeCohomologyMayerVietoris.setCongr hQ (p + 1)).symm
            (IntegralRelativeCohomologyMayerVietoris.connecting A B hA hB p
              (IntegralRelativeCohomologyMayerVietoris.setCongr hP p a)))) G := by
  subst P
  subst Q
  subst n
  exact connecting_cap U A V B hU hV hcover hA hB hUA hVB p q a F G hFG

end Wikipedia.HopfProblem.DegreeCollapse.IntegralRelativeCapMayerVietoris
