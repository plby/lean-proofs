import Wikipedia.NoExoticSixSphere.JamesSphereQuotientBottomSphere
import Wikipedia.NoExoticSixSphere.JamesSphereSuspensionComparison

/-!
# The native Hopf map through the genuine full James quotient

The original Hopf homomorphism factors through the actual quotient map.
On the embedded bottom sphere, the factor is exactly the existing cubical
suspension. These native identities preserve the real basepoints and
coordinate reorderings. The required metastable comparison of the bottom
sphere with the whole quotient remains a separate proof obligation.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.JamesSphere.FirstStageQuotient

theorem native_hopf_quotientMap (n d : ℕ) [NeZero d]
    (c : π_ d (WordHomology.Words n) 1) :
    HigherHomotopy.map (N := Fin d) (hopfMap n) (hopfMap_basepoint n)
      (HigherHomotopy.map (N := Fin d) (quotientMap n) rfl c) =
    HigherHomotopy.map (N := Fin d) (hopf n) (hopf_one n) c := by
  refine Quotient.inductionOn c fun p ↦ ?_
  apply congrArg (fun q : GenLoop (Fin d) (WordHomology.Words (n + n)) 1 ↦
    (Quotient.mk' q : π_ d (WordHomology.Words (n + n)) 1))
  apply Subtype.ext
  apply ContinuousMap.ext
  intro u
  exact hopfMap_quotientMap n (p u)

theorem native_hopf_bottomSphere (n d : ℕ) [NeZero d]
    (c : π_ d (Sphere (n + n)) (spherePole (n + n))) :
    HigherHomotopy.map (N := Fin d) (hopfMap n) (hopfMap_basepoint n)
      (HigherHomotopy.map (N := Fin d) (bottomSphere n) (bottomSphere_pole n) c) =
    HigherHomotopy.map (N := Fin d) (inclusion (n + n)) (NativeHopf.inclusion_pole (n + n))
      c := by
  refine Quotient.inductionOn c fun p ↦ ?_
  apply congrArg (fun q : GenLoop (Fin d) (WordHomology.Words (n + n)) 1 ↦
    (Quotient.mk' q : π_ d (WordHomology.Words (n + n)) 1))
  apply Subtype.ext
  apply ContinuousMap.ext
  intro u
  exact hopfMap_bottomSphere n (p u)

def sphereHopfHom (n : ℕ) (hn : 2 ≤ n) (d : ℕ) [NeZero d] :
    π_ d (Space n) (basepoint n) →*
      π_ (d + 1) (Sphere (n + n + 1)) (spherePole (n + n + 1)) :=
  (SuspensionComparison.coordinateEquiv (n + n) (d + 1)).toMonoidHom.comp
    ((NativeHopf.spherePiEquiv (n + n) (by omega) d).toMonoidHom.comp
      (HigherHomotopy.mapMonoidHom (N := Fin d) (hopfMap n) (hopfMap_basepoint n)))

theorem sphereHopfHom_quotientMap (n : ℕ) (hn : 2 ≤ n) (d : ℕ) [NeZero d]
    (c : π_ d (WordHomology.Words n) 1) :
    sphereHopfHom n hn d (HigherHomotopy.map (N := Fin d) (quotientMap n) rfl c) =
      SuspensionComparison.orderedHopfHom n hn d
        (SuspensionComparison.coordinateEquiv n (d + 1) (NativeHopf.spherePiEquiv n hn d c)) := by
  change SuspensionComparison.coordinateEquiv (n + n) (d + 1)
    (NativeHopf.spherePiEquiv (n + n) (by omega) d
      (HigherHomotopy.map (N := Fin d) (hopfMap n) (hopfMap_basepoint n)
        (HigherHomotopy.map (N := Fin d) (quotientMap n) rfl c))) =
    SuspensionComparison.coordinateEquiv (n + n) (d + 1)
      (NativeHopf.hopfHom n hn d ((SuspensionComparison.coordinateEquiv n (d + 1)).symm
        (SuspensionComparison.coordinateEquiv n (d + 1) (NativeHopf.spherePiEquiv n hn d c))))
  rw [native_hopf_quotientMap, MulEquiv.symm_apply_apply, NativeHopf.hopfHom_comparison]

theorem sphereHopfHom_bottomSphere (n : ℕ) (hn : 2 ≤ n) (d : ℕ) [NeZero d]
    (c : π_ d (Sphere (n + n)) (spherePole (n + n))) :
    sphereHopfHom n hn d
      (HigherHomotopy.map (N := Fin d) (bottomSphere n) (bottomSphere_pole n) c) =
    CubicalSphereSuspension.hom d (n + n) c := by
  change SuspensionComparison.coordinateEquiv (n + n) (d + 1)
    (NativeHopf.spherePiEquiv (n + n) (by omega) d
      (HigherHomotopy.map (N := Fin d) (hopfMap n) (hopfMap_basepoint n)
        (HigherHomotopy.map (N := Fin d) (bottomSphere n) (bottomSphere_pole n) c))) = _
  rw [native_hopf_bottomSphere]
  exact SuspensionComparison.coordinateEquiv_letterHom (n + n) (by omega) d c

end NoExoticSixSphere.JamesSphere.FirstStageQuotient
