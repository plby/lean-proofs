import Wikipedia.NoExoticSixSphere.JamesSphereBottomHomotopy
import Wikipedia.NoExoticSixSphere.JamesSphereQuotientNativeHopf
import Wikipedia.NoExoticSixSphere.CubicalSuspensionRange

/-!
# The actual quotient Hopf factor is an isomorphism in the metastable range

The original bottom-sphere map is an isomorphism through degree `3 * n - 2`.
Its composite with the actual quotient Hopf factor is the checked cubical
suspension, which is an isomorphism in this range. Thus the quotient factor
itself is an isomorphism. This is not a claim that the full Hopf map is an
isomorphism, or that the relative-fiber to quotient comparison is proved.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.JamesSphere.FirstStageQuotient

theorem sphereHopfHom_bijective_range (n d : ℕ) [NeZero d] (hn : 2 ≤ n)
    (hdn : d + 2 ≤ 3 * n) : Function.Bijective (sphereHopfHom n hn d) := by
  let E := bottomSpherePiEquiv n d hn hdn
  have hc : (sphereHopfHom n hn d : _ → _) ∘ E =
      CubicalSphereSuspension.hom d (n + n) := by
    funext c
    exact sphereHopfHom_bottomSphere n hn d c
  have hb := CubicalSphereSuspension.hom_bijective
    (m := d) (n := n + n) (by omega)
  rw [← hc] at hb
  exact (Function.Bijective.of_comp_iff (sphereHopfHom n hn d) E.bijective).mp hb

def sphereHopfPiEquiv (n d : ℕ) [NeZero d] (hn : 2 ≤ n) (hdn : d + 2 ≤ 3 * n) :
    π_ d (Space n) (basepoint n) ≃*
      π_ (d + 1) (Sphere (n + n + 1)) (spherePole (n + n + 1)) :=
  MulEquiv.ofBijective (sphereHopfHom n hn d) (sphereHopfHom_bijective_range n d hn hdn)

end NoExoticSixSphere.JamesSphere.FirstStageQuotient
