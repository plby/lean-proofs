import Wikipedia.NoExoticSixSphere.JamesSphereBottomHomology
import Wikipedia.NoExoticSixSphere.JamesSphereQuotientHomologyRange

/-!
# The original bottom sphere induces native isomorphisms in the metastable range

The actual homology input is now proved. Applying the checked finite-range
Hurewicz comparison gives bijectivity of the original bottom-sphere map in
degrees `d ≤ 3 * n - 2`, including the genuine quotient basepoint.
The separate relative-fiber to quotient comparison is not asserted here.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.JamesSphere.FirstStageQuotient

theorem bottomSphere_pi_bijective_range (n d : ℕ) (hn : 2 ≤ n) (hd : 0 < d)
    (hdn : d + 2 ≤ 3 * n) :
    Function.Bijective (HigherHomotopy.map (N := Fin d) (bottomSphere n)
      (bottomSphere_pole n)) := by
  rcases n with _ | _ | n
  · omega
  · omega
  · exact bottomSphere_pi_bijective_of_homology n (3 * (n + 2) - 2) (by omega)
      (fun k hk hkD ↦ bottomSphere_homology_bijective_range (n + 2) (by omega)
        k hk (by omega)) d hd (by omega)

def bottomSpherePiEquiv (n d : ℕ) [NeZero d] (hn : 2 ≤ n) (hdn : d + 2 ≤ 3 * n) :
    π_ d (Sphere (n + n)) (spherePole (n + n)) ≃*
      π_ d (Space n) (basepoint n) :=
  MulEquiv.ofBijective
    (HigherHomotopy.mapMonoidHom (N := Fin d) (bottomSphere n) (bottomSphere_pole n))
    (bottomSphere_pi_bijective_range n d hn (Nat.pos_of_ne_zero (NeZero.ne d)) hdn)

end NoExoticSixSphere.JamesSphere.FirstStageQuotient
