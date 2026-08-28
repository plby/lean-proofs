import Wikipedia.NoExoticSixSphere.JamesSphereEHPAssembly
import Wikipedia.NoExoticSixSphere.JamesSphereFiberQuotientFirstHomotopy

/-!
# Unconditional EHP exactness through the first fiber-comparison range

The comparison input is now discharged for positive fiber degree at most
`2n - 1`. All three consecutive exact terms retain the original suspension,
coordinate-corrected James--Hopf map, and transported fiber projection.
For `n = 2` this covers the whole range `d <= 3n - 3`; the higher metastable
degrees for larger `n` are not covered. No Whitehead-product formula for
the connecting map is asserted.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.JamesSphere.EHP

variable (n d : ℕ) [NeZero d] (hn : 2 ≤ n) (hdn : d + 1 ≤ 2 * n)

def connectingHomFirstRange :
    π_ (d + 1 + 1) (Sphere (n + n + 1)) (spherePole (n + n + 1)) →*
      π_ d (Sphere n) (spherePole n) :=
  connectingHom n d hn (by omega) (FiberQuotient.hom_bijective_first_range n d hn hdn)

include hdn in
theorem hopf_eq_one_iff_first_range
    (c : π_ (d + 1 + 1) (Sphere (n + 1)) (spherePole (n + 1))) :
    SuspensionComparison.orderedHopfHom n hn (d + 1) c = 1 ↔
      ∃ a : π_ (d + 1) (Sphere n) (spherePole n),
        CubicalSphereSuspension.hom (d + 1) n a = c :=
  hopf_eq_one_iff_of_comparison n d hn (by omega)
    (FiberQuotient.hom_bijective_first_range n d hn hdn) c

theorem connecting_eq_one_iff_first_range
    (c : π_ (d + 1 + 1) (Sphere (n + n + 1)) (spherePole (n + n + 1))) :
    connectingHomFirstRange n d hn hdn c = 1 ↔
      ∃ a : π_ (d + 1 + 1) (Sphere (n + 1)) (spherePole (n + 1)),
        SuspensionComparison.orderedHopfHom n hn (d + 1) a = c :=
  connecting_eq_one_iff_of_comparison n d hn (by omega)
    (FiberQuotient.hom_bijective_first_range n d hn hdn) c

theorem suspension_eq_one_iff_first_range (c : π_ d (Sphere n) (spherePole n)) :
    CubicalSphereSuspension.hom d n c = 1 ↔
      ∃ a : π_ (d + 1 + 1) (Sphere (n + n + 1)) (spherePole (n + n + 1)),
        connectingHomFirstRange n d hn hdn a = c :=
  suspension_eq_one_iff_of_comparison n d hn (by omega)
    (FiberQuotient.hom_bijective_first_range n d hn hdn) c

end NoExoticSixSphere.JamesSphere.EHP
