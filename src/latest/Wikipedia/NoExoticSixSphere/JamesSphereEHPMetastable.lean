import Wikipedia.NoExoticSixSphere.JamesSphereEHPAssembly
import Wikipedia.NoExoticSixSphere.JamesSphereFiberQuotientRange

/-!
# Unconditional EHP exactness in the full required metastable range

The actual full James fiber-to-quotient comparison is now proved
bijective for positive `d <= 3n - 3`, with `n >= 2`. This discharges
the comparison input in all three consecutive exactness statements.
The suspension and James--Hopf maps are the original native maps.
The connecting map is the transported genuine fiber projection; its
identification with a Whitehead-product formula is not asserted here.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.JamesSphere.EHP

variable (n d : ℕ) [NeZero d] (hn : 2 ≤ n) (hdn : d + 3 ≤ 3 * n)

def connectingHomMetastable :
    π_ (d + 1 + 1) (Sphere (n + n + 1)) (spherePole (n + n + 1)) →*
      π_ d (Sphere n) (spherePole n) :=
  connectingHom n d hn hdn (FiberQuotient.hom_bijective_range n d hn hdn)

include hdn in
theorem hopf_eq_one_iff_metastable
    (c : π_ (d + 1 + 1) (Sphere (n + 1)) (spherePole (n + 1))) :
    SuspensionComparison.orderedHopfHom n hn (d + 1) c = 1 ↔
      ∃ a : π_ (d + 1) (Sphere n) (spherePole n),
        CubicalSphereSuspension.hom (d + 1) n a = c :=
  hopf_eq_one_iff_of_comparison n d hn hdn
    (FiberQuotient.hom_bijective_range n d hn hdn) c

theorem connecting_eq_one_iff_metastable
    (c : π_ (d + 1 + 1) (Sphere (n + n + 1)) (spherePole (n + n + 1))) :
    connectingHomMetastable n d hn hdn c = 1 ↔
      ∃ a : π_ (d + 1 + 1) (Sphere (n + 1)) (spherePole (n + 1)),
        SuspensionComparison.orderedHopfHom n hn (d + 1) a = c :=
  connecting_eq_one_iff_of_comparison n d hn hdn
    (FiberQuotient.hom_bijective_range n d hn hdn) c

theorem suspension_eq_one_iff_metastable (c : π_ d (Sphere n) (spherePole n)) :
    CubicalSphereSuspension.hom d n c = 1 ↔
      ∃ a : π_ (d + 1 + 1) (Sphere (n + n + 1)) (spherePole (n + n + 1)),
        connectingHomMetastable n d hn hdn a = c :=
  suspension_eq_one_iff_of_comparison n d hn hdn
    (FiberQuotient.hom_bijective_range n d hn hdn) c

end NoExoticSixSphere.JamesSphere.EHP
