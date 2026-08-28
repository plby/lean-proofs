import Wikipedia.NoExoticSixSphere.PartialFramePatchHomotopy
import Wikipedia.NoExoticSixSphere.ProductHomotopyConnectivity
import Wikipedia.NoExoticSixSphere.SphereHomotopyGroups
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedIso
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# The actual second homology of the two-column overlap vanishes

The native second homotopy groups of the two sphere factors vanish. Actual
product connectivity and the constructed second Hurewicz isomorphism then
prove second singular homology vanishing. The proved overlap homotopy
equivalence transfers this to the original open intersection in `Space 5 2`.
-/

noncomputable section

namespace NoExoticSixSphere

open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

theorem sphereProduct_secondHomology_subsingleton (m n : ℕ) :
    Subsingleton (SingularHomology (Sphere (m + 3) × Sphere (n + 3)) 2) := by
  let x := spherePole (m + 3)
  let y := spherePole (n + 3)
  let : SimplyConnectedSpace (Sphere (m + 3)) := EuclideanSphere.simplyConnectedSpace (m + 1)
  let : SimplyConnectedSpace (Sphere (n + 3)) := EuclideanSphere.simplyConnectedSpace (n + 1)
  let : SimplyConnectedSpace (Sphere (m + 3) × Sphere (n + 3)) :=
    HigherHomotopy.simplyConnected_product
  let : Subsingleton (HomotopyGroup (Fin 2) (Sphere (m + 3)) x) :=
    subsingleton_sphereHomotopyGroup (by omega) x
  let : Subsingleton (HomotopyGroup (Fin 2) (Sphere (n + 3)) y) :=
    subsingleton_sphereHomotopyGroup (by omega) y
  let : Subsingleton (HomotopyGroup (Fin 2) (Sphere (m + 3) × Sphere (n + 3)) (x, y)) :=
    HigherHomotopy.subsingleton_product x y
  exact (Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected.hurewiczLinearEquiv
    (x, y)).symm.injective.subsingleton

namespace Stiefel.ColumnBundle

open GLOrthonormalization ContinuousMap

def twoColumnOverlapHomotopyEquiv (n : ℕ) (v : UnitSphere (Vector 2))
    (w : UnitSphere (Vector 1)) :
    Overlap v (spherePole (n + 1)) (antipode (spherePole (n + 1))) ≃ₕ Sphere n × Sphere n :=
  (overlapHomotopyEquiv n v).trans
    ((Homeomorph.refl (Sphere n)).prodCongr (OneColumn.homeomorph w)).toHomotopyEquiv

def twoColumnOverlapHomologyEquiv (n : ℕ) (v : UnitSphere (Vector 2))
    (w : UnitSphere (Vector 1)) (k : ℕ) :
    SingularHomology (Overlap v (spherePole (n + 1)) (antipode (spherePole (n + 1)))) k ≃ₗ[ℤ]
      SingularHomology (Sphere n × Sphere n) k :=
  homotopyEquivHomologyEquiv (twoColumnOverlapHomotopyEquiv n v w) k

theorem twoColumnOverlap_secondHomology_subsingleton (v : UnitSphere (Vector 2)) :
    Subsingleton (SingularHomology (Overlap v (spherePole 4) (antipode (spherePole 4))) 2) := by
  let : Subsingleton (SingularHomology (Sphere 3 × Sphere 3) 2) :=
    sphereProduct_secondHomology_subsingleton 0 0
  exact (twoColumnOverlapHomologyEquiv 3 v (spherePole 0) 2).injective.subsingleton

end Stiefel.ColumnBundle

end NoExoticSixSphere
