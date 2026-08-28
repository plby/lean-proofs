import Wikipedia.NoExoticSixSphere.JamesSphereQuotientHopfRange
import Wikipedia.NoExoticSixSphere.SphereConnectivity
import Wikipedia.HopfProblem.OrbitPairSphereNullhomotopyCriterion
import Wikipedia.HopfProblem.SixthHurewiczIso
import Wikipedia.HomotopyGroupsOfSpheres.SphereSeven

/-!
# The original James quotient's sixth homology has an actual Hopf marking

The original bottom S6 map proves that the quotient J(S3)/S3 has trivial
native groups below degree six. Its genuine sixth Hurewicz map is
therefore an equivalence. The original quotient Hopf factor and the
proved seventh-sphere marking give an integral coordinate on this
actual homology group, with an exact Hurewicz formula.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.JamesSphere.QuotientHurewiczSix

abbrev Space := FirstStageQuotient.Space 3
abbrev point : Space := FirstStageQuotient.basepoint 3

theorem pi_below_six (d : ℕ) (hd : 0 < d) (hlt : d < 6) :
    Subsingleton (π_ d Space point) := by
  let : Subsingleton (π_ d (Sphere 6) (spherePole 6)) :=
    OrbitPair.SphereNullhomotopy.pi_subsingleton_of_sphere_nullhomotopies hd
      (fun f ↦ sphere_sphere_nullhomotopic hlt f) (spherePole 6)
  exact (FirstStageQuotient.bottomSphere_pi_bijective_range 3 d
    (by decide) hd (by omega)).surjective.subsingleton

def hurewiczEquiv : π_ 6 Space point ≃* Multiplicative (SingularHomology Space 6) := by
  let : SimplyConnectedSpace Space := FirstStageQuotient.simplyConnectedSpace 1
  let := pi_below_six 2 (by decide) (by decide)
  let := pi_below_six 3 (by decide) (by decide)
  let := pi_below_six 4 (by decide) (by decide)
  let := pi_below_six 5 (by decide) (by decide)
  exact SixthHurewicz.hurewiczPi6Equiv point

theorem hurewiczEquiv_apply (c : π_ 6 Space point) :
    hurewiczEquiv c = Multiplicative.ofAdd (SixthHurewicz.hurewiczFunction point c) := rfl

def hopfEquiv : π_ 6 Space point ≃* π_ 7 (Sphere 7) (spherePole 7) :=
  FirstStageQuotient.sphereHopfPiEquiv 3 6 (by decide) (by decide)

theorem hopfEquiv_apply (c : π_ 6 Space point) :
    hopfEquiv c = FirstStageQuotient.sphereHopfHom 3 (by decide) 6 c := rfl

def integerMulEquiv : Multiplicative (SingularHomology Space 6) ≃* Multiplicative ℤ :=
  hurewiczEquiv.symm.trans
    (hopfEquiv.trans (Wikipedia.HomotopyGroupsOfSpheres.pi7_sphere_seven_mulEquiv (spherePole 7)))

def integerEquiv : SingularHomology Space 6 ≃ₗ[ℤ] ℤ :=
  integerMulEquiv.toAdditive.toIntLinearEquiv

theorem integerEquiv_hurewicz (c : π_ 6 Space point) :
    integerEquiv (SixthHurewicz.hurewiczFunction point c) =
      (Wikipedia.HomotopyGroupsOfSpheres.pi7_sphere_seven_mulEquiv (spherePole 7)
        (FirstStageQuotient.sphereHopfHom 3 (by decide) 6 c)).toAdd := by
  change (Wikipedia.HomotopyGroupsOfSpheres.pi7_sphere_seven_mulEquiv (spherePole 7)
    (hopfEquiv (hurewiczEquiv.symm (hurewiczEquiv c)))).toAdd = _
  rw [MulEquiv.symm_apply_apply, hopfEquiv_apply]

end NoExoticSixSphere.JamesSphere.QuotientHurewiczSix
