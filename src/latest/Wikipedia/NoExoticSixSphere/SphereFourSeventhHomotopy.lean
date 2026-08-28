import Wikipedia.NoExoticSixSphere.JamesSphereThreeRetraction
import Wikipedia.NoExoticSixSphere.SplitCyclicGroupExtension
import Wikipedia.HomotopyGroupsOfSpheres.SphereThreeSix
import Wikipedia.HomotopyGroupsOfSpheres.SphereSeven

/-!
# The actual seventh homotopy group of the four-sphere

Quaternion multiplication kills the original three-sphere EHP connecting
map. The proved EHP exactness therefore gives a short exact sequence with
the actual suspension inclusion and James--Hopf projection. The already
proved groups `pi_6(S^3) = Z/12` and `pi_7(S^7) = Z` split this sequence.
The resulting isomorphism retains both of those original maps.
-/

noncomputable section

open scoped Topology
open Wikipedia.HomotopyGroupsOfSpheres

namespace NoExoticSixSphere.SphereFourSeventh

def suspension : π_ 6 (Sphere 3) (spherePole 3) →* π_ 7 (Sphere 4) (spherePole 4) :=
  CubicalSphereSuspension.hom 6 3

def hopf : π_ 7 (Sphere 4) (spherePole 4) →* π_ 7 (Sphere 7) (spherePole 7) :=
  JamesSphere.SuspensionComparison.orderedHopfHom 3 (by decide) 6

theorem suspension_injective : Function.Injective suspension :=
  JamesSphere.ThreeRetraction.suspension_injective 6

theorem hopf_surjective : Function.Surjective hopf :=
  JamesSphere.ThreeAttaching.hopf_surjective 5 (by decide)

theorem hopf_kernel (c : π_ 7 (Sphere 4) (spherePole 4)) :
    hopf c = 1 ↔ ∃ a : π_ 6 (Sphere 3) (spherePole 3), suspension a = c :=
  JamesSphere.EHP.hopf_eq_one_iff_metastable 3 5 (by decide) (by decide) c

def splitEquiv :
    (π_ 6 (Sphere 3) (spherePole 3) × π_ 7 (Sphere 7) (spherePole 7)) ≃*
      π_ 7 (Sphere 4) (spherePole 4) :=
  SplitCyclicGroupExtension.equiv suspension hopf (pi7_sphere_seven_mulEquiv (spherePole 7))
    hopf_surjective suspension_injective hopf_kernel

def groupEquiv : π_ 7 (Sphere 4) (spherePole 4) ≃*
    (Multiplicative ℤ × Multiplicative (ZMod 12)) :=
  splitEquiv.symm.trans
    ((MulEquiv.prodCongr (pi6_sphere_three_mulEquiv (spherePole 3))
      (pi7_sphere_seven_mulEquiv (spherePole 7))).trans MulEquiv.prodComm)

theorem groupEquiv_hopf (c : π_ 7 (Sphere 4) (spherePole 4)) :
    (groupEquiv c).1 = pi7_sphere_seven_mulEquiv (spherePole 7) (hopf c) :=
  congrArg (pi7_sphere_seven_mulEquiv (spherePole 7))
    (SplitCyclicGroupExtension.equiv_symm_snd suspension hopf
      (pi7_sphere_seven_mulEquiv (spherePole 7)) hopf_surjective suspension_injective hopf_kernel c)

theorem splitEquiv_one (a : π_ 6 (Sphere 3) (spherePole 3)) :
    splitEquiv (a, 1) = suspension a := by
  change suspension a * SplitCyclicGroupExtension.sectionMap hopf
    (pi7_sphere_seven_mulEquiv (spherePole 7)) hopf_surjective 1 = suspension a
  rw [map_one, mul_one]

theorem groupEquiv_suspension (a : π_ 6 (Sphere 3) (spherePole 3)) :
    groupEquiv (suspension a) = (1, pi6_sphere_three_mulEquiv (spherePole 3) a) := by
  have h : splitEquiv.symm (suspension a) = (a, 1) :=
    splitEquiv.symm_apply_eq.mpr (splitEquiv_one a).symm
  change (pi7_sphere_seven_mulEquiv (spherePole 7) (splitEquiv.symm (suspension a)).2,
    pi6_sphere_three_mulEquiv (spherePole 3) (splitEquiv.symm (suspension a)).1) = _
  rw [h]
  simp only [map_one]

end NoExoticSixSphere.SphereFourSeventh
