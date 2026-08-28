import Wikipedia.NoExoticSixSphere.SphereFourSeventhHomotopy
import Wikipedia.HomotopyGroupsOfSpheres.SphereSevenMapGenerators
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The actual four-sphere attachment generates the suspension kernel

Use the proved integral generator of the original seventh sphere group.
Its image under the original second James-cell attaching map is a single
specified class of the original seventh group of S4. EHP identifies its
integer powers with the entire kernel of the actual suspension to S5.
The native suspension is onto, so its quotient is the actual eighth group
of S5. No value of the attaching class in numerical coordinates is assumed.
-/

noncomputable section

open scoped Topology
open Wikipedia.HomotopyGroupsOfSpheres

namespace NoExoticSixSphere.SphereFourAttaching

def attachingClass : π_ 7 (Sphere 4) (spherePole 4) :=
  JamesSphere.EHPCell.attachingHom 4 (by decide) 7 (sphereSevenGenerator (spherePole 7))

theorem attaching_image_iff (c : π_ 7 (Sphere 4) (spherePole 4)) :
    (∃ a : π_ 7 (Sphere 7) (spherePole 7),
      JamesSphere.EHPCell.attachingHom 4 (by decide) 7 a = c) ↔
      ∃ k : ℤ, attachingClass ^ k = c := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨k, rfl⟩ := sphereSevenGenerator_generates (spherePole 7) a
    exact ⟨k, (map_zpow (JamesSphere.EHPCell.attachingHom 4 (by decide) 7)
      (sphereSevenGenerator (spherePole 7)) k).symm.trans ha⟩
  · rintro ⟨k, hk⟩
    exact ⟨sphereSevenGenerator (spherePole 7) ^ k,
      (map_zpow (JamesSphere.EHPCell.attachingHom 4 (by decide) 7)
        (sphereSevenGenerator (spherePole 7)) k).trans hk⟩

def suspension : π_ 7 (Sphere 4) (spherePole 4) →* π_ 8 (Sphere 5) (spherePole 5) :=
  CubicalSphereSuspension.hom 7 4

theorem suspension_eq_one_iff (c : π_ 7 (Sphere 4) (spherePole 4)) :
    suspension c = 1 ↔ ∃ k : ℤ, attachingClass ^ k = c :=
  (JamesSphere.EHPCell.suspension_eq_one_iff_attaching 4 7
    (by decide) (by decide) c).trans (attaching_image_iff c)

theorem suspension_ker : suspension.ker = Subgroup.zpowers attachingClass := by
  ext c
  exact (suspension_eq_one_iff c).trans Subgroup.mem_zpowers_iff.symm

theorem suspension_attachingClass : suspension attachingClass = 1 :=
  (suspension_eq_one_iff attachingClass).mpr ⟨1, zpow_one _⟩

theorem suspension_surjective : Function.Surjective suspension :=
  CubicalSphereSuspension.hom_surjective (by decide)

def quotientEquiv :
    (π_ 7 (Sphere 4) (spherePole 4) ⧸ Subgroup.zpowers attachingClass) ≃*
      π_ 8 (Sphere 5) (spherePole 5) :=
  (QuotientGroup.quotientMulEquivOfEq suspension_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective suspension suspension_surjective)

theorem quotientEquiv_mk (c : π_ 7 (Sphere 4) (spherePole 4)) :
    quotientEquiv (QuotientGroup.mk c) = suspension c := rfl

end NoExoticSixSphere.SphereFourAttaching
