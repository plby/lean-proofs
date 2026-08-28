import Wikipedia.NoExoticSixSphere.JamesSphereUnitalAttaching
import Wikipedia.HopfProblem.UnitQuaternionSphere

/-!
# Quaternion multiplication contracts the actual three-sphere attaching map

The usual quaternion coordinates send the group identity to the original
sphere pole. Transporting multiplication through this actual homeomorphism
gives the two unit identities, hence the concrete characteristic-disk
extension. Its based nullhomotopy kills the original EHP connecting map
in every degree of the proved metastable range for the three-sphere.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem.UnitQuaternionSphere

namespace NoExoticSixSphere.JamesSphere.ThreeAttaching

theorem quaternion_one_pole : sphereHomeomorph (1 : UnitQuaternions) = spherePole 3 := by
  apply Subtype.ext
  ext i
  fin_cases i <;> rfl

theorem inverse_pole : sphereHomeomorph.symm (spherePole 3) = 1 :=
  sphereHomeomorph.symm_apply_eq.mpr quaternion_one_pole.symm

def multiplication : C(Sphere 3 × Sphere 3, Sphere 3) :=
  ⟨fun p ↦ sphereHomeomorph (sphereHomeomorph.symm p.1 * sphereHomeomorph.symm p.2),
    sphereHomeomorph.continuous.comp
      ((sphereHomeomorph.symm.continuous.comp continuous_fst).mul
        (sphereHomeomorph.symm.continuous.comp continuous_snd))⟩

theorem multiplication_left (x : Sphere 3) : multiplication (spherePole 3, x) = x := by
  change sphereHomeomorph (sphereHomeomorph.symm (spherePole 3) * sphereHomeomorph.symm x) = x
  rw [inverse_pole, one_mul, Homeomorph.apply_symm_apply]

theorem multiplication_right (x : Sphere 3) : multiplication (x, spherePole 3) = x := by
  change sphereHomeomorph (sphereHomeomorph.symm x * sphereHomeomorph.symm (spherePole 3)) = x
  rw [inverse_pole, mul_one, Homeomorph.apply_symm_apply]

def attachingNullhomotopy :
    (CellBoundary.attaching 3).HomotopyRel (ContinuousMap.const _ (spherePole 3))
      {CellBoundary.corner 3 (by decide)} :=
  UnitalAttaching.nullhomotopy 3 multiplication multiplication_left multiplication_right (by decide)

theorem attachingHom_eq_one (d : ℕ) [NeZero d]
    (c : π_ d (Sphere 5) (spherePole 5)) : EHPCell.attachingHom 3 (by decide) d c = 1 :=
  UnitalAttaching.attachingHom_eq_one 3 multiplication multiplication_left multiplication_right
    (by decide) d c

theorem connecting_eq_one (d : ℕ) [NeZero d] (hd : d ≤ 6)
    (c : π_ (d + 1 + 1) (Sphere 7) (spherePole 7)) :
    EHP.connectingHomMetastable 3 d (by decide) (by omega) c = 1 :=
  UnitalAttaching.connecting_eq_one 3 multiplication multiplication_left multiplication_right
    d (by decide) (by omega) c

theorem suspension_injective (d : ℕ) [NeZero d] (hd : d ≤ 6) :
    Function.Injective (CubicalSphereSuspension.hom d 3) :=
  UnitalAttaching.suspension_injective 3 multiplication multiplication_left multiplication_right
    d (by decide) (by omega)

theorem hopf_surjective (d : ℕ) [NeZero d] (hd : d ≤ 6) :
    Function.Surjective (SuspensionComparison.orderedHopfHom 3 (by decide) (d + 1)) := by
  intro c
  exact (EHP.connecting_eq_one_iff_metastable 3 d (by decide) (by omega) c).mp
    (connecting_eq_one d hd c)

end NoExoticSixSphere.JamesSphere.ThreeAttaching
