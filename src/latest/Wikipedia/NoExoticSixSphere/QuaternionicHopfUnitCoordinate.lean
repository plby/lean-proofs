import Wikipedia.NoExoticSixSphere.QuaternionicHopfBaseExactness
import Wikipedia.NoExoticSixSphere.CyclicKernelPrimitiveCoordinate
import Wikipedia.NoExoticSixSphere.JamesSphereAttachingCubeGenerator

/-!
# The explicit quaternionic Hopf map has original Hopf coordinate of absolute value one

Use the actual Hopf exact sequence and the checked groups `pi7(S7)`,
`pi7(S4)`, and `pi6(S3)`. The native identity sphere class is a generator.
Exactness forces its image to have primitive free coordinate in the
ORIGINAL James--Hopf marking. No coordinate is assigned by definition.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.QuaternionicHopf

open Wikipedia.HomotopyGroupsOfSpheres
open Wikipedia.HopfProblem.UnitQuaternionSphere
open JamesSphere.AttachingSquare

def fiberSixEquiv : HomotopyGroup (Fin 6) FiberGroup 1 ≃* Multiplicative (ZMod 12) :=
  (homeomorphMulEquiv (N := Fin 6) sphereHomeomorph 1).trans
    (pi6_sphere_three_mulEquiv (sphereHomeomorph 1))

theorem connectingSix_surjective : Function.Surjective (connectingHom 6) := by
  intro a
  exact (connecting_range_eq_kernel a).mpr (Subsingleton.elim _ _)

theorem projection_range_eq_connecting_ker (n : ℕ) [NeZero n] :
    (projectionMap n).range = (connectingHom n).ker := by
  ext a
  exact projectionMap_range_eq_connecting_kernel a

theorem connecting_range_eq_inclusion_ker (n : ℕ) [NeZero n] :
    (connectingHom n).range = (inclusionMap n).ker := by
  ext a
  exact connecting_range_eq_kernel a

def hopfImageCoordinates : ℤ →+ ℤ × ZMod 12 where
  toFun k :=
    let c := SphereFourSeventh.groupEquiv (projectionMap 6 (cubeIdentityClass ^ k))
    (c.1.toAdd, c.2.toAdd)
  map_zero' := by simp only [zpow_zero, map_one]; rfl
  map_add' k l := by simp only [zpow_add, map_mul]; rfl

def connectingCoordinates : ℤ × ZMod 12 →+ ZMod 12 where
  toFun x := (fiberSixEquiv (connectingHom 6 (SphereFourSeventh.groupEquiv.symm
    (Multiplicative.ofAdd x.1, Multiplicative.ofAdd x.2)))).toAdd
  map_zero' := by
    change (fiberSixEquiv (connectingHom 6 (SphereFourSeventh.groupEquiv.symm 1))).toAdd = 0
    rw [map_one, map_one, map_one]
    rfl
  map_add' x y := by
    change (fiberSixEquiv (connectingHom 6 (SphereFourSeventh.groupEquiv.symm
      ((Multiplicative.ofAdd x.1, Multiplicative.ofAdd x.2) *
        (Multiplicative.ofAdd y.1, Multiplicative.ofAdd y.2))))).toAdd = _
    rw [map_mul, map_mul, map_mul]
    rfl

theorem coordinate_kernel (x : ℤ × ZMod 12) :
    connectingCoordinates x = 0 ↔ ∃ k : ℤ, hopfImageCoordinates k = x := by
  constructor
  · intro h
    have he : connecting 6 (SphereFourSeventh.groupEquiv.symm
        (Multiplicative.ofAdd x.1, Multiplicative.ofAdd x.2)) = 1 := by
      apply fiberSixEquiv.injective
      rw [map_one]
      exact congrArg Multiplicative.ofAdd h
    obtain ⟨a, ha⟩ := (projectionMap_range_eq_connecting_kernel _).mpr he
    obtain ⟨k, hk⟩ := cubeIdentity_generates a
    rw [← hk] at ha
    have hh := congrArg SphereFourSeventh.groupEquiv ha
    rw [MulEquiv.apply_symm_apply] at hh
    exact ⟨k, congrArg (fun c : Multiplicative ℤ × Multiplicative (ZMod 12) ↦
      (c.1.toAdd, c.2.toAdd)) hh⟩
  · rintro ⟨k, hk⟩
    have he : projectionMap 6 (cubeIdentityClass ^ k) = SphereFourSeventh.groupEquiv.symm
        (Multiplicative.ofAdd x.1, Multiplicative.ofAdd x.2) := by
      apply SphereFourSeventh.groupEquiv.injective
      rw [MulEquiv.apply_symm_apply]
      exact congrArg (fun c : ℤ × ZMod 12 ↦
        (Multiplicative.ofAdd c.1, Multiplicative.ofAdd c.2)) hk
    have hh := connecting_projectionMap (cubeIdentityClass ^ k)
    rw [he] at hh
    change (fiberSixEquiv (connecting 6 (SphereFourSeventh.groupEquiv.symm
      (Multiplicative.ofAdd x.1, Multiplicative.ofAdd x.2)))).toAdd = 0
    rw [hh, map_one]
    rfl

theorem image_identity_nativeClass : projectionMap 6 cubeIdentityClass = nativeClass := rfl

theorem image_coordinate_one : (hopfImageCoordinates 1).1 = hopfNumber := by
  change (SphereFourSeventh.groupEquiv (projectionMap 6 (cubeIdentityClass ^ (1 : ℤ)))).1.toAdd =
    hopfNumber
  rw [zpow_one, image_identity_nativeClass]
  exact (OriginalHopfSixthSquare.hopfCoordinate_eq nativeClass).symm

theorem hopfNumber_natAbs : hopfNumber.natAbs = 1 := by
  rw [← image_coordinate_one]
  exact CyclicKernelPrimitiveCoordinate.first_one_natAbs
    hopfImageCoordinates connectingCoordinates coordinate_kernel

theorem suspendedSmashClass_eq : suspendedSmashClass = SixthStemSmashSquare.nativeClass :=
  suspendedSmashClass_eq_of_hopfNumber hopfNumber_natAbs

end NoExoticSixSphere.QuaternionicHopf
