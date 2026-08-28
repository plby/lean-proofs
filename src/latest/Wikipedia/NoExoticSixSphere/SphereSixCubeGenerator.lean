import Wikipedia.NoExoticSixSphere.SphereHomotopyGroups
import Wikipedia.NoExoticSixSphere.SmoothSphereCubeReflection
import Wikipedia.NoExoticSixSphere.SixthHurewiczNativeNaturality
import Wikipedia.HopfProblem.SixthHurewiczIso
import Wikipedia.HopfProblem.SphereHomologyTop
import Wikipedia.HopfProblem.SphereHomologySimplyConnectedTopology

/-!
# The original native six-cube gives a primitive sphere homology class

Actual sphere/cube maps and native cyclicity prove that the cube
identity generates pi6(S6). The genuine Hurewicz isomorphism transfers
this to H6. Relative to the previously constructed sphere top class,
the resulting generator is the top class or its negative. No cube
orientation or triangulation sign is assumed.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris SphereHomology

namespace NoExoticSixSphere.SphereSixCube

local instance piTwo : Subsingleton (π_ 2 (Sphere 6) (spherePole 6)) :=
  subsingleton_sphereHomotopyGroup (by decide) _

local instance piThree : Subsingleton (π_ 3 (Sphere 6) (spherePole 6)) :=
  subsingleton_sphereHomotopyGroup (by decide) _

local instance piFour : Subsingleton (π_ 4 (Sphere 6) (spherePole 6)) :=
  subsingleton_sphereHomotopyGroup (by decide) _

local instance piFive : Subsingleton (π_ 5 (Sphere 6) (spherePole 6)) :=
  subsingleton_sphereHomotopyGroup (by decide) _

def hurewiczEquiv : π_ 6 (Sphere 6) (spherePole 6) ≃*
    Multiplicative (SingularHomology (Sphere 6) 6) :=
  SixthHurewicz.hurewiczPi6Equiv (spherePole 6)

def integerEquiv : π_ 6 (Sphere 6) (spherePole 6) ≃* Multiplicative ℤ :=
  hurewiczEquiv.trans (unitSphereHomologyTopEquiv 5).toAddEquiv.toMultiplicative

def chosenGenerator : π_ 6 (Sphere 6) (spherePole 6) :=
  integerEquiv.symm (Multiplicative.ofAdd 1)

theorem cyclic_generator_generates {G : Type*} [Group G] (e : G ≃* Multiplicative ℤ) :
    Function.Surjective (fun k : ℤ ↦ (e.symm (Multiplicative.ofAdd 1)) ^ k) := by
  intro a
  refine ⟨(e a).toAdd, e.injective ?_⟩
  rw [map_zpow, MulEquiv.apply_symm_apply]
  change Multiplicative.ofAdd ((e a).toAdd • (1 : ℤ)) = e a
  rw [Int.zsmul_eq_mul, mul_one]
  rfl

theorem chosenGenerator_generates : Function.Surjective (fun k : ℤ ↦ chosenGenerator ^ k) :=
  cyclic_generator_generates integerEquiv

def identityClass : π_ 6 (Sphere 6) (spherePole 6) :=
  SmoothCube.sphereClass ⟨ContinuousMap.id _, rfl⟩

theorem identity_map {X : Type*} [TopologicalSpace X] {x : X}
    (f : SmoothCube.BasedMap 6 X x) :
    HigherHomotopy.map (N := Fin 6) f.val f.property identityClass =
      SmoothCube.sphereClass f := rfl

theorem identity_generates : Function.Surjective (fun k : ℤ ↦ identityClass ^ k) := by
  intro a
  obtain ⟨f, hf⟩ := SmoothCube.sphereClass_surjective (by decide : 0 < 6) a
  let F := HigherHomotopy.mapMonoidHom (N := Fin 6) f.val f.property
  have ha : F identityClass = a := (identity_map f).trans hf
  obtain ⟨k, hk⟩ := chosenGenerator_generates identityClass
  obtain ⟨j, hj⟩ := chosenGenerator_generates (F chosenGenerator)
  refine ⟨j, ?_⟩
  calc
    identityClass ^ j = (chosenGenerator ^ k) ^ j := congrArg (fun c ↦ c ^ j) hk.symm
    _ = (chosenGenerator ^ j) ^ k := by rw [← zpow_mul, ← zpow_mul, mul_comm k j]
    _ = (F chosenGenerator) ^ k := congrArg (fun c ↦ c ^ k) hj
    _ = F (chosenGenerator ^ k) := (map_zpow F _ k).symm
    _ = F identityClass := congrArg F hk
    _ = a := ha

def generator : SingularHomology (Sphere 6) 6 :=
  SixthHurewicz.hurewiczFunction (spherePole 6) identityClass

theorem generator_generates : Function.Surjective (fun k : ℤ ↦ k • generator) := by
  intro a
  let c := hurewiczEquiv.symm (Multiplicative.ofAdd a)
  have ha : hurewiczEquiv c = Multiplicative.ofAdd a := hurewiczEquiv.apply_symm_apply _
  obtain ⟨k, hk⟩ := identity_generates c
  refine ⟨k, ?_⟩
  exact congrArg Multiplicative.toAdd
    (((map_zpow hurewiczEquiv identityClass k).symm.trans (congrArg hurewiczEquiv hk)).trans ha)

theorem generator_coordinate_natAbs : Int.natAbs (unitSphereHomologyTopEquiv 5 generator) = 1 := by
  obtain ⟨k, hk⟩ := generator_generates (unitSphereTopClass 5)
  have he := congrArg (unitSphereHomologyTopEquiv 5) hk
  rw [map_zsmul, Int.zsmul_eq_mul, unitSphereHomologyTopEquiv_topClass] at he
  have hn := congrArg Int.natAbs he
  rw [Int.natAbs_mul] at hn
  exact Nat.eq_one_of_mul_eq_one_left hn

theorem generator_eq_top_or_neg :
    generator = unitSphereTopClass 5 ∨ generator = -unitSphereTopClass 5 := by
  rcases Int.isUnit_iff.mp (Int.isUnit_iff_natAbs_eq.mpr generator_coordinate_natAbs) with h | h
  · left
    apply (unitSphereHomologyTopEquiv 5).injective
    rw [h, unitSphereHomologyTopEquiv_topClass]
  · right
    apply (unitSphereHomologyTopEquiv 5).injective
    rw [h, map_neg, unitSphereHomologyTopEquiv_topClass]

end NoExoticSixSphere.SphereSixCube
