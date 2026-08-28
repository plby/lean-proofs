import Wikipedia.HopfProblem.DegreeCollapseHopfConnectingSuspension
import Wikipedia.HopfProblem.DegreeCollapseSphereSelfMapSurjectivity
import Wikipedia.NoExoticSixSphere.CubicalSuspensionRange
import Wikipedia.NoExoticSixSphere.SphereHomotopyGroups

/-!
# The actual Hopf connecting map is surjective on suspended classes

Its clutching sphere map is surjective on pi3 because both suspension
and the original Hopf connecting map are surjective there. An actual
based right homotopy inverse promotes this to every positive degree.
The comparison retains the original unit-quaternion fiber and the
original product suspension.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.HopfClutching

open NoExoticSixSphere SmoothCube CubicalSphereSuspension SphereComposition
open QuaternionicHopf
open Wikipedia.HopfProblem.UnitQuaternionSphere

def baseMap : Based 4 4 := ⟨ContinuousMap.id _, rfl⟩

def baseLift : CubeLift (toGenLoop baseMap) := chosenLift (toGenLoop baseMap)

def clutching : BasedMap 3 FiberGroup 1 :=
  HopfConnectingSuspension.boundarySphere (by decide : 0 < 3) baseLift

theorem sphereHomeomorph_one : sphereHomeomorph (1 : FiberGroup) = spherePole 3 := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

def sphereClutching : Based 3 3 :=
  ⟨(sphereHomeomorph : C(FiberGroup, Sphere 3)).comp clutching.val,
    (congrArg sphereHomeomorph clutching.property).trans sphereHomeomorph_one⟩

theorem connecting_three_surjective : Function.Surjective (connecting 3) := by
  let : Subsingleton (π_ 3 (Sphere 7) (spherePole 7)) :=
    subsingleton_sphereHomotopyGroup (by decide : 3 < 7) (spherePole 7)
  intro a
  exact (connecting_range_eq_kernel a).mpr (Subsingleton.elim _ _)

theorem sphereClutching_map {k : ℕ} [NeZero k] (c : π_ k (Sphere 3) (spherePole 3)) :
    mapHom sphereClutching k c =
      HigherHomotopy.map (N := Fin k) (sphereHomeomorph : C(FiberGroup, Sphere 3))
        sphereHomeomorph_one (connecting k (hom k 3 c)) := by
  have h := HopfConnectingSuspension.connecting_suspension_map
    (by decide : 0 < 3) baseLift c
  change connecting k (HigherHomotopy.map (N := Fin (k + 1))
      (ContinuousMap.id (Sphere 4)) rfl (hom k 3 c)) =
    HigherHomotopy.map (N := Fin k) clutching.val clutching.property c at h
  have hid := SphereSelfMapSurjectivity.native_map_id (N := Fin (k + 1))
    (x := spherePole 4) (hom k 3 c)
  have h' : connecting k (hom k 3 c) =
      HigherHomotopy.map (N := Fin k) clutching.val clutching.property c :=
    (congrArg (connecting k) hid).symm.trans h
  have hcomp := HigherHomotopy.map_comp clutching.val clutching.property
    (sphereHomeomorph : C(FiberGroup, Sphere 3)) sphereHomeomorph_one c
  exact hcomp.symm.trans (congrArg (HigherHomotopy.map (N := Fin k)
    (sphereHomeomorph : C(FiberGroup, Sphere 3)) sphereHomeomorph_one) h'.symm)

theorem sphereClutching_top_surjective : Function.Surjective (mapHom sphereClutching 3) := by
  have hnative : Function.Surjective (fun c : π_ 3 (Sphere 3) (spherePole 3) ↦
      HigherHomotopy.map (N := Fin 3) (sphereHomeomorph : C(FiberGroup, Sphere 3))
        sphereHomeomorph_one (connecting 3 (hom 3 3 c))) :=
    (SphereSelfMapSurjectivity.native_homeomorph_surjective sphereHomeomorph
      sphereHomeomorph_one).comp (connecting_three_surjective.comp
        (hom_surjective (by decide : 3 + 2 < 2 * (3 + 1))))
  intro x
  obtain ⟨c, hc⟩ := hnative x
  exact ⟨c, (sphereClutching_map c).trans hc⟩

theorem sphereClutching_map_surjective (k : ℕ) [NeZero k] :
    Function.Surjective (mapHom sphereClutching k) :=
  SphereSelfMapSurjectivity.mapHom_surjective sphereClutching sphereClutching_top_surjective

theorem connecting_suspension_surjective (k : ℕ) [NeZero k] :
    Function.Surjective (fun c : π_ k (Sphere 3) (spherePole 3) ↦
      connecting k (hom k 3 c)) := by
  intro a
  obtain ⟨c, hc⟩ := sphereClutching_map_surjective k
    (HigherHomotopy.map (N := Fin k) (sphereHomeomorph : C(FiberGroup, Sphere 3))
      sphereHomeomorph_one a)
  refine ⟨c, ?_⟩
  apply SphereSelfMapSurjectivity.native_homeomorph_injective sphereHomeomorph
    sphereHomeomorph_one
  exact (sphereClutching_map c).symm.trans hc

end Wikipedia.HopfProblem.DegreeCollapse.HopfClutching
