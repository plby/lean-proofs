import Wikipedia.HopfProblem.DegreeCollapseQuaternionicConnectingSuspension
import Wikipedia.HopfProblem.DegreeCollapseNinthSphereQuotient

/-!
# Every original pi9(S3) class factors through the actual clutching sphere

The identity sphere in the original quaternionic two-frame fibration
has a chosen actual lift. Its terminal face supplies a based S6-to-S3
clutching map. The proved connecting surjectivity and the original
third-stem suspension isomorphism show that every pi9(S3) class is
obtained by postcomposing a pi9(S6) class with this map.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicClutching

open NoExoticSixSphere SmoothCube CubicalSphereSuspension SphereComposition
open Wikipedia.HomotopyGroupsOfSpheres QuaternionicFibration

def baseMap : BasedMap 7 BaseSphere north :=
  ⟨(baseSphereHomeomorph.symm : C(NoExoticSixSphere.Sphere 7, BaseSphere)),
    baseSphereHomeomorph.symm_apply_eq.mpr NinthSphereQuotient.baseSphereHomeomorph_north.symm⟩

def sphereCoordinates {k : ℕ} (f : BasedMap k BaseSphere north) : Based k 7 :=
  ⟨(baseSphereHomeomorph : C(BaseSphere, NoExoticSixSphere.Sphere 7)).comp f.val,
    (congrArg baseSphereHomeomorph f.property).trans
      NinthSphereQuotient.baseSphereHomeomorph_north⟩

theorem baseMap_sphereCoordinates {k : ℕ} (f : BasedMap k BaseSphere north) :
    SphereLiftFamily.compose baseMap (sphereCoordinates f) = f := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  exact baseSphereHomeomorph.symm_apply_apply (f.val z)

def baseLift : CubeLift (toGenLoop baseMap) := chosenLift (toGenLoop baseMap)

def clutching : BasedMap 6 northSubgroup 1 :=
  QuaternionicConnectingSuspension.boundarySphere (by decide : 0 < 6) baseLift

theorem class_factorization (a : π_ 9 northSubgroup 1) :
    ∃ g : Based 9 6, sphereClass (SphereLiftFamily.compose clutching g) = a := by
  obtain ⟨b, hb⟩ := QuaternionicPiNine.connecting_nine_surjective a
  obtain ⟨f, hf⟩ := sphereClass_surjective (by decide : 0 < 10) b
  obtain ⟨c, hc⟩ := (StableThirdAttaching.stepEquiv 1).surjective
    (sphereClass (sphereCoordinates f))
  obtain ⟨g, hg⟩ := sphereClass_surjective (by decide : 0 < 9) c
  have hE : sphereClass (productBasedMap g) = sphereClass (sphereCoordinates f) := by
    rw [← hom_sphereClass, hg]
    exact hc
  have hp : sphereClass (SphereLiftFamily.compose baseMap (productBasedMap g)) = b := by
    rw [SphereLiftFamily.sphereClass_compose, hE,
      ← SphereLiftFamily.sphereClass_compose, baseMap_sphereCoordinates]
    exact hf
  exact ⟨g, (QuaternionicConnectingSuspension.connecting_suspended_precomposition
    (by decide : 0 < 6) baseLift g).symm.trans ((congrArg (connecting 9) hp).trans hb)⟩

theorem fiberSphereHomeomorph_one : fiberSphereHomeomorph 1 = spherePole 3 := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

def fiberCoordinates {k : ℕ} (f : BasedMap k northSubgroup 1) : Based k 3 :=
  ⟨(fiberSphereHomeomorph : C(northSubgroup, NoExoticSixSphere.Sphere 3)).comp f.val,
    (congrArg fiberSphereHomeomorph f.property).trans fiberSphereHomeomorph_one⟩

theorem fiberCoordinates_class {k : ℕ} (f : BasedMap k northSubgroup 1) :
    sphereClass (fiberCoordinates f) =
      HigherHomotopy.map (N := Fin k)
        (fiberSphereHomeomorph : C(northSubgroup, NoExoticSixSphere.Sphere 3))
        fiberSphereHomeomorph_one (sphereClass f) := rfl

def fiberLift {k : ℕ} (f : Based k 3) : BasedMap k northSubgroup 1 :=
  ⟨(fiberSphereHomeomorph.symm : C(NoExoticSixSphere.Sphere 3, northSubgroup)).comp f.val,
    (congrArg fiberSphereHomeomorph.symm f.property).trans
      (fiberSphereHomeomorph.symm_apply_eq.mpr fiberSphereHomeomorph_one.symm)⟩

theorem fiberCoordinates_fiberLift {k : ℕ} (f : Based k 3) :
    fiberCoordinates (fiberLift f) = f := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  exact fiberSphereHomeomorph.apply_symm_apply (f.val z)

def sphereClutching : Based 6 3 := fiberCoordinates clutching

theorem fiberCoordinates_compose {k : ℕ} (g : Based k 6) :
    fiberCoordinates (SphereLiftFamily.compose clutching g) = comp sphereClutching g := by
  apply Subtype.ext
  rfl

theorem sphere_class_factorization (x : π_ 9 (NoExoticSixSphere.Sphere 3) (spherePole 3)) :
    ∃ g : Based 9 6, mapHom sphereClutching 9 (sphereClass g) = x := by
  obtain ⟨f, hf⟩ := sphereClass_surjective (by decide : 0 < 9) x
  obtain ⟨g, hg⟩ := class_factorization (sphereClass (fiberLift f))
  have h := congrArg (HigherHomotopy.map (N := Fin 9)
    (fiberSphereHomeomorph : C(northSubgroup, NoExoticSixSphere.Sphere 3))
      fiberSphereHomeomorph_one) hg
  rw [← fiberCoordinates_class, ← fiberCoordinates_class,
    fiberCoordinates_compose, fiberCoordinates_fiberLift] at h
  exact ⟨g, (mapHom_sphereClass sphereClutching g).trans (h.trans hf)⟩

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicClutching

