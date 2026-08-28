import Wikipedia.NoExoticSixSphere.JamesAttachingNativeLift
import Wikipedia.NoExoticSixSphere.SmoothSphereGroupInversion
import Wikipedia.NoExoticSixSphere.QuaternionCommutatorNativeGenerator

/-!
# The retracted attaching family and the actual quaternion commutator

Evaluate the checked James-space homotopy in unit quaternions. The
original reflected letters are based-homotopic to their inverses.
This gives a homotopy to the ordinary quaternion commutator. The
existing topological-group normalization fixes both axes throughout,
retaining both endpoint maps exactly.
-/

noncomputable section

open scoped Topology unitInterval commutatorElement
open Wikipedia.HopfProblem.UnitQuaternionSphere
open Wikipedia.HomotopyGroupsOfSpheres

namespace NoExoticSixSphere.JamesSphere.ThreeRetraction

open AttachingSquare QuaternionCommutatorNativeSphere

theorem wordEvaluation_one : wordEvaluation 1 = 1 :=
  map_one (James.lift (spherePole 3) sphereHomeomorph.symm)

theorem wordEvaluation_mul (a b : WordHomology.Words 3) :
    wordEvaluation (a * b) = wordEvaluation a * wordEvaluation b :=
  map_mul (James.lift (spherePole 3) sphereHomeomorph.symm) a b

theorem wordEvaluation_inclusion (x : Sphere 3) :
    wordEvaluation (inclusion 3 x) = sphereHomeomorph.symm x :=
  James.lift_letter (spherePole 3) sphereHomeomorph.symm ThreeAttaching.inverse_pole x

def quaternionParameters : C(UnitQuaternions × UnitQuaternions, (Fin 2 → Sphere 3)) :=
  ⟨fun q ↦ ![sphereHomeomorph q.1, sphereHomeomorph q.2], by
    apply continuous_pi
    intro i
    fin_cases i
    · exact sphereHomeomorph.continuous.comp continuous_fst
    · exact sphereHomeomorph.continuous.comp continuous_snd⟩

def quaternionPairing : C(UnitQuaternions × UnitQuaternions, Sphere 6) :=
  (SecondStage.arrayPairing 3).comp quaternionParameters

theorem quaternionPairing_wedge (z : UnitQuaternions × UnitQuaternions)
    (hz : z ∈ Samelson.wedge (1 : UnitQuaternions) 1) :
    quaternionPairing z = spherePole 6 := by
  apply (SphereMooreCommutator.arrayPairing_pole_iff 3 _).mpr
  rcases hz with h | h
  · refine ⟨0, ?_⟩
    change sphereHomeomorph z.1 = spherePole 3
    rw [h, sphereHomeomorph_one]
  · refine ⟨1, ?_⟩
    change sphereHomeomorph z.2 = spherePole 3
    rw [h, sphereHomeomorph_one]

def correctedQuaternionSphere : SmoothCube.BasedMap 6 UnitQuaternions 1 :=
  ⟨wordEvaluation.comp correctedRepresentative.val,
    (congrArg wordEvaluation correctedRepresentative.property).trans wordEvaluation_one⟩

def correctedQuaternionProduct : C(UnitQuaternions × UnitQuaternions, UnitQuaternions) :=
  correctedQuaternionSphere.val.comp quaternionPairing

theorem correctedQuaternionProduct_wedge (z : UnitQuaternions × UnitQuaternions)
    (hz : z ∈ Samelson.wedge (1 : UnitQuaternions) 1) : correctedQuaternionProduct z = 1 := by
  change correctedQuaternionSphere.val (quaternionPairing z) = 1
  rw [quaternionPairing_wedge z hz]
  exact correctedQuaternionSphere.property

def fourWordQuaternionProduct : C(UnitQuaternions × UnitQuaternions, UnitQuaternions) :=
  wordEvaluation.comp ((MeridianCommutator.fourWordMap 3 (by decide) 0).comp quaternionParameters)

theorem fourWordQuaternionProduct_apply (z : UnitQuaternions × UnitQuaternions) :
    fourWordQuaternionProduct z = z.1 * z.2 *
      sphereHomeomorph.symm (SmoothCube.reflection 3 (by decide) 0 (sphereHomeomorph z.1)) *
        sphereHomeomorph.symm (SmoothCube.reflection 3 (by decide) 0 (sphereHomeomorph z.2)) := by
  change wordEvaluation (MeridianCommutator.fourWordMap 3 (by decide) 0
    (quaternionParameters z)) = _
  rw [MeridianCommutator.fourWordMap_apply, wordEvaluation_mul, wordEvaluation_mul,
    wordEvaluation_mul]
  simp only [wordEvaluation_inclusion]
  change sphereHomeomorph.symm (sphereHomeomorph z.1) *
    sphereHomeomorph.symm (sphereHomeomorph z.2) * _ * _ = _
  rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]
  rfl

theorem correctedQuaternion_fourWord :
    correctedQuaternionProduct.Homotopic fourWordQuaternionProduct :=
  ((ContinuousMap.Homotopic.refl wordEvaluation).comp
    correctedRepresentative_fourWord).comp (ContinuousMap.Homotopic.refl quaternionParameters)

theorem fourWordQuaternion_commutator :
    fourWordQuaternionProduct.Homotopic (Samelson.commutatorMap (G := UnitQuaternions)) := by
  obtain ⟨H⟩ := SmoothCube.reflected_homotopic_inverted (by decide : 0 < 3) 0 quaternionSphere
  refine ⟨{
    toFun := fun u ↦ u.2.1 * u.2.2 * H (u.1, sphereHomeomorph u.2.1) *
      H (u.1, sphereHomeomorph u.2.2)
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · exact ((continuous_fst.comp continuous_snd).mul
      (continuous_snd.comp continuous_snd)).mul
      (H.continuous.comp (continuous_fst.prodMk
        (sphereHomeomorph.continuous.comp (continuous_fst.comp continuous_snd)))) |>.mul
      (H.continuous.comp (continuous_fst.prodMk
        (sphereHomeomorph.continuous.comp (continuous_snd.comp continuous_snd))))
  · intro z
    rw [H.apply_zero, H.apply_zero]
    exact (fourWordQuaternionProduct_apply z).symm
  · intro z
    rw [H.apply_one, H.apply_one]
    change z.1 * z.2 * (sphereHomeomorph.symm (sphereHomeomorph z.1))⁻¹ *
      (sphereHomeomorph.symm (sphereHomeomorph z.2))⁻¹ = ⁅z.1, z.2⁆
    rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]
    rfl

def correctedQuaternionCommutatorHomotopy :
    correctedQuaternionProduct.HomotopyRel (Samelson.commutatorMap (G := UnitQuaternions))
      (Samelson.wedge (1 : UnitQuaternions) 1) :=
  Samelson.fixWedge 1 1
    (correctedQuaternion_fourWord.trans fourWordQuaternion_commutator).some
    correctedQuaternionProduct_wedge Samelson.commutatorMap_wedge

end NoExoticSixSphere.JamesSphere.ThreeRetraction
