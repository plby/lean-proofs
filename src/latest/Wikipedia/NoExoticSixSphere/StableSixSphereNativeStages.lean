import Wikipedia.NoExoticSixSphere.StableSixSphereStages
import Wikipedia.NoExoticSixSphere.SphereBasedHomotopyComparison
import Wikipedia.NoExoticSixSphere.SmoothSphereBasepointAdjustment

/-!
# The actual sixth-stem stages and native homotopy groups

The sphere maps defining the existing stages are identified with Mathlib's
actual cube-relative homotopy groups. Simple connectivity of the target
turns ordinary homotopies into based ones. Thus forgetting the basepoint
is a proved equivalence here, not a definition of a replacement group.
-/

noncomputable section

open Function

namespace NoExoticSixSphere.SmoothCube

theorem sphereClass_basedEquiv_symm {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}
    (hn : 0 < n) (p : GenLoop (Fin n) X x) :
    sphereClass ((basedEquiv hn).symm p) = (⟦p⟧ : HomotopyGroup (Fin n) X x) := by
  change (⟦basedEquiv hn ((basedEquiv hn).symm p)⟧ : HomotopyGroup (Fin n) X x) = ⟦p⟧
  rw [Equiv.apply_symm_apply]

end NoExoticSixSphere.SmoothCube

namespace NoExoticSixSphere.StableSixSphereMaps

open SmoothCube

abbrev NativeStage (k : ℕ) :=
  HomotopyGroup (Fin (k + 8)) (Sphere (k + 2)) (spherePole (k + 2))

def ofNative {k : ℕ} : NativeStage k → Stage k :=
  Quotient.lift (fun p ↦ classOf ((basedEquiv (by omega : 0 < k + 8)).symm p).val)
    (by
      intro p q h
      apply (classOf_eq_iff _ _).mpr
      apply ContinuousMap.HomotopicRel.homotopic
      apply (sphereClass_eq_iff (by omega : 0 < k + 8) _ _).mp
      rw [sphereClass_basedEquiv_symm, sphereClass_basedEquiv_symm]
      exact Quotient.sound h)

theorem ofNative_sphereClass {k : ℕ}
    (f : BasedMap (k + 8) (Sphere (k + 2)) (spherePole (k + 2))) :
    ofNative (sphereClass f) = classOf f.val := by
  change classOf (((basedEquiv (by omega : 0 < k + 8)).symm
    (basedEquiv (by omega : 0 < k + 8) f)).val) = classOf f.val
  rw [Equiv.symm_apply_apply]

theorem ofNative_injective (k : ℕ) : Injective (ofNative (k := k)) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h p =>
    induction y using Quotient.inductionOn with
    | h q =>
      intro he
      let P := (basedEquiv (by omega : 0 < k + 8)).symm p
      let Q := (basedEquiv (by omega : 0 < k + 8)).symm q
      have hmap : P.val.Homotopic Q.val := (classOf_eq_iff _ _).mp he
      have hrel : P.val.HomotopicRel Q.val {spherePole (k + 8)} :=
        (sphere_homotopicRel_point_iff (spherePole (k + 8))
          (P.property.trans Q.property.symm)).mpr hmap
      have hclass := (sphereClass_eq_iff (by omega : 0 < k + 8) P Q).mpr hrel
      exact (sphereClass_basedEquiv_symm _ p).symm.trans
        (hclass.trans (sphereClass_basedEquiv_symm _ q))

theorem ofNative_surjective (k : ℕ) : Surjective (ofNative (k := k)) := by
  intro x
  induction x using Quotient.inductionOn with
  | h f =>
    obtain ⟨F, hF⟩ := exists_based_map_homotopic (by omega : 0 < k + 8) f
      (spherePole (k + 2))
    refine ⟨sphereClass F, ?_⟩
    rw [ofNative_sphereClass]
    exact (classOf_eq_iff _ _).mpr hF.symm

def nativeStageEquiv (k : ℕ) : NativeStage k ≃ Stage k :=
  Equiv.ofBijective ofNative ⟨ofNative_injective k, ofNative_surjective k⟩

theorem nativeStageEquiv_sphereClass {k : ℕ}
    (f : BasedMap (k + 8) (Sphere (k + 2)) (spherePole (k + 2))) :
    nativeStageEquiv k (sphereClass f) = classOf f.val := ofNative_sphereClass f

theorem nativeStageEquiv_one (k : ℕ) : nativeStageEquiv k 1 = stageZero k := by
  let f : BasedMap (k + 8) (Sphere (k + 2)) (spherePole (k + 2)) :=
    ⟨ContinuousMap.const _ (spherePole (k + 2)), rfl⟩
  have hf : sphereClass f = (1 : NativeStage k) := by
    rw [HomotopyGroup.one_def]
    rfl
  rw [← hf, nativeStageEquiv_sphereClass]
  rfl

theorem nativeStageEquiv_eq_stageZero_iff {k : ℕ} (x : NativeStage k) :
    nativeStageEquiv k x = stageZero k ↔ x = 1 := by
  rw [← nativeStageEquiv_one k, (nativeStageEquiv k).injective.eq_iff]

end NoExoticSixSphere.StableSixSphereMaps
