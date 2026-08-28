import Wikipedia.NoExoticSixSphere.SmoothSphereCubeReflection
import Wikipedia.NoExoticSixSphere.LoopSpaceNativeReversal
import Wikipedia.NoExoticSixSphere.JamesSphereMeridianCommutator

/-!
# Reversed meridians and an actual reflection of the letter sphere

Both reversal in path time and reflection of one sphere-cube coordinate
act by inversion on the original native class. The cube/sphere homotopy
correspondence gives a based path-family homotopy. The actual Moore
normalization equivalence then supplies an ordinary Moore-family
homotopy, which is sufficient for induced homology maps. No based
inverse for Moore normalization is assumed.
-/

noncomputable section

open scoped Topology unitInterval

namespace NoExoticSixSphere.Moore.Loop

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {y₀ : Y}

theorem homotopic_of_normalization (f g : C(X, Loop y₀))
    (h : (normalizationMap.comp f).Homotopic (normalizationMap.comp g)) : f.Homotopic g := by
  have hf : f.Homotopic (realizationMap.comp (normalizationMap.comp f)) :=
    ⟨adjustmentHomotopy.compContinuousMap f⟩
  have hg : g.Homotopic (realizationMap.comp (normalizationMap.comp g)) :=
    ⟨adjustmentHomotopy.compContinuousMap g⟩
  exact hf.trans (((ContinuousMap.Homotopic.refl realizationMap).comp h).trans hg.symm)

end NoExoticSixSphere.Moore.Loop

namespace NoExoticSixSphere.JamesSphere.MeridianCommutator

def meridianPaths (n : ℕ) : C(Sphere n, Path (spherePole (n + 1)) (spherePole (n + 1))) :=
  ⟨unitLoop n, continuous_unitLoop n⟩

theorem reversed_meridian_paths (n : ℕ) [NeZero n] (hn : 0 < n) (i : Fin n) :
    ((GeneralizedLoopCurrying.reverseMap (spherePole (n + 1))).comp (meridianPaths n)).HomotopicRel
      ((meridianPaths n).comp (SmoothCube.reflection n hn i)) {spherePole n} := by
  let f : SmoothCube.BasedMap n
      (Path (spherePole (n + 1)) (spherePole (n + 1))) (Path.refl (spherePole (n + 1))) :=
    ⟨meridianPaths n, unitLoop_pole n⟩
  let g : SmoothCube.BasedMap n
      (Path (spherePole (n + 1)) (spherePole (n + 1))) (Path.refl (spherePole (n + 1))) :=
    ⟨(GeneralizedLoopCurrying.reverseMap (spherePole (n + 1))).comp (meridianPaths n),
      (congrArg (GeneralizedLoopCurrying.reverseMap (spherePole (n + 1)))
        (unitLoop_pole n)).trans (GeneralizedLoopCurrying.reverseMap_refl _)⟩
  apply (SmoothCube.sphereClass_eq_iff hn g (SmoothCube.reflected hn i f)).mp
  exact (GeneralizedLoopCurrying.reverse_native (SmoothCube.sphereClass f)).trans
    (SmoothCube.reflected_sphereClass hn i f).symm

def reversedMeridians (n : ℕ) : C(Sphere n, Moore.Loop (spherePole (n + 1))) :=
  Moore.Loop.reverseMap.comp (meridians n)

theorem reversedMeridians_normalization (n : ℕ) :
    Moore.Loop.normalizationMap.comp (reversedMeridians n) =
      (GeneralizedLoopCurrying.reverseMap (spherePole (n + 1))).comp (meridianPaths n) := by
  apply ContinuousMap.ext
  intro x
  exact (Moore.Loop.toPath_reverse (mooreGenerator n x)).trans
    (congrArg Path.symm (toPath_mooreGenerator n x))

theorem reflectedMeridians_normalization (n : ℕ) (hn : 0 < n) (i : Fin n) :
    Moore.Loop.normalizationMap.comp ((meridians n).comp (SmoothCube.reflection n hn i)) =
      (meridianPaths n).comp (SmoothCube.reflection n hn i) := by
  apply ContinuousMap.ext
  intro x
  exact toPath_mooreGenerator n _

theorem reversed_meridians (n : ℕ) [NeZero n] (hn : 0 < n) (i : Fin n) :
    (reversedMeridians n).Homotopic ((meridians n).comp (SmoothCube.reflection n hn i)) := by
  apply Moore.Loop.homotopic_of_normalization
  rw [reversedMeridians_normalization, reflectedMeridians_normalization]
  exact (reversed_meridian_paths n hn i).homotopic

end NoExoticSixSphere.JamesSphere.MeridianCommutator
