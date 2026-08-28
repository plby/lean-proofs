import Wikipedia.NoExoticSixSphere.PartialFrameBasepointAlignment
import Wikipedia.NoExoticSixSphere.PartialFrameBasedParity
import Wikipedia.NoExoticSixSphere.InjectiveOperatorSphereParity

/-!
# Frame parity completely classifies free sphere maps

Path connectedness and actual ambient path transport align the two
basepoints. The checked based classification then supplies a genuine free
homotopy. Normalization extends this completeness statement to the original
injective-operator sphere maps.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse

theorem sphereThirdObstruction_eq_iff_homotopic (r : ℕ)
    (f g : C(Sphere 3, Space (3 + (r + 2)) (r + 2))) :
    sphereThirdObstruction r f = sphereThirdObstruction r g ↔ f.Homotopic g := by
  constructor
  · intro h
    let : PathConnectedSpace (Space (3 + (r + 2)) (r + 2)) :=
      pathConnectedSpace (by decide : 0 < 3) (r + 2)
    let p := SphereCube.point 3
    let γ := PathConnectedSpace.somePath (f p) (g p)
    obtain ⟨f', H, hp⟩ := FramePath.exists_homotopic_with_value (d := 3)
      (by omega) f p (g p) γ
    have he : sphereThirdObstruction r f' = sphereThirdObstruction r g :=
      (sphereThirdObstruction_homotopic r H).symm.trans h
    obtain ⟨K⟩ := (sphereThirdObstruction_eq_iff_homotopicRel r f' g hp).mp he
    exact H.trans ⟨K.toHomotopy⟩
  · intro h
    exact sphereThirdObstruction_homotopic r h

namespace Monomorphism

theorem normalize_homotopic_iff {X : Type*} [TopologicalSpace X] {N n : ℕ}
    (f g : C(X, Space N n)) :
    ((normalize N n).comp f).Homotopic ((normalize N n).comp g) ↔ f.Homotopic g := by
  constructor
  · rintro ⟨H⟩
    let Hf := (normalizationHomotopy N n).compContinuousMap f
    let Hg := (normalizationHomotopy N n).compContinuousMap g
    let K := (ContinuousMap.Homotopy.refl (inclusion N n)).comp H
    exact ⟨Hf.trans (K.trans Hg.symm)⟩
  · rintro ⟨H⟩
    exact ⟨(ContinuousMap.Homotopy.refl (normalize N n)).comp H⟩

theorem sphereParity_eq_iff_homotopic (r : ℕ)
    (f g : C(Sphere 3, Space (3 + (r + 2)) (r + 2))) :
    sphereParity r f = sphereParity r g ↔ f.Homotopic g := by
  exact (sphereThirdObstruction_eq_iff_homotopic r
    ((normalize _ _).comp f) ((normalize _ _).comp g)).trans (normalize_homotopic_iff f g)

end Monomorphism
end NoExoticSixSphere.Stiefel
