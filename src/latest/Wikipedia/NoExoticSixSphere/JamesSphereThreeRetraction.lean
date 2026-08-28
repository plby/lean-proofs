import Wikipedia.NoExoticSixSphere.JamesSphereThreeAttaching

/-!
# Quaternion evaluation splits the actual three-sphere suspension in every degree

Multiplication of the original quaternion letters defines a continuous
map out of the full James space. Its restriction to the actual one-letter
sphere is the identity. The proved all-degree James comparison therefore
gives a left inverse to the original cubical suspension, without using
EHP outside its established metastable range.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem.UnitQuaternionSphere

namespace NoExoticSixSphere.JamesSphere.ThreeRetraction

def wordEvaluation : C(WordHomology.Words 3, UnitQuaternions) :=
  ⟨James.lift (spherePole 3) sphereHomeomorph.symm,
    James.continuous_lift (spherePole 3) sphereHomeomorph.symm
      ThreeAttaching.inverse_pole sphereHomeomorph.symm.continuous⟩

def retraction : C(WordHomology.Words 3, Sphere 3) :=
  (sphereHomeomorph : C(UnitQuaternions, Sphere 3)).comp wordEvaluation

theorem retraction_one : retraction 1 = spherePole 3 := by
  change sphereHomeomorph (James.lift (spherePole 3) sphereHomeomorph.symm 1) = _
  rw [map_one]
  exact ThreeAttaching.quaternion_one_pole

theorem retraction_inclusion (x : Sphere 3) : retraction (inclusion 3 x) = x := by
  change sphereHomeomorph
    (James.lift (spherePole 3) sphereHomeomorph.symm (James.letter (spherePole 3) x)) = x
  rw [James.lift_letter (spherePole 3) sphereHomeomorph.symm ThreeAttaching.inverse_pole]
  exact sphereHomeomorph.apply_symm_apply x

def retractionHom (d : ℕ) [NeZero d] :=
  HigherHomotopy.mapMonoidHom (N := Fin d) retraction retraction_one

theorem retractionHom_inclusion (d : ℕ) [NeZero d] (c : π_ d (Sphere 3) (spherePole 3)) :
    retractionHom d
      (HigherHomotopy.map (N := Fin d) (inclusion 3) (NativeHopf.inclusion_pole 3) c) = c := by
  refine Quotient.inductionOn c fun p ↦ ?_
  apply congrArg (fun q : GenLoop (Fin d) (Sphere 3) (spherePole 3) ↦
    (Quotient.mk _ q : π_ d (Sphere 3) (spherePole 3)))
  apply Subtype.ext
  apply ContinuousMap.ext
  intro u
  exact retraction_inclusion (p.val u)

def sectionHom (d : ℕ) [NeZero d] :=
  (retractionHom d).comp
    (InclusionRange.orderedComparison 3 (by decide) d).symm.toMonoidHom

theorem sectionHom_suspension (d : ℕ) [NeZero d] (c : π_ d (Sphere 3) (spherePole 3)) :
    sectionHom d (CubicalSphereSuspension.hom d 3 c) = c := by
  change retractionHom d ((InclusionRange.orderedComparison 3 (by decide) d).symm
    (CubicalSphereSuspension.hom d 3 c)) = c
  rw [← InclusionRange.orderedComparison_inclusion 3 (by decide) d c,
    MulEquiv.symm_apply_apply]
  exact retractionHom_inclusion d c

theorem suspension_injective (d : ℕ) [NeZero d] :
    Function.Injective (CubicalSphereSuspension.hom d 3) :=
  (show Function.LeftInverse (sectionHom d) (CubicalSphereSuspension.hom d 3) from
    sectionHom_suspension d).injective

end NoExoticSixSphere.JamesSphere.ThreeRetraction
