import Wikipedia.HopfProblem.DegreeCollapseSphereAdjunction
import Wikipedia.HopfProblem.DegreeCollapseGroupSpherePrecomposition
import Wikipedia.NoExoticSixSphere.JamesSphereOrderedLoopComparison
import Wikipedia.NoExoticSixSphere.JamesSphereThreeRetraction

/-!
# The actual quaternion James retraction under suspended precomposition

Choose an original James-space representative of a sphere class.
The ordered loop comparison identifies its loop-space representative
with the actual sphere adjoint. Precomposition preserves that based
homotopy, so the retraction of a suspended composite is the composite
of the original retracted representative with the unsuspended map.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.JamesRetractionComposition

open NoExoticSixSphere SmoothCube SphereLiftFamily CubicalSphereSuspension
open JamesSphere

variable {m n : ℕ} [NeZero m] [NeZero n]

def wordRepresentative (f : SphereComposition.Based (n + 1) 4) :
    BasedMap n (WordHomology.Words 3) 1 :=
  Classical.choose (sphereClass_surjective (Nat.pos_of_neZero n)
    ((InclusionRange.orderedComparison 3 (by decide) n).symm (sphereClass f)))

theorem wordRepresentative_class (f : SphereComposition.Based (n + 1) 4) :
    sphereClass (wordRepresentative f) =
      (InclusionRange.orderedComparison 3 (by decide) n).symm (sphereClass f) :=
  Classical.choose_spec (sphereClass_surjective (Nat.pos_of_neZero n)
    ((InclusionRange.orderedComparison 3 (by decide) n).symm (sphereClass f)))

def loopRepresentative (q : BasedMap n (WordHomology.Words 3) 1) :
    BasedMap n (Path (spherePole 4) (spherePole 4)) (Path.refl (spherePole 4)) :=
  ⟨(AttachingSquare.orderedLoopComparison 3).comp q.val,
    (congrArg (AttachingSquare.orderedLoopComparison 3) q.property).trans
      (AttachingSquare.orderedLoopComparison_one 3)⟩

theorem wordRepresentative_loop_class (f : SphereComposition.Based (n + 1) 4) :
    sphereClass (loopRepresentative (wordRepresentative f)) =
      sphereClass (SphereAdjunction.adjoint f) := by
  apply (GeneralizedLoopCurrying.homotopyMulEquiv n (spherePole 4)).injective
  rw [SphereAdjunction.adjoint_native]
  calc
    GeneralizedLoopCurrying.homotopyMulEquiv n (spherePole 4)
        (sphereClass (loopRepresentative (wordRepresentative f))) =
      InclusionRange.orderedComparison 3 (by decide) n
        (sphereClass (wordRepresentative f)) :=
      (AttachingSquare.orderedComparison_loopMap 3 (by decide) n
        (sphereClass (wordRepresentative f))).symm
    _ = sphereClass f := by rw [wordRepresentative_class, MulEquiv.apply_symm_apply]

theorem word_precomposition (f : SphereComposition.Based (n + 1) 4)
    (g : SphereComposition.Based m n) :
    InclusionRange.orderedComparison 3 (by decide) m
      (sphereClass (compose (wordRepresentative f) g)) =
        sphereClass (compose f (productBasedMap g)) := by
  rw [AttachingSquare.orderedComparison_loopMap]
  change GeneralizedLoopCurrying.homotopyMulEquiv m (spherePole 4)
    (sphereClass (compose (loopRepresentative (wordRepresentative f)) g)) = _
  rw [GroupSpherePrecomposition.compose_class_congr (wordRepresentative_loop_class f) g,
    ← SphereAdjunction.adjoint_compose]
  exact SphereAdjunction.adjoint_native (compose f (productBasedMap g))

def retractionRepresentative (f : SphereComposition.Based (n + 1) 4) :
    SphereComposition.Based n 3 :=
  ⟨ThreeRetraction.retraction.comp (wordRepresentative f).val,
    (congrArg ThreeRetraction.retraction (wordRepresentative f).property).trans
      ThreeRetraction.retraction_one⟩

theorem retractionRepresentative_class (f : SphereComposition.Based (n + 1) 4) :
    sphereClass (retractionRepresentative f) =
      ThreeRetraction.sectionHom n (sphereClass f) := by
  change ThreeRetraction.retractionHom n (sphereClass (wordRepresentative f)) = _
  rw [wordRepresentative_class]
  rfl

theorem retraction_precomposition (f : SphereComposition.Based (n + 1) 4)
    (g : SphereComposition.Based m n) :
    ThreeRetraction.sectionHom m (sphereClass (compose f (productBasedMap g))) =
      sphereClass (compose (retractionRepresentative f) g) := by
  rw [← word_precomposition f g]
  change ThreeRetraction.retractionHom m
    ((InclusionRange.orderedComparison 3 (by decide) m).symm
      (InclusionRange.orderedComparison 3 (by decide) m
        (sphereClass (compose (wordRepresentative f) g)))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.JamesRetractionComposition
