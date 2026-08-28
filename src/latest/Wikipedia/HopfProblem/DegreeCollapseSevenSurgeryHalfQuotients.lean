import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryHalfHomology
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Integral homology comparisons retaining both actual half inclusions

Degree three of the common body is the old half modulo the original
attaching image, and also the new half modulo the actual belt image.
The equivalences preserve the actual maps, including any integral torsion.
Away from degrees three and four, the endpoint maps are isomorphisms in
all degrees at least two.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization
open SingularMayerVietoris

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2) (T : TimeData A)

local instance : CompactSpace (PositiveHalf A hR T) := compactSpace_positiveHalf A hR T

def oldHalfQuotientEquiv :
    (SingularHomology (OldPositiveHalf A T) 3 ⧸
      LinearMap.range (singularHomologyMap (halfAttachingSphere A hR T) 3)) ≃ₗ[ℤ]
        SingularHomology (HalfBody A hR T) 3 := by
  let e := (Submodule.quotEquivOfEq _ _ (half_exact_at_old A hR T 3 (by decide))).trans
    ((singularHomologyMap (oldHalfInclusion A hR T) 3).quotKerEquivOfSurjective
      (oldHalf_surjective_three A hR T))
  let ea : (SingularHomology (OldPositiveHalf A T) 3 ⧸
      LinearMap.range (singularHomologyMap (halfAttachingSphere A hR T) 3)) ≃+
        SingularHomology (HalfBody A hR T) 3 := {
    toEquiv := e.toEquiv
    map_add' := fun x y ↦ e.map_add' x y }
  exact ea.toIntLinearEquiv

theorem oldHalfQuotientEquiv_mk (x : SingularHomology (OldPositiveHalf A T) 3) :
    oldHalfQuotientEquiv A hR T (Submodule.Quotient.mk x) =
      singularHomologyMap (oldHalfInclusion A hR T) 3 x := by
  change (singularHomologyMap (oldHalfInclusion A hR T) 3).quotKerEquivOfSurjective
    (oldHalf_surjective_three A hR T)
    (Submodule.quotEquivOfEq _ _ (half_exact_at_old A hR T 3 (by decide))
      (Submodule.Quotient.mk x)) = _
  rw [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

def newHalfQuotientEquiv :
    (SingularHomology (PositiveHalf A hR T) 3 ⧸
      LinearMap.range (singularHomologyMap (halfBeltSphere A hR T) 3)) ≃ₗ[ℤ]
        SingularHomology (HalfBody A hR T) 3 := by
  let e := (Submodule.quotEquivOfEq _ _ (half_exact_at_new A hR T 3 (by decide))).trans
    ((singularHomologyMap (newHalfInclusion A hR T) 3).quotKerEquivOfSurjective
      (newHalf_surjective_three A hR T))
  let ea : (SingularHomology (PositiveHalf A hR T) 3 ⧸
      LinearMap.range (singularHomologyMap (halfBeltSphere A hR T) 3)) ≃+
        SingularHomology (HalfBody A hR T) 3 := {
    toEquiv := e.toEquiv
    map_add' := fun x y ↦ e.map_add' x y }
  exact ea.toIntLinearEquiv

theorem newHalfQuotientEquiv_mk (x : SingularHomology (PositiveHalf A hR T) 3) :
    newHalfQuotientEquiv A hR T (Submodule.Quotient.mk x) =
      singularHomologyMap (newHalfInclusion A hR T) 3 x := by
  change (singularHomologyMap (newHalfInclusion A hR T) 3).quotKerEquivOfSurjective
    (newHalf_surjective_three A hR T)
    (Submodule.quotEquivOfEq _ _ (half_exact_at_new A hR T 3 (by decide))
      (Submodule.Quotient.mk x)) = _
  rw [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

def halfQuotientEquiv :
    (SingularHomology (OldPositiveHalf A T) 3 ⧸
      LinearMap.range (singularHomologyMap (halfAttachingSphere A hR T) 3)) ≃ₗ[ℤ]
    (SingularHomology (PositiveHalf A hR T) 3 ⧸
      LinearMap.range (singularHomologyMap (halfBeltSphere A hR T) 3)) :=
  (oldHalfQuotientEquiv A hR T).trans (newHalfQuotientEquiv A hR T).symm

theorem halfQuotientEquiv_body (x : SingularHomology (OldPositiveHalf A T) 3) :
    newHalfQuotientEquiv A hR T (halfQuotientEquiv A hR T (Submodule.Quotient.mk x)) =
      singularHomologyMap (oldHalfInclusion A hR T) 3 x := by
  change newHalfQuotientEquiv A hR T ((newHalfQuotientEquiv A hR T).symm
    (oldHalfQuotientEquiv A hR T (Submodule.Quotient.mk x))) = _
  rw [LinearEquiv.apply_symm_apply, oldHalfQuotientEquiv_mk]

theorem oldHalf_bijective_other (k : ℕ) (hk : 0 < k)
    (hk3 : k + 1 ≠ 3) (hk4 : k + 1 ≠ 4) :
    Bijective (singularHomologyMap (oldHalfInclusion A hR T) (k + 1)) := by
  let : Subsingleton (SingularHomology (Sphere 3) k) :=
    SphereHomology.unitSphere_homology_subsingleton 2 k (by omega) (by omega)
  let : Subsingleton (SingularHomology (Sphere 3) (k + 1)) :=
    SphereHomology.unitSphere_homology_subsingleton 2 (k + 1) (by omega) hk3
  exact ⟨(SurgeryPairBody.oldHandleData (halfBoundaryPair A hR T)).old_injective (k + 1)
    (Nat.succ_ne_zero k),
    (SurgeryPairBody.oldHandleData (halfBoundaryPair A hR T)).old_surjective k⟩

theorem newHalf_bijective_other (k : ℕ) (hk : 0 < k)
    (hk3 : k + 1 ≠ 3) (hk4 : k + 1 ≠ 4) :
    Bijective (singularHomologyMap (newHalfInclusion A hR T) (k + 1)) := by
  let : Subsingleton (SingularHomology (Sphere 3) k) :=
    SphereHomology.unitSphere_homology_subsingleton 2 k (by omega) (by omega)
  let : Subsingleton (SingularHomology (Sphere 3) (k + 1)) :=
    SphereHomology.unitSphere_homology_subsingleton 2 (k + 1) (by omega) hk3
  exact ⟨(SurgeryPairBody.newHandleData (halfBoundaryPair A hR T)).old_injective (k + 1)
    (Nat.succ_ne_zero k),
    (SurgeryPairBody.newHandleData (halfBoundaryPair A hR T)).old_surjective k⟩

def halfHomologyEquivOther (k : ℕ) (hk : 0 < k) (hk3 : k + 1 ≠ 3) (hk4 : k + 1 ≠ 4) :
    SingularHomology (OldPositiveHalf A T) (k + 1) ≃ₗ[ℤ]
      SingularHomology (PositiveHalf A hR T) (k + 1) :=
  (LinearEquiv.ofBijective (singularHomologyMap (oldHalfInclusion A hR T) (k + 1))
    (oldHalf_bijective_other A hR T k hk hk3 hk4)).trans
      (LinearEquiv.ofBijective (singularHomologyMap (newHalfInclusion A hR T) (k + 1))
        (newHalf_bijective_other A hR T k hk hk3 hk4)).symm

theorem halfHomologyEquivOther_body (k : ℕ) (hk : 0 < k)
    (hk3 : k + 1 ≠ 3) (hk4 : k + 1 ≠ 4)
    (x : SingularHomology (OldPositiveHalf A T) (k + 1)) :
    singularHomologyMap (newHalfInclusion A hR T) (k + 1)
      (halfHomologyEquivOther A hR T k hk hk3 hk4 x) =
        singularHomologyMap (oldHalfInclusion A hR T) (k + 1) x :=
  (LinearEquiv.ofBijective (singularHomologyMap (newHalfInclusion A hR T) (k + 1))
    (newHalf_bijective_other A hR T k hk hk3 hk4)).apply_symm_apply _

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
