import Wikipedia.HopfProblem.DegreeCollapseSurgeryNativeEndComparison
import Wikipedia.SmoothSixDPoincare.FramedSurgeryBeltComplement

/-!
# The exact native surgery-end homology sequence with its actual belt map

The attaching sphere of the reverse core is the canonical embedded belt
sphere. Transport the genuine cell sequence through the explicit native
end comparison. The maps at the old term are exactly the original belt
map and native boundary inclusion; the connecting map comes from the
actual reverse attachment, not an abstractly chosen exact sequence.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TraceBody

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
open Wikipedia.SmoothSixDPoincare
open SingularMayerVietoris PeriodTorusHigherHomology

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

def nativeBeltMap : C(Sphere 2, UnitSurgery.Target A hR) :=
  FramedSurgery.beltMap (E := Vector 4) (UnitSurgery.face A hR) 2

def nativeOldHomeomorph : UnitSurgery.Target A hR ≃ₜ (reverseCorePresentation A hR).old :=
  (flatBoundaryHomeomorph A hR).trans (flatOldHomeomorph A hR)

def nativeOldHomologyEquiv (n : ℕ) : SingularHomology (UnitSurgery.Target A hR) n ≃ₗ[ℤ]
    SingularHomology (reverseCorePresentation A hR).old n :=
  homotopyEquivHomologyEquiv (nativeOldHomeomorph A hR).toHomotopyEquiv n

theorem reverse_attachingSphere_eq_belt : (reverseCorePresentation A hR).attachingSphere =
    (nativeOldHomeomorph A hR).toHomotopyEquiv.toFun.comp (nativeBeltMap A hR) := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  apply Subtype.ext
  change A.map (0, s.val) = (flatBoundaryHomeomorph A hR
    (FramedSurgery.beltMap (E := Vector 4) (UnitSurgery.face A hR) 2 s)).val
  rw [FramedSurgery.beltMap_eq_closedNewMap, flatBoundaryHomeomorph_newFace]
  rfl

theorem native_attaching_homology_compare (n : ℕ) (u : SingularHomology (Sphere 2) n) :
    (reverseCorePresentation A hR).attachingHomologyMap n u =
      nativeOldHomologyEquiv A hR n (singularHomologyMap (nativeBeltMap A hR) n u) := by
  change singularHomologyMap (reverseCorePresentation A hR).attachingSphere n u = _
  rw [reverse_attachingSphere_eq_belt, singularHomologyMap_comp, LinearMap.comp_apply]
  rfl

theorem native_old_homology_compare (n : ℕ) (u : SingularHomology (UnitSurgery.Target A hR) n) :
    reverseCoreHomologyEquiv A hR n ((reverseCorePresentation A hR).oldHomologyMap n
      (nativeOldHomologyEquiv A hR n u)) =
        singularHomologyMap (nativeTargetInclusion A hR) n u := by
  let B := reverseCoreUnionTraceHomotopyEquiv A hR
  let old := subtypeInclusion (reverseCorePresentation A hR).old
  have hmaps : (B.toFun.comp old).comp
      (nativeOldHomeomorph A hR).toHomotopyEquiv.toFun = flatTargetInclusion A hR := by
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (reverseCoreUnionTraceHomotopyEquiv_ambient A hR _)
  rw [nativeTarget_homology_eq_flat]
  change singularHomologyMap B.toFun n
    (singularHomologyMap old n (singularHomologyMap
      (nativeOldHomeomorph A hR).toHomotopyEquiv.toFun n u)) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    ← LinearMap.comp_apply, ← singularHomologyMap_comp, hmaps]

theorem native_end_exact (n : ℕ) (hn : n ≠ 0) :
    LinearMap.range (singularHomologyMap (nativeBeltMap A hR) n) =
      LinearMap.ker (singularHomologyMap (nativeTargetInclusion A hR) n) := by
  refine HomologyTransport.exact_of_equivalences (LinearEquiv.refl ℤ _)
    (nativeOldHomologyEquiv A hR n).symm (reverseCoreHomologyEquiv A hR n)
    ((reverseCorePresentation A hR).attachingHomologyMap n)
    ((reverseCorePresentation A hR).oldHomologyMap n)
    (singularHomologyMap (nativeBeltMap A hR) n) _ ?_ ?_
    ((reverseCorePresentation A hR).cell_exact_at_old n hn)
  · intro u
    change singularHomologyMap (nativeBeltMap A hR) n u =
      (nativeOldHomologyEquiv A hR n).symm
        ((reverseCorePresentation A hR).attachingHomologyMap n u)
    rw [native_attaching_homology_compare, LinearEquiv.symm_apply_apply]
  · intro u
    have h := native_old_homology_compare A hR n ((nativeOldHomologyEquiv A hR n).symm u)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

def nativeConnecting (k : ℕ) : SingularHomology (ambientSet A) (k + 1) →ₗ[ℤ]
    SingularHomology (Sphere 2) k :=
  ((reverseCorePresentation A hR).cellConnectingMap k).comp
    (reverseCoreHomologyEquiv A hR (k + 1)).symm.toLinearMap

theorem nativeConnecting_compare (k : ℕ)
    (u : SingularHomology ↥(flatBoundarySet A hR ∪ range (reverseCoreMap A hR)) (k + 1)) :
    nativeConnecting A hR k (reverseCoreHomologyEquiv A hR (k + 1) u) =
      (reverseCorePresentation A hR).cellConnectingMap k u := by
  change (reverseCorePresentation A hR).cellConnectingMap k
    ((reverseCoreHomologyEquiv A hR (k + 1)).symm (reverseCoreHomologyEquiv A hR (k + 1) u)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem native_end_exact_at_trace (k : ℕ) :
    LinearMap.range (singularHomologyMap (nativeTargetInclusion A hR) (k + 1)) =
      LinearMap.ker (nativeConnecting A hR k) := by
  refine HomologyTransport.exact_of_equivalences
    (nativeOldHomologyEquiv A hR (k + 1)).symm (reverseCoreHomologyEquiv A hR (k + 1))
    (LinearEquiv.refl ℤ _) ((reverseCorePresentation A hR).oldHomologyMap (k + 1))
    ((reverseCorePresentation A hR).cellConnectingMap k)
    (singularHomologyMap (nativeTargetInclusion A hR) (k + 1)) (nativeConnecting A hR k) ?_ ?_
    ((reverseCorePresentation A hR).cell_exact_at_ambient k)
  · intro u
    have h := native_old_homology_compare A hR (k + 1)
      ((nativeOldHomologyEquiv A hR (k + 1)).symm u)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  · exact nativeConnecting_compare A hR k

theorem native_end_exact_at_belt (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (nativeConnecting A hR k) =
      LinearMap.ker (singularHomologyMap (nativeBeltMap A hR) k) := by
  refine HomologyTransport.exact_of_equivalences (reverseCoreHomologyEquiv A hR (k + 1))
    (LinearEquiv.refl ℤ _) (nativeOldHomologyEquiv A hR k).symm
    ((reverseCorePresentation A hR).cellConnectingMap k)
    ((reverseCorePresentation A hR).attachingHomologyMap k)
    (nativeConnecting A hR k) (singularHomologyMap (nativeBeltMap A hR) k) ?_ ?_
    ((reverseCorePresentation A hR).cell_exact_at_sphere k hk)
  · exact nativeConnecting_compare A hR k
  · intro u
    change singularHomologyMap (nativeBeltMap A hR) k u =
      (nativeOldHomologyEquiv A hR k).symm
        ((reverseCorePresentation A hR).attachingHomologyMap k u)
    rw [native_attaching_homology_compare, LinearEquiv.symm_apply_apply]

end Wikipedia.HopfProblem.DegreeCollapse.TraceBody
