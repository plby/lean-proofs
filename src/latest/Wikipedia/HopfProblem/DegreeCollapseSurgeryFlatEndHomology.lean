import Wikipedia.HopfProblem.DegreeCollapseSurgeryReverseCore

/-!
# Middle homology injects from the actual flat surgery boundary

The reverse core is a three-cell. Its attaching two-sphere has zero third
homology, so the literal flat-boundary inclusion is injective on H3.
Transporting through the checked closed-piece homeomorphism gives the
corresponding map from the original canonical surgery target. Comparing
this flat representative with the native rounded-end inclusion remains a
separate geometric obligation.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TraceBody

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open Wikipedia.SmoothSixDPoincare
open SingularMayerVietoris PeriodTorusHigherHomology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

def flatOldHomeomorph : flatBoundarySet A hR ≃ₜ (reverseCorePresentation A hR).old where
  toFun x := ⟨⟨x.val, Or.inl x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def flatBoundaryInclusion : C(flatBoundarySet A hR, RoundedTrace.ambientSet A) :=
  ⟨fun x ↦ ⟨x.val, RoundedTrace.unrounded_subset A
      (body_subset_unrounded A (flatBoundary_subset_body A hR x.property))⟩,
    continuous_subtype_val.subtype_mk _⟩

def flatOldHomologyEquiv (n : ℕ) : SingularHomology (flatBoundarySet A hR) n ≃ₗ[ℤ]
    SingularHomology (reverseCorePresentation A hR).old n :=
  homotopyEquivHomologyEquiv (flatOldHomeomorph A hR).toHomotopyEquiv n

def reverseCoreHomologyEquiv (n : ℕ) :
    SingularHomology ↥(flatBoundarySet A hR ∪ range (reverseCoreMap A hR)) n ≃ₗ[ℤ]
      SingularHomology (RoundedTrace.ambientSet A) n :=
  homotopyEquivHomologyEquiv (reverseCoreUnionTraceHomotopyEquiv A hR) n

theorem flat_old_homology_compare (n : ℕ) (u : SingularHomology (flatBoundarySet A hR) n) :
    reverseCoreHomologyEquiv A hR n ((reverseCorePresentation A hR).oldHomologyMap n
      (flatOldHomologyEquiv A hR n u)) =
        singularHomologyMap (flatBoundaryInclusion A hR) n u := by
  let B := reverseCoreUnionTraceHomotopyEquiv A hR
  let old := subtypeInclusion (reverseCorePresentation A hR).old
  have hmaps : (B.toFun.comp old).comp
      (flatOldHomeomorph A hR).toHomotopyEquiv.toFun = flatBoundaryInclusion A hR := by
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (reverseCoreUnionTraceHomotopyEquiv_ambient A hR _)
  change singularHomologyMap B.toFun n
    (singularHomologyMap old n (singularHomologyMap
      (flatOldHomeomorph A hR).toHomotopyEquiv.toFun n u)) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    ← LinearMap.comp_apply, ← singularHomologyMap_comp, hmaps]

theorem flatBoundary_homology_injective_three :
    Injective (singularHomologyMap (flatBoundaryInclusion A hR) 3) := by
  let : Subsingleton (SingularHomology (Sphere 2) 3) :=
    SphereHomology.unitSphere_homology_subsingleton 1 3 (by decide) (by decide)
  have hold : Injective ((reverseCorePresentation A hR).oldHomologyMap 3) := by
    apply LinearMap.ker_eq_bot.mp
    rw [← (reverseCorePresentation A hR).cell_exact_at_old 3 (by decide)]
    apply bot_unique
    rintro y ⟨x, rfl⟩
    change (reverseCorePresentation A hR).attachingHomologyMap 3 x = 0
    rw [Subsingleton.elim x 0, map_zero]
  intro x y h
  apply (flatOldHomologyEquiv A hR 3).injective
  apply hold
  apply (reverseCoreHomologyEquiv A hR 3).injective
  rw [flat_old_homology_compare, flat_old_homology_compare, h]

def flatTargetInclusion : C(UnitSurgery.Target A hR, RoundedTrace.ambientSet A) :=
  (flatBoundaryInclusion A hR).comp (flatBoundaryHomeomorph A hR).toHomotopyEquiv.toFun

theorem flatTarget_homology_injective_three :
    Injective (singularHomologyMap (flatTargetInclusion A hR) 3) := by
  change Injective (singularHomologyMap ((flatBoundaryInclusion A hR).comp
    (flatBoundaryHomeomorph A hR).toHomotopyEquiv.toFun) 3)
  rw [singularHomologyMap_comp]
  exact (flatBoundary_homology_injective_three A hR).comp
    (homotopyEquivHomologyEquiv (flatBoundaryHomeomorph A hR).toHomotopyEquiv 3).injective

end Wikipedia.HopfProblem.DegreeCollapse.TraceBody
