import Wikipedia.NoExoticSixSphere.RoundedTraceChosenCollapseHomotopy
import Wikipedia.NoExoticSixSphere.SphereCollapseRegularValue

/-!
# The actual trace preserves the homotopy class of its chosen sphere collapses

Conjugating the checked one-point homotopy by the stereographic
compactification homeomorphisms gives a based homotopy of actual sphere
maps. Relative smoothing then supplies homotopic smooth regular
representatives with exactly the original and surgery manifolds as fibers.
No nullhomotopy or filling is inferred from this comparison.
-/

noncomputable section

open Function Set Topology
open scoped Manifold ContDiff unitInterval

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def chosenOriginalSphereCollapse :
    C(Sphere (e.ambientDimension + 6), Sphere ((e.ambientDimension + 6) - 6)) :=
  (originalFramedTubeData A).collapseData.sphereMap

variable [T2Space M] (hR : A.radius = 2)

def chosenSurgerySphereCollapse :
    C(Sphere (e.ambientDimension + 6), Sphere ((e.ambientDimension + 6) - 6)) := by
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  let := UnitSurgery.compactSpace_target A hR
  exact (surgeryFramedTubeData A hR).collapseData.sphereMap

theorem exists_chosenEndSphereCollapse_homotopy :
    ∃ H : (chosenSurgerySphereCollapse A hR).Homotopy (chosenOriginalSphereCollapse A),
      ∀ t : I, H (t, sphereInfinity (e.ambientDimension + 6)) =
        sphereInfinity ((e.ambientDimension + 6) - 6) := by
  obtain ⟨H, hH⟩ := exists_chosenEndCollapse_homotopy A hR
  let S : C(Sphere (e.ambientDimension + 6), OnePoint (Vector (e.ambientDimension + 6))) :=
    ⟨(euclideanOnePointSphere (e.ambientDimension + 6)).symm,
      (euclideanOnePointSphere (e.ambientDimension + 6)).symm.continuous⟩
  let T : C(OnePoint (Vector ((e.ambientDimension + 6) - 6)),
      Sphere ((e.ambientDimension + 6) - 6)) :=
    ⟨euclideanOnePointSphere ((e.ambientDimension + 6) - 6),
      (euclideanOnePointSphere ((e.ambientDimension + 6) - 6)).continuous⟩
  let H' : (chosenSurgerySphereCollapse A hR).Homotopy (chosenOriginalSphereCollapse A) := {
    toContinuousMap := T.comp (H.toContinuousMap.comp ((ContinuousMap.id I).prodMap S))
    map_zero_left := fun y ↦ congrArg T (H.map_zero_left (S y))
    map_one_left := fun y ↦ congrArg T (H.map_one_left (S y)) }
  refine ⟨H', ?_⟩
  intro t
  change euclideanOnePointSphere ((e.ambientDimension + 6) - 6)
    (H (t, (euclideanOnePointSphere (e.ambientDimension + 6)).symm
      (euclideanOnePointSphere (e.ambientDimension + 6) OnePoint.infty))) = _
  rw [Homeomorph.symm_apply_apply, hH]
  rfl

theorem exists_regular_homotopic_end_representatives :
    letI := UnitSurgery.targetChartedSpace A hR;
    ∃ gs go : C(Sphere (e.ambientDimension + 6), Sphere ((e.ambientDimension + 6) - 6)),
      ContMDiff (𝓡 (e.ambientDimension + 6)) (𝓡 ((e.ambientDimension + 6) - 6)) ∞ gs ∧
      ContMDiff (𝓡 (e.ambientDimension + 6)) (𝓡 ((e.ambientDimension + 6) - 6)) ∞ go ∧
      gs.Homotopic go ∧
      (∀ y, gs y = sphereZero ((e.ambientDimension + 6) - 6) ↔
        ∃ p, (UnitSurgery.inducedEmbedding A hR).compactifiedEmbedding p = y) ∧
      (∀ y, go y = sphereZero ((e.ambientDimension + 6) - 6) ↔
        ∃ m, (OriginalEnd.embedding A).compactifiedEmbedding m = y) ∧
      (∀ y, gs y = sphereZero ((e.ambientDimension + 6) - 6) → Function.Surjective
        (mfderiv (𝓡 (e.ambientDimension + 6)) (𝓡 ((e.ambientDimension + 6) - 6)) gs y)) ∧
      (∀ y, go y = sphereZero ((e.ambientDimension + 6) - 6) → Function.Surjective
        (mfderiv (𝓡 (e.ambientDimension + 6)) (𝓡 ((e.ambientDimension + 6) - 6)) go y)) ∧
      (∀ p, (gs : Sphere (e.ambientDimension + 6) → Sphere ((e.ambientDimension + 6) - 6))
        =ᶠ[𝓝 ((UnitSurgery.inducedEmbedding A hR).compactifiedEmbedding p)]
          chosenSurgerySphereCollapse A hR) ∧
      (∀ m, (go : Sphere (e.ambientDimension + 6) → Sphere ((e.ambientDimension + 6) - 6))
        =ᶠ[𝓝 ((OriginalEnd.embedding A).compactifiedEmbedding m)]
          chosenOriginalSphereCollapse A) := by
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  let := UnitSurgery.compactSpace_target A hR
  obtain ⟨gs, hgs, hs, hsf, hsr, hse⟩ :=
    (surgeryFramedTubeData A hR).collapseData.exists_smoothSphereMap_regular
  obtain ⟨go, hgo, ho, hof, hor, hoe⟩ :=
    (originalFramedTubeData A).collapseData.exists_smoothSphereMap_regular
  obtain ⟨H, _⟩ := exists_chosenEndSphereCollapse_homotopy A hR
  have hmid : (chosenSurgerySphereCollapse A hR).Homotopic (chosenOriginalSphereCollapse A) := ⟨H⟩
  exact ⟨gs, go, hgs, hgo, hs.symm.trans (hmid.trans ho), hsf, hof, hsr, hor, hse, hoe⟩

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
