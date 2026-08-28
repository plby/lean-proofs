import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryTimeFunction
import Wikipedia.NoExoticSixSphere.SuperlevelNormalForm
import Wikipedia.NoExoticSixSphere.SuperlevelBoundary

/-!
# Surgery preserves regularity of the actual zero-time seam

The old patch's defining function has exactly its original germ at every
zero. Its regularity descends through the actual smooth open surgery patch.
The resulting native superlevel atlas therefore has the unchanged zero
locus as its genuine manifold boundary.
-/

noncomputable section

open Function Set Filter Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [T2Space M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2) (T : TimeData A)

theorem oldTime_germ (p : OldPatch A hR) (hp : T.time p.val = 0) :
    oldTime A hR T =ᶠ[𝓝 p] (fun q : OldPatch A hR ↦ T.time q.val) := by
  have hc : Tendsto (fun q : OldPatch A hR ↦ T.time q.val) (𝓝 p) (𝓝 (0 : ℝ)) :=
    hp ▸ (T.smooth.continuous.comp continuous_subtype_val).tendsto p
  exact (SurgeryTimeProfile.profile_germ T.margin_pos).comp_tendsto hc

theorem regular_oldTime_zero (p : OldPatch A hR) (hp : T.time p.val = 0) :
    Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) (oldTime A hR T) p) := by
  rw [(oldTime_germ A hR T p hp).mfderiv_eq]
  change Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ)
    (T.time ∘ (Subtype.val : OldPatch A hR → M)) p)
  rw [mfderiv_comp p (T.smooth.mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))]
  have hv := isLocalDiffeomorphAt_openSubset_val (I := 𝓡 7) (OldPatch A hR) p
  exact (T.regular p.val hp).comp (hv.mfderivToContinuousLinearEquiv (by simp)).surjective

variable [IsManifold (𝓡 7) ∞ M]

theorem regular_timeFunction_zero (p : Target A hR) (hp : timeFunction A hR T p = 0) :
    letI := targetChartedSpace A hR;
    Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) (timeFunction A hR T) p) := by
  let := targetChartedSpace A hR
  obtain ⟨q, hq, rfl⟩ := (timeFunction_zero_iff A hR T p).mp hp
  have hc := mfderiv_comp q ((contMDiff_timeFunction A hR T).mdifferentiableAt (by simp))
    ((contMDiff_oldMap A hR).mdifferentiableAt (by simp))
  intro y
  obtain ⟨v, hv⟩ := regular_oldTime_zero A hR T q hq y
  refine ⟨mfderiv (𝓡 7) (𝓡 7)
    (FramedSurgery.oldMap (E := Vector 4) (face A hR) 3) q v, ?_⟩
  exact (congrArg (fun D : Vector 7 →L[ℝ] ℝ ↦ D v) hc).symm.trans hv

def positiveHalfAtlas : letI := targetChartedSpace A hR;
    SuperlevelAtlas (K := Vector 6) (𝓡 7) (timeFunction A hR T) := by
  let := targetChartedSpace A hR
  let := target_isManifold A hR
  exact Classical.choice (nonempty_superlevelAtlas (contMDiff_timeFunction A hR T)
    (regular_timeFunction_zero A hR T) 6 (by simp))

abbrev PositiveHalf := {p : Target A hR // 0 ≤ timeFunction A hR T p}

@[instance_reducible]
def positiveHalfChartedSpace : letI := targetChartedSpace A hR;
    ChartedSpace (ProductHalfSpace.Space (Vector 6)) (PositiveHalf A hR T) := by
  let := targetChartedSpace A hR
  exact (positiveHalfAtlas A hR T).chartedSpace

theorem positiveHalf_isManifold : letI := targetChartedSpace A hR;
    letI := positiveHalfChartedSpace A hR T;
    IsManifold (ProductHalfSpace.model (Vector 6)) ∞ (PositiveHalf A hR T) := by
  let := targetChartedSpace A hR
  exact (positiveHalfAtlas A hR T).isManifold

theorem positiveHalf_boundary_iff (p : PositiveHalf A hR T) :
    letI := targetChartedSpace A hR; letI := positiveHalfChartedSpace A hR T;
    (ProductHalfSpace.model (Vector 6)).IsBoundaryPoint p ↔ timeFunction A hR T p.val = 0 := by
  let := targetChartedSpace A hR
  exact (positiveHalfAtlas A hR T).isBoundaryPoint_iff p

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
