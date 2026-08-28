import Wikipedia.HopfProblem.DegreeCollapseLowSurgerySmoothTime
import Wikipedia.NoExoticSixSphere.SuperlevelNormalForm
import Wikipedia.NoExoticSixSphere.SuperlevelBoundary

/-!

# Regularity of the retained native zero level and its actual positive half

The original profile has the unchanged time germ at every zero. The smooth
native exterior map then transfers surjectivity of the actual derivative to
the new time function. The resulting superlevel atlas is built from this
native function, not supplied as a regularity or boundary assumption.
-/

noncomputable section

open Function Set Metric Filter Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.NativeSurgery

open NoExoticSixSphere GLOrthonormalization RoundedTrace SurgeryPair

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M} (A : FramedAttachingProduct e a f)
  (hR : A.radius = 2) (T : TimeData A)

theorem oldProfile_exterior_germ (m : retainedExterior A) (hm : T.time m.val = 0) :
    (fun p : retainedExterior A ↦ oldProfile A T p.val) =ᶠ[𝓝 m]
      (fun p : retainedExterior A ↦ T.time p.val) := by
  have hc : Tendsto (fun p : retainedExterior A ↦ T.time p.val) (𝓝 m) (𝓝 (0 : ℝ)) :=
    hm ▸ (T.smooth.continuous.comp continuous_subtype_val).tendsto m
  exact (SurgeryTimeProfile.profile_germ T.margin_pos).comp_tendsto hc

theorem regular_oldProfile_exterior_zero (m : retainedExterior A) (hm : T.time m.val = 0) :
    Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ)
      (fun p : retainedExterior A ↦ oldProfile A T p.val) m) := by
  rw [(oldProfile_exterior_germ A T m hm).mfderiv_eq]
  change Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ)
    (T.time ∘ (Subtype.val : retainedExterior A → M)) m)
  rw [mfderiv_comp m (T.smooth.mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))]
  have hv := isLocalDiffeomorphAt_openSubset_val (I := 𝓡 7) (retainedExterior A) m
  exact (T.regular m.val hm).comp (hv.mfderivToContinuousLinearEquiv (by simp)).surjective

variable [IsManifold (𝓡 7) ∞ M]

theorem regular_timeFunction_zero (y : otherBoundaryPart A)
    (hy : timeFunction A hR T y = 0) : letI := boundaryChartedSpace A;
    Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) (timeFunction A hR T) y) := by
  let := boundaryChartedSpace A
  obtain ⟨r, hr, rfl⟩ := (timeFunction_zero_iff A hR T y).mp hy
  let m := closedExteriorPoint A r
  have he : timeFunction A hR T ∘ exteriorMap A =
      (fun p : retainedExterior A ↦ oldProfile A T p.val) :=
    funext (timeFunction_exteriorMap A hR T)
  have hc := mfderiv_comp m ((contMDiff_timeFunction A hR T).mdifferentiableAt (by simp))
    ((contMDiff_exteriorMap A).mdifferentiableAt (by simp))
  rw [he] at hc
  intro z
  obtain ⟨w, hw⟩ := regular_oldProfile_exterior_zero A T m hr z
  refine ⟨mfderiv (𝓡 7) (𝓡 7) (exteriorMap A) m w, ?_⟩
  exact (congrArg (fun D : Vector 7 →L[ℝ] ℝ ↦ D w) hc).symm.trans hw

def positiveHalfAtlas : letI := boundaryChartedSpace A;
    SuperlevelAtlas (K := Vector 6) (𝓡 7) (timeFunction A hR T) := by
  let := boundaryChartedSpace A
  let := boundary_isManifold A
  exact Classical.choice (nonempty_superlevelAtlas (contMDiff_timeFunction A hR T)
    (regular_timeFunction_zero A hR T) 6 (by simp))

abbrev PositiveHalf := {p : otherBoundaryPart A // 0 ≤ timeFunction A hR T p}

@[instance_reducible]
def positiveHalfChartedSpace : letI := boundaryChartedSpace A;
    ChartedSpace (ProductHalfSpace.Space (Vector 6)) (PositiveHalf A hR T) := by
  let := boundaryChartedSpace A
  exact (positiveHalfAtlas A hR T).chartedSpace

theorem positiveHalf_isManifold : letI := boundaryChartedSpace A;
    letI := positiveHalfChartedSpace A hR T;
    IsManifold (ProductHalfSpace.model (Vector 6)) ∞ (PositiveHalf A hR T) := by
  let := boundaryChartedSpace A
  exact (positiveHalfAtlas A hR T).isManifold

theorem positiveHalf_boundary_iff (p : PositiveHalf A hR T) :
    letI := boundaryChartedSpace A; letI := positiveHalfChartedSpace A hR T;
    (ProductHalfSpace.model (Vector 6)).IsBoundaryPoint p ↔ timeFunction A hR T p.val = 0 := by
  let := boundaryChartedSpace A
  exact (positiveHalfAtlas A hR T).isBoundaryPoint_iff p

theorem compactSpace_positiveHalf : CompactSpace (PositiveHalf A hR T) := by
  let := compactSpace_otherBoundaryPart A
  exact isCompact_iff_compactSpace.mp
    (isClosed_le continuous_const (timeFunction A hR T).continuous).isCompact

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.NativeSurgery
