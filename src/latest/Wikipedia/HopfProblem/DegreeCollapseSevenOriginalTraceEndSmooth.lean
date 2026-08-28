import Wikipedia.HopfProblem.DegreeCollapseSevenExistingColumnsSmooth

/-!
# The retained original seven-manifold maps smoothly into the native boundary

The upper-end map was fixed before choosing the trace atlas. Its native
smoothness follows through the actual unchanged cylinder chart, and every
image point is a boundary point of the globally glued eight-dimensional
manifold. The separate atlas on that boundary and its end diffeomorphism are
not supplied here.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem originalEnd_mem_cylinderOnly (m : M) : originalEnd A m ∈ cylinderOnlyPart A :=
  originalEnd_mem_retainedRegion A m

def originalEndLift (m : M) : cylinderOnlyPart A :=
  ⟨originalEnd A m, originalEnd_mem_cylinderOnly A m⟩

theorem originalEndLift_coordinates (m : M) :
    (unchangedCylinderHomeomorph A (originalEndLift A m)).val.val =
      (m, UnroundedTrace.height A) :=
  HeightCylinder.injective_heightCylinder e
    (unchangedCylinderHomeomorph_ambient A (originalEndLift A m))

theorem contMDiff_originalEndLift : letI := unchangedCylinderChartedSpace A;
    ContMDiff (𝓡 7) (ProductHalfSpace.model (Vector 7)) ∞ (originalEndLift A) := by
  let := unchangedCylinderChartedSpace A
  apply (contMDiff_unchangedCylinder_iff_parameters A _).mpr
  have he : (fun m : M ↦ (unchangedCylinderHomeomorph A (originalEndLift A m)).val.val) =
      (fun m : M ↦ (m, UnroundedTrace.height A)) := funext (originalEndLift_coordinates A)
  rw [he]
  exact contMDiff_id.prodMk contMDiff_const

theorem contMDiff_originalEnd : letI := traceChartedSpace A;
    ContMDiff (𝓡 7) (ProductHalfSpace.model (Vector 7)) ∞ (originalEnd A) := by
  let := traceChartedSpace A
  let := pieceAtlas A .cylinder
  exact ((openCover A).contMDiff_inclusion .cylinder).comp (contMDiff_originalEndLift A)

theorem injective_mfderiv_originalEnd (m : M) : letI := traceChartedSpace A;
    Injective (mfderiv (𝓡 7) (ProductHalfSpace.model (Vector 7)) (originalEnd A) m) := by
  let := traceChartedSpace A
  let j : M → M × ℝ := fun x ↦ (x, UnroundedTrace.height A)
  have hj : ContMDiff (𝓡 7) ((𝓡 7).prod 𝓘(ℝ, ℝ)) ∞ j :=
    contMDiff_id.prodMk contMDiff_const
  have hDj : mfderiv (𝓡 7) ((𝓡 7).prod 𝓘(ℝ, ℝ)) j m =
      (ContinuousLinearMap.id ℝ (Vector 7)).prod 0 :=
    ((hasMFDerivAt_id m).prodMk (hasMFDerivAt_const (UnroundedTrace.height A) m)).mfderiv
  have hij : Injective (mfderiv (𝓡 7) ((𝓡 7).prod 𝓘(ℝ, ℝ)) j m) := by
    rw [hDj]
    intro v w h
    exact congrArg Prod.fst h
  have hi : Injective (mfderiv (𝓡 7) (𝓡 (e.ambientDimension + 6))
      ((Subtype.val : ambientSet A → Vector (e.ambientDimension + 6)) ∘ originalEnd A) m) := by
    change Injective (mfderiv (𝓡 7) (𝓡 (e.ambientDimension + 6))
      (HeightCylinder.heightCylinder e ∘ j) m)
    rw [mfderiv_comp m ((HeightCylinder.contMDiff_heightCylinder e).mdifferentiableAt (by simp))
      (hj.mdifferentiableAt (by simp))]
    exact (HeightCylinder.injective_heightCylinderDerivative e (j m)).comp hij
  have hcomp := mfderiv_comp m ((trace_contMDiff_ambient A).mdifferentiableAt (by simp))
    ((contMDiff_originalEnd A).mdifferentiableAt (by simp))
  intro v w h
  apply hi
  rw [hcomp]
  exact congrArg (traceAmbientDerivative A (originalEnd A m)) h

theorem originalEnd_isBoundaryPoint (m : M) : letI := traceChartedSpace A;
    (ProductHalfSpace.model (Vector 7)).IsBoundaryPoint (originalEnd A m) := by
  let := traceChartedSpace A
  apply (trace_isBoundaryPoint_iff A _).mpr
  apply mem_iUnion.mpr
  refine ⟨.cylinder, originalEndLift A m, ?_, rfl⟩
  change (unchangedCylinderHomeomorph A (originalEndLift A m)).val.val.2 = 0 ∨
    (unchangedCylinderHomeomorph A (originalEndLift A m)).val.val.2 = UnroundedTrace.height A
  rw [originalEndLift_coordinates]
  exact Or.inr rfl

theorem traceNormalFrame_originalEnd (m : M) :
    traceNormalFrame A (originalEnd A m) = boundaryFrameOperator (a.orthonormal m).val := by
  rw [← columns_eq_traceNormalFrame]
  exact columns_originalEnd A m

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
