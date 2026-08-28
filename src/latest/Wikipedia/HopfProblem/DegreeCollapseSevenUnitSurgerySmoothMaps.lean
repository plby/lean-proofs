import Wikipedia.HopfProblem.DegreeCollapseSevenUnitSurgeryOverlapMaps

/-!
# Smooth maps into the independently constructed unit-surgery boundary

The target atlas is the canonical surgery atlas constructed from its two
native patches. All three rounded-end coordinate maps are smooth in that
atlas, with their already verified exact point maps.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel SevenRoundedHandleCorner RoundedTrace
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

def boundaryData : FramedSurgery.SmoothBoundaryData (E := Vector 4) (F := Vector 4)
    (face A hR) 3 :=
  Classical.choice (FramedSurgery.nonempty_smoothBoundaryData (E := Vector 4) (F := Vector 4)
    (face A hR) 3)

@[instance_reducible]
def targetChartedSpace : ChartedSpace (Vector 7) (Target A hR) := (boundaryData A hR).charted

theorem target_isManifold : letI := targetChartedSpace A hR;
    IsManifold (𝓡 7) ∞ (Target A hR) := (boundaryData A hR).smooth

theorem contMDiff_oldMap : letI := targetChartedSpace A hR;
    ContMDiff (𝓡 7) (𝓡 7) ∞ (FramedSurgery.oldMap (E := Vector 4) (face A hR) 3) := by
  let D := boundaryData A hR
  let := targetChartedSpace A hR
  have hs : ContMDiff (𝓡 7) (𝓡 7) ∞ D.oldPartial := by
    intro x
    have hx : x ∈ D.oldPartial.source := by rw [D.old_source]; trivial
    exact D.oldPartial.contMDiffOn_toFun.contMDiffAt (D.oldPartial.open_source.mem_nhds hx)
  exact hs.congr (fun x ↦ (D.old_point x).symm)

theorem contMDiff_newMap : letI := targetChartedSpace A hR;
    ContMDiff ((𝓡 4).prod (𝓡 3)) (𝓡 7) ∞
      (FramedSurgery.newMap (E := Vector 4) (face A hR) 3) := by
  let D := boundaryData A hR
  let := targetChartedSpace A hR
  have hs : ContMDiff ((𝓡 4).prod (𝓡 3)) (𝓡 7) ∞ D.newPartial := by
    intro x
    have hx : x ∈ D.newPartial.source := by rw [D.new_source]; trivial
    exact D.newPartial.contMDiffOn_toFun.contMDiffAt (D.newPartial.open_source.mem_nhds hx)
  exact hs.congr (fun x ↦ (D.new_point x).symm)

variable [CompactSpace M]

omit [IsManifold (𝓡 7) ∞ M] in
theorem contMDiff_exteriorPoint : ContMDiff (𝓡 7) (𝓡 7) ∞ (exteriorPoint A hR) := by
  apply (ContMDiff.subtypeVal_comp_iff (OldPatch A hR) (exteriorPoint A hR)).mp
  exact contMDiff_subtype_val

omit [IsManifold (𝓡 7) ∞ M] [T2Space M] in
theorem contMDiff_handlePoint :
    ContMDiff ((𝓡 4).prod (𝓡 3)) ((𝓡 4).prod (𝓡 3)) ∞ (handlePoint A) := by
  have hv : ContMDiff ((𝓡 4).prod (𝓡 3)) ((𝓡 4).prod (𝓡 3)) ∞
      (Subtype.val : boundaryHandleParameters A → Vector 4 × Sphere 3) := contMDiff_subtype_val
  have hx : ContMDiff ((𝓡 4).prod (𝓡 3)) (𝓡 4) ∞
      (fun p : boundaryHandleParameters A ↦ (handlePoint A p).1) := by
    apply (ContMDiff.subtypeVal_comp_iff (FramedSurgery.openUnitDisk (Vector 4)) _).mp
    exact contMDiff_fst.comp hv
  exact hx.prodMk (contMDiff_snd.comp hv)

omit [IsManifold (𝓡 7) ∞ M] [T2Space M] in
theorem contMDiff_collarOriginalVector :
    ContMDiff boundaryParameterModel (𝓡 4) ∞ (collarOriginalVector A) := by
  have hv : ContMDiff boundaryParameterModel boundaryParameterModel ∞
      (Subtype.val : boundaryCollarParameters A → BoundaryParameters) := contMDiff_subtype_val
  have hu : ContMDiff boundaryParameterModel 𝓘(ℝ, ℝ) ∞
      (fun p : boundaryCollarParameters A ↦ p.val.2.2) :=
    contMDiff_snd.comp (contMDiff_snd.comp hv)
  have hs : ContMDiff boundaryParameterModel (𝓡 4) ∞
      (fun p : boundaryCollarParameters A ↦ p.val.2.1.val) :=
    (contMDiff_coe_sphere (E := Vector 4) (n := 3)).comp
      (contMDiff_fst.comp (contMDiff_snd.comp hv))
  intro p
  have hr : ContDiffAt ℝ ∞ (fun u : ℝ ↦ Real.sqrt (1 + u)) p.val.2.2 :=
    (contDiffAt_const.add contDiffAt_id).sqrt
      (by change 1 + p.val.2.2 ≠ 0; linarith [collar_parameter_gt_neg_one A p])
  have hρ : ContMDiffAt boundaryParameterModel 𝓘(ℝ, ℝ) ∞
      (fun q : boundaryCollarParameters A ↦ Real.sqrt (1 + q.val.2.2)) p :=
    hr.comp_contMDiffAt (f := fun q : boundaryCollarParameters A ↦ q.val.2.2) (x := p) (hu p)
  exact hρ.smul (hs p)

omit [IsManifold (𝓡 7) ∞ M] in
theorem contMDiff_collarPoint : ContMDiff boundaryParameterModel (𝓡 7) ∞ (collarPoint A hR) := by
  apply (ContMDiff.subtypeVal_comp_iff (OldPatch A hR) (collarPoint A hR)).mp
  have hp : ContMDiff boundaryParameterModel ((𝓡 3).prod (𝓡 4)) ∞
      (fun p : boundaryCollarParameters A ↦ (p.val.1, collarOriginalVector A p)) :=
    (contMDiff_fst.comp contMDiff_subtype_val).prodMk (contMDiff_collarOriginalVector A)
  intro p
  have h : ContMDiffAt boundaryParameterModel (𝓡 7) ∞
      (fun q : boundaryCollarParameters A ↦ A.tube (q.val.1, collarOriginalVector A q)) p :=
    (A.tube_localDiffeomorph p.val.1 _ (collarOriginalVector_mem A hR p)).contMDiffAt.comp p (hp p)
  exact h

theorem contMDiff_exteriorMap : letI := targetChartedSpace A hR;
    ContMDiff (𝓡 7) (𝓡 7) ∞ (exteriorMap A hR) := by
  let := targetChartedSpace A hR
  exact (contMDiff_oldMap A hR).comp (contMDiff_exteriorPoint A hR)

theorem contMDiff_handleMap : letI := targetChartedSpace A hR;
    ContMDiff ((𝓡 4).prod (𝓡 3)) (𝓡 7) ∞ (handleMap A hR) := by
  let := targetChartedSpace A hR
  exact (contMDiff_newMap A hR).comp (contMDiff_handlePoint A)

theorem contMDiff_collarMap : letI := targetChartedSpace A hR;
    ContMDiff boundaryParameterModel (𝓡 7) ∞ (collarMap A hR) := by
  let := targetChartedSpace A hR
  exact (contMDiff_oldMap A hR).comp (contMDiff_collarPoint A hR)

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
