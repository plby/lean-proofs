import Wikipedia.NoExoticSixSphere.SmoothOpenCover
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# The glued atlas retains each local smooth structure

Each open-cover inclusion, with the independently supplied atlas on its
source, is a local diffeomorphism into the glued atlas. In particular,
smoothness and the interior/boundary distinction agree on every piece.
-/

open scoped Manifold ContDiff
open Set TopologicalSpace IsManifold

namespace NoExoticSixSphere.SmoothOpenCover

variable {B H X ι : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace X]
  {U : ι → Opens X} (A : SmoothOpenCover I U)

theorem chart_target (p : Σ i, U i) : letI := A.localAtlas p.1;
    (A.chart p).target = (A.localChart p.1 p.2).target := by
  let := A.localAtlas p.1
  simp only [chart, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
    Opens.openPartialHomeomorphSubtypeCoe_source, preimage_univ, inter_univ]
  rfl

noncomputable def globalChart (p : Σ i, U i) :
    letI := A.chartedSpace; PartialDiffeomorph I I X H ∞ := by
  let := A.chartedSpace
  let := A.isManifold
  have hp : A.chart p ∈ maximalAtlas I ∞ X := subset_maximalAtlas ⟨p, rfl⟩
  exact
    { toPartialEquiv := (A.chart p).toPartialEquiv
      open_source := (A.chart p).open_source
      open_target := (A.chart p).open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hp
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hp }

theorem isLocalDiffeomorphAt_inclusion (i : ι) (x : U i) :
    letI := A.chartedSpace; letI := A.localAtlas i;
    IsLocalDiffeomorphAt I I ∞ (Subtype.val : U i → X) x := by
  let := A.chartedSpace
  let := A.localAtlas i
  let c := A.localChart i x
  let d := A.globalChart ⟨i, x⟩
  have hx : x ∈ c.source := _root_.mem_chart_source H x
  have ht : c x ∈ d.target := by
    change c x ∈ (A.chart ⟨i, x⟩).target
    rw [A.chart_target]
    exact c.map_source' hx
  refine ⟨c.trans d.symm, ⟨hx, ht⟩, ?_⟩
  intro y hy
  change y.val = (c.symm (c y)).val
  exact (congrArg Subtype.val (c.left_inv' hy.1)).symm

theorem contMDiff_inclusion (i : ι) :
    letI := A.chartedSpace; letI := A.localAtlas i;
    ContMDiff I I ∞ (Subtype.val : U i → X) := by
  let := A.chartedSpace
  let := A.localAtlas i
  exact fun x ↦ (A.isLocalDiffeomorphAt_inclusion i x).contMDiffAt

theorem isBoundaryPoint_inclusion_iff (i : ι) (x : U i) :
    letI := A.chartedSpace; letI := A.localAtlas i;
    I.IsBoundaryPoint x ↔ I.IsBoundaryPoint x.val := by
  let := A.chartedSpace
  let := A.isManifold
  let := A.localAtlas i
  let := A.localSmooth i
  exact (A.isLocalDiffeomorphAt_inclusion i x).isBoundaryPoint_iff (by simp)

end NoExoticSixSphere.SmoothOpenCover
