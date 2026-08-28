import Wikipedia.NoExoticSixSphere.OpenOverlap

/-!
# Gluing compatible local smooth structures on an open cover

Each open piece has an atlas in a common model. Smooth ambient-identity maps
on overlaps allow their charts to be extended to the original topological
space and assembled into one compatible atlas. No new topology is introduced.
-/

open scoped Manifold ContDiff
open Set TopologicalSpace

namespace NoExoticSixSphere

variable {B H X ι : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] (I : ModelWithCorners ℝ B H) [TopologicalSpace X]
  (U : ι → Opens X)

structure SmoothOpenCover where
  covers : ∀ x : X, ∃ i, x ∈ U i
  localAtlas : ∀ i, ChartedSpace H (U i)
  localSmooth : ∀ i, letI := localAtlas i; IsManifold I ∞ (U i)
  overlapSmooth : ∀ i j, letI := localAtlas i; letI := localAtlas j;
    ContMDiff I I ∞ (OpenOverlap.map (U i) (U j))

namespace SmoothOpenCover

variable {I U} (A : SmoothOpenCover I U)

noncomputable def localChart (i : ι) (x : U i) :
    letI := A.localAtlas i; PartialDiffeomorph I I (U i) H ∞ := by
  let := A.localAtlas i
  let := A.localSmooth i
  exact
    { toPartialEquiv := (chartAt H x).toPartialEquiv
      open_source := (chartAt H x).open_source
      open_target := (chartAt H x).open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }

noncomputable def chart (p : Σ i, U i) : OpenPartialHomeomorph X H := by
  let := A.localAtlas p.1
  exact ((U p.1).openPartialHomeomorphSubtypeCoe ⟨p.2⟩).symm.trans
    (A.localChart p.1 p.2).toOpenPartialHomeomorph

theorem mem_chart_source (p : Σ i, U i) : p.2.val ∈ (A.chart p).source := by
  let := A.localAtlas p.1
  let e := (U p.1).openPartialHomeomorphSubtypeCoe ⟨p.2⟩
  refine ⟨?_, ?_⟩
  · change p.2.val ∈ e.target
    rw [Opens.openPartialHomeomorphSubtypeCoe_target]
    exact p.2.property
  · have hleft : e.symm p.2.val = p.2 := e.left_inv (by
      rw [Opens.openPartialHomeomorphSubtypeCoe_source]
      trivial)
    change e.symm p.2.val ∈ (chartAt H p.2).source
    rw [hleft]
    exact _root_.mem_chart_source H p.2

noncomputable def indexAt (x : X) : Σ i, U i :=
  ⟨(A.covers x).choose, ⟨x, (A.covers x).choose_spec⟩⟩

@[instance_reducible]
noncomputable def chartedSpace : ChartedSpace H X where
  atlas := range A.chart
  chartAt x := A.chart (A.indexAt x)
  mem_chart_source x := A.mem_chart_source (A.indexAt x)
  chart_mem_atlas x := ⟨A.indexAt x, rfl⟩

noncomputable def transitionDiffeomorph (p q : Σ i, U i) : PartialDiffeomorph I I H H ∞ := by
  let := A.localAtlas p.1
  let := A.localAtlas q.1
  let e := OpenOverlap.partialDiffeomorph (I := I) (U p.1) (U q.1) ⟨p.2⟩ ⟨q.2⟩
    (A.overlapSmooth p.1 q.1) (A.overlapSmooth q.1 p.1)
  exact (A.localChart p.1 p.2).symm.trans (e.trans (A.localChart q.1 q.2))

theorem transition_eq (p q : Σ i, U i) :
    (A.chart p).symm.trans (A.chart q) = (A.transitionDiffeomorph p q).toOpenPartialHomeomorph := by
  let := A.localAtlas p.1
  let := A.localAtlas q.1
  let ei := (U p.1).openPartialHomeomorphSubtypeCoe ⟨p.2⟩
  let ej := (U q.1).openPartialHomeomorphSubtypeCoe ⟨q.2⟩
  let ci := (A.localChart p.1 p.2).toOpenPartialHomeomorph
  let cj := (A.localChart q.1 q.2).toOpenPartialHomeomorph
  change (ei.symm.trans ci).symm.trans (ej.symm.trans cj) =
    ci.symm.trans ((ei.trans ej.symm).trans cj)
  simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc]

theorem isManifold : letI := A.chartedSpace; IsManifold I ∞ X := by
  let := A.chartedSpace
  apply isManifold_of_contDiffOn I ∞ X
  rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
  rw [A.transition_eq]
  let Ψ := A.transitionDiffeomorph p q
  change ContDiffOn ℝ ∞ (I ∘ Ψ ∘ I.symm) (I.symm ⁻¹' Ψ.source ∩ range I)
  exact (I.contMDiff.comp_contMDiffOn
    (Ψ.contMDiffOn_toFun.comp (I.contMDiffOn_symm.mono inter_subset_right)
      (fun _ hz ↦ hz.1))).contDiffOn

end SmoothOpenCover

end NoExoticSixSphere
