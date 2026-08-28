import Wikipedia.SmoothSixDPoincare.SmoothClosedFace
import Wikipedia.SmoothSixDPoincare.OpenSubtypePartialDiffeomorph

/-! # Retain full framed faces through native smooth open embeddings -/

noncomputable section

open Set Function Topology TopologicalSpace Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SmoothClosedFace

variable {E H F K G L B N X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace L]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {Q : ModelWithCorners ℝ G L}
  [TopologicalSpace B] [ChartedSpace H B] [NormedAddCommGroup N] [NormedSpace ℝ N]
  [TopologicalSpace X] [ChartedSpace K X] [TopologicalSpace Y] [ChartedSpace L Y]
  [CompactSpace (B × MorseHandle.UnitDisk N)] [T2Space Y]
  (A : SmoothClosedFace I J B N X)

def postcomposeOpen (p : PartialDiffeomorph J Q X Y ∞) (hp : p.source = univ) :
    SmoothClosedFace I Q B N Y := by
  have hc : Continuous p := (contMDiffOn_univ.mp (hp ▸ p.contMDiffOn)).continuous
  have hi : Injective p := fun x y h =>
    p.injOn (hp.symm ▸ mem_univ x) (hp.symm ▸ mem_univ y) h
  exact {
    map := ⟨fun z => p (A.map z), hc.comp A.map.continuous⟩
    closedEmbedding := (hc.comp A.map.continuous).isClosedEmbedding
      (hi.comp A.closedEmbedding.injective)
    chart := A.chart.trans p
    source := fun _ hz => ⟨A.source hz, hp.symm ▸ mem_univ _⟩
    point := fun x w => congrArg p (A.point x w) }

theorem postcomposeOpen_map (p : PartialDiffeomorph J Q X Y ∞) (hp : p.source = univ)
    (z : B × MorseHandle.UnitDisk N) : (A.postcomposeOpen p hp).map z = p (A.map z) := rfl

theorem postcomposeOpen_chart_target (p : PartialDiffeomorph J Q X Y ∞)
    (hp : p.source = univ) : (A.postcomposeOpen p hp).chart.target = p '' A.chart.target := by
  ext y
  change (y ∈ p.target ∧ p.symm y ∈ A.chart.target) ↔ _
  constructor
  · rintro ⟨hy, hx⟩
    exact ⟨p.symm y, hx, p.right_inv hy⟩
  · rintro ⟨x, hx, rfl⟩
    have hs : x ∈ p.source := hp.symm ▸ mem_univ x
    have he : p.symm (p x) = x := p.left_inv hs
    exact ⟨p.map_source hs, he.symm ▸ hx⟩

variable [T2Space X]

def restrictToOpen (U : Opens X) [Nonempty U] (hU : A.chart.target ⊆ U) :
    SmoothClosedFace I J B N U := by
  have hmap (z : B × MorseHandle.UnitDisk N) : A.map z ∈ U := by
    rw [← A.point z.1 z.2]
    exact hU (A.chart.map_source (A.source ⟨mem_univ _, z.2.property⟩))
  let i : PartialDiffeomorph J J U X ∞ := PartialChart.openInclusion U
  refine {
    map := ⟨fun z => ⟨A.map z, hmap z⟩, A.map.continuous.subtype_mk _⟩
    closedEmbedding := ?_
    chart := A.chart.trans i.symm
    source := ?_
    point := ?_ }
  · apply (A.map.continuous.subtype_mk _).isClosedEmbedding
    intro x y h
    exact A.closedEmbedding.injective (congrArg Subtype.val h)
  · intro z hz
    refine ⟨A.source hz, ?_⟩
    change A.chart z ∈ i.target
    rw [PartialChart.openInclusion_target]
    exact hU (A.chart.map_source (A.source hz))
  · intro x w
    apply Subtype.ext
    change (i.symm (A.chart (x, w.val))).val = A.map (x, w)
    exact (PartialChart.openInclusion_symm_coe (I := J) U
      (hU (A.chart.map_source (A.source ⟨mem_univ _, w.property⟩)))).trans (A.point x w)

theorem restrictToOpen_map (U : Opens X) [Nonempty U] (hU : A.chart.target ⊆ U)
    (z : B × MorseHandle.UnitDisk N) : ((A.restrictToOpen U hU).map z).val = A.map z := rfl

theorem restrictToOpen_chart_target (U : Opens X) [Nonempty U] (hU : A.chart.target ⊆ U) :
    (A.restrictToOpen U hU).chart.target = {x : U | x.val ∈ A.chart.target} := by
  ext x
  change (x ∈ (PartialChart.openInclusion (I := J) U).source ∧
    (PartialChart.openInclusion (I := J) U) x ∈ A.chart.target) ↔ _
  simp only [PartialChart.openInclusion_source, mem_univ, PartialChart.openInclusion_apply,
    true_and, mem_ofPred_eq]

end Wikipedia.SmoothSixDPoincare.SmoothClosedFace
