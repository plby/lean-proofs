import Wikipedia.SmoothSixDPoincare.SmoothClosedFace
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-! # Place the same full smooth face in one disjoint summand -/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

namespace PartialChart

variable {E H X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H Y]

def sumInl (x₀ : X) : PartialDiffeomorph I I X (X ⊕ Y) ∞ where
  toFun := Sum.inl
  invFun := Sum.elim id (fun _ => x₀)
  source := univ
  target := range Sum.inl
  map_source' x _ := ⟨x, rfl⟩
  map_target' _ _ := mem_univ _
  left_inv' _ _ := rfl
  right_inv' _ h := by obtain ⟨x, rfl⟩ := h; rfl
  open_source := isOpen_univ
  open_target := isOpen_range_inl
  contMDiffOn_toFun := ContMDiff.inl.contMDiffOn
  contMDiffOn_invFun := (contMDiff_id.sumElim contMDiff_const).contMDiffOn

theorem sumInl_apply (x₀ x : X) : sumInl (I := I) (Y := Y) x₀ x = Sum.inl x := rfl

theorem sumInl_source (x₀ : X) : (sumInl (I := I) (Y := Y) x₀).source = univ := rfl

theorem sumInl_target (x₀ : X) :
    (sumInl (I := I) (Y := Y) x₀).target = range Sum.inl := rfl

end PartialChart

namespace SmoothClosedFace

variable {E H F H' X N Y Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace X] [ChartedSpace H X] [NormedAddCommGroup N] [NormedSpace ℝ N]
  [TopologicalSpace Y] [ChartedSpace H' Y] [TopologicalSpace Z] [ChartedSpace H' Z]
  (A : SmoothClosedFace I J X N Y) (y₀ : Y)

def sumLeft : SmoothClosedFace I J X N (Y ⊕ Z) where
  map := ⟨fun z => Sum.inl (A.map z), continuous_inl.comp A.map.continuous⟩
  closedEmbedding := IsClosedEmbedding.inl.comp A.closedEmbedding
  chart := A.chart.trans (PartialChart.sumInl y₀)
  source := fun _ hz => ⟨A.source hz, mem_univ _⟩
  point x w := congrArg Sum.inl (A.point x w)

theorem sumLeft_map (z : X × MorseHandle.UnitDisk N) :
    (A.sumLeft (Z := Z) y₀).map z = Sum.inl (A.map z) := rfl

end SmoothClosedFace
end Wikipedia.SmoothSixDPoincare
