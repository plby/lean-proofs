import Wikipedia.SmoothSixDPoincare.SmoothClosedFace
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Restrict a framed chart without changing any closed-face coordinates

An open neighborhood of the entire closed face restricts the existing
chart. In particular, two disjoint closed faces admit framed neighborhoods
avoiding the other face; no new embedding or parametrization is chosen.
-/

noncomputable section

open Set Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SmoothClosedFace

variable {E H F K B N X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup N] [NormedSpace ℝ N]
  [TopologicalSpace X] [ChartedSpace K X]
  (C : SmoothClosedFace I J B N X)

def restrictChartTarget (U : Set X) (hU : IsOpen U) (hface : range C.map ⊆ U) :
    SmoothClosedFace I J B N X where
  map := C.map
  closedEmbedding := C.closedEmbedding
  chart := {
    toPartialEquiv := (C.chart.toOpenPartialHomeomorph.trans
      (OpenPartialHomeomorph.ofSet U hU)).toPartialEquiv
    open_source := (C.chart.toOpenPartialHomeomorph.trans
      (OpenPartialHomeomorph.ofSet U hU)).open_source
    open_target := (C.chart.toOpenPartialHomeomorph.trans
      (OpenPartialHomeomorph.ofSet U hU)).open_target
    contMDiffOn_toFun := C.chart.contMDiffOn.mono inter_subset_left
    contMDiffOn_invFun := C.chart.symm.contMDiffOn.mono inter_subset_right }
  source := by
    intro z hz
    refine ⟨C.source hz, ?_⟩
    change C.chart z ∈ U
    rw [C.point z.1 ⟨z.2, hz.2⟩]
    exact hface (mem_range_self _)
  point := C.point

theorem restrictChartTarget_map (U : Set X) (hU : IsOpen U) (hface : range C.map ⊆ U) :
    (C.restrictChartTarget U hU hface).map = C.map := rfl

theorem restrictChartTarget_target (U : Set X) (hU : IsOpen U) (hface : range C.map ⊆ U) :
    (C.restrictChartTarget U hU hface).chart.target = U ∩ C.chart.target := rfl

theorem restrictChartTarget_source (U : Set X) (hU : IsOpen U) (hface : range C.map ⊆ U) :
    (C.restrictChartTarget U hU hface).chart.source = C.chart.source ∩ C.chart ⁻¹' U := rfl

def avoidClosed (S : Set X) (hS : IsClosed S) (hdisjoint : Disjoint (range C.map) S) :
    SmoothClosedFace I J B N X :=
  C.restrictChartTarget Sᶜ hS.isOpen_compl
    (fun _ hx hs => disjoint_left.mp hdisjoint hx hs)

theorem avoidClosed_map (S : Set X) (hS : IsClosed S)
    (hdisjoint : Disjoint (range C.map) S) : (C.avoidClosed S hS hdisjoint).map = C.map := rfl

theorem avoidClosed_target (S : Set X) (hS : IsClosed S)
    (hdisjoint : Disjoint (range C.map) S) :
    (C.avoidClosed S hS hdisjoint).chart.target = Sᶜ ∩ C.chart.target := rfl

theorem avoidClosed_disjoint (S : Set X) (hS : IsClosed S)
    (hdisjoint : Disjoint (range C.map) S) :
    Disjoint (C.avoidClosed S hS hdisjoint).chart.target S := by
  rw [C.avoidClosed_target, disjoint_left]
  exact fun _ hx hs => hx.1 hs

end Wikipedia.SmoothSixDPoincare.SmoothClosedFace
