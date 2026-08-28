import Wikipedia.NoExoticSixSphere.CutCurveComponents
import Wikipedia.NoExoticSixSphere.HalfLineLocalConnectivity
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# The actual cut-curve components are open and only accumulate at cuts

The half-line atlas makes the original space locally connected. Removing a
finite closed set preserves this locally. Components are therefore open in
the original space; any point in their ambient closure that is not a cut
already belongs to the component.
-/

open Set Function Topology

namespace NoExoticSixSphere.CurveDecomposition

open InvolutionQuotient

variable {X : Type*} [TopologicalSpace X]

theorem isOpen_cutComponent [LocallyConnectedSpace X] {S : Set X} (hS : IsClosed S)
    (x : {x : X // x ∉ S}) : IsOpen (cutComponent S x) := by
  let := hS.isOpen_compl.locallyConnectedSpace
  exact hS.isOpen_compl.isOpenEmbedding_subtypeVal.isOpenMap _ isOpen_connectedComponent

theorem closure_cutComponent_away_from_cuts {S : Set X} (x : {x : X // x ∉ S})
    {y : X} (hy : y ∈ closure (cutComponent S x)) (hyn : y ∉ S) :
    y ∈ cutComponent S x := by
  let z : {x : X // x ∉ S} := ⟨y, hyn⟩
  have hz : z ∈ closure (connectedComponent x) := by
    rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    exact hy
  rw [isClosed_connectedComponent.closure_eq] at hz
  exact ⟨z, hz, rfl⟩

theorem frontier_cutComponent_subset [LocallyConnectedSpace X] {S : Set X}
    (hS : IsClosed S) (x : {x : X // x ∉ S}) : frontier (cutComponent S x) ⊆ S := by
  intro y hy
  by_contra hyn
  have hmem := closure_cutComponent_away_from_cuts x (frontier_subset_closure hy) hyn
  exact hy.2 ((isOpen_cutComponent hS x).interior_eq.symm ▸ hmem)

theorem chartedSpace_locallyConnected [ChartedSpace HalfLine X] : LocallyConnectedSpace X :=
  ChartedSpace.locallyConnectedSpace HalfLine X

end NoExoticSixSphere.CurveDecomposition
