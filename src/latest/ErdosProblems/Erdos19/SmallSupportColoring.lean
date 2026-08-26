import ErdosProblems.Erdos19.SmallSupportPacking
import ErdosProblems.Erdos19.MatchingCoreCompletion
import ErdosProblems.Erdos19.AuxiliaryDegreeCore
import ErdosProblems.Erdos19.SupportedGreedy

/-! # Coloring when the large edges have small support

No density hypothesis is needed: pair completeness makes every vertex outside
the large-edge support adjacent in the graph part to every other vertex.
-/

namespace Erdos19.SetHypergraph

attribute [local instance] Classical.propDecidable

theorem twoGraph_adj_of_outside_large_support {V : Type*} [Fintype V]
    (H : SetHypergraph V) (hcomplete : H.IsPairComplete)
    (hsize : ∀ e : H, 2 ≤ e.1.ncard) {x y : V} (hxy : x ≠ y)
    (hy : y ∉ H.largePart.vertexSupport) : H.twoGraph.Adj x y := by
  obtain ⟨e, he, hx, hye⟩ := hcomplete x y hxy
  have hsmall : e.ncard = 2 := by
    have hmin := hsize ⟨e, he⟩
    change 2 ≤ e.ncard at hmin
    have hnot : ¬3 ≤ e.ncard := fun h ↦ hy ⟨⟨e, he, h⟩, hye⟩
    omega
  have heq := eq_pair_of_ncard_eq_two hsmall hxy hx hye
  exact ⟨hxy, heq ▸ he⟩

theorem edgeColorable_of_auxiliary_palette {V : Type*} [Fintype V]
    (H : SetHypergraph V) (hlinear : H.IsLinear) (hcomplete : H.IsPairComplete)
    (hsize : ∀ e : H, 2 ≤ e.1.ncard) (t : ℕ)
    (large : H.largePart.EdgeColoring (Fin (2 * t + 1)))
    (hsmall : 2 * H.largePart.vertexSupport.ncard + 3 * (2 * t + 1) + 1 ≤ Fintype.card V) :
    H.EdgeColorable (Fintype.card V) := by
  classical
  let B := H.largePart.vertexSupport
  let q := 2 * t + 1
  have hq : q < Fintype.card V := by dsimp only [q, B]; omega
  have hJH : H.largePart ⊆ H := fun _ h ↦ h.1
  let C := H.largePart.colorCovered large
  have hCB : ∀ i, C i ⊆ B := by
    intro i v hv
    obtain ⟨e, _, he⟩ := hv
    exact ⟨e, he⟩
  obtain ⟨f, _, M, hM, hdis, hcover⟩ := exists_matching_packing_with_auxiliary_clique H.twoGraph B t C hCB
    (fun x y hxy hy ↦ H.twoGraph_adj_of_outside_large_support hcomplete hsize hxy hy) hsmall
  have hbudget : ∀ v, (H.twoGraph.neighborSet v).ncard +
      (∑ i : Fin q, if v ∈ C i then 1 else 0) ≤ Fintype.card V - 1 := by
    intro v
    have h := H.large_coloring_parity_degree_budget hlinear hcomplete hsize large v
    change (H.twoGraph.neighborSet v).ncard + (∑ i : Fin q, if v ∈ C i then 1 else 0) + _ ≤ _ at h
    omega
  obtain ⟨hdegree, hcore⟩ := residual_matching_core_of_auxiliary_targets H.twoGraph q hq C f M
    hM hdis hbudget hcover
  have hrest : ∀ e : H, e.1 ∉ H.largePart → e.1.ncard = 2 := by
    intro e he
    have hmin := hsize e
    have hnot : ¬3 ≤ e.1.ncard := fun h ↦ he ⟨e.2, h⟩
    omega
  have havoid : ∀ e : H.largePart, ∀ x ∈ e.1, x ∉ (M (large.color e)).verts := by
    intro e x hx hMx
    rw [(hM (large.color e)).2] at hMx
    exact auxiliaryTarget_subset _ _ hMx ⟨e, rfl, hx⟩
  have hc := H.edgeColorable_of_avoiding_matching_family_core H.largePart hJH hrest q
    (Fintype.card V - q) (by omega) large M (fun i ↦ (hM i).1) havoid hdegree hcore
  have hpalette : q + (Fintype.card V - q) = Fintype.card V := by omega
  simpa only [hpalette] using hc

theorem edgeColorable_of_small_large_support {V : Type*} [Fintype V]
    (H : SetHypergraph V) (hlinear : H.IsLinear) (hcomplete : H.IsPairComplete)
    (hsize : ∀ e : H, 2 ≤ e.1.ncard)
    (hsmall : 8 * H.largePart.vertexSupport.ncard + 4 ≤ Fintype.card V) :
    H.EdgeColorable (Fintype.card V) := by
  have hJH : H.largePart ⊆ H := fun _ h ↦ h.1
  obtain ⟨large⟩ := H.largePart.edgeColorable_two_mul_support_add_one H.largePart.vertexSupport
    (hlinear.mono hJH) (fun e ↦ by have h := e.2.2; omega) (fun e v hv ↦ ⟨e, hv⟩)
  exact H.edgeColorable_of_auxiliary_palette hlinear hcomplete hsize
    H.largePart.vertexSupport.ncard large (by omega)

theorem edgeColorable_of_support_at_most_eighth {V : Type*} [Fintype V]
    (H : SetHypergraph V) (hlinear : H.IsLinear) (hcomplete : H.IsPairComplete)
    (hsize : ∀ e : H, 2 ≤ e.1.ncard) (hn : 0 < Fintype.card V)
    (hsmall : 8 * H.largePart.vertexSupport.ncard ≤ Fintype.card V) :
    H.EdgeColorable (Fintype.card V) := by
  classical
  let B := H.largePart.vertexSupport
  by_cases hBzero : B.ncard = 0
  · have hBempty : B = ∅ := (Set.ncard_eq_zero (Set.toFinite B)).mp hBzero
    haveI : Nonempty V := Fintype.card_pos_iff.mp hn
    apply H.edgeColorable_of_edge_ncard_le_two hlinear
    intro e
    by_contra he
    have h3 : 3 ≤ e.1.ncard := by omega
    obtain ⟨v, hv⟩ := (Set.ncard_pos (Set.toFinite e.1)).mp (by omega : 0 < e.1.ncard)
    have hvB : v ∈ B := ⟨⟨e.1, e.2, h3⟩, hv⟩
    rw [hBempty] at hvB
    exact hvB
  · have hBthree : 3 ≤ B.ncard := by
      obtain ⟨v, hv⟩ := (Set.ncard_pos (Set.toFinite B)).mp (by omega : 0 < B.ncard)
      obtain ⟨e, _⟩ := hv
      have hsub : e.1 ⊆ B := fun x hx ↦ ⟨e, hx⟩
      exact e.2.2.trans (Set.ncard_le_ncard hsub)
    have hJH : H.largePart ⊆ H := fun _ h ↦ h.1
    have hc := H.largePart.edgeColorable_support_add_div_add_one B (hlinear.mono hJH) 3
      (by omega) (fun e ↦ e.2.2) (fun e v hv ↦ ⟨e, hv⟩)
    have hpalette : B.ncard + B.ncard / (3 - 1) + 1 ≤ 2 * (B.ncard - 1) + 1 := by omega
    obtain ⟨large⟩ := hc.mono hpalette
    apply H.edgeColorable_of_auxiliary_palette hlinear hcomplete hsize (B.ncard - 1) large
    change 2 * B.ncard + 3 * (2 * (B.ncard - 1) + 1) + 1 ≤ _
    change 8 * B.ncard ≤ _ at hsmall
    omega

#print axioms edgeColorable_of_small_large_support
#print axioms edgeColorable_of_support_at_most_eighth

end Erdos19.SetHypergraph
