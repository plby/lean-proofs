import ErdosProblems.Erdos19.VizingAugmentation
import ErdosProblems.Erdos19.VizingMissing
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-! # Completing a coloring with one uncolored edge -/

namespace Erdos19.Vizing

open Finset

attribute [local instance] Classical.propDecidable

variable {V K : Type*} [Fintype V]

noncomputable def maskToGraph (H : SimpleGraph V) (C : PartialColoring V K) :
    PartialColoring V K := fun e ↦ if e ∈ H.edgeSet then C e else none

@[simp] theorem maskToGraph_of_mem (H : SimpleGraph V) (C : PartialColoring V K)
    (e : Sym2 V) (he : e ∈ H.edgeSet) : maskToGraph H C e = C e := by simp [maskToGraph, he]

@[simp] theorem maskToGraph_of_not_mem (H : SimpleGraph V) (C : PartialColoring V K)
    (e : Sym2 V) (he : e ∉ H.edgeSet) : maskToGraph H C e = none := by simp [maskToGraph, he]

theorem maskToGraph_proper (G H : SimpleGraph V) (C : PartialColoring V K)
    (hC : IsProper H C) : IsProper G (maskToGraph H C) := by
  intro u v w a _ _ hvc hwc
  have huv : H.Adj u v := by
    by_contra h
    have he : s(u, v) ∉ H.edgeSet := h
    simp only [maskToGraph_of_not_mem H C _ he] at hvc
    contradiction
  have huw : H.Adj u w := by
    by_contra h
    have he : s(u, w) ∉ H.edgeSet := h
    simp only [maskToGraph_of_not_mem H C _ he] at hwc
    contradiction
  rw [maskToGraph_of_mem H C _ huv] at hvc
  rw [maskToGraph_of_mem H C _ huw] at hwc
  exact hC huv huw hvc hwc

theorem complete_of_coloredEdges_card_ge (G : SimpleGraph V) (C : PartialColoring V K)
    (hcard : G.edgeFinset.card ≤ (coloredEdges G C).card) :
    ∀ x y, G.Adj x y → ∃ a, C s(x, y) = some a := by
  classical
  have hsub : coloredEdges G C ⊆ G.edgeFinset := filter_subset _ _
  have heq : coloredEdges G C = G.edgeFinset := eq_of_subset_of_card_le hsub hcard
  intro x y hxy
  have he : s(x, y) ∈ coloredEdges G C := by
    rw [heq]
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hxy
  have hsome := ((mem_coloredEdges G C _).mp he).2
  cases hc : C s(x, y) with
  | none => simp [hc] at hsome
  | some a => exact ⟨a, rfl⟩

theorem edge_card_le_colored_add_one (G : SimpleGraph V) (C : PartialColoring V K)
    (e : Sym2 V) (hother : ∀ f, f ∈ G.edgeSet → f ≠ e → (C f).isSome) :
    G.edgeFinset.card ≤ (coloredEdges G C).card + 1 := by
  classical
  have hsub : G.edgeFinset ⊆ insert e (coloredEdges G C) := by
    intro f hf
    by_cases hfe : f = e
    · exact mem_insert.mpr (Or.inl hfe)
    · have hfG : f ∈ G.edgeSet := by simpa only [SimpleGraph.mem_edgeFinset] using hf
      exact mem_insert_of_mem ((mem_coloredEdges G C f).mpr ⟨hfG, hother f hfG hfe⟩)
  exact (card_le_card hsub).trans (card_insert_le _ _)

/-- With a degree-sized palette, a single uncolored edge can be completed
when every other neighbor of its first endpoint has smaller degree. -/
theorem exists_complete_extension_of_single_uncolored [Fintype K] [DecidableEq K]
    (G : SimpleGraph V) (C : PartialColoring V K) (hC : IsProper G C)
    (x y : V) (hxy : G.Adj x y) (hzero : C s(x, y) = none)
    (hother : ∀ f, f ∈ G.edgeSet → f ≠ s(x, y) → (C f).isSome)
    (hdegree : ∀ v, G.degree v ≤ Fintype.card K)
    (hlow : ∀ z, G.Adj x z → z ≠ y → G.degree z < Fintype.card K) :
    ∃ C' : PartialColoring V K, IsProper G C' ∧
      ∀ u v, G.Adj u v → ∃ a, C' s(u, v) = some a := by
  have hxmiss := exists_missing_of_uncolored G C x y hxy hzero (hdegree x)
  have hymiss := exists_missing_of_uncolored G C y x hxy.symm
    (by simpa only [Sym2.eq_swap] using hzero) (hdegree y)
  have hneighbors : ∀ z, G.Adj x z → ∃ a, Missing G C z a := by
    intro z hxz
    by_cases hzy : z = y
    · exact hzy ▸ hymiss
    · exact exists_missing_of_degree_lt G C z (hlow z hxz hzy)
  obtain ⟨C', hC', hmore⟩ := exists_improvement_of_missing_neighbors G C hC x y hxy hzero
    hxmiss hneighbors
  have hcards := edge_card_le_colored_add_one G C s(x, y) hother
  exact ⟨C', hC', complete_of_coloredEdges_card_ge G C' (by omega)⟩

#print axioms maskToGraph_proper
#print axioms exists_complete_extension_of_single_uncolored

end Erdos19.Vizing
