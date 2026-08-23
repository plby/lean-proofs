import ErdosProblems.Erdos1105.SwapRepresentative
import ErdosProblems.Erdos1105.AdjoinRepresentative

namespace Erdos1105

open SimpleGraph

/-- Three triangles with a common central vertex. -/
def threePetalGraph : SimpleGraph (Fin 7) where
  Adj a b := a ≠ b ∧ (a = 0 ∨ b = 0 ∨
    s(a, b) ∈ ({s(1, 2), s(3, 4), s(5, 6)} : Finset (Sym2 (Fin 7))))
  symm := ⟨by
    intro a b h
    refine ⟨h.1.symm, ?_⟩
    rw [show s(b, a) = s(a, b) from Sym2.eq_swap]
    tauto⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

instance : DecidableRel threePetalGraph.Adj := by
  unfold threePetalGraph
  infer_instance

def threePetalPath (i : Fin 4) : Fin 6 → Fin 7 :=
  ![![1, 0, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6],
    ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 3, 4, 5]] i

lemma threePetalPath_injective (i : Fin 4) : Function.Injective (threePetalPath i) := by
  fin_cases i <;> decide

/-- Four explicit paths suffice: their only common edge is the new edge
between the second and third triangles. The finite check is kernel-reduced. -/
lemma threePetalPaths_robust (e : Sym2 (Fin 7)) (he : e ∈ threePetalGraph.edgeSet) :
    ∃ i : Fin 4, ∀ a b : Fin 6, (pathGraph 6).Adj a b →
      ((threePetalGraph.deleteEdges {e}) ⊔ edge 4 5).Adj
        (threePetalPath i a) (threePetalPath i b) := by
  have h : ∀ x y : Fin 7, threePetalGraph.Adj x y →
      ∃ i : Fin 4, ∀ a b : Fin 6, (pathGraph 6).Adj a b →
        ((threePetalGraph.deleteEdges {s(x, y)}) ⊔ edge 4 5).Adj
          (threePetalPath i a) (threePetalPath i b) := by
    simp only [sup_adj, deleteEdges_adj, Set.mem_singleton_iff, edge_adj, pathGraph_adj]
    decide
  induction e using Sym2.inductionOn with
  | _ x y => exact h x y he

theorem path_six_in_threePetal_swap (e : Sym2 (Fin 7)) (he : e ∈ threePetalGraph.edgeSet) :
    pathGraph 6 ⊑ (threePetalGraph.deleteEdges {e}) ⊔ edge 4 5 := by
  obtain ⟨i, hi⟩ := threePetalPaths_robust e he
  exact ⟨{ toHom := { toFun := threePetalPath i, map_rel' := fun h ↦ hi _ _ h }
           injective' := threePetalPath_injective i }⟩

/-- A rainbow three-triangle graph already forces a rainbow six-vertex
path in any coloring of the complete graph on its vertices. -/
theorem rainbow_path_six_of_threePetalGraph {C : Type*}
    (c : (⊤ : SimpleGraph (Fin 7)).edgeSet → C)
    (hR : Set.InjOn (extendColor c) threePetalGraph.edgeSet) :
    ∃ f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin 7)), IsRainbow f c := by
  classical
  let d : (⊤ : SimpleGraph (Fin 7)).edgeSet := ⟨s(4, 5), by decide⟩
  by_cases hcol : ∃ e ∈ threePetalGraph.edgeSet, extendColor c d.val = extendColor c e
  · obtain ⟨e, he, hce⟩ := hcol
    let Q := swapRepresentative threePetalGraph e d.val
    have hQ := swapRepresentative_rainbow c threePetalGraph hR ⟨e, he⟩ d hce
    have hle : threePetalGraph.deleteEdges {e} ⊔ edge 4 5 ≤ Q := by
      apply sup_le (deleteEdges_le_swapRepresentative threePetalGraph e d)
      apply (edge_le_iff Q).mpr
      exact Or.inr ((mem_swapRepresentative threePetalGraph e d d.val).mpr (Or.inr rfl))
    obtain ⟨f⟩ := (path_six_in_threePetal_swap e he).trans ⟨Copy.ofLE _ _ hle⟩
    exact ⟨(Copy.ofLE Q ⊤ le_top).comp f, isRainbow_comp_of_color_injOn le_top c hQ f⟩
  · let Q := adjoinRepresentative threePetalGraph d
    have hQ := adjoinRepresentative_rainbow c threePetalGraph hR d
      (fun e he hc ↦ hcol ⟨e, he, hc⟩)
    have he : s(0, 1) ∈ threePetalGraph.edgeSet := by decide
    have hle : threePetalGraph.deleteEdges {s(0, 1)} ⊔ edge 4 5 ≤ Q := by
      apply sup_le ((threePetalGraph.deleteEdges_le _).trans (le_adjoinRepresentative _ d))
      apply (edge_le_iff Q).mpr
      exact Or.inr (added_mem_adjoinRepresentative _ d)
    obtain ⟨f⟩ := (path_six_in_threePetal_swap s(0, 1) he).trans ⟨Copy.ofLE _ _ hle⟩
    exact ⟨(Copy.ofLE Q ⊤ le_top).comp f, isRainbow_comp_of_color_injOn le_top c hQ f⟩

end Erdos1105

#print axioms Erdos1105.rainbow_path_six_of_threePetalGraph
