import ErdosProblems.Erdos1105.SwapRepresentative
import ErdosProblems.Erdos1105.HamiltonianDeletion

namespace Erdos1105

open SimpleGraph

/-- A representative of the colors used by an arbitrary ambient graph.
The label function is defined on unordered pairs only for convenience;
the palette and injectivity conditions refer exclusively to actual edges. -/
structure ColorRepresentative {V C : Type*} (G : SimpleGraph V) (c : Sym2 V → C)
    (R : SimpleGraph V) : Prop where
  le : R ≤ G
  rainbow : Set.InjOn c R.edgeSet
  palette : ∀ e ∈ G.edgeSet, ∃ f ∈ R.edgeSet, c f = c e

theorem ColorRepresentative.swap {V C : Type*} {G R : SimpleGraph V} {c : Sym2 V → C}
    (hR : ColorRepresentative G c R) (e : R.edgeSet) (d : G.edgeSet) (hcol : c d.val = c e.val) :
    ColorRepresentative G c (swapRepresentative R e.val d.val) := by
  let d' : (⊤ : SimpleGraph V).edgeSet := ⟨d.val, edgeSet_mono le_top d.property⟩
  constructor
  · intro a b hab
    rcases (mem_swapRepresentative R e.val d' s(a, b)).mp hab with h | h
    · exact hR.le h.1
    · change s(a, b) ∈ G.edgeSet
      rw [h]
      exact d.property
  · intro a ha b hb hab
    rcases (mem_swapRepresentative R e.val d' a).mp ha with ⟨ha, hane⟩ | rfl <;>
      rcases (mem_swapRepresentative R e.val d' b).mp hb with ⟨hb, hbne⟩ | rfl
    · exact hR.rainbow ha hb hab
    · exact (hane (hR.rainbow ha e.property (hab.trans hcol))).elim
    · exact (hbne (hR.rainbow hb e.property (hab.symm.trans hcol))).elim
    · rfl
  · intro a ha
    obtain ⟨f, hf, hfa⟩ := hR.palette a ha
    by_cases hfe : f = e.val
    · exact ⟨d.val, (mem_swapRepresentative R e.val d' d.val).mpr (Or.inr rfl),
        hcol.trans (hfe ▸ hfa)⟩
    · exact ⟨f, (mem_swapRepresentative R e.val d' f).mpr (Or.inl ⟨hf, hfe⟩), hfa⟩

theorem reachable_delete_of_not_isBridge {V : Type*} (G : SimpleGraph V)
    {e : Sym2 V} {u v : V} (hne : ¬G.IsBridge e) (huv : G.Reachable u v) :
    (G.deleteEdges {e}).Reachable u v := by
  induction e using Sym2.inductionOn with
  | _ a b => exact reachable_delete_edge_of_not_isBridge G hne huv

theorem preconnected_swap_of_not_isBridge {V : Type*} {R : SimpleGraph V}
    (hconn : R.Preconnected) {e : Sym2 V} (hne : ¬R.IsBridge e)
    (d : (⊤ : SimpleGraph V).edgeSet) : (swapRepresentative R e d.val).Preconnected := by
  intro u v
  exact (reachable_delete_of_not_isBridge R hne (hconn u v)).mono
    (deleteEdges_le_swapRepresentative R e d)

/-- A color which labels a bridge in every connected representative. -/
def AlwaysBridgeColor {V C : Type*} (G : SimpleGraph V) (c : Sym2 V → C) (i : C) : Prop :=
  ∀ R : SimpleGraph V, ColorRepresentative G c R → R.Preconnected →
    ∀ e ∈ R.edgeSet, c e = i → R.IsBridge e

end Erdos1105

#print axioms Erdos1105.ColorRepresentative.swap
