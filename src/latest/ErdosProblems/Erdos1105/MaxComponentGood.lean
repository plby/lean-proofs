import ErdosProblems.Erdos1105.ReplaceComponent
import ErdosProblems.Erdos1105.GoodColoring

namespace Erdos1105

open SimpleGraph Finset

/-- The first component in the recursive decomposition has bridge
colors covering both its internal cuts and every edge to its complement.
If there are no ambient edges to the complement, no bridges are removed. -/
theorem MaxRepresentativeComponent.good_bridge_set {V C : Type*}
    [Fintype V] [DecidableEq V] {G R : SimpleGraph V} {c : Sym2 V → C} {S : Finset V}
    (hmax : MaxRepresentativeComponent G c R S) :
    ∃ X : Set (Sym2 (S : Set V)), X ⊆ (R.induce (S : Set V)).edgeSet ∧
      (∀ e ∈ X, (R.induce (S : Set V)).IsBridge e) ∧
      (∀ a b : (S : Set V), G.Adj a.val b.val →
        ¬((R.induce (S : Set V)).deleteEdges X).Reachable a b →
          ∃ e ∈ X, inducedColor c S e = c s(a.val, b.val)) ∧
      (∀ a ∈ S, ∀ b ∉ S, G.Adj a b → ∃ e ∈ X, inducedColor c S e = c s(a, b)) := by
  classical
  by_cases hcross : ∃ a ∈ S, ∃ b ∉ S, G.Adj a b
  · obtain ⟨a, ha, b, hb, hab⟩ := hcross
    have hcommon : ∃ e ∈ (R.induce (S : Set V)).edgeSet,
        AlwaysBridgeColor (G.induce (S : Set V)) (inducedColor c S) (inducedColor c S e) := by
      obtain ⟨e, he, hcol⟩ := hmax.representative.palette s(a, b) hab
      have heS := hmax.cross_internal hmax.representative hmax.component ha hb hab ⟨e, he⟩ hcol
      induction e using Sym2.inductionOn with
      | _ x y =>
        obtain ⟨hx, hy⟩ := pair_toFinset_subset.mp heS
        refine ⟨s(⟨x, hx⟩, ⟨y, hy⟩), he, ?_⟩
        change AlwaysBridgeColor _ _ (c s(x, y))
        rw [hcol]
        exact hmax.cross_alwaysBridgeColor ha hb hab
    obtain ⟨X, _, hsub, hbridge, hinside, halways⟩ := exists_good_bridge_set
      hmax.induced_representative hmax.component.connected hcommon
    refine ⟨X, hsub, hbridge, hinside, ?_⟩
    intro a ha b hb hab
    obtain ⟨e, he, hcol⟩ := hmax.representative.palette s(a, b) hab
    have heS := hmax.cross_internal hmax.representative hmax.component ha hb hab ⟨e, he⟩ hcol
    induction e using Sym2.inductionOn with
    | _ x y =>
      obtain ⟨hx, hy⟩ := pair_toFinset_subset.mp heS
      refine ⟨s(⟨x, hx⟩, ⟨y, hy⟩), halways _ he ?_, hcol⟩
      change AlwaysBridgeColor _ _ (c s(x, y))
      rw [hcol]
      exact hmax.cross_alwaysBridgeColor ha hb hab
  · refine ⟨∅, Set.empty_subset _, by simp, ?_, ?_⟩
    · intro a b _ hnot
      exact (hnot (by simpa using hmax.component.connected a b)).elim
    · intro a ha b hb hab
      exact (hcross ⟨a, ha, b, hb, hab⟩).elim

end Erdos1105

#print axioms Erdos1105.MaxRepresentativeComponent.good_bridge_set
