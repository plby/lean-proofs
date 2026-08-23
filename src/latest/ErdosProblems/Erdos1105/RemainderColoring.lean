import ErdosProblems.Erdos1105.MaxComponentGood
import ErdosProblems.Erdos1105.SpliceGraphs

namespace Erdos1105

open SimpleGraph Finset

/-- Delete a component's vertices and all colors represented inside it. -/
def remainderGraph {V C : Type*} [Fintype V] [DecidableEq V] (G R : SimpleGraph V)
    (c : Sym2 V → C) (S : Finset V) : SimpleGraph (↑(Sᶜ) : Set V) where
  Adj a b := G.Adj a.val b.val ∧
    ∀ e ∈ R.edgeSet, e.toFinset ⊆ S → c e ≠ c s(a.val, b.val)
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨fun a h ↦ G.loopless.irrefl a.val h.1⟩

theorem MaxRepresentativeComponent.remainder_edge {V C : Type*}
    [Fintype V] [DecidableEq V] {G R : SimpleGraph V} {c : Sym2 V → C} {S : Finset V}
    (hmax : MaxRepresentativeComponent G c R S) (a b : (↑(Sᶜ) : Set V)) (hab : R.Adj a.val b.val) :
    (remainderGraph G R c S).Adj a b := by
  refine ⟨hmax.representative.le hab, ?_⟩
  intro e he heS hcol
  have heq := hmax.representative.rainbow he hab hcol
  rw [heq] at heS
  exact mem_compl.mp a.property (pair_toFinset_subset.mp heS).1

/-- A representative of the reduced coloring can be combined with the
original component without losing or duplicating any color. -/
theorem MaxRepresentativeComponent.splice_representative {V C : Type*}
    [Fintype V] [DecidableEq V] {G R : SimpleGraph V} {c : Sym2 V → C} {S : Finset V}
    (hmax : MaxRepresentativeComponent G c R S) {B : SimpleGraph (↑(Sᶜ) : Set V)}
    (hB : ColorRepresentative (remainderGraph G R c S) (inducedColor c (↑(Sᶜ) : Set V)) B) :
    ColorRepresentative G c (spliceGraphs S (R.induce (S : Set V)) B) := by
  constructor
  · intro a b hab
    rcases hab with ⟨_, _, hab⟩ | ⟨_, _, hab⟩
    · exact hmax.representative.le hab
    · exact (hB.le hab).1
  · intro e he f hf hef
    induction e using Sym2.inductionOn with
    | _ a b =>
      induction f using Sym2.inductionOn with
      | _ x y =>
        rcases he with ⟨ha, hb, hab⟩ | ⟨ha, hb, hab⟩ <;>
          rcases hf with ⟨hx, hy, hxy⟩ | ⟨hx, hy, hxy⟩
        · exact hmax.representative.rainbow hab hxy hef
        · exact ((hB.le hxy).2 s(a, b) hab (pair_toFinset_subset.mpr ⟨ha, hb⟩) hef).elim
        · exact ((hB.le hab).2 s(x, y) hxy (pair_toFinset_subset.mpr ⟨hx, hy⟩) hef.symm).elim
        · have h := @hB.rainbow s(⟨a, ha⟩, ⟨b, hb⟩) hab s(⟨x, hx⟩, ⟨y, hy⟩) hxy hef
          exact congrArg (Sym2.map Subtype.val) h
  · intro e he
    obtain ⟨f, hf, hcol⟩ := hmax.representative.palette e he
    induction f using Sym2.inductionOn with
    | _ a b =>
      by_cases ha : a ∈ S
      · have hb := hmax.component.closed a ha b hf
        exact ⟨s(a, b), Or.inl ⟨ha, hb, hf⟩, hcol⟩
      · have hf' : R.Adj a b := hf
        have hb : b ∉ S := fun hb ↦ ha (hmax.component.closed b hb a hf'.symm)
        obtain ⟨x, y, hxy, hc⟩ := hB.palette_adj
          (hmax.remainder_edge ⟨a, mem_compl.mpr ha⟩ ⟨b, mem_compl.mpr hb⟩ hf)
        exact ⟨s(x.val, y.val), Or.inr ⟨x.property, y.property, hxy⟩, hc.trans hcol⟩

end Erdos1105

#print axioms Erdos1105.MaxRepresentativeComponent.splice_representative
