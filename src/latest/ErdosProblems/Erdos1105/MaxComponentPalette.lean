import ErdosProblems.Erdos1105.RepresentativeComponents

namespace Erdos1105

open SimpleGraph Finset

lemma pair_toFinset_subset {V : Type*} [DecidableEq V] {a b : V} {S : Finset V} :
    (s(a, b) : Sym2 V).toFinset ⊆ S ↔ a ∈ S ∧ b ∈ S := by
  constructor
  · intro h
    exact ⟨h (by simp), h (by simp)⟩
  · rintro ⟨ha, hb⟩ x hx
    have hx : x = a ∨ x = b := by simpa using hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb

theorem GraphComponent.swap_internal_external {V : Type*} [DecidableEq V]
    {R : SimpleGraph V} {S : Finset V} (hS : GraphComponent R S)
    {e : Sym2 V} (he : ¬e.toFinset ⊆ S) {a b : V}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    GraphComponent (swapRepresentative R e s(a, b)) S := by
  classical
  let d : (⊤ : SimpleGraph V).edgeSet := ⟨s(a, b), by simpa using hab⟩
  constructor
  · exact hS.nonempty
  · apply hS.connected.mono
    intro x y hxy
    change s(x.val, y.val) ∈ (swapRepresentative R e d.val).edgeSet
    apply (mem_swapRepresentative R e d _).mpr
    refine Or.inl ⟨hxy, ?_⟩
    intro h
    apply he
    rw [← h]
    exact pair_toFinset_subset.mpr ⟨x.property, y.property⟩
  · intro x hx y hxy
    rcases (mem_swapRepresentative R e d s(x, y)).mp hxy with h | h
    · exact hS.closed x hx y h.1
    · rcases Sym2.eq_iff.mp h with h | h
      · exact h.2 ▸ hb
      · exact h.2 ▸ ha

/-- All colors used inside a maximum-order, maximum-edge component
already have their representatives inside that component. -/
theorem MaxRepresentativeComponent.internal_palette {V C : Type*}
    [Fintype V] [DecidableEq V] {G R : SimpleGraph V} {c : Sym2 V → C} {S : Finset V}
    (hmax : MaxRepresentativeComponent G c R S) {a b : V}
    (ha : a ∈ S) (hb : b ∈ S) (hab : G.Adj a b) :
    ∃ e ∈ R.edgeSet, e.toFinset ⊆ S ∧ c e = c s(a, b) := by
  classical
  obtain ⟨e, he, hcol⟩ := hmax.representative.palette s(a, b) hab
  refine ⟨e, he, ?_, hcol⟩
  by_contra hout
  let d : G.edgeSet := ⟨s(a, b), hab⟩
  let d' : (⊤ : SimpleGraph V).edgeSet := ⟨s(a, b), edgeSet_mono le_top hab⟩
  let Q := swapRepresentative R e s(a, b)
  have hQ : ColorRepresentative G c Q := hmax.representative.swap ⟨e, he⟩ d hcol.symm
  have hcomp : GraphComponent Q S :=
    hmax.component.swap_internal_external hout ha hb hab.ne
  have hnot : s(a, b) ∉ R.edgeSet := by
    intro h
    have heq := hmax.representative.rainbow h he hcol.symm
    exact hout (heq ▸ pair_toFinset_subset.mpr ⟨ha, hb⟩)
  have hsub : E767EGApi.edgesInside R S ⊆ E767EGApi.edgesInside Q S := by
    intro f hf
    obtain ⟨hfR, hfS⟩ := mem_filter.mp hf
    apply mem_filter.mpr
    refine ⟨?_, hfS⟩
    apply mem_edgeFinset.mpr
    apply (mem_swapRepresentative R e d' f).mpr
    exact Or.inl ⟨mem_edgeFinset.mp hfR, fun h ↦ hout (h ▸ hfS)⟩
  have hdQ : s(a, b) ∈ E767EGApi.edgesInside Q S := by
    apply mem_filter.mpr
    exact ⟨mem_edgeFinset.mpr ((mem_swapRepresentative R e d' _).mpr (Or.inr rfl)),
      pair_toFinset_subset.mpr ⟨ha, hb⟩⟩
  have hdR : s(a, b) ∉ E767EGApi.edgesInside R S := by
    exact fun h ↦ hnot (mem_edgeFinset.mp (mem_filter.mp h).1)
  have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨hsub, fun h ↦ hdR (h ▸ hdQ)⟩)
  exact (not_lt_of_ge (hmax.max_edges Q hQ hcomp)) hlt

def inducedColor {V C : Type*} (c : Sym2 V → C) (S : Set V) : Sym2 S → C :=
  c ∘ Sym2.map Subtype.val

theorem MaxRepresentativeComponent.induced_representative {V C : Type*}
    [Fintype V] [DecidableEq V] {G R : SimpleGraph V} {c : Sym2 V → C} {S : Finset V}
    (hmax : MaxRepresentativeComponent G c R S) :
    ColorRepresentative (G.induce (S : Set V)) (inducedColor c S) (R.induce (S : Set V)) := by
  classical
  constructor
  · exact fun _ _ h ↦ hmax.representative.le h
  · intro e he f hf hef
    apply Sym2.map.injective Subtype.val_injective
    let φ : R.induce (S : Set V) →g R := ⟨Subtype.val, fun h ↦ h⟩
    exact hmax.representative.rainbow
      (φ.map_mem_edgeSet he) (φ.map_mem_edgeSet hf) hef
  · intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      obtain ⟨f, hf, hfS, hcol⟩ := hmax.internal_palette a.property b.property he
      induction f using Sym2.inductionOn with
      | _ x y =>
        obtain ⟨hx, hy⟩ := pair_toFinset_subset.mp hfS
        exact ⟨s(⟨x, hx⟩, ⟨y, hy⟩), hf, hcol⟩

end Erdos1105

#print axioms Erdos1105.MaxRepresentativeComponent.internal_palette
