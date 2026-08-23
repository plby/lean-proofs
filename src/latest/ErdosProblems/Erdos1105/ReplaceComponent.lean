import ErdosProblems.Erdos1105.MaxComponentCross

namespace Erdos1105

open SimpleGraph Finset

theorem ColorRepresentative.palette_adj {V C : Type*} {G R : SimpleGraph V}
    {c : Sym2 V → C} (hR : ColorRepresentative G c R) {a b : V} (hab : G.Adj a b) :
    ∃ x y, R.Adj x y ∧ c s(x, y) = c s(a, b) := by
  obtain ⟨e, he, hcol⟩ := hR.palette s(a, b) hab
  induction e using Sym2.inductionOn with
  | _ x y => exact ⟨x, y, he, hcol⟩

/-- Replace one entire component, retaining the graph on its complement. -/
def replaceComponent {V : Type*} (R : SimpleGraph V) (S : Finset V)
    (K : SimpleGraph (S : Set V)) : SimpleGraph V where
  Adj a b := (∃ ha : a ∈ S, ∃ hb : b ∈ S, K.Adj ⟨a, ha⟩ ⟨b, hb⟩) ∨
    (R.Adj a b ∧ a ∉ S ∧ b ∉ S)
  symm := by
    constructor
    intro a b h
    rcases h with ⟨ha, hb, h⟩ | ⟨h, ha, hb⟩
    · exact Or.inl ⟨hb, ha, h.symm⟩
    · exact Or.inr ⟨h.symm, hb, ha⟩
  loopless := by
    constructor
    intro a h
    rcases h with ⟨ha, _, h⟩ | ⟨h, _, _⟩
    · exact K.loopless.irrefl ⟨a, ha⟩ h
    · exact R.loopless.irrefl a h

theorem replaceComponent_is_component {V : Type*} {R : SimpleGraph V} {S : Finset V}
    (hne : S.Nonempty) {K : SimpleGraph (S : Set V)} (hK : K.Preconnected) :
    GraphComponent (replaceComponent R S K) S := by
  constructor
  · exact hne
  · apply hK.mono
    intro a b hab
    exact Or.inl ⟨a.property, b.property, hab⟩
  · intro a ha b hab
    rcases hab with ⟨_, hb, _⟩ | ⟨_, hna, _⟩
    · exact hb
    · exact (hna ha).elim

theorem MaxRepresentativeComponent.internal_external_color_ne {V C : Type*}
    [Fintype V] [DecidableEq V] {G R : SimpleGraph V} {c : Sym2 V → C} {S : Finset V}
    (hmax : MaxRepresentativeComponent G c R S) {a b x y : V}
    (ha : a ∈ S) (hb : b ∈ S) (hab : G.Adj a b) (hxy : R.Adj x y) (hx : x ∉ S) :
    c s(a, b) ≠ c s(x, y) := by
  intro heq
  obtain ⟨e, he, heS, hcol⟩ := hmax.internal_palette ha hb hab
  have h := hmax.representative.rainbow he hxy (hcol.trans heq)
  rw [h] at heS
  exact hx (pair_toFinset_subset.mp heS).1

theorem MaxRepresentativeComponent.replace_representative {V C : Type*}
    [Fintype V] [DecidableEq V] {G R : SimpleGraph V} {c : Sym2 V → C} {S : Finset V}
    (hmax : MaxRepresentativeComponent G c R S) {K : SimpleGraph (S : Set V)}
    (hK : ColorRepresentative (G.induce (S : Set V)) (inducedColor c S) K) :
    ColorRepresentative G c (replaceComponent R S K) := by
  classical
  constructor
  · intro a b hab
    rcases hab with ⟨ha, hb, hab⟩ | ⟨hab, _, _⟩
    · exact hK.le hab
    · exact hmax.representative.le hab
  · intro e he f hf hef
    induction e using Sym2.inductionOn with
    | _ a b =>
      induction f using Sym2.inductionOn with
      | _ x y =>
        rcases he with ⟨ha, hb, hab⟩ | ⟨hab, ha, hb⟩ <;>
          rcases hf with ⟨hx, hy, hxy⟩ | ⟨hxy, hx, hy⟩
        · have h := @hK.rainbow s(⟨a, ha⟩, ⟨b, hb⟩) hab s(⟨x, hx⟩, ⟨y, hy⟩) hxy hef
          exact congrArg (Sym2.map Subtype.val) h
        · exact (hmax.internal_external_color_ne ha hb (hK.le hab) hxy hx hef).elim
        · exact (hmax.internal_external_color_ne hx hy (hK.le hxy) hab ha hef.symm).elim
        · exact hmax.representative.rainbow hab hxy hef
  · intro e he
    obtain ⟨f, hf, hcol⟩ := hmax.representative.palette e he
    induction f using Sym2.inductionOn with
    | _ a b =>
      by_cases ha : a ∈ S
      · have hb := hmax.component.closed a ha b hf
        obtain ⟨x, y, hxy, hc⟩ := hK.palette_adj
          (show (G.induce (S : Set V)).Adj ⟨a, ha⟩ ⟨b, hb⟩ from hmax.representative.le hf)
        exact ⟨s(x.val, y.val), Or.inl ⟨x.property, y.property, hxy⟩, hc.trans hcol⟩
      · have hf' : R.Adj a b := hf
        have hb : b ∉ S := fun hb ↦ ha (hmax.component.closed b hb a hf'.symm)
        exact ⟨s(a, b), Or.inr ⟨hf, ha, hb⟩, hcol⟩

/-- Every cross-component color is a forced bridge color for the entire
induced coloring, not merely for the chosen representative. -/
theorem MaxRepresentativeComponent.cross_alwaysBridgeColor {V C : Type*}
    [Fintype V] [DecidableEq V] {G R : SimpleGraph V} {c : Sym2 V → C} {S : Finset V}
    (hmax : MaxRepresentativeComponent G c R S) {a b : V}
    (ha : a ∈ S) (hb : b ∉ S) (hab : G.Adj a b) :
    AlwaysBridgeColor (G.induce (S : Set V)) (inducedColor c S) (c s(a, b)) := by
  intro K hK hconn e he hcol
  let Q := replaceComponent R S K
  have hQ := hmax.replace_representative hK
  have hS : GraphComponent Q S := replaceComponent_is_component hmax.component.nonempty hconn
  let φ : K →g Q :=
    { toFun := Subtype.val
      map_rel' := fun {x y} h ↦ Or.inl ⟨x.property, y.property, h⟩ }
  have heQ : Sym2.map Subtype.val e ∈ Q.edgeSet := φ.map_mem_edgeSet he
  have hbridge := hmax.cross_bridge hQ hS ha hb hab ⟨Sym2.map Subtype.val e, heQ⟩ hcol
  have hbridge' := isBridge_induce_of_isBridge Q (S : Set V) e hbridge
  have hle : K ≤ Q.induce (S : Set V) :=
    fun x y h ↦ Or.inl ⟨x.property, y.property, h⟩
  exact SimpleGraph.IsBridge.anti hle hbridge'

end Erdos1105

#print axioms Erdos1105.MaxRepresentativeComponent.cross_alwaysBridgeColor
