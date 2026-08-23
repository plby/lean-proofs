import ErdosProblems.Erdos1105.BridgeSwitch
import ErdosProblems.Erdos1105.BridgeCuts

namespace Erdos1105

open SimpleGraph

/-- The bridge-color closure lemma (Yuan's Lemma 9). A color forced to
be a bridge in every connected representative belongs to a nonempty set
of bridge colors covering all edges between the resulting components. -/
theorem exists_good_bridge_set {V C : Type*} {G R : SimpleGraph V} {c : Sym2 V → C}
    (hR : ColorRepresentative G c R) (hconn : R.Preconnected)
    (hcommon : ∃ e ∈ R.edgeSet, AlwaysBridgeColor G c (c e)) :
    ∃ X : Set (Sym2 V), X.Nonempty ∧ X ⊆ R.edgeSet ∧
      (∀ e ∈ X, R.IsBridge e) ∧
      (∀ a b, G.Adj a b → ¬(R.deleteEdges X).Reachable a b →
        ∃ e ∈ X, c e = c s(a, b)) ∧
      (∀ e ∈ R.edgeSet, AlwaysBridgeColor G c (c e) → e ∈ X) := by
  classical
  let B : Set R.edgeSet := {f | ¬∃ e : R.edgeSet, ¬R.IsBridge e.val ∧
    Relation.ReflTransGen (BridgeSwitch G R c) e f}
  let X : Set (Sym2 V) := Subtype.val '' B
  have hXsub : X ⊆ R.edgeSet := by
    rintro _ ⟨e, _, rfl⟩
    exact e.property
  have hXbridge : ∀ e ∈ X, R.IsBridge e := by
    rintro _ ⟨e, he, rfl⟩
    by_contra hnb
    exact he ⟨e, hnb, .refl⟩
  have halways : ∀ e ∈ R.edgeSet, AlwaysBridgeColor G c (c e) → e ∈ X := by
    intro e he hforce
    refine ⟨⟨e, he⟩, ?_, rfl⟩
    rintro ⟨f, hf, hreach⟩
    exact bridge_switch_reachable_not_always_bridge hR hconn hf hreach hforce
  have hXne : X.Nonempty := by
    obtain ⟨e, he, hc⟩ := hcommon
    exact ⟨e, halways e he hc⟩
  refine ⟨X, hXne, hXsub, hXbridge, ?_, halways⟩
  intro a b hab hcross
  obtain ⟨f, hfX, hfcut⟩ := exists_separating_bridge_of_deleted_bridges hconn hXbridge hcross
  obtain ⟨f', hfB, hff⟩ := hfX
  obtain ⟨e, he, hcol⟩ := hR.palette s(a, b) hab
  have heB : (⟨e, he⟩ : R.edgeSet) ∈ B := by
    rintro ⟨start, hs, hreach⟩
    apply hfB
    refine ⟨start, hs, hreach.tail ?_⟩
    refine ⟨?_, a, b, hab, hcol.symm, ?_⟩
    · rw [hff]
      exact hXbridge f ⟨f', hfB, hff⟩
    · rwa [hff]
  exact ⟨e, ⟨⟨e, he⟩, heB, rfl⟩, hcol⟩

end Erdos1105

#print axioms Erdos1105.exists_good_bridge_set
