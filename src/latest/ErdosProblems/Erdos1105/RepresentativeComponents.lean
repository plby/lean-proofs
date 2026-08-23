import ErdosProblems.Erdos1105.ColorRepresentative
import ErdosProblems.Erdos1105.Disintegration

namespace Erdos1105

open SimpleGraph Finset

theorem exists_colorRepresentative {V C : Type*} (G : SimpleGraph V) (c : Sym2 V → C) :
    ∃ R, ColorRepresentative G c R := by
  classical
  let P := Set.range (fun e : G.edgeSet ↦ c e.val)
  have hpick : ∀ i : P, ∃ e : G.edgeSet, c e.val = i.val := fun i ↦ i.property
  choose pick hpick using hpick
  let R := fromEdgeSet (Set.range fun i : P ↦ (pick i).val)
  have hR : R.edgeSet = Set.range (fun i : P ↦ (pick i).val) := by
    rw [edgeSet_fromEdgeSet]
    ext e
    constructor
    · exact fun h ↦ h.1
    · rintro ⟨i, rfl⟩
      exact ⟨Set.mem_range_self i, G.not_isDiag_of_mem_edgeSet (pick i).property⟩
  refine ⟨R, ?_, ?_, ?_⟩
  · rw [← edgeSet_subset_edgeSet, hR]
    rintro _ ⟨i, rfl⟩
    exact (pick i).property
  · intro e he f hf hcol
    rw [hR] at he hf
    obtain ⟨i, rfl⟩ := he
    obtain ⟨j, rfl⟩ := hf
    have hij : i = j := Subtype.ext ((hpick i).symm.trans (hcol.trans (hpick j)))
    exact congrArg (fun i ↦ (pick i).val) hij
  · intro e he
    let i : P := ⟨c e, ⟨⟨e, he⟩, rfl⟩⟩
    exact ⟨(pick i).val, hR ▸ Set.mem_range_self i, hpick i⟩

/-- A connected component represented by its finite vertex set. -/
structure GraphComponent {V : Type*} (R : SimpleGraph V) (S : Finset V) : Prop where
  nonempty : S.Nonempty
  connected : (R.induce (S : Set V)).Preconnected
  closed : ∀ a ∈ S, ∀ b, R.Adj a b → b ∈ S

theorem GraphComponent.mem_of_reachable {V : Type*} {R : SimpleGraph V} {S : Finset V}
    (hS : GraphComponent R S) {a b : V} (ha : a ∈ S) (hab : R.Reachable a b) : b ∈ S := by
  obtain ⟨p⟩ := hab
  induction p with
  | nil => exact ha
  | @cons u v w huv p ih => exact ih (hS.closed u ha v huv)

theorem GraphComponent.reachable {V : Type*} {R : SimpleGraph V} {S : Finset V}
    (hS : GraphComponent R S) {a b : V} (ha : a ∈ S) (hb : b ∈ S) : R.Reachable a b :=
  (hS.connected ⟨a, ha⟩ ⟨b, hb⟩).map
    (show R.induce (S : Set V) →g R from ⟨Subtype.val, fun h ↦ h⟩)

noncomputable def componentVertices {V : Type*} [Fintype V] (R : SimpleGraph V)
    (D : R.ConnectedComponent) : Finset V := by
  classical
  exact univ.filter (fun v ↦ v ∈ D.supp)

@[simp] theorem mem_componentVertices {V : Type*} [Fintype V] (R : SimpleGraph V)
    (D : R.ConnectedComponent) (v : V) : v ∈ componentVertices R D ↔ v ∈ D.supp := by
  classical
  simp [componentVertices]

theorem graphComponent_supp {V : Type*} [Fintype V] (R : SimpleGraph V)
    (D : R.ConnectedComponent) : GraphComponent R (componentVertices R D) := by
  classical
  constructor
  · obtain ⟨a, ha⟩ := D.nonempty_supp
    exact ⟨a, (mem_componentVertices R D a).mpr ha⟩
  · intro a b
    let φ : D.toSimpleGraph →g R.induce (componentVertices R D : Set V) :=
      { toFun := fun x ↦ ⟨x.val, (mem_componentVertices R D x.val).mpr x.property⟩
        map_rel' := fun h ↦ h }
    exact (D.reachable_toSimpleGraph ((mem_componentVertices R D a.val).mp a.property)
      ((mem_componentVertices R D b.val).mp b.property)).map φ
  · intro a ha b hab
    exact (mem_componentVertices R D b).mpr
      (D.mem_supp_of_adj_mem_supp ((mem_componentVertices R D a).mp ha) hab)

theorem exists_graphComponent {V : Type*} [Fintype V] (R : SimpleGraph V) (a : V) :
    ∃ S, GraphComponent R S ∧ a ∈ S := by
  classical
  refine ⟨componentVertices R (R.connectedComponentMk a), graphComponent_supp R _, ?_⟩
  simp

/-- Maximize component order first, then its number of edges. -/
structure MaxRepresentativeComponent {V C : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : Sym2 V → C) (R : SimpleGraph V) (S : Finset V) : Prop where
  representative : ColorRepresentative G c R
  component : GraphComponent R S
  max_order : ∀ Q T, ColorRepresentative G c Q → GraphComponent Q T → T.card ≤ S.card
  max_edges : ∀ Q, ColorRepresentative G c Q → GraphComponent Q S →
    (by classical exact (E767EGApi.edgesInside Q S).card) ≤
      (by classical exact (E767EGApi.edgesInside R S).card)

theorem exists_maxRepresentativeComponent {V C : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (G : SimpleGraph V) (c : Sym2 V → C) :
    ∃ R S, MaxRepresentativeComponent G c R S := by
  classical
  let A := (univ : Finset (SimpleGraph V × Finset V)).filter
    (fun p ↦ ColorRepresentative G c p.1 ∧ GraphComponent p.1 p.2)
  have hA : A.Nonempty := by
    obtain ⟨R, hR⟩ := exists_colorRepresentative G c
    obtain ⟨a⟩ := ‹Nonempty V›
    obtain ⟨S, hS, _⟩ := exists_graphComponent R a
    exact ⟨(R, S), mem_filter.mpr ⟨mem_univ _, hR, hS⟩⟩
  obtain ⟨p, hp, hpmax⟩ := A.exists_max_image (fun p ↦ p.2.card) hA
  let B := A.filter (fun q ↦ q.2.card = p.2.card)
  have hB : B.Nonempty := ⟨p, mem_filter.mpr ⟨hp, rfl⟩⟩
  obtain ⟨q, hq, hqmax⟩ := B.exists_max_image
    (fun q ↦ (E767EGApi.edgesInside q.1 q.2).card) hB
  have hqA := (mem_filter.mp hq).1
  have hqcard := (mem_filter.mp hq).2
  have hqprop := (mem_filter.mp hqA).2
  refine ⟨q.1, q.2, hqprop.1, hqprop.2, ?_, ?_⟩
  · intro R S hR hS
    rw [hqcard]
    exact hpmax (R, S) (mem_filter.mpr ⟨mem_univ _, hR, hS⟩)
  · intro R hR hS
    exact hqmax (R, q.2) (mem_filter.mpr
      ⟨mem_filter.mpr ⟨mem_univ _, hR, hS⟩, hqcard⟩)

/-- In any representative, a connected set has at most the maximal
component order. This avoids requiring the set itself to be a component. -/
theorem MaxRepresentativeComponent.card_le {V C : Type*} [Fintype V] [DecidableEq V]
    {G R : SimpleGraph V} {c : Sym2 V → C} {S : Finset V}
    (hmax : MaxRepresentativeComponent G c R S) {Q : SimpleGraph V}
    (hQ : ColorRepresentative G c Q) {T : Finset V} {a : V} (ha : a ∈ T)
    (hT : ∀ b ∈ T, Q.Reachable a b) : T.card ≤ S.card := by
  obtain ⟨U, hU, haU⟩ := exists_graphComponent Q a
  apply (card_le_card (show T ⊆ U from fun b hb ↦ hU.mem_of_reachable haU (hT b hb))).trans
  exact hmax.max_order Q U hQ hU

end Erdos1105

#print axioms Erdos1105.exists_maxRepresentativeComponent
