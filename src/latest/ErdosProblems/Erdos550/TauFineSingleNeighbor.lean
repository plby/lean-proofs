import Mathlib
import ErdosProblems.Erdos550.OffTuranDirect

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A τ-fine separator with at most one seed neighbour per nonseed vertex

This is the strengthened separator used by the amended direct off-Turán route.
Starting with the two-attachment separator, we promote every nonseed vertex
which is adjacent to two of its seeds.  The tree property and the existing
at-most-two-attachments conclusion imply that this one promotion round is
already closed: in each old nonseed component there is at most one promoted
vertex, and deleting it leaves pieces with at most two attachments.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Vertices outside `S` having at least two neighbours in `S`. -/
def doubleSeedNeighbors
    (T : SimpleGraph α) [DecidableRel T.Adj] (S : Finset α) : Finset α :=
  Finset.univ.filter fun v => v ∉ S ∧ 2 ≤ (T.neighborFinset v ∩ S).card

lemma doubleSeedNeighbors_disjoint
    (T : SimpleGraph α) [DecidableRel T.Adj] (S : Finset α) :
    Disjoint S (doubleSeedNeighbors T S) := by
  rw [Finset.disjoint_left]
  intro v hvS hvB
  simpa [doubleSeedNeighbors, hvS] using! hvB

/-- The bipartite subgraph consisting of the edges between old seeds and the
vertices requiring promotion. -/
def seedPromotionGraph
    (T : SimpleGraph α) [DecidableRel T.Adj] (S : Finset α) : SimpleGraph α where
  Adj a b := T.Adj a b ∧
    ((a ∈ S ∧ b ∈ doubleSeedNeighbors T S) ∨
     (b ∈ S ∧ a ∈ doubleSeedNeighbors T S))
  symm := by
    constructor
    intro a b h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    constructor
    intro a h
    exact h.1.ne rfl

lemma promotionGraph_degree_ge_two
    (T : SimpleGraph α) [DecidableRel T.Adj] (S : Finset α)
    {v : α} (hv : v ∈ doubleSeedNeighbors T S) :
    2 ≤ (seedPromotionGraph T S).degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply le_trans (Finset.mem_filter.mp hv).2.2
  apply Finset.card_le_card
  intro s hs
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hs
  simp only [SimpleGraph.mem_neighborFinset, seedPromotionGraph]
  exact ⟨hs.1, Or.inr ⟨hs.2, hv⟩⟩

lemma promotionGraph_active_subset
    (T : SimpleGraph α) [DecidableRel T.Adj] (S : Finset α) :
    (Finset.univ.filter fun v => 0 < (seedPromotionGraph T S).degree v) ⊆
      S ∪ doubleSeedNeighbors T S := by
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_pos] at hv
  obtain ⟨w, hw⟩ := hv
  simp only [SimpleGraph.mem_neighborFinset, seedPromotionGraph] at hw
  rcases hw.2 with h | h
  · exact Finset.mem_union_left _ h.1
  · exact Finset.mem_union_right _ h.2

/-- In a tree, the vertices requiring promotion are no more numerous than the
old seeds.  Count edges in the forest formed by seed--promotion incidences. -/
lemma doubleSeedNeighbors_card_le
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S : Finset α)
    (_hattach : ∀ c : (seedDeleted T S).ConnectedComponent,
      (∃ v ∈ c.supp, v ∉ S) → (componentSeeds T S c).card ≤ 2) :
    (doubleSeedNeighbors T S).card ≤ S.card := by
  let P := seedPromotionGraph T S
  by_cases hB : (doubleSeedNeighbors T S).Nonempty
  · have hactive : (Finset.univ.filter fun v => 0 < P.degree v).Nonempty := by
      obtain ⟨v, hv⟩ := hB
      refine ⟨v, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (promotionGraph_degree_ge_two T S hv).trans_lt' (by omega)
    have hac : P.IsAcyclic := hT.2.anti (by
      intro a b hab
      exact hab.1)
    have he := acyclic_edges_lt_active P hac hactive
    have hbi : P.IsBipartiteWith (S : Set α)
        (doubleSeedNeighbors T S : Set α) := by
      refine ⟨?_, ?_⟩
      · simpa [Finset.disjoint_coe] using! doubleSeedNeighbors_disjoint T S
      · intro a b hab
        rcases hab.2 with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.2, h.1⟩
    have hdeg : 2 * (doubleSeedNeighbors T S).card ≤ P.edgeFinset.card := by
      rw [← P.isBipartiteWith_sum_degrees_eq_card_edges' hbi]
      calc
        2 * (doubleSeedNeighbors T S).card =
            ∑ v ∈ doubleSeedNeighbors T S, 2 := by simp [Nat.mul_comm]
        _ ≤ ∑ v ∈ doubleSeedNeighbors T S, P.degree v :=
          Finset.sum_le_sum fun v hv => promotionGraph_degree_ge_two T S hv
    have ha : (Finset.univ.filter fun v => 0 < P.degree v).card ≤
        (S ∪ doubleSeedNeighbors T S).card := by
      apply Finset.card_le_card
      simpa [P] using! promotionGraph_active_subset T S
    have hdis := doubleSeedNeighbors_disjoint T S
    rw [Finset.card_union_of_disjoint hdis] at ha
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hB]

lemma tree_common_neighbors_unique
    (T : SimpleGraph α) (hT : T.IsTree) {a b x y : α}
    (hab : a ≠ b) (hax : T.Adj a x) (hbx : T.Adj b x)
    (hay : T.Adj a y) (hby : T.Adj b y) : x = y := by
  by_contra hxy
  let wa : T.Walk x y := .cons hax.symm (.cons hay (.nil))
  let wb : T.Walk x y := .cons hbx.symm (.cons hby (.nil))
  have hpa : wa.IsPath := by
    simp [wa, SimpleGraph.Walk.cons_isPath_iff, hxy, hay.ne, hax.symm.ne]
  have hpb : wb.IsPath := by
    simp [wb, SimpleGraph.Walk.cons_isPath_iff, hxy, hby.ne, hbx.symm.ne]
  have he : (⟨wa, hpa⟩ : T.Path x y) = ⟨wb, hpb⟩ := hT.2.path_unique _ _
  have hv := congrArg (fun p : T.Path x y => p.1.getVert 1) he
  simpa [wa, wb] using! hab hv

lemma tree_no_triangle
    (T : SimpleGraph α) (hT : T.IsTree) {a b c : α}
    (hab : T.Adj a b) (hbc : T.Adj b c) (hca : T.Adj c a) : False := by
  let p : T.Walk a c := .cons hab (.cons hbc (.nil))
  have hp : p.IsPath := by
    simp [p, SimpleGraph.Walk.cons_isPath_iff, hca.symm.ne, hab.ne, hbc.ne]
  have he : SimpleGraph.Path.singleton hca.symm =
      (⟨p, hp⟩ : T.Path a c) := hT.2.path_unique _ _
  have hl := congrArg (fun q : T.Path a c => q.1.length) he
  simpa [p] using! hl

/-- One promotion round closes the local two-seed-neighbour condition. -/
lemma outside_promoted_has_at_most_one_seed_neighbor
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S : Finset α)
    (hattach : ∀ c : (seedDeleted T S).ConnectedComponent,
      (∃ v ∈ c.supp, v ∉ S) → (componentSeeds T S c).card ≤ 2) :
    ∀ v ∉ S ∪ doubleSeedNeighbors T S,
      ((T.neighborFinset v) ∩ (S ∪ doubleSeedNeighbors T S)).card ≤ 1 := by
  intro v hv
  rw [Finset.card_le_one_iff]
  intro x y hx hy
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_union] at hx hy
  have hvS : v ∉ S := fun h => hv (Finset.mem_union_left _ h)
  have hvB : v ∉ doubleSeedNeighbors T S := fun h => hv (Finset.mem_union_right _ h)
  rcases hx.2 with hxS | hxB <;> rcases hy.2 with hyS | hyB
  · by_contra hxy
    apply hvB
    simp only [doubleSeedNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hvS, ?_⟩
    have hs : {x,y} ⊆ T.neighborFinset v ∩ S := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact ⟨hx.1, hxS⟩
      · simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact ⟨hy.1, hyS⟩
    have hc := Finset.card_le_card hs
    rw [Finset.card_pair hxy] at hc
    exact hc
  · have hydata := (Finset.mem_filter.mp hyB).2
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (T.neighborFinset y ∩ S).card)
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at ha hb
    have hxa : x ≠ a := fun e => by
      subst a
      exact tree_no_triangle T hT hx.1 ha.1.symm hy.1.symm
    have hxb : x ≠ b := fun e => by
      subst b
      exact tree_no_triangle T hT hx.1 hb.1.symm hy.1.symm
    let c := (seedDeleted T S).connectedComponentMk v
    have hvC : v ∈ c.supp := by simp [c, SimpleGraph.ConnectedComponent.supp]
    have hyC := component_supp_closed_of_nonseed_adj T S c hvC hvS hydata.1 hy.1
    have hsx := seed_mem_componentSeeds_of_adj T S c hxS hvC hx.1.symm
    have hsa := seed_mem_componentSeeds_of_adj T S c ha.2 hyC ha.1.symm
    have hsb := seed_mem_componentSeeds_of_adj T S c hb.2 hyC hb.1.symm
    have hs : {x,a,b} ⊆ componentSeeds T S c := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hsx
      · exact hsa
      · exact hsb
    have hc := Finset.card_le_card hs
    have hc2 := hattach c ⟨v,hvC,hvS⟩
    have hcard : ({x,a,b} : Finset α).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hxa,hxb]), Finset.card_pair hab]
    omega
  · symm
    have hxdata := (Finset.mem_filter.mp hxB).2
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (T.neighborFinset x ∩ S).card)
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at ha hb
    have hya : y ≠ a := fun e => by
      subst a
      exact tree_no_triangle T hT hy.1 ha.1.symm hx.1.symm
    have hyb : y ≠ b := fun e => by
      subst b
      exact tree_no_triangle T hT hy.1 hb.1.symm hx.1.symm
    let c := (seedDeleted T S).connectedComponentMk v
    have hvC : v ∈ c.supp := by simp [c, SimpleGraph.ConnectedComponent.supp]
    have hxC := component_supp_closed_of_nonseed_adj T S c hvC hvS hxdata.1 hx.1
    have hsy := seed_mem_componentSeeds_of_adj T S c hyS hvC hy.1.symm
    have hsa := seed_mem_componentSeeds_of_adj T S c ha.2 hxC ha.1.symm
    have hsb := seed_mem_componentSeeds_of_adj T S c hb.2 hxC hb.1.symm
    have hs : {y,a,b} ⊆ componentSeeds T S c := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hsy
      · exact hsa
      · exact hsb
    have hc := Finset.card_le_card hs
    have hc2 := hattach c ⟨v,hvC,hvS⟩
    have hcard : ({y,a,b} : Finset α).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hya,hyb]), Finset.card_pair hab]
    omega
  · have hxdata := (Finset.mem_filter.mp hxB).2
    have hydata := (Finset.mem_filter.mp hyB).2
    let c := (seedDeleted T S).connectedComponentMk v
    have hvC : v ∈ c.supp := by simp [c, SimpleGraph.ConnectedComponent.supp]
    have hxC := component_supp_closed_of_nonseed_adj T S c hvC hvS hxdata.1 hx.1
    have hyC := component_supp_closed_of_nonseed_adj T S c hvC hvS hydata.1 hy.1
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (T.neighborFinset x ∩ S).card)
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at ha hb
    have hsa := seed_mem_componentSeeds_of_adj T S c ha.2 hxC ha.1.symm
    have hsb := seed_mem_componentSeeds_of_adj T S c hb.2 hxC hb.1.symm
    have hc2 := hattach c ⟨v,hvC,hvS⟩
    have hseedsub : componentSeeds T S c ⊆ {a,b} := by
      intro z hz
      by_contra hn
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      have hs : {a,b,z} ⊆ componentSeeds T S c := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · exact hsa
        · exact hsb
        · exact hz
      have hc := Finset.card_le_card hs
      have hza : z ≠ a := hn.1
      have hzb : z ≠ b := hn.2
      have hcard : ({a,b,z} : Finset α).card = 3 := by
        have hzmem : z ∉ ({a,b} : Finset α) := by simp [hza, hzb]
        have hzcard : (insert z ({a,b} : Finset α)).card = 3 := by
          rw [Finset.card_insert_of_notMem hzmem, Finset.card_pair hab]
        have heq : ({a,b,z} : Finset α) = insert z {a,b} := by
          ext w
          simp [or_comm, or_left_comm]
        rw [heq]
        exact hzcard
      omega
    have hySeeds : T.neighborFinset y ∩ S ⊆ componentSeeds T S c := by
      intro z hz
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hz
      exact seed_mem_componentSeeds_of_adj T S c hz.2 hyC hz.1.symm
    have hyab := hySeeds.trans hseedsub
    have heq : T.neighborFinset y ∩ S = {a,b} :=
      Finset.eq_of_subset_of_card_le hyab (by
        have := Finset.card_pair hab
        omega)
    have hay : T.Adj a y := by
      have : a ∈ T.neighborFinset y ∩ S := by rw [heq]; simp
      exact ((show T.Adj y a by simpa only [SimpleGraph.mem_neighborFinset] using!
        (Finset.mem_inter.mp this).1)).symm
    have hby : T.Adj b y := by
      have : b ∈ T.neighborFinset y ∩ S := by rw [heq]; simp
      exact ((show T.Adj y b by simpa only [SimpleGraph.mem_neighborFinset] using!
        (Finset.mem_inter.mp this).1)).symm
    exact tree_common_neighbors_unique T hT hab ha.1.symm hb.1.symm hay hby

lemma refined_component_support_mem_old
    (T : SimpleGraph α) [DecidableRel T.Adj] (S B : Finset α)
    (c : (seedDeleted T (S ∪ B)).ConnectedComponent)
    {v x : α} (hv : v ∈ c.supp) (hx : x ∈ c.supp) :
    x ∈ ((seedDeleted T S).connectedComponentMk v).supp := by
  have hr : (seedDeleted T (S ∪ B)).Reachable x v := by
    have hx' : (seedDeleted T (S ∪ B)).connectedComponentMk x = c := by
      simpa [SimpleGraph.ConnectedComponent.supp] using! hx
    have hv' : (seedDeleted T (S ∪ B)).connectedComponentMk v = c := by
      simpa [SimpleGraph.ConnectedComponent.supp] using! hv
    have heq := hx'.trans hv'.symm
    simp only [SimpleGraph.connectedComponentMk] at heq
    rw [Quot.eq] at heq
    have he : Equivalence (seedDeleted T (S ∪ B)).Reachable :=
      ⟨SimpleGraph.Reachable.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
    exact he.eqvGen_eq.symm ▸ heq
  have hr' : (seedDeleted T S).Reachable x v := by
    rw [SimpleGraph.Reachable] at hr ⊢
    obtain ⟨w⟩ := hr
    let f : (seedDeleted T (S ∪ B)) →g (seedDeleted T S) := {
      toFun := fun x => x
      map_rel' := fun {a b} hab => by
        rw [seedDeleted_adj_iff] at hab ⊢
        exact ⟨hab.1, fun ha => hab.2.1 (Finset.mem_union_left B ha),
          fun hb => hab.2.2 (Finset.mem_union_left B hb)⟩ }
    exact ⟨w.map f⟩
  have heq : (seedDeleted T S).connectedComponentMk x =
      (seedDeleted T S).connectedComponentMk v := by
    simp only [SimpleGraph.connectedComponentMk]
    rw [Quot.eq]
    have he : Equivalence (seedDeleted T S).Reachable :=
      ⟨SimpleGraph.Reachable.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
    exact he.eqvGen_eq.symm ▸ hr'
  simpa [SimpleGraph.ConnectedComponent.supp] using! heq

lemma old_component_contains_at_most_one_promoted
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S : Finset α)
    (hattach : ∀ c : (seedDeleted T S).ConnectedComponent,
      (∃ v ∈ c.supp, v ∉ S) → (componentSeeds T S c).card ≤ 2)
    (c : (seedDeleted T S).ConnectedComponent)
    (hc : ∃ v ∈ c.supp, v ∉ S) {x y : α}
    (hxC : x ∈ c.supp) (hyC : y ∈ c.supp)
    (hxB : x ∈ doubleSeedNeighbors T S)
    (hyB : y ∈ doubleSeedNeighbors T S) : x = y := by
  have hxdata := (Finset.mem_filter.mp hxB).2
  have hydata := (Finset.mem_filter.mp hyB).2
  have hxSeeds : T.neighborFinset x ∩ S ⊆ componentSeeds T S c := by
    intro z hz
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hz
    exact seed_mem_componentSeeds_of_adj T S c hz.2 hxC hz.1.symm
  have hySeeds : T.neighborFinset y ∩ S ⊆ componentSeeds T S c := by
    intro z hz
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hz
    exact seed_mem_componentSeeds_of_adj T S c hz.2 hyC hz.1.symm
  have hc2 := hattach c hc
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (T.neighborFinset x ∩ S).card)
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at ha hb
  have hxa := seed_mem_componentSeeds_of_adj T S c ha.2 hxC ha.1.symm
  have hxb := seed_mem_componentSeeds_of_adj T S c hb.2 hxC hb.1.symm
  have hsub : componentSeeds T S c ⊆ {a,b} := by
    intro z hz
    by_contra hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    have hs : {a,b,z} ⊆ componentSeeds T S c := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hxa
      · exact hxb
      · exact hz
    have hle := Finset.card_le_card hs
    have hza : z ≠ a := hn.1
    have hzb : z ≠ b := hn.2
    have hcard : ({a,b,z} : Finset α).card = 3 := by
      have hzmem : z ∉ ({a,b} : Finset α) := by simp [hza,hzb]
      have hzcard : (insert z ({a,b} : Finset α)).card = 3 := by
        rw [Finset.card_insert_of_notMem hzmem, Finset.card_pair hab]
      have heq : ({a,b,z} : Finset α) = insert z {a,b} := by
        ext w
        simp [or_comm, or_left_comm]
      rw [heq]
      exact hzcard
    omega
  have hyab := hySeeds.trans hsub
  have heq : T.neighborFinset y ∩ S = {a,b} :=
    Finset.eq_of_subset_of_card_le hyab (by
      have := Finset.card_pair hab
      omega)
  have hay : T.Adj a y := by
    have : a ∈ T.neighborFinset y ∩ S := by rw [heq]; simp
    exact ((show T.Adj y a by simpa only [SimpleGraph.mem_neighborFinset] using!
      (Finset.mem_inter.mp this).1)).symm
  have hby : T.Adj b y := by
    have : b ∈ T.neighborFinset y ∩ S := by rw [heq]; simp
    exact ((show T.Adj y b by simpa only [SimpleGraph.mem_neighborFinset] using!
      (Finset.mem_inter.mp this).1)).symm
  exact tree_common_neighbors_unique T hT hab ha.1.symm hb.1.symm hay hby

lemma component_not_attach_promoted_and_two_neighbors
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    (S' : Finset α) (c : (seedDeleted T S').ConnectedComponent)
    (hc : ∃ v ∈ c.supp, v ∉ S') {p a b : α}
    (hpS : p ∈ S') (haS : a ∈ S') (hbS : b ∈ S')
    (hab : a ≠ b) (hap : T.Adj a p) (hpb : T.Adj p b)
    (haa : a ∈ componentSeeds T S' c)
    (hbb : b ∈ componentSeeds T S' c) : False := by
  obtain ⟨xa, hxaC, haxa⟩ := (mem_componentSeeds_iff T S' c a).mp haa |>.2
  obtain ⟨xb, hxbC, hbxb⟩ := (mem_componentSeeds_iff T S' c b).mp hbb |>.2
  have hreach : (seedDeleted T S').Reachable xa xb := by
    have hxa' : (seedDeleted T S').connectedComponentMk xa = c := by
      simpa [SimpleGraph.ConnectedComponent.supp] using! hxaC
    have hxb' : (seedDeleted T S').connectedComponentMk xb = c := by
      simpa [SimpleGraph.ConnectedComponent.supp] using! hxbC
    have heq := hxa'.trans hxb'.symm
    simp only [SimpleGraph.connectedComponentMk] at heq
    rw [Quot.eq] at heq
    have he : Equivalence (seedDeleted T S').Reachable :=
      ⟨SimpleGraph.Reachable.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
    exact he.eqvGen_eq.symm ▸ heq
  obtain ⟨q⟩ := hreach
  let f : (seedDeleted T S') →g T := {
    toFun := fun x => x
    map_rel' := fun {u v} huv => (seedDeleted_adj_iff T S' u v).mp huv |>.1 }
  let middle : T.Walk xa xb := (q.map f).toPath
  let around : T.Walk a b := (SimpleGraph.Walk.cons haxa middle).concat hbxb.symm
  have hmiddlePath : middle.IsPath := (q.map f).toPath.property
  have haNot : a ∉ middle.support := by
    intro ha
    have haS' : a ∈ S' := haS
    have haMap : a ∈ (q.map f).support :=
      (q.map f).support_toPath_subset (by simpa [middle] using! ha)
    have haQ : a ∈ q.support := by simpa [f] using! haMap
    have haC := deleted_walk_support_mem_component T S' c hxaC q haQ
    exact component_supp_disjoint_seeds T S' c hc a haC haS'
  have hbNot : b ∉ (SimpleGraph.Walk.cons haxa middle).support := by
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
    intro hb
    rcases hb with rfl | hb
    · exact hab rfl
    · have hbMap : b ∈ (q.map f).support :=
        (q.map f).support_toPath_subset (by simpa [middle] using! hb)
      have hbQ : b ∈ q.support := by simpa [f] using! hbMap
      have hbC := deleted_walk_support_mem_component T S' c hxaC q hbQ
      exact component_supp_disjoint_seeds T S' c hc b hbC hbS
  have haround : around.IsPath := by
    apply SimpleGraph.Walk.IsPath.concat
    · exact hmiddlePath.cons haNot
    · exact hbNot
  let short : T.Walk a b := SimpleGraph.Walk.cons hap (SimpleGraph.Walk.cons hpb (.nil))
  have hshort : short.IsPath := by
    have hpa_ne : p ≠ b := hpb.ne
    have hap_ne : a ≠ p := hap.ne
    have hab_ne : a ≠ b := hab
    simp [short, SimpleGraph.Walk.cons_isPath_iff, hpa_ne, hap_ne, hab_ne]
  have heq : (⟨short, hshort⟩ : T.Path a b) = ⟨around, haround⟩ :=
    hT.2.path_unique _ _
  have hpNotMiddle : p ∉ middle.support := by
    intro hp
    have hpMap : p ∈ (q.map f).support :=
      (q.map f).support_toPath_subset (by simpa [middle] using! hp)
    have hpQ : p ∈ q.support := by simpa [f] using! hpMap
    have hpC := deleted_walk_support_mem_component T S' c hxaC q hpQ
    exact component_supp_disjoint_seeds T S' c hc p hpC hpS
  have hpNotAround : p ∉ around.support := by
    simp [around, middle, hpNotMiddle, hap.symm.ne, hpb.ne]
  have hpShort : p ∈ short.support := by simp [short]
  have hwalk : short = around := congrArg Subtype.val heq
  have hpAround : p ∈ around.support := by
    rw [← hwalk]
    exact hpShort
  exact hpNotAround hpAround

/-- Promoting all vertices with two old seed neighbours preserves the
at-most-two-attachments property of every nonseed component. -/
lemma doubleSeedNeighbors_components_two_attachments
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S : Finset α)
    (hattach : ∀ c : (seedDeleted T S).ConnectedComponent,
      (∃ v ∈ c.supp, v ∉ S) → (componentSeeds T S c).card ≤ 2) :
    ∀ c : (seedDeleted T (S ∪ doubleSeedNeighbors T S)).ConnectedComponent,
      (∃ v ∈ c.supp, v ∉ S ∪ doubleSeedNeighbors T S) →
        (componentSeeds T (S ∪ doubleSeedNeighbors T S) c).card ≤ 2 := by
  intro c hc
  obtain ⟨v, hvC, hvNew⟩ := hc
  let B := doubleSeedNeighbors T S
  let d := (seedDeleted T S).connectedComponentMk v
  have hvS : v ∉ S := fun h => hvNew (Finset.mem_union_left _ h)
  have hvD : v ∈ d.supp := by simp [d, SimpleGraph.ConnectedComponent.supp]
  have hdnon : ∃ w ∈ d.supp, w ∉ S := ⟨v, hvD, hvS⟩
  have suppOld : ∀ {x}, x ∈ c.supp → x ∈ d.supp := by
    intro x hx
    exact refined_component_support_mem_old T S B c hvC hx
  have attachOld : ∀ {s}, s ∈ componentSeeds T (S ∪ B) c → s ∈ S →
      s ∈ componentSeeds T S d := by
    intro s hs hsS
    obtain ⟨_, x, hxC, hsx⟩ := (mem_componentSeeds_iff T _ c s).mp hs
    exact seed_mem_componentSeeds_of_adj T S d hsS (suppOld hxC) hsx
  have promotedInside : ∀ {p}, p ∈ componentSeeds T (S ∪ B) c → p ∈ B → p ∈ d.supp := by
    intro p hp hpB
    obtain ⟨_, x, hxC, hpx⟩ := (mem_componentSeeds_iff T _ c p).mp hp
    have hxD := suppOld hxC
    have hxS : x ∉ S := component_supp_disjoint_seeds T S d hdnon x hxD
    have hpS : p ∉ S := (Finset.mem_filter.mp hpB).2.1
    exact component_supp_closed_of_nonseed_adj T S d hxD hxS hpS hpx.symm
  have promotedUnique : ∀ {p q},
      p ∈ componentSeeds T (S ∪ B) c → q ∈ componentSeeds T (S ∪ B) c →
      p ∈ B → q ∈ B → p = q := by
    intro p q hp hq hpB hqB
    exact old_component_contains_at_most_one_promoted T hT S hattach d hdnon
      (promotedInside hp hpB) (promotedInside hq hqB) hpB hqB
  have oneBtwoS : ∀ {p a b},
      p ∈ componentSeeds T (S ∪ B) c → a ∈ componentSeeds T (S ∪ B) c →
      b ∈ componentSeeds T (S ∪ B) c → p ∈ B → a ∈ S → b ∈ S → a ≠ b → False := by
    intro p a b hp ha hb hpB haS hbS hab
    have hpdata := (Finset.mem_filter.mp hpB).2
    obtain ⟨u, hu, w, hw, huw⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (T.neighborFinset p ∩ S).card)
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hu hw
    have hpD := promotedInside hp hpB
    have huOld := seed_mem_componentSeeds_of_adj T S d hu.2 hpD hu.1.symm
    have hwOld := seed_mem_componentSeeds_of_adj T S d hw.2 hpD hw.1.symm
    have haOld := attachOld ha haS
    have hbOld := attachOld hb hbS
    have hc2 := hattach d hdnon
    have haCases : a = u ∨ a = w := by
      by_contra hn
      push_neg at hn
      have hs : {a,u,w} ⊆ componentSeeds T S d := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact haOld
        · exact huOld
        · exact hwOld
      have hle := Finset.card_le_card hs
      have hcard : ({a,u,w} : Finset α).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hn.1,hn.2]), Finset.card_pair huw]
      omega
    have hbCases : b = u ∨ b = w := by
      by_contra hn
      push_neg at hn
      have hs : {b,u,w} ⊆ componentSeeds T S d := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hbOld
        · exact huOld
        · exact hwOld
      have hle := Finset.card_le_card hs
      have hcard : ({b,u,w} : Finset α).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hn.1,hn.2]), Finset.card_pair huw]
      omega
    rcases haCases with rfl | rfl <;> rcases hbCases with rfl | rfl
    · exact hab rfl
    · exact component_not_attach_promoted_and_two_neighbors T hT (S ∪ B) c
        ⟨v, hvC, hvNew⟩
        (Finset.mem_union_right S hpB) (Finset.mem_union_left B hu.2)
        (Finset.mem_union_left B hw.2) huw hu.1.symm hw.1 ha hb
    · exact component_not_attach_promoted_and_two_neighbors T hT (S ∪ B) c
        ⟨v, hvC, hvNew⟩
        (Finset.mem_union_right S hpB) (Finset.mem_union_left B hw.2)
        (Finset.mem_union_left B hu.2) huw.symm hw.1.symm hu.1 ha hb
    · exact hab rfl
  by_contra hn
  have hnot : ¬ (componentSeeds T (S ∪ B) c).card ≤ 2 := by
    simpa [B] using! hn
  have hgt : 2 < (componentSeeds T (S ∪ B) c).card := Nat.lt_of_not_ge hnot
  obtain ⟨s₁, hs₁, s₂, hs₂, s₃, hs₃, h₁₂, h₁₃, h₂₃⟩ :=
    Finset.two_lt_card.mp hgt
  have hU₁ := componentSeeds_subset T (S ∪ B) c hs₁
  have hU₂ := componentSeeds_subset T (S ∪ B) c hs₂
  have hU₃ := componentSeeds_subset T (S ∪ B) c hs₃
  rcases Finset.mem_union.mp hU₁ with hS₁ | hB₁
  · rcases Finset.mem_union.mp hU₂ with hS₂ | hB₂
    · rcases Finset.mem_union.mp hU₃ with hS₃ | hB₃
      · have hs : {s₁,s₂,s₃} ⊆ componentSeeds T S d := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl
          · exact attachOld hs₁ hS₁
          · exact attachOld hs₂ hS₂
          · exact attachOld hs₃ hS₃
        have hle := Finset.card_le_card hs
        have hc2 := hattach d hdnon
        have hcard : ({s₁,s₂,s₃} : Finset α).card = 3 := by simp [h₁₂,h₁₃,h₂₃]
        omega
      · exact oneBtwoS hs₃ hs₁ hs₂ hB₃ hS₁ hS₂ h₁₂
    · rcases Finset.mem_union.mp hU₃ with hS₃ | hB₃
      · exact oneBtwoS hs₂ hs₁ hs₃ hB₂ hS₁ hS₃ h₁₃
      · exact h₂₃ (promotedUnique hs₂ hs₃ hB₂ hB₃)
  · rcases Finset.mem_union.mp hU₂ with hS₂ | hB₂
    · rcases Finset.mem_union.mp hU₃ with hS₃ | hB₃
      · exact oneBtwoS hs₁ hs₂ hs₃ hB₁ hS₂ hS₃ h₂₃
      · exact h₁₃ (promotedUnique hs₁ hs₃ hB₁ hB₃)
    · exact h₁₂ (promotedUnique hs₁ hs₂ hB₁ hB₂)

/-- Component smallness remains monotone when both the old and new bounds are
restricted to components containing a nonseed vertex. -/
lemma promoted_components_small_nonseed
    (T : SimpleGraph α) [DecidableRel T.Adj]
    (S₀ B : Finset α) (K : ℝ)
    (hsmall : ∀ c : (seedDeleted T S₀).ConnectedComponent,
      (∃ v ∈ c.supp, v ∉ S₀) → (Nat.card c.supp : ℝ) ≤ K) :
    ∀ c : (seedDeleted T (S₀ ∪ B)).ConnectedComponent,
      (∃ v ∈ c.supp, v ∉ S₀ ∪ B) → (Nat.card c.supp : ℝ) ≤ K := by
  intro c hc
  obtain ⟨v, hv_mem, hv_notin⟩ := hc
  simp only [Nat.card_eq_fintype_card, Fintype.card_ofFinset, ConnectedComponent.mem_supp_iff] at hv_notin
  -- seedDeleted T (S₀ ∪ B) has fewer edges than seedDeleted T S₀
  have adj_implication : ∀ a b, (seedDeleted T (S₀ ∪ B)).Adj a b → (seedDeleted T S₀).Adj a b := by
    intro a b hadj
    rw [seedDeleted_adj_iff] at hadj ⊢
    exact ⟨hadj.1, fun ha => hadj.2.1 (Finset.mem_union_left B ha), fun hb => hadj.2.2 (Finset.mem_union_left B hb)⟩
  -- All vertices in c.supp are reachable from v in seedDeleted T (S₀ ∪ B), hence in seedDeleted T S₀
  let c' := (seedDeleted T S₀).connectedComponentMk v
  have hsupp_subset : c.supp ⊆ c'.supp := by
    intro x hx
    have hreach_S₀B : (seedDeleted T (S₀ ∪ B)).Reachable x v := by
      simp +decide [SimpleGraph.ConnectedComponent.supp] at hx ⊢
      have hv_eq : (seedDeleted T (S₀ ∪ B)).connectedComponentMk v = c := by
        simp +decide [SimpleGraph.ConnectedComponent.supp] at hv_mem
        exact hv_mem
      have heq : (seedDeleted T (S₀ ∪ B)).connectedComponentMk x =
                 (seedDeleted T (S₀ ∪ B)).connectedComponentMk v := by rw [hx, hv_eq]
      simp only [connectedComponentMk] at heq
      rw [Quot.eq] at heq
      have heqv : Equivalence (seedDeleted T (S₀ ∪ B)).Reachable :=
        ⟨SimpleGraph.Reachable.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
      exact heqv.eqvGen_eq.symm ▸ heq
    have hreach_S₀ : (seedDeleted T S₀).Reachable x v := by
      rw [SimpleGraph.Reachable] at hreach_S₀B ⊢
      obtain ⟨w⟩ := hreach_S₀B
      let f : (seedDeleted T (S₀ ∪ B)) →g (seedDeleted T S₀) := {
        toFun := (fun a => a)
        map_rel' := @fun a b hab => adj_implication a b hab
      }
      refine ⟨w.map f⟩
    simp +decide only [ConnectedComponent.mem_supp_iff]
    have heqv : Equivalence (seedDeleted T S₀).Reachable :=
      ⟨SimpleGraph.Reachable.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
    show Quot.mk (seedDeleted T S₀).Reachable x = Quot.mk (seedDeleted T S₀).Reachable v
    rw [Quot.eq]
    exact heqv.eqvGen_eq.symm ▸ hreach_S₀
  have hcard : Nat.card c.supp ≤ Nat.card c'.supp := by
    apply Set.ncard_le_ncard hsupp_subset
  have hv_in_c' : v ∈ c'.supp := by simp [c']
  exact (hsmall c' ⟨v, hv_in_c', hv_notin.1⟩).trans' (Nat.cast_le.mpr hcard)

/-- The construction behind `tree_tau_fine_two_attachment`, exposing the two
facts needed for a subsequent promotion round. -/
lemma tree_tau_fine_two_attachment_strong_data
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    (τ : ℝ) (hτ : 0 < τ) (hn : (1 : ℝ) ≤ τ * Fintype.card α) :
    ∃ S : Finset α,
      (S.card : ℝ) ≤ 2 / τ ∧
      (∀ c : (seedDeleted T S).ConnectedComponent,
        (∃ v ∈ c.supp, v ∉ S) →
          (Nat.card c.supp : ℝ) ≤ τ * Fintype.card α) ∧
      (∀ c : (seedDeleted T S).ConnectedComponent,
        (∃ v ∈ c.supp, v ∉ S) → (componentSeeds T S c).card ≤ 2) := by
  obtain ⟨S₀, hS₀, hsmall⟩ := tree_tau_fine T hT τ hτ hn
  let B := promotedBranchVertices T S₀
  refine ⟨S₀ ∪ B, ?_, ?_, ?_⟩
  · have hB : B.card ≤ S₀.card := promotedBranchVertices_card_le T hT S₀
    have hu : (S₀ ∪ B).card ≤ S₀.card + B.card := Finset.card_union_le S₀ B
    have hcard : ((S₀ ∪ B).card : ℝ) ≤ 2 * S₀.card := by
      exact_mod_cast hu.trans (by omega)
    calc
      ((S₀ ∪ B).card : ℝ) ≤ 2 * S₀.card := hcard
      _ ≤ 2 * (1 / τ) := by gcongr
      _ = 2 / τ := by ring
  · apply promoted_components_small_nonseed T S₀ B
      (τ * Fintype.card α)
    intro c hc
    simpa only [seedDeleted] using! hsmall c
  · exact promoted_components_two_attachments T hT S₀

/-- A τ-fine two-attachment separator in which every nonseed vertex has at
most one seed neighbour.  Thus any tree vertex adjacent to two seeds is itself
a seed, eliminating same-side two-anchor candidate intersections. -/
theorem tree_tau_fine_single_neighbor_two_attachment
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    (τ : ℝ) (hτ : 0 < τ) (hn : (1 : ℝ) ≤ τ * Fintype.card α) :
    ∃ S : Finset α,
      (S.card : ℝ) ≤ 4 / τ ∧
      (∀ v ∉ S, ((T.neighborFinset v) ∩ S).card ≤ 1) ∧
      (∀ c : (seedDeleted T S).ConnectedComponent,
        (∃ v ∈ c.supp, v ∉ S) →
          (Nat.card c.supp : ℝ) ≤ τ * Fintype.card α ∧
          (componentSeeds T S c).card ≤ 2) := by
  obtain ⟨S₀, hS₀, hsmall, hattach⟩ :=
    tree_tau_fine_two_attachment_strong_data T hT τ hτ hn
  let B := doubleSeedNeighbors T S₀
  refine ⟨S₀ ∪ B, ?_, ?_, ?_⟩
  · have hB : B.card ≤ S₀.card := doubleSeedNeighbors_card_le T hT S₀ hattach
    have hu : (S₀ ∪ B).card ≤ S₀.card + B.card := Finset.card_union_le S₀ B
    have hcard : ((S₀ ∪ B).card : ℝ) ≤ 2 * S₀.card := by
      exact_mod_cast hu.trans (by omega)
    calc
      ((S₀ ∪ B).card : ℝ) ≤ 2 * S₀.card := hcard
      _ ≤ 2 * (2 / τ) := by gcongr
      _ = 4 / τ := by ring
  · exact outside_promoted_has_at_most_one_seed_neighbor T hT S₀ hattach
  · intro c hc
    constructor
    · exact promoted_components_small_nonseed T S₀ B
        (τ * Fintype.card α) hsmall c hc
    · exact doubleSeedNeighbors_components_two_attachments T hT S₀ hattach c hc

end Erdos550
