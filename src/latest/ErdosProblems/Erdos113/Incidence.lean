import ErdosProblems.Erdos113.ManyLifts
import ErdosProblems.Erdos113.Paths

open scoped SimpleGraph

namespace Erdos113Incidence

noncomputable section

open Erdos113Cycles Erdos113Alternating56 Erdos113LiftCounting
  Erdos113ManyLifts

variable {T V : Type*} [Fintype T] [DecidableEq T]
  [Fintype V] [DecidableEq V]

def Linked {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (t : T) (y : V) : Prop :=
  (∃ b, y ∈ L.middle t b) ∨ ∃ a, y ∈ L.middle a t

noncomputable def leftPartners {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (t : T) : Finset V :=
  by classical exact Finset.univ.filter (Linked L t)

noncomputable def rightPartners {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (y : V) : Finset T :=
  by classical exact Finset.univ.filter fun t ↦ Linked L t y

@[simp] lemma mem_leftPartners {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {t : T} {y : V} :
    y ∈ leftPartners L t ↔ Linked L t y := by
  simp [leftPartners]

@[simp] lemma mem_rightPartners {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {t : T} {y : V} :
    t ∈ rightPartners L y ↔ Linked L t y := by
  simp [rightPartners]

lemma linked_ne_embed {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {t : T} {y : V} (h : Linked L t y) (u : T) :
    y ≠ L.embed u := by
  rcases h with ⟨b, hy⟩ | ⟨a, hy⟩
  · exact L.middle_disjoint hy u
  · exact L.middle_disjoint hy u

def incidenceRel {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (u y : V) : Prop :=
  ∃ t, L.embed t = u ∧ Linked L t y

def incidenceGraph {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) : SimpleGraph V :=
  SimpleGraph.fromRel (incidenceRel L)

noncomputable instance incidenceGraph_decidableRel
    {F : SimpleGraph T} {G : SimpleGraph V} (L : LiftSystem F G) :
    DecidableRel (incidenceGraph L).Adj := Classical.decRel _

@[simp] lemma incidenceGraph_adj_iff {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {u y : V} :
    (incidenceGraph L).Adj u y ↔
      u ≠ y ∧ (incidenceRel L u y ∨ incidenceRel L y u) := by
  exact SimpleGraph.fromRel_adj _ _ _

lemma incidenceGraph_adj_embed_of_linked
    {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {t : T} {y : V} (h : Linked L t y) :
    (incidenceGraph L).Adj (L.embed t) y := by
  rw [incidenceGraph_adj_iff]
  exact ⟨(linked_ne_embed L h t).symm, Or.inl ⟨t, rfl, h⟩⟩

lemma liftedTuple_hom_incidence {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {p : (x : Fin 28 → T) × (Fin 28 → V)}
    (hp : p ∈ liftPairs F G L) :
    IsHomCycle (incidenceGraph L) (liftedTuple L p) := by
  have hpdata := (mem_liftPairs L).mp hp
  have hchoices := (mem_validChoices.mp hpdata.2).1
  apply alternatingTuple_hom
  · intro i
    apply incidenceGraph_adj_embed_of_linked
    exact Or.inl ⟨p.1 (i + 1), hchoices i⟩
  · intro i
    exact (incidenceGraph_adj_embed_of_linked L
      (Or.inr ⟨p.1 i, hchoices i⟩)).symm

theorem liftedCycles_genuine_incidence {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {z : Fin 56 → V}
    (hz : z ∈ liftedCycles F G L) :
    IsGenuineCycle (incidenceGraph L) z := by
  rw [liftedCycles, Finset.mem_image] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  exact ⟨(liftedTuple_genuine L hp).1, liftedTuple_hom_incidence L hp⟩

noncomputable def embeddedVertices {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) : Finset V :=
  Finset.univ.image L.embed

def incidenceSide {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (v : V) : Bool :=
  decide (v ∈ embeddedVertices L)

@[simp] lemma incidenceSide_eq_true {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {v : V} :
    incidenceSide L v = true ↔ v ∈ embeddedVertices L := by
  simp [incidenceSide]

@[simp] lemma incidenceSide_embed {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (t : T) : incidenceSide L (L.embed t) = true := by
  simp [incidenceSide, embeddedVertices]

lemma incidenceSide_linked {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {t : T} {y : V} (h : Linked L t y) :
    incidenceSide L y = false := by
  rw [Bool.eq_false_iff]
  intro hy
  rw [incidenceSide_eq_true] at hy
  obtain ⟨u, _hu, hueq⟩ := Finset.mem_image.mp hy
  exact linked_ne_embed L h u hueq.symm

lemma incidenceGraph_cross {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {u y : V} (h : (incidenceGraph L).Adj u y) :
    incidenceSide L y = !(incidenceSide L u) := by
  rcases (incidenceGraph_adj_iff L).mp h with ⟨_, hrel | hrel⟩
  · obtain ⟨t, rfl, hty⟩ := hrel
    simp [incidenceSide_linked L hty]
  · obtain ⟨t, rfl, htu⟩ := hrel
    simp [incidenceSide_linked L htu]

lemma incidenceGraph_degree_embed_le {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (t : T) :
    (incidenceGraph L).degree (L.embed t) ≤ (leftPartners L t).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro y hy
  rw [mem_leftPartners]
  have hadj := ((incidenceGraph L).mem_neighborFinset (L.embed t) y).mp hy
  rcases (incidenceGraph_adj_iff L).mp hadj with ⟨_, hrel | hrel⟩
  · obtain ⟨u, hu, huy⟩ := hrel
    have hut : u = t := L.embed_injective hu
    simpa [hut] using huy
  · obtain ⟨u, _huy, huembed⟩ := hrel
    exact False.elim ((linked_ne_embed L huembed t) rfl)

lemma incidenceGraph_degree_nonembedded_le {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {y : V} (hy : y ∉ embeddedVertices L) :
    (incidenceGraph L).degree y ≤ (rightPartners L y).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  calc
    ((incidenceGraph L).neighborFinset y).card ≤
        ((rightPartners L y).image L.embed).card := by
      apply Finset.card_le_card
      intro z hz
      have hadj := ((incidenceGraph L).mem_neighborFinset y z).mp hz
      rcases (incidenceGraph_adj_iff L).mp hadj with ⟨_, hrel | hrel⟩
      · obtain ⟨t, hty, _htz⟩ := hrel
        exact False.elim (hy (by simp [embeddedVertices, ← hty]))
      · obtain ⟨t, htz, hty⟩ := hrel
        rw [Finset.mem_image]
        exact ⟨t, by simpa using hty, htz⟩
    _ ≤ (rightPartners L y).card := Finset.card_image_le

theorem incidenceGraph_degree_le
    {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (A B : ℕ)
    (hleft : ∀ t, (leftPartners L t).card ≤ A)
    (hright : ∀ y, (rightPartners L y).card ≤ B) (v : V) :
    (incidenceGraph L).degree v ≤ if incidenceSide L v then A else B := by
  by_cases hv : v ∈ embeddedVertices L
  · obtain ⟨t, _ht, htv⟩ := Finset.mem_image.mp hv
    subst v
    simp [incidenceSide_embed,
      (incidenceGraph_degree_embed_le L t).trans (hleft t)]
  · have hs : incidenceSide L v = false := by
      simp [incidenceSide, hv]
    rw [hs]
    exact (incidenceGraph_degree_nonembedded_le L hv).trans (hright v)

theorem incidenceGraph_isBipartiteWith
    {F : SimpleGraph T} {G : SimpleGraph V} (L : LiftSystem F G) :
    (incidenceGraph L).IsBipartiteWith (↑(embeddedVertices L) : Set V)
      (↑((embeddedVertices L)ᶜ) : Set V) := by
  refine ⟨?_, ?_⟩
  · rw [Set.disjoint_left]
    intro a ha hb
    have hnot : a ∉ embeddedVertices L := by simpa using hb
    exact hnot ha
  intro u y huy
  have hcross := incidenceGraph_cross L huy
  by_cases hu : u ∈ embeddedVertices L
  · left
    refine ⟨hu, ?_⟩
    have hsu : incidenceSide L u = true := by simp [incidenceSide, hu]
    rw [hsu] at hcross
    have hsy : incidenceSide L y = false := by simpa using hcross
    simpa [incidenceSide] using hsy
  · right
    refine ⟨by simpa using hu, ?_⟩
    have hsu : incidenceSide L u = false := by simp [incidenceSide, hu]
    rw [hsu] at hcross
    have hsy : incidenceSide L y = true := by simpa using hcross
    simpa [incidenceSide] using hsy

theorem incidenceGraph_edge_card_le
    {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (A : ℕ)
    (hleft : ∀ t, (leftPartners L t).card ≤ A) :
    (incidenceGraph L).edgeFinset.card ≤ Fintype.card T * A := by
  have hsum := (incidenceGraph L).isBipartiteWith_sum_degrees_eq_card_edges
    (s := embeddedVertices L) (t := (embeddedVertices L)ᶜ)
    (incidenceGraph_isBipartiteWith L)
  calc
    (incidenceGraph L).edgeFinset.card =
        ∑ v ∈ embeddedVertices L, (incidenceGraph L).degree v := by
      simpa using hsum.symm
    _ ≤ ∑ _v ∈ embeddedVertices L, A := by
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨t, _ht, htv⟩ := Finset.mem_image.mp hv
      subst v
      exact (incidenceGraph_degree_embed_le L t).trans (hleft t)
    _ = (embeddedVertices L).card * A := by simp
    _ ≤ Fintype.card T * A := by
      gcongr
      exact Finset.card_image_le

end


end Erdos113Incidence
