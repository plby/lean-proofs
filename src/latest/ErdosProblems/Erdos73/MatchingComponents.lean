import ErdosProblems.Erdos73.DegreeTwoPaths
import ErdosProblems.Erdos556.MatchingInterface

/-! Finite edge counts in the components of the union of two matchings. -/

namespace Erdos73

open SimpleGraph Finset Erdos556
open Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def matchingUnion {M N : Finset (Sym2 V)}
    (hM : EdgeMatching G M) (hN : EdgeMatching G N) : SimpleGraph V :=
  hM.toSubgraph.spanningCoe ⊔ hN.toSubgraph.spanningCoe

theorem matchingUnion_le {M N : Finset (Sym2 V)}
    (hM : EdgeMatching G M) (hN : EdgeMatching G N) : matchingUnion hM hN ≤ G := by
  intro x y h
  rcases h with h | h
  · exact hM.1 _ h
  · exact hN.1 _ h

theorem matching_neighbors_unique {M : Finset (Sym2 V)} (hM : EdgeMatching G M)
    {v a b : V} (ha : s(v, a) ∈ M) (hb : s(v, b) ∈ M) : a = b :=
  hM.toSubgraph_isMatching.eq_of_adj_left ha hb

theorem matchingUnion_twoNeighbors {M N : Finset (Sym2 V)}
    (hM : EdgeMatching G M) (hN : EdgeMatching G N) :
    AtMostTwoNeighbors (matchingUnion hM hN) := by
  intro v a b c ha hb hc
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc
  · exact Or.inl (matching_neighbors_unique hM ha hb)
  · exact Or.inl (matching_neighbors_unique hM ha hb)
  · exact Or.inr (Or.inl (matching_neighbors_unique hM ha hc))
  · exact Or.inr (Or.inr (matching_neighbors_unique hN hb hc))
  · exact Or.inr (Or.inr (matching_neighbors_unique hM hb hc))
  · exact Or.inr (Or.inl (matching_neighbors_unique hN ha hc))
  · exact Or.inl (matching_neighbors_unique hN ha hb)
  · exact Or.inl (matching_neighbors_unique hN ha hb)

theorem matchingUnion_left_matching {M N : Finset (Sym2 V)}
    (hM : EdgeMatching G M) (hN : EdgeMatching G N) :
    EdgeMatching (matchingUnion hM hN) M := by
  refine ⟨?_, hM.2⟩
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v => exact Or.inl he

theorem matchingUnion_right_matching {M N : Finset (Sym2 V)}
    (hM : EdgeMatching G M) (hN : EdgeMatching G N) :
    EdgeMatching (matchingUnion hM hN) N := by
  refine ⟨?_, hN.2⟩
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v => exact Or.inr he

def matchingOn (M : Finset (Sym2 V)) (S : Finset V) : Finset (Sym2 V) :=
  M.filter (fun e => e.toFinset ⊆ S)

theorem matchingOn_subset (M : Finset (Sym2 V)) (S : Finset V) : matchingOn M S ⊆ M :=
  Finset.filter_subset _ _

theorem matchingOn_isMatching {M : Finset (Sym2 V)} (hM : EdgeMatching G M)
    (S : Finset V) : EdgeMatching G (matchingOn M S) := hM.mono (matchingOn_subset M S)

theorem mem_matchingOn {M : Finset (Sym2 V)} {S : Finset V} {u v : V} :
    s(u, v) ∈ matchingOn M S ↔ s(u, v) ∈ M ∧ u ∈ S ∧ v ∈ S := by
  simp [matchingOn, Sym2.toFinset_mk_eq, Finset.insert_subset_iff]

theorem matchingOn_support_subset (M : Finset (Sym2 V)) (S : Finset V) :
    matchingSupport (matchingOn M S) ⊆ S := by
  intro v hv
  obtain ⟨e, he, hv⟩ := matchingSupport_mem.mp hv
  exact (Finset.mem_filter.mp he).2 (Sym2.mem_toFinset.mpr hv)

theorem matchingOn_support_eq_inter {M : Finset (Sym2 V)} (hM : EdgeMatching G M)
    (S : Finset V) (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S) :
    matchingSupport (matchingOn M S) = matchingSupport M ∩ S := by
  ext u
  constructor
  · intro hu
    exact Finset.mem_inter.mpr ⟨matchingSupport_mono (matchingOn_subset M S) hu,
      matchingOn_support_subset M S hu⟩
  · rintro hu
    obtain ⟨huM, huS⟩ := Finset.mem_inter.mp hu
    obtain ⟨e, he, hue⟩ := matchingSupport_mem.mp huM
    obtain ⟨v, rfl⟩ := Sym2.mem_iff_exists.mp hue
    exact matchingSupport_mem.mpr ⟨s(u, v),
      mem_matchingOn.mpr ⟨he, huS, hclosed u huS v (hM.1 _ he)⟩, Sym2.mem_mk_left _ _⟩

variable [Fintype V]

open scoped Classical in
noncomputable def componentMatching (M : Finset (Sym2 V)) (C : G.ConnectedComponent) :
    Finset (Sym2 V) := matchingOn M C.supp.toFinset

open scoped Classical in
theorem componentMatching_support {M : Finset (Sym2 V)} (hM : EdgeMatching G M)
    (C : G.ConnectedComponent) :
    matchingSupport (componentMatching M C) = matchingSupport M ∩ C.supp.toFinset := by
  apply matchingOn_support_eq_inter hM
  intro u hu v huv
  exact Set.mem_toFinset.mpr ((C.mem_supp_congr_adj huv).mp (Set.mem_toFinset.mp hu))

open scoped Classical in
theorem componentMatching_partition {M : Finset (Sym2 V)} (hM : EdgeMatching G M) :
    Finset.univ.biUnion (componentMatching (G := G) M) = M := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨C, _, he⟩ := Finset.mem_biUnion.mp he
    exact matchingOn_subset M C.supp.toFinset he
  · intro he
    induction e using Sym2.inductionOn with
    | _ u v =>
      apply Finset.mem_biUnion.mpr
      refine ⟨G.connectedComponentMk u, Finset.mem_univ _, mem_matchingOn.mpr ⟨he, ?_, ?_⟩⟩
      · exact Set.mem_toFinset.mpr rfl
      · exact Set.mem_toFinset.mpr (ConnectedComponent.sound (hM.1 _ he).reachable.symm)

open scoped Classical in
theorem componentMatching_disjoint (M : Finset (Sym2 V)) :
    Pairwise (fun C D : G.ConnectedComponent =>
      Disjoint (componentMatching M C) (componentMatching M D)) := by
  classical
  intro C D hne
  apply Finset.disjoint_left.mpr
  intro e heC heD
  induction e using Sym2.inductionOn with
  | _ u v =>
    have huC := Set.mem_toFinset.mp (mem_matchingOn.mp heC).2.1
    have huD := Set.mem_toFinset.mp (mem_matchingOn.mp heD).2.1
    exact hne (ConnectedComponent.eq_of_common_vertex huC huD)

open scoped Classical in
theorem sum_componentMatching_card {M : Finset (Sym2 V)} (hM : EdgeMatching G M) :
    ∑ C : G.ConnectedComponent, (componentMatching M C).card = M.card := by
  classical
  calc
    _ = (Finset.univ.biUnion (componentMatching (G := G) M)).card :=
      (Finset.card_biUnion (fun C _ D _ hne => componentMatching_disjoint M hne)).symm
    _ = M.card := congrArg Finset.card (componentMatching_partition hM)

end Erdos73
