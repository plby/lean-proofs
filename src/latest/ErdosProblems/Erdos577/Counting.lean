import ErdosProblems.Erdos577.Basic

/-! Finite contact counts, including overlapping sets, for the quadrilateral proof. -/

namespace Erdos577

open Finset
open scoped BigOperators

variable {V I : Type*}
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The number of neighbors in a specified finite vertex set. -/
def degreeIn (v : V) (s : Finset V) : ℕ := (s.filter (G.Adj v)).card

/-- Incidence sum; edges inside an overlap contribute in both directions. -/
def contacts (s t : Finset V) : ℕ := ∑ v ∈ s, degreeIn G v t

lemma degreeIn_le_card (v : V) (s : Finset V) : degreeIn G v s ≤ s.card :=
  card_filter_le _ _

@[simp] lemma degreeIn_empty (v : V) : degreeIn G v ∅ = 0 := by
  simp [degreeIn]

@[simp] lemma degreeIn_singleton (v w : V) :
    degreeIn G v {w} = if G.Adj v w then 1 else 0 := by
  by_cases h : G.Adj v w <;> simp [degreeIn, filter_singleton, h]

@[simp] lemma degreeIn_univ [Fintype V] (v : V) : degreeIn G v univ = G.degree v := by
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  rfl

lemma degreeIn_mono (v : V) {s t : Finset V} (hst : s ⊆ t) :
    degreeIn G v s ≤ degreeIn G v t :=
  card_le_card (filter_subset_filter _ hst)

lemma degreeIn_union [DecidableEq V] (v : V) {s t : Finset V} (h : Disjoint s t) :
    degreeIn G v (s ∪ t) = degreeIn G v s + degreeIn G v t := by
  unfold degreeIn
  rw [filter_union, card_union_of_disjoint (disjoint_filter_filter h)]

lemma degreeIn_insert [DecidableEq V] (v w : V) {s : Finset V} (hw : w ∉ s) :
    degreeIn G v (insert w s) = (if G.Adj v w then 1 else 0) + degreeIn G v s := by
  by_cases h : G.Adj v w <;> simp [degreeIn, filter_insert, h, hw, Nat.add_comm]

lemma degreeIn_clique {s : Finset V} (h : G.IsClique s)
    {v : V} (hv : v ∈ s) : degreeIn G v s = s.card - 1 := by
  classical
  have he : s.filter (G.Adj v) = s.erase v := by
    ext w
    simp only [mem_filter, mem_erase]
    exact ⟨fun hw ↦ ⟨hw.2.ne.symm, hw.1⟩,
      fun hw ↦ ⟨hw.2, h hv hw.2 hw.1.symm⟩⟩
  rw [degreeIn, he, card_erase_of_mem hv]

lemma degreeIn_image [DecidableEq V] (v : V) (s : Finset I)
    (f : I → V) (hf : Function.Injective f) :
    degreeIn G v (s.image f) = ∑ i ∈ s, if G.Adj v (f i) then 1 else 0 := by
  rw [degreeIn, card_eq_sum_ones, sum_filter, sum_image]
  exact fun _ _ _ _ h ↦ hf h

lemma contacts_image_left [DecidableEq V] (s : Finset I) (f : I → V)
    (hf : Function.Injective f) (t : Finset V) :
    contacts G (s.image f) t = ∑ i ∈ s, degreeIn G (f i) t := by
  exact sum_image (fun _ _ _ _ h ↦ hf h)

@[simp] lemma contacts_empty_left (s : Finset V) : contacts G ∅ s = 0 := by
  simp [contacts]

@[simp] lemma contacts_empty_right (s : Finset V) : contacts G s ∅ = 0 := by
  simp [contacts]

@[simp] lemma contacts_singleton_left (v : V) (s : Finset V) :
    contacts G {v} s = degreeIn G v s := by
  simp [contacts]

lemma contacts_comm (s t : Finset V) : contacts G s t = contacts G t s := by
  simp only [contacts, degreeIn, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  apply sum_congr rfl
  intro w _
  by_cases h : G.Adj v w
  · simp [h, h.symm]
  · have hs : ¬G.Adj w v := fun hw ↦ h hw.symm
    simp [h, hs]

@[simp] lemma contacts_singleton_right (v : V) (s : Finset V) :
    contacts G s {v} = degreeIn G v s := by
  rw [contacts_comm, contacts_singleton_left]

lemma contacts_union_left [DecidableEq V] {s t : Finset V} (h : Disjoint s t) (u : Finset V) :
    contacts G (s ∪ t) u = contacts G s u + contacts G t u := by
  exact sum_union h

lemma contacts_union_right [DecidableEq V] (s : Finset V) {t u : Finset V} (h : Disjoint t u) :
    contacts G s (t ∪ u) = contacts G s t + contacts G s u := by
  rw [contacts_comm, contacts_union_left G h, contacts_comm G t, contacts_comm G u]

lemma contacts_biUnion_left [DecidableEq V] (s : Finset I) (b : I → Finset V)
    (h : (s : Set I).PairwiseDisjoint b) (t : Finset V) :
    contacts G (s.biUnion b) t = ∑ i ∈ s, contacts G (b i) t := by
  exact sum_biUnion h

lemma contacts_biUnion_right [DecidableEq V] (s : Finset V) (t : Finset I) (b : I → Finset V)
    (h : (t : Set I).PairwiseDisjoint b) :
    contacts G s (t.biUnion b) = ∑ i ∈ t, contacts G s (b i) := by
  rw [contacts_comm, contacts_biUnion_left G t b h]
  apply sum_congr rfl
  intro i _
  exact contacts_comm G (b i) s

lemma contacts_le_card_mul (s t : Finset V) : contacts G s t ≤ s.card * t.card := by
  calc
    contacts G s t ≤ ∑ _ ∈ s, t.card := sum_le_sum fun v _ ↦ degreeIn_le_card G v t
    _ = s.card * t.card := by simp

lemma minimum_degree_sum [Fintype V] (s : Finset V) (d : ℕ)
    (h : ∀ v ∈ s, d ≤ G.degree v) : s.card * d ≤ contacts G s univ := by
  calc
    s.card * d = ∑ _ ∈ s, d := by simp
    _ ≤ ∑ v ∈ s, G.degree v := sum_le_sum h
    _ = contacts G s univ := by simp [contacts]

/-- The finite averaging step also handles an empty family of outside blocks. -/
lemma exists_heavy_block (s : Finset V) (t : Finset I) (b : I → Finset V) (d : ℕ)
    (h : t.card * d < ∑ i ∈ t, contacts G s (b i)) :
    ∃ i ∈ t, d < contacts G s (b i) := by
  by_contra! hn
  have hh : (∑ i ∈ t, contacts G s (b i)) ≤ t.card * d := by
    calc
      (∑ i ∈ t, contacts G s (b i)) ≤ ∑ _ ∈ t, d := sum_le_sum hn
      _ = t.card * d := by simp
  exact (not_lt_of_ge hh) h

section InducedEdges

/-- The actual induced edge count, not the doubled contact count. -/
def edgeCount (s : Finset V) : ℕ := (G.induce (s : Set V)).edgeFinset.card

lemma degree_induce_eq_degreeIn (s : Finset V) (v : s) :
    (G.induce (s : Set V)).degree v = degreeIn G v s := by
  unfold SimpleGraph.degree degreeIn
  refine card_bij (fun w _ ↦ (w : V)) ?_ ?_ ?_
  · intro w hw
    refine mem_filter.mpr ⟨w.property, ?_⟩
    exact ((G.induce (s : Set V)).mem_neighborFinset v w).mp hw
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro w hw
    refine ⟨⟨w, (mem_filter.mp hw).1⟩, ?_, rfl⟩
    exact ((G.induce (s : Set V)).mem_neighborFinset _ _).mpr (mem_filter.mp hw).2

lemma contacts_self_eq_twice_edgeCount (s : Finset V) :
    contacts G s s = 2 * edgeCount G s := by
  calc
    contacts G s s = ∑ v : s, degreeIn G v s := (s.sum_coe_sort _).symm
    _ = ∑ v : s, (G.induce (s : Set V)).degree v := by
      apply sum_congr rfl
      intro v _
      exact (degree_induce_eq_degreeIn G s v).symm
    _ = 2 * edgeCount G s := (G.induce (s : Set V)).sum_degrees_eq_twice_card_edges

lemma edgeCount_le_choose_two (s : Finset V) : edgeCount G s ≤ s.card.choose 2 := by
  have hs : Fintype.card (s : Set V) = s.card := by
    change Fintype.card s = s.card
    exact Fintype.card_coe s
  simpa only [edgeCount, hs] using
    (G.induce (s : Set V)).card_edgeFinset_le_card_choose_two

lemma edgeCount_le_six {s : Finset V} (hs : s.card = 4) : edgeCount G s ≤ 6 := by
  have h := edgeCount_le_choose_two G s
  norm_num [hs] at h
  exact h

end InducedEdges

end Erdos577
