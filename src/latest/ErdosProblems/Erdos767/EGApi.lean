import Mathlib

namespace E767EGApi

open scoped Sym2

noncomputable section

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Deleting one vertex -/

/-- The graph induced on all vertices except `v`. -/
abbrev deleteVertex (G : SimpleGraph V) (v : V) :=
  G.induce ({v} : Set V)ᶜ

@[simp] lemma card_deleteVertex_type (v : V) :
    Fintype.card ↑(({v} : Set V)ᶜ) = Fintype.card V - 1 := by
  rw [Fintype.card_compl_set]
  simp

lemma card_edgeFinset_eq_deleteVertex_add_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.edgeFinset.card = (deleteVertex G v).edgeFinset.card + G.degree v := by
  have hdelete : (deleteVertex G v).edgeFinset.card =
      G.edgeFinset.card - G.degree v := by
    exact (G.card_edgeFinset_induce_compl_singleton v).trans
      (G.card_edgeFinset_deleteIncidenceSet v)
  rw [hdelete, Nat.sub_add_cancel (G.degree_le_card_edgeFinset v)]

/-! ## Splitting at a closed set of vertices -/

/-- Ambient edges with both endpoints in `s`.  Taking a `Finset` rather than a `Set`
keeps the induced-subtype `Fintype` instance canonical. -/
def edgesInside (G : SimpleGraph V) (s : Finset V) [DecidableRel G.Adj] : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦ e.toFinset ⊆ s

lemma card_edgesInside (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    (edgesInside G s).card = (G.induce (↑s : Set V)).edgeFinset.card := by
  exact G.card_filter_edgeFinset_toFinset_subset s

/-- If every edge has both ends on the same side of `s`, the ambient edge set is the
disjoint union of the edges induced by `s` and by its complement. -/
lemma edgeFinset_eq_edgesInside_union_compl
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V)
    (hclosed : ∀ u v, G.Adj u v → (u ∈ s ↔ v ∈ s)) :
    G.edgeFinset = edgesInside G s ∪ edgesInside G sᶜ := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      by_cases huv : G.Adj u v
      · have hsides := hclosed u v huv
        by_cases hu : u ∈ s
        · have hv : v ∈ s := hsides.mp hu
          simp [edgesInside, SimpleGraph.mem_edgeFinset, huv, hu, hv,
            Finset.subset_iff]
        · have hv : v ∉ s := fun hv ↦ hu (hsides.mpr hv)
          simp [edgesInside, SimpleGraph.mem_edgeFinset, huv, hu, hv,
            Finset.subset_iff]
      · simp [edgesInside, SimpleGraph.mem_edgeFinset, huv, Finset.subset_iff]

lemma disjoint_edgesInside_compl
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    Disjoint (edgesInside G s) (edgesInside G sᶜ) := by
  rw [Finset.disjoint_left]
  intro e hs hsc
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hu_pair : u ∈ s(u, v).toFinset := by simp
      have hu_s : u ∈ s := (Finset.mem_filter.mp hs).2 hu_pair
      have hu_sc : u ∈ sᶜ := (Finset.mem_filter.mp hsc).2 hu_pair
      exact (Finset.mem_compl.mp hu_sc) hu_s

/-- Exact edge-count decomposition across any vertex cut with no crossing edge. -/
lemma card_edgeFinset_eq_card_induce_add_card_induce_compl
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V)
    (hclosed : ∀ u v, G.Adj u v → (u ∈ s ↔ v ∈ s)) :
    G.edgeFinset.card =
      (G.induce (↑s : Set V)).edgeFinset.card +
        (G.induce (↑(sᶜ) : Set V)).edgeFinset.card := by
  rw [edgeFinset_eq_edgesInside_union_compl G s hclosed,
    Finset.card_union_of_disjoint (disjoint_edgesInside_compl G s),
    card_edgesInside, card_edgesInside]

/-! ## Splitting at a binary separation (the parts may share a cutvertex) -/

lemma edgeFinset_eq_edgesInside_union_of_edge_cover
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (hcover : ∀ u v, G.Adj u v →
      (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B)) :
    G.edgeFinset = edgesInside G A ∪ edgesInside G B := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      by_cases huv : G.Adj u v
      · rcases hcover u v huv with hA | hB
        · simp [edgesInside, SimpleGraph.mem_edgeFinset, huv, hA,
            Finset.subset_iff]
        · simp [edgesInside, SimpleGraph.mem_edgeFinset, huv, hB,
            Finset.subset_iff]
      · simp [edgesInside, SimpleGraph.mem_edgeFinset, huv, Finset.subset_iff]

lemma disjoint_edgesInside_of_inter_card_le_one
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (hinter : (A ∩ B).card ≤ 1) :
    Disjoint (edgesInside G A) (edgesInside G B) := by
  rw [Finset.disjoint_left]
  intro e heA heB
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hadj : G.Adj u v :=
        SimpleGraph.mem_edgeFinset.mp (Finset.mem_filter.mp heA).1
      have hp_u : u ∈ s(u, v).toFinset := by simp
      have hp_v : v ∈ s(u, v).toFinset := by simp
      have huA : u ∈ A := (Finset.mem_filter.mp heA).2 hp_u
      have hvA : v ∈ A := (Finset.mem_filter.mp heA).2 hp_v
      have huB : u ∈ B := (Finset.mem_filter.mp heB).2 hp_u
      have hvB : v ∈ B := (Finset.mem_filter.mp heB).2 hp_v
      have hpair : {u, v} ⊆ A ∩ B := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨huA, huB⟩
        · exact Finset.mem_inter.mpr ⟨hvA, hvB⟩
      have htwo : 2 ≤ (A ∩ B).card := by
        have := Finset.card_le_card hpair
        simpa [hadj.ne] using this
      omega

/-- Exact edge-count decomposition for a separation whose overlap has at most one vertex.
The hypothesis `hcover` is the convenient edge-level form of "no edge joins the two open
sides". -/
lemma card_edgeFinset_eq_card_induce_add_card_induce_of_separation
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (hcover : ∀ u v, G.Adj u v →
      (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B))
    (hinter : (A ∩ B).card ≤ 1) :
    G.edgeFinset.card =
      (G.induce (↑A : Set V)).edgeFinset.card +
        (G.induce (↑B : Set V)).edgeFinset.card := by
  rw [edgeFinset_eq_edgesInside_union_of_edge_cover G A B hcover,
    Finset.card_union_of_disjoint
      (disjoint_edgesInside_of_inter_card_le_one G A B hinter),
    card_edgesInside, card_edgesInside]

lemma card_sub_one_add_card_sub_one_le_of_separation
    (A B : Finset V) (hunion : A ∪ B = Finset.univ)
    (hinter : (A ∩ B).card ≤ 1) (hA : A.Nonempty) (hB : B.Nonempty) :
    (A.card - 1) + (B.card - 1) ≤ Fintype.card V - 1 := by
  have hcount := Finset.card_union_add_card_inter A B
  rw [hunion, Finset.card_univ] at hcount
  have hApos : 1 ≤ A.card := Finset.one_le_card.mpr hA
  have hBpos : 1 ≤ B.card := Finset.one_le_card.mpr hB
  omega

lemma card_coe_lt_card_of_ne_univ (A : Finset V)
    (hA : A ≠ Finset.univ) : Fintype.card ↑A < Fintype.card V := by
  simpa only [Fintype.card_coe, Finset.card_univ] using
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ A, hA⟩)

/-! ## A connected component supplies such a cut -/

lemma component_closed (G : SimpleGraph V) (C : G.ConnectedComponent) :
    ∀ u v, G.Adj u v → (u ∈ C.supp ↔ v ∈ C.supp) := by
  intro u v huv
  exact C.mem_supp_congr_adj huv

lemma card_edgeFinset_eq_component_add_compl
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : G.ConnectedComponent) :
    G.edgeFinset.card =
      (G.induce (↑C.supp.toFinset : Set V)).edgeFinset.card +
        (G.induce (↑(C.supp.toFinsetᶜ) : Set V)).edgeFinset.card := by
  apply card_edgeFinset_eq_card_induce_add_card_induce_compl G C.supp.toFinset
  intro u v huv
  simpa using component_closed G C u v huv

/-- A failure of preconnectedness gives a nonempty proper component support. -/
lemma exists_component_with_nonempty_proper_support
    (G : SimpleGraph V) (hG : ¬ G.Preconnected) :
    ∃ C : G.ConnectedComponent, C.supp.Nonempty ∧ C.supp ≠ Set.univ := by
  simp only [SimpleGraph.Preconnected] at hG
  push_neg at hG
  obtain ⟨u, v, huv⟩ := hG
  let C := G.connectedComponentMk u
  refine ⟨C, C.nonempty_supp, ?_⟩
  intro hC
  have hvC : v ∈ C.supp := by simp [hC]
  have huC : u ∈ C.supp := by simp [C]
  exact huv (C.reachable_of_mem_supp huC hvC)

lemma card_component_pos (G : SimpleGraph V) (C : G.ConnectedComponent) :
    0 < Fintype.card C := by
  exact Fintype.card_pos_iff.mpr ⟨⟨C.out, C.out_eq⟩⟩

lemma card_component_lt_of_support_ne_univ
    (G : SimpleGraph V) (C : G.ConnectedComponent) (hC : C.supp ≠ Set.univ) :
    Fintype.card C < Fintype.card V := by
  let e : C ≃ {x // x ∈ C.supp.toFinset} :=
    { toFun := fun x ↦ ⟨x, by simpa using x.prop⟩
      invFun := fun x ↦ ⟨x, by
        change ↑x ∈ C.supp
        exact Set.mem_toFinset.mp x.prop⟩
      left_inv := fun x ↦ Subtype.ext rfl
      right_inv := fun x ↦ Subtype.ext rfl }
  rw [Fintype.card_congr e]
  have hne : C.supp.toFinset ≠ (Finset.univ : Finset V) := by
    intro h
    apply hC
    ext x
    have hx := Finset.ext_iff.mp h x
    simpa using hx
  simpa only [Fintype.card_coe, Finset.card_univ] using
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _, hne⟩)

end

end E767EGApi

