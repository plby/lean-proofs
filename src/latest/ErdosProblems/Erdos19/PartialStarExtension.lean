import ErdosProblems.Erdos19.StarColorSelection

/-! # Updating a partial coloring by a star

Distinct colors on the new pairs increase every color's vertex coverage by
at most two. Away from the center, linearity permits at most one new edge
through a vertex, so the number of used reserved colors increases by at most one.
-/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

variable {V C : Type*} [Fintype V] [DecidableEq C]

noncomputable def recolorOn (H : SetHypergraph V) (T : Finset H) (c : H → C)
    (color : T → C) : H → C :=
  fun e ↦ if he : e ∈ T then color ⟨e, he⟩ else c e

theorem recolorOn_of_mem (H : SetHypergraph V) (T : Finset H) (c : H → C)
    (color : T → C) (e : H) (he : e ∈ T) :
    H.recolorOn T c color e = color ⟨e, he⟩ := by
  simp [recolorOn, he]

theorem recolorOn_of_not_mem (H : SetHypergraph V) (T : Finset H) (c : H → C)
    (color : T → C) (e : H) (he : e ∉ T) :
    H.recolorOn T c color e = c e := by
  simp [recolorOn, he]

theorem recolorOn_agrees (H : SetHypergraph V) (S T : Finset H)
    (hST : Disjoint S T) (c : H → C) (color : T → C) :
    ∀ e ∈ S, H.recolorOn T c color e = c e := by
  intro e he
  exact H.recolorOn_of_not_mem T c color e (disjoint_left.mp hST he)

theorem recolorOn_proper (H : SetHypergraph V) (S T : Finset H)
    (hST : Disjoint S T) (c : H → C) (hc : H.IsProperOn S c)
    (color : T → C) (hinj : Function.Injective color)
    (havoid : ∀ e : T, ∀ v ∈ e.1.1, color e ∉ H.usedColorsOn S c v) :
    H.IsProperOn (S ∪ T) (H.recolorOn T c color) := by
  intro e he f hf hne hinter
  have hagree := H.recolorOn_agrees S T hST c color
  rcases mem_union.mp he with he | he
  · rw [hagree e he]
    rcases mem_union.mp hf with hf | hf
    · rw [hagree f hf]
      exact hc e he f hf hne hinter
    · rw [H.recolorOn_of_mem T c color f hf]
      intro heq
      obtain ⟨v, hve, hvf⟩ := hinter
      apply havoid ⟨f, hf⟩ v hvf
      exact (H.mem_usedColorsOn S c v _).mpr ⟨e, he, hve, heq⟩
  · rw [H.recolorOn_of_mem T c color e he]
    rcases mem_union.mp hf with hf | hf
    · rw [hagree f hf]
      intro heq
      obtain ⟨v, hve, hvf⟩ := hinter
      apply havoid ⟨e, he⟩ v hve
      exact (H.mem_usedColorsOn S c v _).mpr ⟨f, hf, hvf, heq.symm⟩
    · rw [H.recolorOn_of_mem T c color f hf]
      exact fun h ↦ hne (congrArg (fun z : T ↦ z.1) (hinj h))

theorem recolorOn_coverage (H : SetHypergraph V) (S T : Finset H)
    (hST : Disjoint S T) (c : H → C) (color : T → C)
    (hinj : Function.Injective color) (r A : ℕ)
    (hsize : ∀ e ∈ T, e.1.ncard ≤ r)
    (hcover : ∀ a, (H.coveredVertices {e | e ∈ S ∧ c e = a}).ncard ≤ A) :
    ∀ a, (H.coveredVertices
      {e | e ∈ S ∪ T ∧ H.recolorOn T c color e = a}).ncard ≤ A + r := by
  intro a
  have hagree := H.recolorOn_agrees S T hST c color
  by_cases hex : ∃ e : T, color e = a
  · obtain ⟨e, hecolor⟩ := hex
    have hsub : H.coveredVertices
        {f | f ∈ S ∪ T ∧ H.recolorOn T c color f = a} ⊆
        H.coveredVertices {f | f ∈ S ∧ c f = a} ∪ e.1.1 := by
      intro v hv
      simp only [coveredVertices, Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq] at hv ⊢
      obtain ⟨f, ⟨hf, hfa⟩, hvf⟩ := hv
      rcases mem_union.mp hf with hf | hf
      · rw [hagree f hf] at hfa
        exact Or.inl ⟨f, ⟨hf, hfa⟩, hvf⟩
      · rw [H.recolorOn_of_mem T c color f hf] at hfa
        have hfe : f = e.1 := congrArg (fun z : T ↦ z.1) (hinj (hfa.trans hecolor.symm))
        exact Or.inr (hfe ▸ hvf)
    exact (Set.ncard_le_ncard hsub).trans
      ((Set.ncard_union_le _ _).trans (Nat.add_le_add (hcover a) (hsize e.1 e.2)))
  · have hsub : H.coveredVertices
        {f | f ∈ S ∪ T ∧ H.recolorOn T c color f = a} ⊆
        H.coveredVertices {f | f ∈ S ∧ c f = a} := by
      intro v hv
      simp only [coveredVertices, Set.mem_iUnion, Set.mem_ofPred_eq] at hv ⊢
      obtain ⟨f, ⟨hf, hfa⟩, hvf⟩ := hv
      rcases mem_union.mp hf with hf | hf
      · exact ⟨f, ⟨hf, (hagree f hf).symm.trans hfa⟩, hvf⟩
      · exact (hex ⟨⟨f, hf⟩, (H.recolorOn_of_mem T c color f hf).symm.trans hfa⟩).elim
    exact ((Set.ncard_le_ncard hsub).trans (hcover a)).trans (Nat.le_add_right A r)

theorem usedColorsOn_recolor_subset (H : SetHypergraph V) (S T : Finset H)
    (hST : Disjoint S T) (c : H → C) (color : T → C) (v : V) :
    H.usedColorsOn (S ∪ T) (H.recolorOn T c color) v ⊆
      H.usedColorsOn S c v ∪ ((T.attach.filter fun e ↦ v ∈ e.1.1).image color) := by
  intro a ha
  obtain ⟨e, he, hv, hcolor⟩ := (H.mem_usedColorsOn _ _ _ _).mp ha
  rcases mem_union.mp he with he | he
  · apply mem_union_left
    exact (H.mem_usedColorsOn _ _ _ _).mpr
      ⟨e, he, hv, (H.recolorOn_agrees S T hST c color e he).symm.trans hcolor⟩
  · apply mem_union_right
    exact mem_image.mpr ⟨⟨e, he⟩, mem_filter.mpr ⟨mem_attach _ _, hv⟩,
      (H.recolorOn_of_mem T c color e he).symm.trans hcolor⟩

theorem star_incident_card_le_one (H : SetHypergraph V) (hlinear : H.IsLinear)
    (T : Finset H) (u v : V) (hvu : v ≠ u) (hcenter : ∀ e ∈ T, u ∈ e.1) :
    (T.attach.filter fun e ↦ v ∈ e.1.1).card ≤ 1 := by
  apply card_le_one.mpr
  intro e he f hf
  by_contra hef
  have heq : u = v := hlinear e.1.2 f.1.2
    (fun h ↦ hef (Subtype.ext (Subtype.ext h)))
    ⟨hcenter e.1 e.2, hcenter f.1 f.2⟩
    ⟨(mem_filter.mp he).2, (mem_filter.mp hf).2⟩
  exact hvu heq.symm

theorem recolorOn_reserved_degree (H : SetHypergraph V) (hlinear : H.IsLinear)
    (S T : Finset H) (hST : Disjoint S T) (c : H → C) (color : T → C)
    (reserved : Finset C) (u v : V) (hvu : v ≠ u)
    (hcenter : ∀ e ∈ T, u ∈ e.1) (d : ℕ)
    (hused : (reserved ∩ H.usedColorsOn S c v).card ≤ d) :
    (reserved ∩ H.usedColorsOn (S ∪ T) (H.recolorOn T c color) v).card ≤ d + 1 := by
  have hsub := H.usedColorsOn_recolor_subset S T hST c color v
  calc
    _ ≤ (reserved ∩ (H.usedColorsOn S c v ∪
        (T.attach.filter fun e ↦ v ∈ e.1.1).image color)).card :=
      card_le_card (inter_subset_inter_left hsub)
    _ ≤ (reserved ∩ H.usedColorsOn S c v).card +
        (reserved ∩ (T.attach.filter fun e ↦ v ∈ e.1.1).image color).card := by
      rw [inter_union_distrib_left]
      exact card_union_le _ _
    _ ≤ d + 1 := Nat.add_le_add hused
      ((card_le_card (inter_subset_right)).trans
        (card_image_le.trans (H.star_incident_card_le_one hlinear T u v hvu hcenter)))

#print axioms recolorOn_proper
#print axioms recolorOn_coverage
#print axioms recolorOn_reserved_degree

end Erdos19.SetHypergraph
