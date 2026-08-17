import ErdosProblems.Erdos807.HostFamily

/-!
# Edge-coordinate overlaps for the stable-slot construction

The bucket construction in `HostFamily` has a useful rigidity property: two
selected host vertices can coincide only when they came from the same global
slot, and then their offsets agree.  This file packages that observation at
the level of complete edge-coordinate blocks and records the corresponding
two-prescription probability bound.
-/

namespace Erdos807
namespace HostFamily

open StructuredFamily

/-! ## Vertex ranges and complete edge blocks -/

/-- The finite range of an embedding from `Fin k`. -/
noncomputable def embeddingRange {k n : ℕ} (e : Fin k ↪ Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.image e

@[simp] theorem card_embeddingRange {k n : ℕ} (e : Fin k ↪ Fin n) :
    (embeddingRange e).card = k := by
  classical
  rw [embeddingRange, Finset.card_image_of_injective _ e.injective]
  simp

@[simp] lemma mem_embeddingRange {k n : ℕ} (e : Fin k ↪ Fin n) (v : Fin n) :
    v ∈ embeddingRange e ↔ ∃ i, e i = v := by
  classical
  simp [embeddingRange]

/-- Membership in a transported complete edge block is equivalent to both
endpoints lying in the range of the embedding. -/
theorem mem_embeddingEdges_iff {k n : ℕ} (e : Fin k ↪ Fin n)
    (a : RandomGraph.Edge n) :
    a ∈ embeddingEdges e ↔ ∀ v ∈ a.1, v ∈ embeddingRange e := by
  classical
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨b, -, rfl⟩
    rcases b with ⟨b, hb⟩
    induction b using Sym2.inductionOn with
    | _ i j =>
        intro v hv
        change v ∈ s(e i, e j) at hv
        rw [Sym2.mem_iff] at hv
        rcases hv with hv | hv
        · rw [hv]
          simp
        · rw [hv]
          simp
  · intro ha
    rcases a with ⟨a, haDiag⟩
    induction a using Sym2.inductionOn with
    | _ u v =>
        have hu : u ∈ embeddingRange e := ha u (by simp [Sym2.mem_iff])
        have hv : v ∈ embeddingRange e := ha v (by simp [Sym2.mem_iff])
        rcases (mem_embeddingRange e u).mp hu with ⟨i, rfl⟩
        rcases (mem_embeddingRange e v).mp hv with ⟨j, rfl⟩
        have hij : i ≠ j := by
          intro h
          apply haDiag
          simpa [h]
        let b : RandomGraph.Edge k := ⟨s(i, j), by simpa [Sym2.mk_isDiag_iff]⟩
        refine Finset.mem_image.mpr ⟨b, Finset.mem_univ _, ?_⟩
        apply Subtype.ext
        rfl

/-! ## Stable-slot intersections -/

/-- Slots on which two choices select the same offset. -/
def agreementSlots {n r : ℕ} (c d : Choice n r) :
    Finset (Fin (templateOrder r)) :=
  Finset.univ.filter fun i ↦ c i = d i

@[simp] lemma mem_agreementSlots {n r : ℕ} {c d : Choice n r}
    {i : Fin (templateOrder r)} :
    i ∈ agreementSlots c d ↔ c i = d i := by
  simp [agreementSlots]

/-- Equality of vertices selected by two choices remembers the slot and the
offset exactly. -/
theorem slotEmbedding_eq_iff {n r : ℕ} (c d : Choice n r)
    (i j : Fin (templateOrder r)) :
    slotEmbedding c i = slotEmbedding d j ↔ i = j ∧ c i = d j := by
  constructor
  · intro h
    have hp : finProdFinEquiv (i, c i) = finProdFinEquiv (j, d j) := by
      apply Fin.ext
      simpa [finProdFinEquiv, Nat.add_comm, Nat.mul_comm] using congrArg Fin.val h
    have hp' : (i, c i) = (j, d j) := finProdFinEquiv.injective hp
    exact ⟨congrArg Prod.fst hp', congrArg Prod.snd hp'⟩
  · rintro ⟨rfl, h⟩
    apply Fin.ext
    simp [h]

/-- The two selected vertex ranges intersect exactly in vertices belonging to
agreement slots. -/
theorem mem_embeddingRange_inter_iff {n r : ℕ} (c d : Choice n r)
    (v : Fin n) :
    v ∈ embeddingRange (slotEmbedding c) ∩ embeddingRange (slotEmbedding d) ↔
      ∃ i ∈ agreementSlots c d, slotEmbedding c i = v := by
  classical
  simp only [Finset.mem_inter, mem_embeddingRange]
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    have hij : slotEmbedding c i = slotEmbedding d j := hi.trans hj.symm
    have hs := (slotEmbedding_eq_iff c d i j).mp hij
    rcases hs with ⟨hij, hcd⟩
    cases hij
    exact ⟨i, mem_agreementSlots.mpr hcd, hi⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, rfl⟩, ⟨i,
      ((slotEmbedding_eq_iff c d i i).mpr
        ⟨rfl, mem_agreementSlots.mp hi⟩).symm⟩⟩

/-- Increasing enumeration of the agreement slots. -/
noncomputable def agreementIndexEmbedding {n r : ℕ} (c d : Choice n r) :
    Fin (agreementSlots c d).card ↪ Fin (templateOrder r) :=
  (agreementSlots c d).orderEmbOfFin rfl |>.toEmbedding

/-- The common host vertices, enumerated through their common stable slots. -/
noncomputable def agreementEmbedding {n r : ℕ} (c d : Choice n r) :
    Fin (agreementSlots c d).card ↪ Fin n :=
  (agreementIndexEmbedding c d).trans (slotEmbedding c)

@[simp] theorem embeddingRange_agreementEmbedding {n r : ℕ}
    (c d : Choice n r) :
    embeddingRange (agreementEmbedding c d) =
      embeddingRange (slotEmbedding c) ∩ embeddingRange (slotEmbedding d) := by
  classical
  ext v
  rw [mem_embeddingRange_inter_iff]
  simp only [mem_embeddingRange]
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨agreementIndexEmbedding c d q, ?_, rfl⟩
    simp [agreementIndexEmbedding]
  · rintro ⟨i, hi, rfl⟩
    have hiRange : i ∈ Set.range ((agreementSlots c d).orderEmbOfFin rfl) := by
      rw [(agreementSlots c d).range_orderEmbOfFin rfl]
      exact hi
    rcases hiRange with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply congrArg (slotEmbedding c) at hq
    simpa [agreementEmbedding, agreementIndexEmbedding] using hq

/-- The common complete edge block of two stable choices is precisely the
complete block on their common vertices. -/
theorem embeddingEdges_inter {n r : ℕ} (c d : Choice n r) :
    embeddingEdges (slotEmbedding c) ∩ embeddingEdges (slotEmbedding d) =
      embeddingEdges (agreementEmbedding c d) := by
  classical
  ext a
  simp only [Finset.mem_inter, mem_embeddingEdges_iff,
    embeddingRange_agreementEmbedding]
  constructor
  · rintro ⟨hc, hd⟩ v hv
    exact ⟨hc v hv, hd v hv⟩
  · intro h
    exact ⟨fun v hv ↦ (h v hv).1, fun v hv ↦ (h v hv).2⟩

/-- Exact number of edge coordinates shared by two stable choices. -/
theorem card_embeddingEdges_inter {n r : ℕ} (c d : Choice n r) :
    (embeddingEdges (slotEmbedding c) ∩ embeddingEdges (slotEmbedding d)).card =
      (agreementSlots c d).card.choose 2 := by
  rw [embeddingEdges_inter, card_embeddingEdges]

/-- Exact size of the union of the two complete coordinate blocks. -/
theorem card_embeddingEdges_union {n r : ℕ} (c d : Choice n r) :
    (embeddingEdges (slotEmbedding c) ∪ embeddingEdges (slotEmbedding d)).card =
      2 * (templateOrder r).choose 2 - (agreementSlots c d).card.choose 2 := by
  rw [Finset.card_union, card_embeddingEdges_inter]
  simp only [card_embeddingEdges]
  omega

end HostFamily

namespace RandomGraph

/-! ## Combining compatible edge prescriptions -/

/-- Two compatible prescriptions combine to the evident prescription on the
union of their coordinate blocks. -/
theorem prescribed_union_of_compatible {n : ℕ}
    {A B C D : Finset (Edge n)} {G : SimpleGraph (Fin n)}
    (hB : B ⊆ A) (hD : D ⊆ C)
    (_hcompat : B ∩ C = D ∩ A)
    (hAB : Prescribed A B G) (hCD : Prescribed C D G) :
    Prescribed (A ∪ C) (B ∪ D) G := by
  rw [Prescribed] at hAB hCD ⊢
  simp only [Erdos565.RandomGraph.restrict] at hAB hCD ⊢
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hxG, hxA | hxC⟩
    · left
      have hx := congrArg (fun S : Finset (Edge n) ↦ x ∈ S) hAB
      simpa [hxG, hxA] using hx
    · right
      have hx := congrArg (fun S : Finset (Edge n) ↦ x ∈ S) hCD
      simpa [hxG, hxC] using hx
  · rintro (hxB | hxD)
    · exact ⟨by
        have hx := congrArg (fun S : Finset (Edge n) ↦ x ∈ S) hAB
        have := hB hxB
        simpa [this, hxB] using hx.symm, Or.inl (hB hxB)⟩
    · exact ⟨by
        have hx := congrArg (fun S : Finset (Edge n) ↦ x ∈ S) hCD
        have := hD hxD
        simpa [this, hxD] using hx.symm, Or.inr (hD hxD)⟩

private theorem restrict_union_eq_left {n : ℕ}
    {A B C D : Finset (Edge n)}
    (hB : B ⊆ A) (hcompat : B ∩ C = D ∩ A) :
    Erdos565.RandomGraph.restrict A (B ∪ D) = B := by
  ext x
  have hc := Finset.ext_iff.mp hcompat x
  simp only [Erdos565.RandomGraph.restrict, Finset.mem_inter,
    Finset.mem_union] at hc ⊢
  constructor
  · rintro ⟨hxB | hxD, hxA⟩
    · exact hxB
    · exact (hc.mpr ⟨hxD, hxA⟩).1
  · intro hxB
    exact ⟨Or.inl hxB, hB hxB⟩

private theorem restrict_union_eq_right {n : ℕ}
    {A B C D : Finset (Edge n)}
    (hD : D ⊆ C) (hcompat : B ∩ C = D ∩ A) :
    Erdos565.RandomGraph.restrict C (B ∪ D) = D := by
  ext x
  have hc := Finset.ext_iff.mp hcompat x
  simp only [Erdos565.RandomGraph.restrict, Finset.mem_inter,
    Finset.mem_union] at hc ⊢
  constructor
  · rintro ⟨hxB | hxD, hxC⟩
    · exact (hc.mp ⟨hxB, hxC⟩).1
    · exact hxD
  · intro hxD
    exact ⟨Or.inr hxD, hD hxD⟩

/-- A conjunction of compatible prescriptions has exactly the probability of
the combined union prescription. -/
theorem probability_prescribed_and_of_compatible {n : ℕ}
    {A B C D : Finset (Edge n)}
    (hB : B ⊆ A) (hD : D ⊆ C)
    (hcompat : B ∩ C = D ∩ A) :
    probability n (fun G ↦ Prescribed A B G ∧ Prescribed C D G) =
      (1 / 2 : ℝ) ^ (A ∪ C).card := by
  have hEvent : (fun G ↦ Prescribed A B G ∧ Prescribed C D G) =
      Prescribed (A ∪ C) (B ∪ D) := by
    funext G
    apply propext
    constructor
    · rintro ⟨hAB, hCD⟩
      exact prescribed_union_of_compatible hB hD hcompat hAB hCD
    · intro hU
      change Erdos565.RandomGraph.restrict (A ∪ C) (edges G) = B ∪ D at hU
      change Erdos565.RandomGraph.restrict A (edges G) = B ∧
        Erdos565.RandomGraph.restrict C (edges G) = D
      constructor
      · rw [← Erdos565.RandomGraph.restrict_restrict_of_subset
            (show A ⊆ A ∪ C from Finset.subset_union_left),
          hU, restrict_union_eq_left hB hcompat]
      · rw [← Erdos565.RandomGraph.restrict_restrict_of_subset
            (show C ⊆ A ∪ C from Finset.subset_union_right),
          hU, restrict_union_eq_right hD hcompat]
  rw [hEvent, probability_prescribed (Finset.union_subset_union hB hD)]

/-- In particular, the conjunction probability is at most the probability of
fixing every coordinate in the union. -/
theorem probability_prescribed_and_le_of_compatible {n : ℕ}
    {A B C D : Finset (Edge n)}
    (hB : B ⊆ A) (hD : D ⊆ C)
    (hcompat : B ∩ C = D ∩ A) :
    probability n (fun G ↦ Prescribed A B G ∧ Prescribed C D G) ≤
      (1 / 2 : ℝ) ^ (A ∪ C).card := by
  exact (probability_prescribed_and_of_compatible hB hD hcompat).le

end RandomGraph
end Erdos807
