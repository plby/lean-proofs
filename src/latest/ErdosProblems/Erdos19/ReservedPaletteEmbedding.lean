import ErdosProblems.Erdos19.CoverPaletteBudget

/-! # Embedding a coloring together with an unused reserved palette -/

namespace Erdos19.SetHypergraph

open Finset

variable {V C D : Type*}

def EdgeColoring.mapEmbedding {H : SetHypergraph V} (c : H.EdgeColoring C) (j : C ↪ D) :
    H.EdgeColoring D where
  color e := j (c.color e)
  valid := fun {e f} hne hinter heq ↦ c.valid hne hinter (j.injective heq)

theorem IsCoverBoundedColoring.mapEmbedding {H : SetHypergraph V}
    (c : H.EdgeColoring C) (A : ℕ) (hc : H.IsCoverBoundedColoring c A) (j : C ↪ D) :
    H.IsCoverBoundedColoring (c.mapEmbedding j) A := by
  intro a
  by_cases hex : ∃ b : C, j b = a
  · obtain ⟨b, rfl⟩ := hex
    have hclass : ({e : H | (c.mapEmbedding j).color e = j b} : Set H) =
        {e : H | c.color e = b} := by
      ext e
      exact j.injective.eq_iff
    simpa only [hclass] using hc b
  · left
    have hclass : ({e : H | (c.mapEmbedding j).color e = a} : Set H) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro e he
      exact hex ⟨c.color e, he⟩
    simp only [hclass, Set.ncard_empty, Nat.zero_le]

theorem exists_coloring_with_unused_palette (H : SetHypergraph V) (q m n A : ℕ)
    (color : H.EdgeColoring (Fin q)) (hbounded : H.IsCoverBoundedColoring color A)
    (hpalette : q + m ≤ n) :
    ∃ c : H.EdgeColoring (Fin n), ∃ reserved : Finset (Fin n),
      H.IsCoverBoundedColoring c A ∧ reserved.card = m ∧
      ∀ e : H, c.color e ∉ reserved := by
  classical
  have hcard : Fintype.card (Fin q ⊕ Fin m) ≤ Fintype.card (Fin n) := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using hpalette
  obtain ⟨embed : (Fin q ⊕ Fin m) ↪ Fin n⟩ := Function.Embedding.nonempty_of_card_le hcard
  let j : Fin q ↪ Fin n :=
    ⟨fun a ↦ embed (Sum.inl a), fun _ _ h ↦ Sum.inl_injective (embed.injective h)⟩
  let reserved := (univ : Finset (Fin m)).image fun a ↦ embed (Sum.inr a)
  have hinj : Function.Injective (fun a : Fin m ↦ embed (Sum.inr a)) :=
    fun _ _ h ↦ Sum.inr_injective (embed.injective h)
  refine ⟨color.mapEmbedding j, reserved, hbounded.mapEmbedding color A j, ?_, ?_⟩
  · simp only [reserved, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  · intro e he
    obtain ⟨a, _, ha⟩ := mem_image.mp he
    exact Sum.inr_ne_inl (embed.injective ha)

theorem exists_palette_of_card (m n : ℕ) (hmn : m ≤ n) :
    ∃ palette : Finset (Fin n), palette.card = m := by
  let j : Fin m ↪ Fin n :=
    ⟨Fin.castLE hmn, fun _ _ h ↦ Fin.ext (congrArg (fun z : Fin n ↦ z.val) h)⟩
  exact ⟨(univ : Finset (Fin m)).image j, by simp only [card_image_of_injective _ j.injective,
    card_univ, Fintype.card_fin]⟩

theorem coveredVertices_eq_empty_of_unused_color (H : SetHypergraph V)
    (color : H.EdgeColoring C) (a : C) (ha : ∀ e : H, color.color e ≠ a) :
    H.coveredVertices {e : H | color.color e = a} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨e, he⟩ := Set.mem_iUnion.mp hv
  obtain ⟨heq, _⟩ := Set.mem_iUnion.mp he
  exact ha e heq

#print axioms exists_coloring_with_unused_palette

end Erdos19.SetHypergraph
