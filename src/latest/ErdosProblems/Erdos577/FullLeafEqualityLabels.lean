import ErdosProblems.Erdos577.FullLeafEqualityMatching

/-! The three matching edges have actual injective labels covering both triples. -/

namespace Erdos577.FullLeafEquality

open Finset

variable {V : Type*} [DecidableEq V]

structure MatchedTriple (G : SimpleGraph V) (t u : Finset V) where
  first : Fin 3 ↪ V
  second : Fin 3 ↪ V
  first_support : univ.image first = t
  second_support : univ.image second = u
  adjacent : ∀ i, G.Adj (first i) (second i)

end Erdos577.FullLeafEquality

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Maximal.matching_triple (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k) :
    Nonempty (FullLeafEquality.MatchedTriple G (s.erase y)
      (FullLeafEquality.matchedSecond p s a y)) := by
  classical
  have htcard : Fintype.card {v // v ∈ s.erase y} = 3 := by
    simpa only [Fintype.card_coe] using hm.1.first_triple_clique.card_eq
  let idx : Fin 3 ≃ {v // v ∈ s.erase y} := (Fintype.equivFinOfCardEq htcard).symm
  let f : Fin 3 ↪ V := {
    toFun := fun i ↦ (idx i).val
    inj' := fun i j hij ↦ idx.injective (Subtype.ext hij) }
  have hf (i : Fin 3) : f i ∈ s.erase y := (idx i).property
  have hneighbors (i : Fin 3) :
      ∃ v ∈ FullLeafEquality.matchedSecond p s a y, G.Adj (f i) v := by
    have hpos : 0 < degreeIn G (f i) (insert (p.vertices 3) a) := by
      rw [hm.first_matching_degree hcard hdeg hn (hf i)]
      decide
    obtain ⟨v, hv⟩ := card_pos.mp hpos
    obtain ⟨hv, hadj⟩ := mem_filter.mp hv
    refine ⟨v, mem_filter.mpr ⟨hv, ?_⟩, hadj⟩
    exact card_pos.mpr ⟨f i, mem_filter.mpr ⟨hf i, hadj.symm⟩⟩
  choose w hw hwadj using hneighbors
  have hwInjective : Function.Injective w := by
    intro i j hij
    have hsecond := (mem_filter.mp (hw i)).1
    have he := (hm.1.matching_unique hcard hn).2 (w i) hsecond (f i) (hf i) (f j) (hf j)
      (hwadj i) (hij.symm ▸ hwadj j)
    exact f.injective he
  let g : Fin 3 ↪ V := ⟨w, hwInjective⟩
  have hfSupport : univ.image f = s.erase y := by
    apply eq_of_subset_of_card_le
    · intro v hv
      obtain ⟨i, _, rfl⟩ := mem_image.mp hv
      exact hf i
    · rw [card_image_of_injective _ f.injective, card_univ, Fintype.card_fin,
        hm.1.first_triple_clique.card_eq]
  have hgSupport : univ.image g = FullLeafEquality.matchedSecond p s a y := by
    apply eq_of_subset_of_card_le
    · intro v hv
      obtain ⟨i, _, rfl⟩ := mem_image.mp hv
      exact hw i
    · rw [card_image_of_injective _ g.injective, card_univ, Fintype.card_fin,
        (hm.matched_second_triangle hcard hdeg hn).card_eq]
  exact ⟨⟨f, g, hfSupport, hgSupport, hwadj⟩⟩

end Erdos577.FullLeafCore
