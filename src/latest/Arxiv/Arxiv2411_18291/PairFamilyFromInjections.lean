import Arxiv.Arxiv2411_18291.PairNeighbors

/-! # A pair packing from two injective maps with disjoint images -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_pair_family_of_injections {I V : Type*} [Fintype I] [DecidableEq V]
    (H : Finset (Block V 2)) (u v : I → V)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hdis : ∀ i j, u i ≠ v j) (hH : ∀ i, PairAdjacent H (u i) (v i)) :
    ∃ C : Finset (Block V 2), C ⊆ H ∧ IsVertexPacking C ∧ C.card = Fintype.card I := by
  classical
  let Q (i : I) : Block V 2 := ⟨{u i, v i}, card_pair (hdis i i)⟩
  have hQH (i : I) : Q i ∈ H := by
    obtain ⟨P, hP, hval⟩ := hH i
    have hPQ : P = Q i := Subtype.ext hval
    exact hPQ ▸ hP
  have hQinj : Function.Injective Q := by
    intro i j hij
    have hi : u i ∈ (Q j).val := by rw [← hij]; exact mem_insert_self _ _
    rcases mem_insert.mp hi with h | h
    · exact hu h
    · exact (hdis i j (mem_singleton.mp h)).elim
  have hQdis : Pairwise fun i j => Disjoint (Q i).val (Q j).val := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hxi hxj
    rcases mem_insert.mp hxi with hxi | hxi
    · rw [hxi] at hxj
      rcases mem_insert.mp hxj with h | h
      · exact hij (hu h)
      · exact hdis i j (mem_singleton.mp h)
    · have hxi' : x = v i := mem_singleton.mp hxi
      rw [hxi'] at hxj
      rcases mem_insert.mp hxj with h | h
      · exact hdis j i h.symm
      · exact hij (hv (mem_singleton.mp h))
  refine ⟨univ.image Q, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨i, _, rfl⟩ := mem_image.mp hP
    exact hQH i
  · intro P hP R hR hPR
    obtain ⟨i, _, rfl⟩ := mem_image.mp hP
    obtain ⟨j, _, rfl⟩ := mem_image.mp hR
    exact hQdis (fun hij => hPR (congrArg Q hij))
  · rw [card_image_of_injective _ hQinj, card_univ]

end Arxiv2411_18291
