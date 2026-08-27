import Arxiv.Arxiv2411_18291.IntersectingGreedyStars

/-! # An admissible double-star pattern with only linearly many edges -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable (A : Type*) [Fintype A] [DecidableEq A] [Zero A]

def greedyRootSpoke (a : {a : A // a ≠ 0}) : Block (Option A) 2 :=
  ⟨{some 0, some a.val}, by rw [card_pair]; exact fun h => a.property (Option.some.inj h).symm⟩

def greedyDoubleStar : Hypergraph (Option A) 2 :=
  univ.image greedyStarSpoke ∪ univ.image (greedyRootSpoke A)

omit [DecidableEq A] [Zero A] in
theorem greedyStarRoots_some (a : A) : some a ∈ greedyStarRoots A :=
  (mem_greedyStarRoots _).mpr ⟨a, rfl⟩

theorem greedyRootSpoke_subset (a : {a : A // a ≠ 0}) :
    (greedyRootSpoke A a).val ⊆ greedyStarRoots A := by
  intro x hx
  rcases mem_insert.mp hx with rfl | hx
  · exact greedyStarRoots_some A 0
  · rw [mem_singleton.mp hx]
    exact greedyStarRoots_some A a.val

theorem greedyDoubleStar_spoke_mem (a : A) : greedyStarSpoke a ∈ greedyDoubleStar A :=
  mem_union_left _ (mem_image.mpr ⟨a, mem_univ _, rfl⟩)

theorem greedyDoubleStar_card_le : (greedyDoubleStar A).card ≤ 2 * Fintype.card A := by
  have hnew : (univ.image (greedyStarSpoke (A := A))).card ≤ Fintype.card A := by
    simpa only [card_univ] using card_image_le (s := (univ : Finset A))
      (f := greedyStarSpoke)
  have hroot : (univ.image (greedyRootSpoke A)).card ≤ Fintype.card A :=
    (card_image_le.trans (by rw [card_univ]; exact Fintype.card_subtype_le _))
  have hu := card_union_le (univ.image (greedyStarSpoke (A := A)))
    (univ.image (greedyRootSpoke A))
  change _ ≤ _
  unfold greedyDoubleStar
  omega

theorem greedyDoubleStar_nonempty : (greedyDoubleStar A).Nonempty :=
  ⟨greedyStarSpoke 0, greedyDoubleStar_spoke_mem A 0⟩

theorem greedyDoubleStar_admissible (b : A) (hb : b ≠ 0) :
    IsAdmissible (greedyDoubleStar A) (greedyStarRoots A) := by
  intro e he heF
  rcases mem_union.mp he with he | he
  · obtain ⟨a, _, rfl⟩ := mem_image.mp he
    by_cases ha : a = 0
    · refine ⟨greedyRootSpoke A ⟨b, hb⟩,
        mem_union_right _ (mem_image.mpr ⟨⟨b, hb⟩, mem_univ _, rfl⟩),
        greedyRootSpoke_subset A _, ?_⟩
      intro x hx
      rcases mem_insert.mp (mem_inter.mp hx).1 with rfl | hx'
      · exact (none_not_mem_greedyStarRoots A (mem_inter.mp hx).2).elim
      · rw [mem_singleton.mp hx', ha]
        exact mem_insert_self _ _
    · refine ⟨greedyRootSpoke A ⟨a, ha⟩,
        mem_union_right _ (mem_image.mpr ⟨⟨a, ha⟩, mem_univ _, rfl⟩),
        greedyRootSpoke_subset A _, ?_⟩
      intro x hx
      rcases mem_insert.mp (mem_inter.mp hx).1 with rfl | hx'
      · exact (none_not_mem_greedyStarRoots A (mem_inter.mp hx).2).elim
      · rw [mem_singleton.mp hx']
        exact mem_insert_of_mem (mem_singleton_self _)
  · obtain ⟨a, _, rfl⟩ := mem_image.mp he
    exact (heF (greedyRootSpoke_subset A a)).elim

end Arxiv2411_18291
