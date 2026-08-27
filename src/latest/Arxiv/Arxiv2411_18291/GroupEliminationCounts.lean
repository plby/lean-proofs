import Arxiv.Arxiv2411_18291.GroupEliminationGeneration

/-!
# Counting retained cliques and repeated representatives together

The removed clique coordinate is injective and exactly accounts for the
deleted family. Representatives are distinct, and each has weight at most
the group size. These bounds retain the square-root multiplicity gain.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [DecidableEq V] {q : ℕ}

omit [DecidableEq V] in
theorem group_representative_injective (G : Finset (Finset (Block V q)))
    (hdis : Pairwise fun c d : G => Disjoint c.val d.val)
    (Q : G → Block V q) (hQ : ∀ c, Q c ∈ c.val) : Function.Injective Q := by
  intro c d h
  by_contra hne
  exact disjoint_left.mp (hdis hne) (hQ c) (h.symm ▸ hQ d)

theorem representativeDegree_le_mul (D : Finset (Block V q))
    (G : Finset (Finset (Block V q))) (hsub : ∀ c ∈ G, c ⊆ D)
    (hdis : Pairwise fun c d : G => Disjoint c.val d.val)
    (Q : G → Block V q) (hQ : ∀ c, Q c ∈ c.val) {m : ℕ}
    (hsize : ∀ c ∈ G, c.card ≤ m) (T : Finset V) :
    representativeDegree G Q T ≤ m * (D.filter fun P => T ⊆ P.val).card := by
  classical
  have hrep (P : Block V q) : (univ.filter fun c : G => Q c = P).card ≤ 1 := by
    apply card_le_one.mpr
    intro c hc d hd
    exact group_representative_injective G hdis Q hQ
      ((mem_filter.mp hc).2.trans (mem_filter.mp hd).2.symm)
  have hdegree : familyDegree Q T ≤ (D.filter fun P => T ⊆ P.val).card := by
    simpa only [one_mul] using repeated_clique_degree_le D Q
      (fun c => hsub c.val c.property (hQ c)) hrep T
  apply le_trans (b := m * familyDegree Q T) _ (Nat.mul_le_mul_left m hdegree)
  simp only [representativeDegree, familyDegree, card_eq_sum_ones, sum_filter, mul_sum]
  apply sum_le_sum
  intro c _
  by_cases h : T ⊆ (Q c).val
  · simpa only [if_pos h, sum_const, nsmul_eq_mul, Nat.cast_id, mul_one]
      using hsize c.val c.property
  · simp only [if_neg h, mul_zero, le_refl]

theorem groupEliminationRight_degree_eq (G : Finset (Finset (Block V q)))
    (hdis : Pairwise fun c d : G => Disjoint c.val d.val)
    (Q : G → Block V q) (T : Finset V) :
    familyDegree (fun i : GroupEliminationIndex G Q => i.2.val) T =
      ((groupEliminationRemoved G Q).filter fun P => T ⊆ P.val).card := by
  classical
  rw [groupEliminationRemoved, filter_image]
  exact (card_image_of_injective _ (groupEliminationRight_injective G hdis Q)).symm

theorem retained_add_eliminated_count (D : Finset (Block V q))
    (G : Finset (Finset (Block V q))) (hsub : ∀ c ∈ G, c ⊆ D)
    (hdis : Pairwise fun c d : G => Disjoint c.val d.val)
    (Q : G → Block V q) (T : Finset V) :
    ((groupEliminationRetained D G Q).filter fun P => T ⊆ P.val).card +
      familyDegree (fun i : GroupEliminationIndex G Q => i.2.val) T =
        (D.filter fun P => T ⊆ P.val).card := by
  classical
  have hrem : groupEliminationRemoved G Q ⊆ D := by
    intro P hP
    obtain ⟨i, _, rfl⟩ := mem_image.mp hP
    exact groupEliminationRight_mem D G hsub Q i
  have hfilter : ((D \ groupEliminationRemoved G Q).filter fun P => T ⊆ P.val) =
      (D.filter fun P => T ⊆ P.val) \
        ((groupEliminationRemoved G Q).filter fun P => T ⊆ P.val) := by
    ext P
    simp only [mem_filter, mem_sdiff]
    tauto
  rw [groupEliminationRight_degree_eq G hdis Q, groupEliminationRetained, hfilter]
  exact card_sdiff_add_card_eq_card (filter_subset_filter _ hrem)

end Arxiv2411_18291
