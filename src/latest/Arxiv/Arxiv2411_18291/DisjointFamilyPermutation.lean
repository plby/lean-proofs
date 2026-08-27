import Arxiv.Arxiv2411_18291.PermutationBlocks

/-!
# Permutations matching finite partitions

Match corresponding parts of two disjoint finite families, then extend the
resulting injection to a permutation. The three regions of a pair of sets
show that the orbit of an ordered pair is determined by their sizes and
the size of their intersection.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V I : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem disjoint_family_val_injective (S : I → Finset V)
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) :
    Function.Injective (fun x : Σ i, S i => (x.2 : V)) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ hxy
  change (x : V) = (y : V) at hxy
  have hij : i = j := by
    by_contra hij
    exact (disjoint_left.mp (hS hij)) x.property (hxy.symm ▸ y.property)
  subst j
  exact congrArg (Sigma.mk i) (Subtype.ext hxy)

omit [DecidableEq V] in
theorem exists_perm_map_disjoint_family [Finite I] (S T : I → Finset V)
    (hS : Pairwise fun i j => Disjoint (S i) (S j))
    (hT : Pairwise fun i j => Disjoint (T i) (T j))
    (hcard : ∀ i, (S i).card = (T i).card) :
    ∃ σ : Equiv.Perm V, ∀ i, (S i).map σ.toEmbedding = T i := by
  let e : (Σ i, S i) ≃ (Σ i, T i) :=
    Equiv.sigmaCongrRight fun i => (S i).equivOfCardEq (hcard i)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun x : Σ i, S i => (x.2 : V)) (fun x : Σ i, S i => ((e x).2 : V))
    (disjoint_family_val_injective S hS) ((disjoint_family_val_injective T hT).comp e.injective)
  refine ⟨σ, fun i => eq_of_subset_of_card_le ?_ ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    have he : σ y = ((S i).equivOfCardEq (hcard i) ⟨y, hy⟩ : V) := hσ ⟨i, ⟨y, hy⟩⟩
    change σ y ∈ T i
    rw [he]
    exact ((S i).equivOfCardEq (hcard i) ⟨y, hy⟩).property
  · simp only [card_map, hcard, le_refl]

theorem exists_perm_map_finset_pair (S T S' T' : Finset V)
    (hS : S.card = S'.card) (hT : T.card = T'.card)
    (hinter : (S ∩ T).card = (S' ∩ T').card) :
    ∃ σ : Equiv.Perm V, S.map σ.toEmbedding = S' ∧ T.map σ.toEmbedding = T' := by
  let F : Fin 3 → Finset V := fun i => if i = 0 then S ∩ T else if i = 1 then S \ T else T \ S
  let F' : Fin 3 → Finset V := fun i =>
    if i = 0 then S' ∩ T' else if i = 1 then S' \ T' else T' \ S'
  have hdisj (A B : Finset V) : Pairwise fun i j : Fin 3 =>
      Disjoint (if i = 0 then A ∩ B else if i = 1 then A \ B else B \ A)
        (if j = 0 then A ∩ B else if j = 1 then A \ B else B \ A) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [disjoint_left]
  have hcard (i : Fin 3) : (F i).card = (F' i).card := by
    fin_cases i <;> norm_num [F, F', card_sdiff, inter_comm T S, inter_comm T' S',
      hS, hT, hinter]
  obtain ⟨σ, hσ⟩ := exists_perm_map_disjoint_family F F' (hdisj S T) (hdisj S' T') hcard
  have h0 : (S ∩ T).map σ.toEmbedding = S' ∩ T' := by
    simpa [F, F'] using hσ 0
  have h1 : (S \ T).map σ.toEmbedding = S' \ T' := by
    simpa [F, F'] using hσ 1
  have h2 : (T \ S).map σ.toEmbedding = T' \ S' := by
    simpa [F, F'] using hσ 2
  refine ⟨σ, ?_, ?_⟩
  · calc
      S.map σ.toEmbedding = ((S ∩ T) ∪ (S \ T)).map σ.toEmbedding := by
        rw [union_comm, sdiff_union_inter]
      _ = (S' ∩ T') ∪ (S' \ T') := by rw [map_union, h0, h1]
      _ = S' := by rw [union_comm, sdiff_union_inter]
  · calc
      T.map σ.toEmbedding = ((S ∩ T) ∪ (T \ S)).map σ.toEmbedding := by
        rw [inter_comm S T, union_comm, sdiff_union_inter]
      _ = (S' ∩ T') ∪ (T' \ S') := by rw [map_union, h0, h2]
      _ = T' := by rw [inter_comm S' T', union_comm, sdiff_union_inter]

end Arxiv2411_18291
