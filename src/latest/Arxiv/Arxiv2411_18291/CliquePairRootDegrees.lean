import Arxiv.Arxiv2411_18291.EliminationRootInputs

/-!
# Elimination root bounds from the two indexed clique degree bounds

Every induced root edge lies on one fixed side of the elimination pair.
Bounding the indexed clique degrees on that side suffices for the greedy
input bound, even when a representative occurs many times.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem familyDegree_reindex {I J V : Type*} [Fintype I] [Fintype J] [DecidableEq V]
    {q : ℕ} (e : I ≃ J) (P : J → Block V q) (T : Finset V) :
    familyDegree (fun i => P (e i)) T = familyDegree P T := by
  classical
  let e' : {i : I // T ⊆ (P (e i)).val} ≃ {j : J // T ⊆ (P j).val} :=
    Equiv.subtypeEquiv e (fun _ => Iff.rfl)
  simpa only [familyDegree, Fintype.card_subtype] using Fintype.card_congr e'

theorem familyDegree_mono_of_subset {I V : Type*} [Fintype I] [DecidableEq V]
    {q r : ℕ} (E : I → Block V r) (P : I → Block V q)
    (hsub : ∀ i, (E i).val ⊆ (P i).val) (T : Finset V) : familyDegree E T ≤ familyDegree P T := by
  apply card_le_card
  intro i hi
  exact mem_filter.mpr ⟨mem_univ _, ((mem_filter.mp hi).2).trans (hsub i)⟩

variable {I W V : Type*} [Fintype I] [Fintype W] [Fintype V]
variable [DecidableEq W] [DecidableEq V] {q r : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {N : Block W q} {e : Block W (r + 1)}

theorem IsEliminationPair.root_inputs_of_degrees (h : IsEliminationPair S N e)
    (P Q : I → Block V q) {θ : ℝ}
    (hP : ∀ T : Block V r, (familyDegree P T.val : ℝ) < θ * Fintype.card V)
    (hQ : ∀ T : Block V r, (familyDegree Q T.val : ℝ) < θ * Fintype.card V)
    (φ : I → ↥(S.base.val ∪ N.val) ↪ V)
    (hφP : ∀ i, rootImage (φ i) S.base subset_union_left = P i)
    (hφQ : ∀ i, rootImage (φ i) N subset_union_right = Q i)
    (f : Block W (r + 1)) (hf : f ∈ S.graph) (hroot : f.val ⊆ S.base.val ∪ N.val) :
    IsEdgeFamilyBounded (fun i => rootImage (φ i) f hroot) θ := by
  rcases h.root_edge_cases hf hroot with hp | hq
  · have hsub (i : I) : (rootImage (φ i) f hroot).val ⊆ (P i).val := by
      rw [← hφP i]
      exact rootImage_subset_rootImage (φ i) f S.base hroot subset_union_left hp
    intro T
    exact (Nat.cast_le.mpr (familyDegree_mono_of_subset _ P hsub T.val)).trans_lt (hP T)
  · have hsub (i : I) : (rootImage (φ i) f hroot).val ⊆ (Q i).val := by
      rw [← hφQ i]
      exact rootImage_subset_rootImage (φ i) f N hroot subset_union_right hq
    intro T
    exact (Nat.cast_le.mpr (familyDegree_mono_of_subset _ Q hsub T.val)).trans_lt (hQ T)

end Arxiv2411_18291
