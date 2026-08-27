import Arxiv.Arxiv2411_18291.RepeatedCliqueRoots
import Arxiv.Arxiv2411_18291.RootedCliquePattern
import Arxiv.Arxiv2411_18291.SeparatedGreedyCandidates

/-!
# Input conditions for clique-rooted greedy placements

A complete root clique makes any containing pattern admissible. Its root
edge images lie inside the prescribed image clique. Finally, the number
of preceding roots sharing an edge is controlled by the repeated-clique
overlap count, with the finite sequence indexing checked explicitly.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r : ℕ} {F : Finset W}

omit [Fintype V] [DecidableEq V] in
theorem admissible_clique_root (H : Hypergraph W (r + 1)) (Q : Block W q)
    (hqr : r + 1 ≤ q) (hQ : cliqueEdges (r + 1) Q ⊆ H) : IsAdmissible H Q.val := by
  intro e _ _
  have hc : (e.val ∩ Q.val).card ≤ r + 1 := by
    simpa only [e.property] using card_le_card (inter_subset_left (s₁ := e.val) (s₂ := Q.val))
  obtain ⟨s, hs, hsQ, hsc⟩ := exists_subsuperset_card_eq inter_subset_right hc
    (by simpa only [Q.property] using hqr)
  exact ⟨⟨s, hsc⟩, hQ ((mem_cliqueEdges _ _).mpr hsQ), hsQ, hs⟩

omit [Fintype W] [Fintype V] [DecidableEq V] in
theorem rootImage_subset_usedVertices (φ : F ↪ V) (e : Block W r) (he : e.val ⊆ F) :
    (rootImage φ e he).val ⊆ usedVertices φ :=
  map_subset_map.mpr (subset_univ _)

omit [Fintype W] [DecidableEq W] [Fintype V] in
theorem prior_clique_overlap_le (m : ℕ) (Q : ℕ → Block V q) {t i : ℕ} (hi : i < t) :
    (priorRelated (fun j k => m ≤ ((Q j).val ∩ (Q k).val).card) i).card ≤
      (cliqueOverlapIndices m (fun j : Fin t => Q j) (Q i)).card := by
  classical
  let s := priorRelated (fun j k => m ≤ ((Q j).val ∩ (Q k).val).card) i
  let f : s ↪ Fin t :=
    ⟨fun j => ⟨j.val, ((mem_priorRelated _ _ _).mp j.property).1.trans hi⟩,
      fun j k h => Subtype.ext (congrArg Fin.val h)⟩
  have hsub : univ.map f ⊆ cliqueOverlapIndices m (fun j : Fin t => Q j) (Q i) := by
    intro j hj
    obtain ⟨k, _, rfl⟩ := mem_map.mp hj
    exact mem_filter.mpr ⟨mem_univ _, ((mem_priorRelated _ _ _).mp k.property).2⟩
  calc
    _ = (univ.map f).card := by rw [card_map, card_univ, Fintype.card_coe]
    _ ≤ _ := card_le_card hsub

omit [Fintype W] [DecidableEq W] [Fintype V] in
theorem prior_clique_overlap_card_le [Finite V] (m : ℕ) (D : Finset (Block V q))
    (Q : ℕ → Block V q) (t : ℕ) (hQ : ∀ i < t, Q i ∈ D) {C M : ℕ}
    (hrep : ∀ P, (univ.filter fun i : Fin t => Q i = P).card ≤ C)
    (hmult : ∀ e : Block V m, (D.filter fun P => e.val ⊆ P.val).card ≤ M) :
    ∀ i < t, (priorRelated (fun j k => m ≤ ((Q j).val ∩ (Q k).val).card) i).card ≤
      q.choose m * (C * M) := by
  intro i hi
  exact (prior_clique_overlap_le m Q hi).trans
    (cliqueOverlapIndices_card_le m D (fun j : Fin t => Q j) (fun j => hQ j j.isLt)
      hrep hmult (Q i))

end Arxiv2411_18291
