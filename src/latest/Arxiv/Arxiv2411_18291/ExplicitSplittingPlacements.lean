import Arxiv.Arxiv2411_18291.SplittingPlacements
import Arxiv.Arxiv2411_18291.ExplicitSeparatedGreedy

/-! # Finite separated placements on all repeated splitting roots -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_splitting_placements_paper_threshold
    {W : Type*} [Fintype W] [DecidableEq W] {q r n : ℕ}
    (S : ExchangeSystem W q (r + 1)) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (8 * q))
    (hS : S.graph.card ≤ (4 * q) ^ (8 * q)) (C M : ℕ) (hC : 0 < C)
    (hconflict : q.choose (r + 1) * (C * M) ≤ (4 * q) ^ (8 * q))
    {A : ℝ} (hA : 1 ≤ A) (hAb : 2 * (C : ℝ) * A ≤ (4 * q : ℝ) ^ (8 * q))
    (D : Finset (Block (Fin n) q)) (B : Hypergraph (Fin n) (r + 1))
    (hD : IsCliqueFamilyBounded r D (A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))))
    (hB : IsGraphBounded B (A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))))
    (hmult : ∀ e : Block (Fin n) (r + 1), (D.filter fun P => e.val ⊆ P.val).card ≤ M)
    (t : ℕ) (Q : ℕ → Block (Fin n) q) (hQ : ∀ i < t, Q i ∈ D)
    (hrep : ∀ P, (univ.filter fun i : Fin t => Q i = P).card ≤ C) :
    ∃ Ψ : (i : Fin t) → EmbeddingExtension (edgeRootMap S.base (Q i)),
      IsGreedyFamily (fun i => edgeRootMap S.base (Q i)) S.graph B Ψ
        (8 * (r + 1).factorial * (C * A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)))) ∧
      (∀ i j : Fin t, i ≠ j → r + 1 ≤ ((Q i).val ∩ (Q j).val).card →
        Disjoint ((univ \ S.base.val).map (Ψ i).val)
          ((univ \ S.base.val).map (Ψ j).val)) ∧
      IsGraphBounded (B ∪ greedyFamilyGraph S.base.val S.graph (fun i => (Ψ i).val))
        (A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)) + S.graph.card *
          (8 * (r + 1).factorial * (C * A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))))) := by
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hAnonneg : 0 ≤ A := le_trans zero_le_one hA
  have hACA : A ≤ (C : ℝ) * A := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC1 hAnonneg
  have hCA : 1 ≤ (C : ℝ) * A := hA.trans hACA
  have hadm := admissible_clique_root S.graph S.base hqr.le
    (S.positive_decomposition.clique_subset S.base_mem)
  let Φ : ℕ → S.base.val ↪ Fin n := fun i => edgeRootMap S.base (Q i)
  let Rel : ℕ → ℕ → Prop := fun i j => r + 1 ≤ ((Q i).val ∩ (Q j).val).card
  have hB' : IsGraphBounded B (C * A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))) :=
    hB.mono (mul_le_mul_of_nonneg_right hACA (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have hroots : ∀ f ∈ S.graph, ∀ hf : f.val ⊆ S.base.val,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf)
        (C * A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))) := by
    intro f _ hf
    have hsub (i : Fin t) : (rootImage (Φ i) f hf).val ⊆ (Q i).val := by
      calc
        _ ⊆ usedVertices (Φ i) := rootImage_subset_usedVertices (Φ i) f hf
        _ = _ := edgeRootMap_usedVertices S.base (Q i)
    have hh := hD.repeated_edgeFamily hqr.le (fun i : Fin t => Q i)
      (fun i => hQ i i.isLt) hC hrep (fun i : Fin t => rootImage (Φ i) f hf) hsub
    simpa only [mul_assoc] using hh
  obtain ⟨Ψ, hΨ, hsep⟩ := exists_absorber_separated_greedy_family_paper_threshold
    hqr hn hw S.graph hS hadm hconflict hCA (by nlinarith only [hAb]) t Φ Rel B hB'
    (prior_clique_overlap_card_le (r + 1) D Q t hQ hrep hmult) hroots
  have hCnonneg : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  refine ⟨Ψ, hΨ, ?_, hΨ.graphBounded hB (by positivity)⟩
  intro i j hij hshare
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hsep i j hlt hshare
  · exact (hsep j i hgt (by simpa only [Rel, inter_comm] using hshare)).symm

end Arxiv2411_18291
