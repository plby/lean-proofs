import Arxiv.Arxiv2411_18291.CliqueRootInputs
import Arxiv.Arxiv2411_18291.AsymptoticSeparatedGreedy
import Arxiv.Arxiv2411_18291.ExchangeConfiguration

/-!
# Separated exchange copies for the splitting stage

For a bounded family of cliques with bounded edge multiplicity, repeat
each root at most `C` times and place the exchange configuration on every
root. The new edge sets are disjoint and avoid the prescribed graph, and
copies whose roots share an edge have disjoint free vertices. This proves
the geometric construction in Step 3 of the absorber, with explicit
constant losses and no loss in the density exponent.
-/

open Finset Filter

noncomputable section

namespace Arxiv2411_18291

variable {W : Type*} [Fintype W] [DecidableEq W] {q r : ℕ}

theorem eventually_exists_splitting_placements (S : ExchangeSystem W q (r + 1))
    (hqr : r + 1 ≤ q) (C M : ℕ) (hC : 0 < C) {A ρ : ℝ}
    (hA : 1 ≤ A) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ D : Finset (Block (Fin n) q),
      ∀ B : Hypergraph (Fin n) (r + 1),
      IsCliqueFamilyBounded r D (A * (n : ℝ) ^ (-ρ)) →
      IsGraphBounded B (A * (n : ℝ) ^ (-ρ)) →
      (∀ e : Block (Fin n) (r + 1), (D.filter fun P => e.val ⊆ P.val).card ≤ M) →
      ∀ t : ℕ, ∀ Q : ℕ → Block (Fin n) q, (∀ i < t, Q i ∈ D) →
      (∀ P, (univ.filter fun i : Fin t => Q i = P).card ≤ C) →
      ∃ Ψ : (i : Fin t) → EmbeddingExtension (edgeRootMap S.base (Q i)),
        IsGreedyFamily (fun i => edgeRootMap S.base (Q i)) S.graph B Ψ
          (8 * (r + 1).factorial * (C * A * (n : ℝ) ^ (-ρ))) ∧
        (∀ i j : Fin t, i ≠ j → r + 1 ≤ ((Q i).val ∩ (Q j).val).card →
          Disjoint ((univ \ S.base.val).map (Ψ i).val)
            ((univ \ S.base.val).map (Ψ j).val)) ∧
        IsGraphBounded (B ∪ greedyFamilyGraph S.base.val S.graph (fun i => (Ψ i).val))
          (A * (n : ℝ) ^ (-ρ) + S.graph.card *
            (8 * (r + 1).factorial * (C * A * (n : ℝ) ^ (-ρ)))) := by
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hAnonneg : 0 ≤ A := by linarith
  have hACA : A ≤ (C : ℝ) * A := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC1 hAnonneg
  have hCA : 1 ≤ (C : ℝ) * A := hA.trans hACA
  have hadm := admissible_clique_root S.graph S.base hqr
    (S.positive_decomposition.clique_subset S.base_mem)
  filter_upwards [eventually_exists_separated_greedy_family S.graph hadm
    (q.choose (r + 1) * (C * M)) hCA hρ hρ1] with n hplace
  intro D B hD hB hmult t Q hQ hrep
  let Φ : ℕ → S.base.val ↪ Fin n := fun i => edgeRootMap S.base (Q i)
  let Rel : ℕ → ℕ → Prop := fun i j => r + 1 ≤ ((Q i).val ∩ (Q j).val).card
  have hB' : IsGraphBounded B (C * A * (n : ℝ) ^ (-ρ)) :=
    hB.mono (mul_le_mul_of_nonneg_right hACA (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have hroots : ∀ f ∈ S.graph, ∀ hf : f.val ⊆ S.base.val,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf)
        (C * A * (n : ℝ) ^ (-ρ)) := by
    intro f _ hf
    have hsub (i : Fin t) : (rootImage (Φ i) f hf).val ⊆ (Q i).val := by
      calc
        _ ⊆ usedVertices (Φ i) := rootImage_subset_usedVertices (Φ i) f hf
        _ = _ := edgeRootMap_usedVertices S.base (Q i)
    have h := hD.repeated_edgeFamily hqr (fun i : Fin t => Q i) (fun i => hQ i i.isLt)
      hC hrep (fun i : Fin t => rootImage (Φ i) f hf) hsub
    simpa only [mul_assoc] using h
  obtain ⟨Ψ, hΨ, hsep⟩ := hplace t Φ Rel B hB'
    (prior_clique_overlap_card_le (r + 1) D Q t hQ hrep hmult) hroots
  have hCnonneg : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  refine ⟨Ψ, hΨ, ?_, hΨ.graphBounded hB (by positivity)⟩
  intro i j hij hshare
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hsep i j hlt hshare
  · exact (hsep j i hgt (by simpa only [Rel, inter_comm] using hshare)).symm

end Arxiv2411_18291
