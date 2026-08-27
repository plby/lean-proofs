import Arxiv.Arxiv2411_18291.ExplicitDecoderPlacement
import Arxiv.Arxiv2411_18291.SparseLocalDecoders

/-! # Sparse local decoders at the absorber's finite working scale -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_sparse_local_decoders_paper_threshold {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)))) :
    ∃ Z : B → Block (Fin n) (q + (r + 1)), ∃ D : Finset (Block (Fin n) q),
      IsCliqueCover (complete (Fin n) (r + 1) \ B) (fun e : B => e.val) Z ∧
      D = cliqueRefinement q (univ.image Z) ∧ IsLocalDecoderFamily B D ∧
      IsGraphBounded (cliqueSupport (r + 1) D)
        ((1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1)) *
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))) := by
  obtain ⟨Z, hZ, hb⟩ := exists_clique_placement_paper_threshold hqr
    (Nat.le_add_left (r + 1) q) (by omega) hn B hB
  exact ⟨Z, cliqueRefinement q (univ.image Z), hZ, rfl, hZ.localDecoderFamily hqr.le,
    hb.subgraph hZ.decomposition.refinement_support_subset⟩

theorem exists_bounded_local_decoder_family_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)))) :
    let C : ℝ := 1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1)
    ∃ D : Finset (Block (Fin n) q), IsLocalDecoderFamily B D ∧
      IsGraphBounded (cliqueSupport (r + 1) D)
        (C * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))) ∧
      IsCliqueFamilyBounded r D
        (q.choose (r + 1) * C * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))) := by
  dsimp only
  obtain ⟨_, D, _, _, hD, hb⟩ := exists_sparse_local_decoders_paper_threshold hqr hn B hB
  refine ⟨D, hD, hb, ?_⟩
  have hmulti := hb.cliqueFamilyBounded D (Nat.choose_pos hqr.le) hD.multiplicity (Subset.refl _)
  simpa only [mul_assoc] using hmulti

end Arxiv2411_18291
