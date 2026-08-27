import Arxiv.Arxiv2411_18291.WeightedDecoderPlacement
import Arxiv.Arxiv2411_18291.WeightedDecoderNumerics

/-! # Weighted decoder regions at the printed threshold

Both the output graph and the variable clique capacities have density
`n^(-2*alpha/5)`. The proof constructs the regions and discharges all
weighted placement inequalities at `n0`.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem IsCliqueCover.decoder_support_subset
    {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}
    {D : Finset (Block V q)} {B : Hypergraph V (r + 1)}
    {Z : B → Block V (q + (r + 1))}
    (hZ : IsCliqueCover (complete V (r + 1) \ B) (fun e : B => e.val) Z)
    (hDB : cliqueSupport (r + 1) D ⊆ B) :
    cliqueSupport (r + 1) (D ∪ cliqueRefinement q (univ.image Z)) ⊆
      cliqueCoverGraph (r := r) Z := by
  intro e he
  obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.mp he
  rcases mem_union.mp hQ with hQD | hQZ
  · exact hZ.root_mem ⟨e, hDB (mem_biUnion.mpr ⟨Q, hQD, heQ⟩)⟩
  · exact hZ.decomposition.refinement_support_subset (mem_biUnion.mpr ⟨Q, hQZ, heQ⟩)

theorem exists_weighted_decoder_paper_threshold {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (D : Finset (Block (Fin n) q)) (B : Hypergraph (Fin n) (r + 1))
    (hD : IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)))) :
    ∃ Z : B → Block (Fin n) (q + (r + 1)),
      IsCliqueCover (complete (Fin n) (r + 1) \ B) (fun e : B => e.val) Z ∧
      IsGraphBounded (cliqueCoverGraph (r := r) Z)
        ((n : ℝ) ^ (-(2 * paperAlpha q (r + 1) / 5))) ∧
      IsCliqueCapacityBounded r (D ∪ cliqueRefinement q (univ.image Z))
        (edgewiseDecoderCapacity D Z) ((n : ℝ) ^ (-(2 * paperAlpha q (r + 1) / 5))) := by
  obtain ⟨hnpos, hsize, hsmall, hfailure⟩ := weighted_decoder_finite_conditions hqr hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
  obtain ⟨Z, hZ, _, hg, hcap⟩ := exists_weighted_decoder_placement hqr.le D B hD hB
    (by positivity) (by positivity)
    (c := (n : ℝ) ^ (paperAlpha q (r + 1) / 10)) (by positivity)
    (by simpa only [Fintype.card_fin] using hsize)
    (by simpa only [Fintype.card_fin] using hnpos) hsmall
    (by simpa only [Block, Fintype.card_finset_len, Fintype.card_fin] using hfailure)
  obtain ⟨hgraph, hcapacity⟩ := weighted_decoder_output_density hqr hn
  exact ⟨Z, hZ, hg.mono hgraph, hcap.mono hcapacity⟩

end Arxiv2411_18291
