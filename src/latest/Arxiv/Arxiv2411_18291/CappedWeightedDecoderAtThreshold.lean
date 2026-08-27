import Arxiv.Arxiv2411_18291.WeightedDecoderPlacement
import Arxiv.Arxiv2411_18291.CappedWeightedDecoderNumerics

/-! # Sparse weighted decoder regions with constant deviation at n0

The generator edge cap bounds each concentration increment. Taking the
deviation parameter equal to one preserves the input density apart from
the fixed decoder coefficient.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_capped_weighted_decoder_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (D : Finset (Block (Fin n) q)) (B : Hypergraph (Fin n) (r + 1))
    (hD : IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))))
    (hcap : ∀ e : Block (Fin n) (r + 1),
      ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
        (n : ℝ) ^ (paperAlpha q (r + 1) / 10)) :
    ∃ Z : B → Block (Fin n) (q + (r + 1)),
      IsCliqueCover (complete (Fin n) (r + 1) \ B) (fun e : B => e.val) Z ∧
      IsGraphBounded (cliqueCoverGraph (r := r) Z)
        ((n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 30))) ∧
      IsCliqueCapacityBounded r (D ∪ cliqueRefinement q (univ.image Z))
        (edgewiseDecoderCapacity D Z) ((n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 30))) := by
  obtain ⟨hnpos, hsize, hsmall, hfailure⟩ := capped_weighted_decoder_finite_conditions hqr hn
  have hweight (e : Block (Fin n) (r + 1)) : (decoderRootWeight D e : ℝ) ≤
      1 + (n : ℝ) ^ (paperAlpha q (r + 1) / 10) := by
    simpa only [decoderRootWeight, Nat.cast_add, Nat.cast_one] using
      add_le_add (le_refl (1 : ℝ)) (hcap e)
  obtain ⟨Z, hZ, _, hg, hC⟩ := exists_weighted_decoder_placement_of_weight_bound
    hqr.le D B hD hB (by positivity) (by positivity) (c := 1) (by norm_num)
    (C := 1 + (n : ℝ) ^ (paperAlpha q (r + 1) / 10)) (by positivity) hweight
    (by simpa only [Fintype.card_fin] using hsize)
    (by simpa only [Fintype.card_fin] using hnpos)
    (by convert hsmall using 1; ring)
    (by
      simp only [Block, Fintype.card_finset_len, Fintype.card_fin]
      convert hfailure using 1; congr 2; ring)
  obtain ⟨hgraph, hcapacity⟩ := capped_weighted_decoder_output_density hqr hn
  refine ⟨Z, hZ, hg.mono ?_, hC.mono ?_⟩
  · convert hgraph using 1; ring
  · convert hcapacity using 1; ring

end Arxiv2411_18291
