import Arxiv.Arxiv2411_18291.VariableSplittingAtThreshold
import Arxiv.Arxiv2411_18291.VariableSplittingDegrees
import Arxiv.Arxiv2411_18291.VariableNearMatching
import Arxiv.Arxiv2411_18291.CliqueSupportBounds

/-! # Fixed signed output and sparse boundary after variable splitting

The constructed family at n0 has a sparse boundary multigraph, not just a
sparse underlying graph. Every generated leave uses its fixed sign families
and admits a matching of the selected near cancellations. This does not
construct a uniformly sparse elimination family for all potential pairs.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem variable_splitting_clique_density {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    2 * (q - r : ℕ) * (n : ℝ) ^ (-(2 * paperAlpha q (r + 1) / 5)) +
      2 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)) ≤
        (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 10)) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hα := paperAlpha_pos hqr
  have hscale : (n : ℝ) ^ (-(2 * paperAlpha q (r + 1) / 5)) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hα])
  have hcoef : (2 * (q - r : ℕ) + 2 : ℝ) ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) / 30) := by
    have hnat : 2 * (q - r) + 2 ≤ 4 * q := by omega
    have hreal : (2 * (q - r : ℕ) + 2 : ℝ) ≤ 4 * q := by exact_mod_cast hnat
    have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
    have hg := paper_threshold_alpha_rpow_lower (s := 1) hqr hn
      (by norm_num : (0 : ℝ) ≤ 1 / 30) (by linarith only [hq])
    exact hreal.trans (by simpa only [pow_one, div_eq_mul_inv, one_mul] using hg)
  calc
    _ ≤ 2 * (q - r : ℕ) * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)) +
        2 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)) := by gcongr
    _ = (2 * (q - r : ℕ) + 2) *
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)) := by ring
    _ ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 30) *
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

theorem VariableSplittingFamily.cliques_bounded_paper_threshold
    {W : Type*} [Fintype W] [DecidableEq W] {q r n : ℕ}
    {S : ExchangeSystem W q (r + 1)} {D : Finset (Block (Fin n) q)}
    {B : Hypergraph (Fin n) (r + 1)} {C : Block (Fin n) q → ℕ}
    (F : VariableSplittingFamily S D B C ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))))
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hC : IsCliqueCapacityBounded r D C ((n : ℝ) ^ (-(2 * paperAlpha q (r + 1) / 5)))) :
    IsCliqueFamilyBounded r F.cliques ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 10))) :=
  (F.cliques_bounded hC).mono (variable_splitting_clique_density hqr hn)

theorem exists_constructed_variable_splitting_output {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (D : Finset (Block (Fin n) q)) (B : Hypergraph (Fin n) (r + 1))
    (hDB : cliqueSupport (r + 1) D ⊆ B)
    (hD : IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)))) :
    ∃ T : FiniteExchangeSystem q (r + 1), ∃ A : Finset (Block T.Vertex q),
      IsExchangeFamily T.system A ∧ IsCrossSimple (r + 1) T.system.positive T.system.negative ∧
      IsPositiveFrameLocal T.system A ∧
      ∃ Z : B → Block (Fin n) (q + (r + 1)),
        IsCliqueCover (complete (Fin n) (r + 1) \ B) (fun e : B => e.val) Z ∧
        ∃ F : VariableSplittingFamily T.system (D ∪ cliqueRefinement q (univ.image Z))
            (cliqueCoverGraph (r := r) Z) (edgewiseDecoderCapacity D Z)
            ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))),
          IsCliqueFamilyBounded r F.cliques ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 10))) ∧
          ∀ L : Hypergraph (Fin n) (r + 1), L ⊆ B → GeneratedBy D (indicator L) →
            ∃ P N : Finset (Block (Fin n) q),
              P ⊆ F.positiveCliques ∧ N ⊆ F.negativeCliques ∧ Disjoint P N ∧
              boundary (r + 1) (indicator P - indicator N) = indicator L ∧
              Nonempty (VariableNearMatching F P N) := by
  classical
  obtain ⟨T, A, hsize, hA, hcross, hlocal, hw⟩ :=
    exists_small_carrier_clique_exchange q (r + 1) (Nat.succ_pos r) hqr
  obtain ⟨Z, hZ, hgraph, hcapacity⟩ := exists_weighted_decoder_paper_threshold hqr hn D B hD hB
  obtain ⟨F⟩ := exists_variable_splitting_paper_threshold T.system hqr hn hw
    (hsize.trans (paper_exchange_graph_bound (Nat.succ_pos r) hqr))
    (D ∪ cliqueRefinement q (univ.image Z)) (edgewiseDecoderCapacity D Z)
    (cliqueCoverGraph (r := r) Z) hcapacity hgraph (hZ.decoder_support_subset hDB)
  refine ⟨T, A, hA, hcross, hlocal, Z, hZ, F,
    F.cliques_bounded_paper_threshold hqr hn hcapacity, ?_⟩
  intro L hLB hgen
  obtain ⟨Φ, hΦ, hs, hcap⟩ :=
    edgewise_representation_of_local_decoders hqr D B L hDB hLB Z hZ hgen
  obtain ⟨P, N, hP, hN, hdis, hb⟩ := F.signed_representation_with_signs hqr.le Φ hcap hs
  have hboundary := hb.trans hΦ
  refine ⟨P, N, hP, hN, hdis, hboundary, F.exists_nearMatching hA P N hP hN ?_⟩
  intro e _
  rw [hboundary]
  unfold indicator
  split_ifs <;> norm_num

end Arxiv2411_18291
