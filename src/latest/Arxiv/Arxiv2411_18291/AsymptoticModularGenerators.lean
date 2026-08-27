import Arxiv.Arxiv2411_18291.GoodGeneratorCriterion
import Arxiv.Arxiv2411_18291.GeneratorCapNumerics

/-!
# Sparse modular generators in typical graphs

The finite construction applies uniformly to typical graphs whose density
lies between fixed multiples of `n^(-α)`. At face cap `n^(1-s)`, it loses
at most an `n^(-t)` fraction of cliques and edges when `s+2*t<α`.
Every retained edge has the expected number of unsaturated cliques to
relative error `n^(-t)`.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_good_modular_generating_data (q r h N : ℕ)
    (hN : 0 < N) (hqh : q.choose (r + 1) ≤ h) (hqr : r + 1 ≤ q)
    {b B α δ s t : ℝ} (hb : 0 < b) (ht : 0 < t) (htδ : t < δ)
    (hs : s < 1) (hgap : s + 2 * t < α)
    (hcount : α * q.choose (r + 1) + δ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-δ)) h →
      b * (n : ℝ) ^ (-α) ≤ density K → density K ≤ B * (n : ℝ) ^ (-α) →
      ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
        IsCliqueFamilyBounded r C.generators (2 ^ q * (n : ℝ) ^ (-s)) ∧
        C.generators.card ≤ N * K.card ∧
        (C.saturated.card : ℝ) ≤ (n : ℝ) ^ (-t) * (cliqueFamily K q).card ∧
        ((K \ C.good).card : ℝ) ≤ (n : ℝ) ^ (-t) * K.card ∧
        ∀ e ∈ C.good,
          |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
            cliqueMainTerm n (density K) q (r + 1) (r + 1)| <
            (n : ℝ) ^ (-t) * cliqueMainTerm n (density K) q (r + 1) (r + 1) := by
  filter_upwards [eventually_precise_clique_numerics q r hb (ht.trans htδ) htδ hcount,
    eventually_generator_cap_numerics q r N (b := B) hs hgap,
    eventually_generator_count_error q htδ] with n hn hcap herr
  intro K hT hdlo hdhi
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn.1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
  have hc0 := Real.rpow_nonneg hnR.le (-δ)
  have hp : 0 < density K := (mul_pos hb (Real.rpow_pos_of_pos hnR _)).trans_le hdlo
  have hε : 0 < (n : ℝ) ^ (-t) := Real.rpow_pos_of_pos hnR _
  have hε1 : (n : ℝ) ^ (-t) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr ht.le)
  have hsize : (q : ℝ) ≤ (2 * (n : ℝ) ^ (-δ) - (n : ℝ) ^ (-δ)) *
      (Fintype.card (Fin n) * density K ^ q.choose (r + 1)) := by
    rw [Fintype.card_fin, show 2 * (n : ℝ) ^ (-δ) - (n : ℝ) ^ (-δ) =
      (n : ℝ) ^ (-δ) by ring]
    exact hn.2.2.2 (density K) hdlo
  have hθ : ((q - r : ℕ) : ℝ) * ⌊(n : ℝ) ^ (1 - s)⌋₊ <
      (2 ^ q * (n : ℝ) ^ (-s)) * Fintype.card (Fin n) := by
    simpa only [Fintype.card_fin] using hcap.2.2.1
  have hsmall : 4 * (q.choose (r + 1) : ℝ) * q.choose r * N *
      Fintype.card (Fin n) * density K ≤
      (⌊(n : ℝ) ^ (1 - s)⌋₊ : ℝ) * ((n : ℝ) ^ (-t)) ^ 2 := by
    simpa only [Fintype.card_fin] using hcap.2.2.2 (density K) hdhi
  simpa only [Fintype.card_fin] using exists_good_modular_generating_data N hN hT hqh hqr
    (by simpa only [Fintype.card_fin] using hn.1) hp (by linarith) (by positivity)
    hn.2.1 hsize ⌊(n : ℝ) ^ (1 - s)⌋₊ hcap.2.1 hε hε1 herr hθ hsmall

end Arxiv2411_18291
