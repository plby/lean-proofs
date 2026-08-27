import Arxiv.Arxiv2411_18291.TypicalPermutationPairs
import Arxiv.Arxiv2411_18291.AsymptoticCliqueCount

/-!
# Polynomial joint-probability errors

Typicality and a polynomial density lower bound discharge every numerical
condition in the joint clique estimate. The result is uniform over the
intersection size, the two clique subfamilies, and the measurable structure
used for the finite permutation space.
-/

open Finset Filter MeasureTheory
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_permuted_clique_pair_probability_le (q r h : ℕ)
    (hqh : q.choose (r + 1) ≤ h) {b α δ κ : ℝ}
    (hb : 0 < b) (hκ : 0 < κ) (hκδ : κ < δ) (hκ1 : κ < 1)
    (hgap : α * q.choose (r + 1) + δ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-δ)) h → b * (n : ℝ) ^ (-α) ≤ density K →
      ∀ [MeasurableSpace (Equiv.Perm (Fin n))] [MeasurableSingletonClass (Equiv.Perm (Fin n))],
      ∀ s, ∀ P : IntersectingBlockPair (Fin n) q q s, s < r + 1 →
      ∀ D E : Finset (Block (Fin n) q), D ⊆ cliqueFamily K q → E ⊆ cliqueFamily K q →
        (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure.real
          {σ | P.val.1 ∈ mapGraph σ.toEmbedding D ∧ P.val.2 ∈ mapGraph σ.toEmbedding E} ≤
          (1 + 16 * (n : ℝ) ^ (-κ)) * density K ^ (2 * q.choose (r + 1)) := by
  have hsmall := ((tendsto_rpow_neg_atTop hκ).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_precise_clique_numerics q r hb (hκ.trans hκδ) hκδ hgap,
    eventually_uniform_shifted_choose_lower q hκ1, hsmall] with n hn hcn hsn
  intro K hT hd _ _ s P hsr D E hD hE
  have hc0 := Real.rpow_nonneg (Nat.cast_nonneg n) (-δ)
  have hε := Real.rpow_nonneg (Nat.cast_nonneg n) (-κ)
  have hsize : (q : ℝ) ≤ (2 * (n : ℝ) ^ (-δ) - (n : ℝ) ^ (-δ)) *
      (Fintype.card (Fin n) * density K ^ q.choose (r + 1)) := by
    rw [Fintype.card_fin, show 2 * (n : ℝ) ^ (-δ) - (n : ℝ) ^ (-δ) =
      (n : ℝ) ^ (-δ) by ring]
    exact hn.2.2.2 (density K) hd
  have hchoose : ∀ a ≤ q, ∀ b ≤ q,
      (1 - (n : ℝ) ^ (-κ)) * (Fintype.card (Fin n) : ℝ) ^ b / b.factorial ≤
        ((Fintype.card (Fin n) - a).choose b : ℝ) := by
    simpa only [Fintype.card_fin] using hcn.2
  exact hT.permuted_clique_pair_probability_le hqh (by linarith) (by positivity) hn.2.1 hsize
    (by simpa only [Fintype.card_fin] using hn.1) hε hsn.le hn.2.2.1 hchoose P hsr D E hD hE

end Arxiv2411_18291
