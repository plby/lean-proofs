import Arxiv.Arxiv2411_18291.AsymptoticPermutationPairs
import Arxiv.Arxiv2411_18291.GoodSubgraphDensity
import Arxiv.Arxiv2411_18291.ColourProbabilityNumerics

/-!
# Colour estimates from a typical host and its good subgraph

Removing a polynomially small fraction of the host edges preserves their
marginal probability. Typicality controls the joint probability for two
edges with any intersection smaller than their rank.
-/

open Finset Filter MeasureTheory
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem cliqueFamily_self {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (K : Hypergraph V r) : cliqueFamily K r = K := by
  ext Q
  simp only [cliqueFamily, mem_filter, mem_univ, true_and]
  constructor
  · intro hQ
    exact hQ ((mem_cliqueEdges Q Q).mpr Subset.rfl)
  · intro hQ e he
    have heQ : e = Q := Subtype.ext (eq_of_subset_of_card_le
      ((mem_cliqueEdges e Q).mp he) (by rw [e.property, Q.property]))
    exact heQ ▸ hQ

theorem density_good_lower {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    {G K : Hypergraph V r} {ε : ℝ} (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤ ε * K.card) : (1 - ε) * density K ≤ density G := by
  have h := (abs_le.mp (density_subgraph_error hGK hloss)).1
  linarith only [h]

theorem eventually_good_edge_colour_estimates (r h : ℕ) (hh : 1 ≤ h)
    {b α δ τ γ χ : ℝ} (hb : 0 < b) (hγ : 0 < γ) (hγχ : γ < χ) (hχδ : χ < δ)
    (hχ1 : χ < 1) (hγτ : γ < τ) (hgap : α + δ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-δ)) h → b * (n : ℝ) ^ (-α) ≤ density K →
      ∀ G : Hypergraph (Fin n) (r + 1), G ⊆ K →
      ((K \ G).card : ℝ) ≤ (n : ℝ) ^ (-τ) * K.card →
      b / 2 * (n : ℝ) ^ (-α) ≤ density G ∧
      (1 - (n : ℝ) ^ (-γ)) * density K ≤ density G ∧
      ∀ [MeasurableSpace (Equiv.Perm (Fin n))] [MeasurableSingletonClass (Equiv.Perm (Fin n))],
      ∀ j < r + 1, ∀ P : IntersectingBlockPair (Fin n) (r + 1) (r + 1) j,
        (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure.real
          {σ | P.val.1 ∈ mapGraph σ.toEmbedding G ∧ P.val.2 ∈ mapGraph σ.toEmbedding G} ≤
          (1 + (n : ℝ) ^ (-γ)) * density K ^ 2 := by
  have hsmall := ((tendsto_rpow_neg_atTop (hγ.trans hγτ)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hqh : (r + 1).choose (r + 1) ≤ h := by simpa only [Nat.choose_self] using hh
  have hgp : α * (r + 1).choose (r + 1) + δ < 1 := by
    simpa only [Nat.choose_self, Nat.cast_one, mul_one] using hgap
  filter_upwards [eventually_permuted_clique_pair_probability_le (r + 1) r h hqh hb
    (hγ.trans hγχ) hχδ hχ1 hgp, eventually_const_mul_rpow_le 16 hγχ,
    eventually_const_mul_rpow_le 1 hγτ, hsmall] with n hpair herr hloss hsn
  intro K hT hd G hGK hKG
  have hgood := density_good_lower hGK hKG
  have hd0 := density_nonneg K
  have hε : (n : ℝ) ^ (-τ) ≤ (n : ℝ) ^ (-γ) := by
    simpa only [one_mul] using hloss
  have hdhalf : density K / 2 ≤ density G := by
    have hmul := mul_le_mul_of_nonneg_right hsn.le hd0
    dsimp only [Function.comp_def] at hmul
    linarith only [hgood, hmul]
  refine ⟨?_, ?_, ?_⟩
  · have hbnd := div_le_div_of_nonneg_right hd (by norm_num : (0 : ℝ) ≤ 2)
    have hbnd' : b / 2 * (n : ℝ) ^ (-α) ≤ density K / 2 := by
      simpa only [div_mul_eq_mul_div] using hbnd
    exact hbnd'.trans hdhalf
  · exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hε 1) hd0).trans hgood
  · intro _ _ j hj P
    have hG : G ⊆ cliqueFamily K (r + 1) := by rw [cliqueFamily_self]; exact hGK
    have hp := hpair K hT hd j P hj G G hG hG
    simp only [Nat.choose_self, mul_one] at hp
    exact hp.trans (mul_le_mul_of_nonneg_right (add_le_add le_rfl herr) (sq_nonneg _))

end Arxiv2411_18291
