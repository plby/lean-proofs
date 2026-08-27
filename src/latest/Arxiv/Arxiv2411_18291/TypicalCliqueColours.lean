import Arxiv.Arxiv2411_18291.CliqueSubfamilyDensity
import Arxiv.Arxiv2411_18291.AsymptoticPermutationPairs
import Arxiv.Arxiv2411_18291.ColourProbabilityNumerics

/-!
# Colour estimates for an almost complete clique family

The unsaturated cliques retain the marginal density of all host cliques.
Their joint probability is bounded by the typical-host pair estimate.
Both errors tend to zero at a common polynomial rate.
-/

open Finset Filter MeasureTheory
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_clique_colour_estimates (q r h : ℕ)
    (hqh : q.choose (r + 1) ≤ h) {b α δ τ γ χ : ℝ}
    (hb : 0 < b) (hγ : 0 < γ) (hγχ : γ < χ) (hχδ : χ < δ)
    (hχ1 : χ < 1) (hχτ : χ < τ) (hgap : α * q.choose (r + 1) + δ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-δ)) h → b * (n : ℝ) ^ (-α) ≤ density K →
      ∀ D : Finset (Block (Fin n) q), D ⊆ cliqueFamily K q →
      (((cliqueFamily K q) \ D).card : ℝ) ≤
        (n : ℝ) ^ (-τ) * (cliqueFamily K q).card →
      b ^ q.choose (r + 1) / 2 * (n : ℝ) ^ (-(α * q.choose (r + 1))) ≤ density D ∧
      (1 - (n : ℝ) ^ (-γ)) * density K ^ q.choose (r + 1) ≤ density D ∧
      ∀ [MeasurableSpace (Equiv.Perm (Fin n))] [MeasurableSingletonClass (Equiv.Perm (Fin n))],
      ∀ j < r + 1, ∀ P : IntersectingBlockPair (Fin n) q q j,
        (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure.real
          {σ | P.val.1 ∈ mapGraph σ.toEmbedding D ∧ P.val.2 ∈ mapGraph σ.toEmbedding D} ≤
          (1 + (n : ℝ) ^ (-γ)) * (density K ^ q.choose (r + 1)) ^ 2 := by
  have hsmall := ((tendsto_rpow_neg_atTop hγ).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_cliqueFamily_relative_error q r h hqh hb
    ((hγ.trans hγχ).trans hχδ) hχδ hgap,
    eventually_permuted_clique_pair_probability_le q r h hqh hb
      (hγ.trans hγχ) hχδ hχ1 hgap,
    eventually_const_mul_rpow_le 16 hγχ, eventually_const_mul_rpow_le 2 hγχ,
    eventually_const_mul_rpow_le 1 hχτ, hsmall, eventually_ge_atTop q]
      with n hcount hpair h16 h2 hloss hsn hqn
  intro K hT hd D hD hKD
  have hε : (n : ℝ) ^ (-τ) ≤ (n : ℝ) ^ (-χ) := by
    simpa only [one_mul] using hloss
  have hsn' : (n : ℝ) ^ (-γ) < 1 / 2 := hsn
  have hχsmall : (n : ℝ) ^ (-χ) ≤ 1 := by linarith only [h2, hsn']
  have hgood := clique_subfamily_density_lower K D hD
    (by simpa only [Fintype.card_fin] using hqn) hχsmall
    (by simpa only [Fintype.card_fin] using hcount K hT hd)
    (hKD.trans (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _)))
  have hd0 := pow_nonneg (density_nonneg K) (q.choose (r + 1))
  have hmarg : (1 - (n : ℝ) ^ (-γ)) * density K ^ q.choose (r + 1) ≤ density D :=
    (mul_le_mul_of_nonneg_right (sub_le_sub_left h2 1) hd0).trans hgood
  have hhalf : density K ^ q.choose (r + 1) / 2 ≤ density D := by
    have hm := mul_le_mul_of_nonneg_right hsn'.le hd0
    linarith only [hmarg, hm]
  refine ⟨?_, hmarg, ?_⟩
  · have hp := pow_le_pow_left₀ (by positivity : 0 ≤ b * (n : ℝ) ^ (-α)) hd
      (q.choose (r + 1))
    rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n), neg_mul] at hp
    have hh := div_le_div_of_nonneg_right hp (by norm_num : (0 : ℝ) ≤ 2)
    apply le_trans _ hhalf
    simpa only [div_mul_eq_mul_div] using hh
  · intro _ _ j hj P
    have hp := hpair K hT hd j P hj D D hD hD
    rw [mul_comm 2, pow_mul] at hp
    exact hp.trans (mul_le_mul_of_nonneg_right (add_le_add le_rfl h16) (sq_nonneg _))

end Arxiv2411_18291
