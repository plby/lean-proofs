import Arxiv.Arxiv2411_18291.ColouredFocusingFamily
import Arxiv.Arxiv2411_18291.TypicalGoodEdgeColours

/-!
# Focusing at the sparse-generator scale

A good subgraph has at least one quarter of the reference density once
the host error and deleted fraction are small. When `ρ ≥ 2*α*choose(q,r)`,
the focusing family is eventually `n^(-0.7*α)`-bounded, including all fixed
coefficients and factorials from the clique count.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_good_reference_density_lower (r : ℕ) {α δ τ : ℝ}
    (hδ : 0 < δ) (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in atTop, ∀ K G : Hypergraph (Fin n) r,
      |density K - (n : ℝ) ^ (-α)| ≤ (n : ℝ) ^ (-δ) * (n : ℝ) ^ (-α) →
      G ⊆ K → ((K \ G).card : ℝ) ≤ (n : ℝ) ^ (-τ) * K.card →
      (1 / 4 : ℝ) * (n : ℝ) ^ (-α) ≤ density G := by
  have hsmallδ := ((tendsto_rpow_neg_atTop hδ).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hsmallτ := ((tendsto_rpow_neg_atTop hτ).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hsmallδ, hsmallτ] with n hδn hτn
  intro K G hd hGK hloss
  have hk := (abs_le.mp hd).1
  have hg := density_good_lower hGK hloss
  have hmδ := mul_le_mul_of_nonneg_right hδn.le (Real.rpow_nonneg (Nat.cast_nonneg n) (-α))
  have hmτ := mul_le_mul_of_nonneg_right hτn.le (density_nonneg K)
  dsimp only [Function.comp_def] at hmδ hmτ
  linarith only [hk, hg, hmδ, hmτ]

variable {I : Type*} [Fintype I]

theorem eventually_exists_sparse_coloured_focusing (q r : ℕ) (hq : r + 1 ≤ q)
    {α ρ : ℝ} (hα : 0 < α) (hρ : 2 * α * q.choose (r + 1) ≤ ρ) (hρ1 : ρ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ K G : Hypergraph (Fin n) (r + 1),
      |density K - (n : ℝ) ^ (-α)| ≤
        (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-α) →
      G ⊆ K → ((K \ G).card : ℝ) ≤ (n : ℝ) ^ (-(α / 10)) * K.card →
      ∀ σ : I → Equiv.Perm (Fin n),
      (∀ e : Block (Fin n) (r + 1),
        ((3 / 8 : ℝ) * density G ^ (q.choose (r + 1) - 1) *
          (n : ℝ) ^ (q - (r + 1))) / (q - (r + 1)).factorial ≤
            (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q).card) →
      ∀ B : Hypergraph (Fin n) (r + 1), IsGraphBounded B ((n : ℝ) ^ (-ρ)) →
      ∃ F : Finset (Block (Fin n) q), IsCliqueFamilyBounded r F ((n : ℝ) ^ (-(7 * α / 10))) ∧
        ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
          IntegrallyDecomposable q J →
          ∃ J' : Block (Fin n) (r + 1) → ℤ, GeneratedBy F (J - J') ∧
            (∀ e, e ∉ permutedUnion σ G → J' e = 0) ∧ IntegrallyDecomposable q J' := by
  let a : ℝ := α * ((q.choose (r + 1) - 1 : ℕ) : ℝ) + α / 2
  have hk : 1 ≤ q.choose (r + 1) := Nat.choose_pos hq
  have hkR : (1 : ℝ) ≤ q.choose (r + 1) := by exact_mod_cast hk
  have hpred : ((q.choose (r + 1) - 1 : ℕ) : ℝ) + 1 = q.choose (r + 1) := by
    exact_mod_cast Nat.sub_add_cancel hk
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hgap : α * ((q.choose (r + 1) - 1 : ℕ) : ℝ) < a := by
    dsimp only [a]
    linarith only [hα]
  have h2a : 2 * a < ρ := by
    dsimp only [a]
    nlinarith only [hα, hρ, hpred]
  have hb1 : ρ - a < 1 := by linarith only [hρ1, ha]
  have hρsmall : 7 * α / 10 < ρ := by nlinarith only [hα, hρ, hkR]
  have hdiff : 7 * α / 10 < ρ - a := by
    dsimp only [a]
    nlinarith only [hα, hρ, hkR, hpred]
  filter_upwards [eventually_exists_coloured_focusing_family (I := I) q r hq
    (b := 1 / 4) (by norm_num) ha hgap h2a hb1,
    eventually_good_reference_density_lower (r + 1) (α := α) (δ := 1 / 10)
      (τ := α / 10) (by norm_num) (by positivity),
    eventually_const_mul_rpow_le 2 hρsmall,
    eventually_const_mul_rpow_le (8 * (r + 1).factorial * q.choose (r + 1)) hdiff]
      with n hfocus hdensity hsmall₁ hsmall₂
  intro K G hd hGK hloss σ hcount B hB
  obtain ⟨F, hF, hJ⟩ := hfocus G (hdensity K G hd hGK hloss) σ hcount B hB
  refine ⟨F, ?_, hJ⟩
  have hbound : (n : ℝ) ^ (-ρ) + q.choose (r + 1) *
      (4 * (r + 1).factorial * (n : ℝ) ^ (-(ρ - a))) ≤ (n : ℝ) ^ (-(7 * α / 10)) := by
    nlinarith only [hsmall₁, hsmall₂]
  intro T
  exact (hF T).trans_le (mul_le_mul_of_nonneg_right hbound (Nat.cast_nonneg _))

end Arxiv2411_18291
