import Arxiv.Arxiv2411_18291.GeneratorSplittingExistence
import Arxiv.Arxiv2411_18291.ColourProbabilityNumerics

/-!
# The initial sparse splitting step for flattening

Every sparse generating family can be replaced by a sparse family with
at most one original-support edge per clique and multiplicity at most two
off that support. The old integer span and old multiplicity bounds persist.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {W : Type*} [Fintype W] [DecidableEq W] {q r : ℕ}

theorem eventually_exists_sparse_split_generators (S : ExchangeSystem W q (r + 1))
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A) (hqr : r + 1 ≤ q)
    {ρ η : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (hηρ : η < ρ) :
    ∀ᶠ n : ℕ in atTop, ∀ D : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r D ((n : ℝ) ^ (-ρ)) →
      ∃ F : Finset (Block (Fin n) q), IsCliqueFamilyBounded r F ((n : ℝ) ^ (-η)) ∧
        (∀ J : Block (Fin n) (r + 1) → ℤ, GeneratedBy D J → GeneratedBy F J) ∧
        (∀ e : Block (Fin n) (r + 1), e ∈ cliqueSupport (r + 1) D →
          (F.filter fun Q => e.val ⊆ Q.val).card ≤ (D.filter fun Q => e.val ⊆ Q.val).card) ∧
        (∀ e : Block (Fin n) (r + 1), e ∉ cliqueSupport (r + 1) D →
          (F.filter fun Q => e.val ⊆ Q.val).card ≤ 2) ∧
        ∀ Q ∈ F, (cliqueEdges (r + 1) Q ∩ cliqueSupport (r + 1) D).card ≤ 1 := by
  filter_upwards [eventually_exists_generator_splitting S hqr hρ hρ1,
    eventually_const_mul_rpow_le (3 + 8 * (r + 1).factorial * S.graph.card) hηρ]
      with n hsplit hsmall
  intro D hD
  obtain ⟨F⟩ := hsplit D hD
  refine ⟨F.cliques, ?_, fun J hJ => F.generated hJ, F.clique_count_original,
    F.clique_count_outside, fun Q hQ => F.clique_inter_card_le_one hA hQ⟩
  have hscale : (n : ℝ) ^ (-ρ) + 2 * ((n : ℝ) ^ (-ρ) + S.graph.card *
      (4 * (r + 1).factorial * (n : ℝ) ^ (-ρ))) ≤ (n : ℝ) ^ (-η) := by
    convert hsmall using 1
    ring
  intro T
  exact (F.cliques_bounded hD T).trans_le
    (mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg _))

end Arxiv2411_18291
