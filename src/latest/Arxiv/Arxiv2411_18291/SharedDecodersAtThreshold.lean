import Arxiv.Arxiv2411_18291.SharedCliqueDecoders
import Arxiv.Arxiv2411_18291.SharedDecoderNumerics

/-! # Shared local decoders with the source coefficient at n0 -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_shared_clique_decoders_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) {C : ℝ} (hC : 1 ≤ C)
    (D : Finset (Block (Fin n) q))
    (hD : IsCliqueFamilyBounded r D
      (C * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)))) :
    ∃ D' : Finset (Block (Fin n) q), D ⊆ D' ∧
      IsCliqueFamilyBounded r D'
        (2 * (4 * q : ℝ) ^ (r + 1) * C *
          (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
      ∀ e ∈ cliqueSupport (r + 1) D, ∃ Z : Block (Fin n) (q + (r + 1)),
        e.val ⊆ Z.val ∧ ∀ Q : Block (Fin n) q, Q.val ⊆ Z.val → Q ∈ D' := by
  obtain ⟨hsize, hnpos, hsample⟩ := shared_decoder_sampling_size hqr hn
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  simpa only [mul_assoc] using exists_shared_clique_decoders_of_numerics D (by omega)
    (mul_nonneg hC0 (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hD
    (by simpa only [Fintype.card_fin] using hsize)
    (by simpa only [Fintype.card_fin] using hnpos)
    (by simpa only [Fintype.card_fin] using hsample)
    (by simpa only [Block, Fintype.card_finset_len, Fintype.card_fin] using
      shared_decoder_failure_lt_one hqr hn hC)

end Arxiv2411_18291
