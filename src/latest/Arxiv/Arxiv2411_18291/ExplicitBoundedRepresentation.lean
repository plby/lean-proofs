import Arxiv.Arxiv2411_18291.ExplicitLocalDecoders
import Arxiv.Arxiv2411_18291.BoundedMultiplicityRepresentation

/-! # Uniform bounded representations from finite sparse decoder placements -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_bounded_multiplicity_representation_family_paper_threshold
    {q r n : ℕ} (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (M : ℕ) (B : Hypergraph (Fin n) (r + 1)) (D₁ : Finset (Block (Fin n) q))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))))
    (hDB : cliqueSupport (r + 1) D₁ ⊆ B)
    (hmult : ∀ e : Block (Fin n) (r + 1), (D₁.filter fun Q => e.val ⊆ Q.val).card ≤ M) :
    let C : ℝ := 1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1)
    ∃ D₂ : Finset (Block (Fin n) q), IsLocalDecoderFamily B D₂ ∧
      IsGraphBounded (cliqueSupport (r + 1) D₂)
        (C * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))) ∧
      ∀ L : Hypergraph (Fin n) (r + 1), L ⊆ B → GeneratedBy D₁ (indicator L) →
        ∃ Φ : Block (Fin n) q → ℤ, boundary (r + 1) Φ = indicator L ∧
          (∀ Q, Q ∉ D₁ ∪ D₂ → Φ Q = 0) ∧
          ∀ Q, |Φ Q| ≤ ((M + 1) * (2 ^ q * (r + 1).factorial) : ℕ) := by
  dsimp only
  obtain ⟨Z, D₂, hZ, rfl, hD₂, hb⟩ := exists_sparse_local_decoders_paper_threshold hqr hn B hB
  exact ⟨_, hD₂, hb, fun L hLB hgen =>
    bounded_multiplicity_representation_of_local_decoders hqr D₁ B L hDB hLB hmult Z hZ hgen⟩

end Arxiv2411_18291
