import Arxiv.Arxiv2411_18291.FlexibleDecoderPlacement
import Arxiv.Arxiv2411_18291.SparseLocalDecoders
import Arxiv.Arxiv2411_18291.BoundedMultiplicityRepresentation

/-! # Local decoders and bounded representations at flexible exponents -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_sparse_local_decoders_at_exponent {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    {A ρ : ℝ} (hA : 1 ≤ A) (hAb : A ≤ (4 * q : ℝ) ^ (24 * q))
    (hρ : paperAlpha q (r + 1) / 3 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (B : Hypergraph (Fin n) (r + 1)) (hB : IsGraphBounded B (A * (n : ℝ) ^ (-ρ))) :
    ∃ Z : B → Block (Fin n) (q + (r + 1)), ∃ D : Finset (Block (Fin n) q),
      IsCliqueCover (complete (Fin n) (r + 1) \ B) (fun e : B => e.val) Z ∧
      D = cliqueRefinement q (univ.image Z) ∧ IsLocalDecoderFamily B D ∧
      IsGraphBounded (cliqueSupport (r + 1) D)
        ((1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1)) *
          (A * (n : ℝ) ^ (-ρ))) := by
  obtain ⟨Z, hZ, hb⟩ := exists_clique_placement_at_exponent hqr
    (Nat.le_add_left (r + 1) q) (by omega) hn hA hAb hρ hρhalf B hB
  exact ⟨Z, cliqueRefinement q (univ.image Z), hZ, rfl, hZ.localDecoderFamily hqr.le,
    hb.subgraph hZ.decomposition.refinement_support_subset⟩

theorem exists_bounded_local_decoder_family_at_exponent {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    {A ρ : ℝ} (hA : 1 ≤ A) (hAb : A ≤ (4 * q : ℝ) ^ (24 * q))
    (hρ : paperAlpha q (r + 1) / 3 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (B : Hypergraph (Fin n) (r + 1)) (hB : IsGraphBounded B (A * (n : ℝ) ^ (-ρ))) :
    let C : ℝ := 1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1)
    ∃ D : Finset (Block (Fin n) q), IsLocalDecoderFamily B D ∧
      IsGraphBounded (cliqueSupport (r + 1) D) (C * (A * (n : ℝ) ^ (-ρ))) ∧
      IsCliqueFamilyBounded r D (q.choose (r + 1) * C * (A * (n : ℝ) ^ (-ρ))) := by
  dsimp only
  obtain ⟨_, D, _, _, hD, hb⟩ :=
    exists_sparse_local_decoders_at_exponent hqr hn hA hAb hρ hρhalf B hB
  refine ⟨D, hD, hb, ?_⟩
  have hmulti := hb.cliqueFamilyBounded D (Nat.choose_pos hqr.le) hD.multiplicity (Subset.refl _)
  simpa only [mul_assoc] using hmulti

theorem exists_bounded_multiplicity_representation_family_at_exponent
    {q r n : ℕ} (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    {A ρ : ℝ} (hA : 1 ≤ A) (hAb : A ≤ (4 * q : ℝ) ^ (24 * q))
    (hρ : paperAlpha q (r + 1) / 3 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (M : ℕ) (B : Hypergraph (Fin n) (r + 1)) (D₁ : Finset (Block (Fin n) q))
    (hB : IsGraphBounded B (A * (n : ℝ) ^ (-ρ)))
    (hDB : cliqueSupport (r + 1) D₁ ⊆ B)
    (hmult : ∀ e : Block (Fin n) (r + 1), (D₁.filter fun Q => e.val ⊆ Q.val).card ≤ M) :
    let C : ℝ := 1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1)
    ∃ D₂ : Finset (Block (Fin n) q), IsLocalDecoderFamily B D₂ ∧
      IsGraphBounded (cliqueSupport (r + 1) D₂) (C * (A * (n : ℝ) ^ (-ρ))) ∧
      ∀ L : Hypergraph (Fin n) (r + 1), L ⊆ B → GeneratedBy D₁ (indicator L) →
        ∃ Φ : Block (Fin n) q → ℤ, boundary (r + 1) Φ = indicator L ∧
          (∀ Q, Q ∉ D₁ ∪ D₂ → Φ Q = 0) ∧
          ∀ Q, |Φ Q| ≤ ((M + 1) * (2 ^ q * (r + 1).factorial) : ℕ) := by
  dsimp only
  obtain ⟨Z, D₂, hZ, rfl, hD₂, hb⟩ :=
    exists_sparse_local_decoders_at_exponent hqr hn hA hAb hρ hρhalf B hB
  exact ⟨_, hD₂, hb, fun L hLB hgen =>
    bounded_multiplicity_representation_of_local_decoders hqr D₁ B L hDB hLB hmult Z hZ hgen⟩

end Arxiv2411_18291
