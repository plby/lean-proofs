import Arxiv.Arxiv2411_18291.DecoderOutputLaw
import Arxiv.Arxiv2411_18291.HalfAlphaDecoderFamily

/-! # Normalized parameters for every sampled decoder output -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem LocalDecoderOutput.normalized_augmentation
    {W : Type*} [Fintype W] {q r n : ℕ}
    (hW : Fintype.card W = q + (r + 1)) (hqr : r + 1 < q)
    (B : Hypergraph (Fin n) (r + 1)) (D₁ : Finset (Block (Fin n) q))
    (hB : IsGraphBounded B (2 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))))
    (hDB : cliqueSupport (r + 1) D₁ ⊆ B)
    (hmult : ∀ e : Block (Fin n) (r + 1), (D₁.filter fun Q => e.val ⊆ Q.val).card ≤ 16) :
    ∀ O : LocalDecoderOutput B hW (2 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))),
    let C := absorberCoefficientCap q (r + 1)
    let A : ℝ := absorberNormalizationFactor q (r + 1)
    let D := D₁ ∪ decoderFamilyOfPlacements hW O.embedding
    let B' := B ∪ cliqueSupport (r + 1) (decoderFamilyOfPlacements hW O.embedding)
    D₁ ⊆ D ∧ B ⊆ B' ∧
      IsCliqueFamilyBounded r D (2 * A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))) ∧
      IsGraphBounded B' (2 * A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))) ∧
      cliqueSupport (r + 1) D ⊆ B' ∧
      (∀ e : Block (Fin n) (r + 1), (D.filter fun Q => e.val ⊆ Q.val).card ≤
        absorberGeneratorMultiplicity q (r + 1)) ∧
      ∀ L : Hypergraph (Fin n) (r + 1), L ⊆ B → GeneratedBy D₁ (indicator L) →
        ∃ Φ : Block (Fin n) q → ℤ, boundary (r + 1) Φ = indicator L ∧
          (∀ Q, Q ∉ D → Φ Q = 0) ∧ ∀ Q, |Φ Q| ≤ C := by
  classical
  intro O
  dsimp only
  let θ := (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))
  let M := absorberGeneratorMultiplicity q (r + 1)
  let A : ℝ := absorberNormalizationFactor q (r + 1)
  let Kdec : ℝ := 1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1)
  let D₂ := decoderFamilyOfPlacements hW O.embedding
  have hD₂ := O.decoder
  have hB₂ := O.bounded
  have hrep := fun L hLB hgen =>
    bounded_multiplicity_representation_of_local_decoders hqr D₁ B L hDB hLB hmult
      (fun e => embeddingClique hW (O.embedding e)) O.cover hgen
  let B' := B ∪ cliqueSupport (r + 1) D₂
  let D := D₁ ∪ D₂
  have hMpos : 0 < M := by dsimp only [M, absorberGeneratorMultiplicity]; omega
  have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
  have hKdec : 1 ≤ Kdec := by
    apply le_add_of_nonneg_right
    positivity
  have hAeq : A = (M : ℝ) * (1 + Kdec) := by
    dsimp only [A, M, Kdec, absorberNormalizationFactor]
    push_cast
    ring
  have hscale : 1 + Kdec ≤ A := by
    rw [hAeq]
    exact le_mul_of_one_le_left (by linarith only [hKdec]) hMreal
  have hb : IsGraphBounded B' ((1 + Kdec) * (2 * θ)) := by
    rw [add_mul, one_mul]
    exact hB.union hB₂
  have hdsub : cliqueSupport (r + 1) D ⊆ B' := by
    dsimp only [D, B', cliqueSupport]
    rw [union_biUnion]
    exact union_subset_union hDB Subset.rfl
  have hm (e : Block (Fin n) (r + 1)) : (D.filter fun Q => e.val ⊆ Q.val).card ≤ M := by
    dsimp only [D, M, absorberGeneratorMultiplicity]
    rw [filter_union]
    exact (card_union_le _ _).trans (Nat.add_le_add (hmult e) (hD₂.multiplicity e))
  have hd : IsCliqueFamilyBounded r D (A * (2 * θ)) := by
    rw [hAeq]
    simpa only [mul_assoc] using hb.cliqueFamilyBounded D hMpos hm hdsub
  have hb' : IsGraphBounded B' (A * (2 * θ)) :=
    hb.mono (mul_le_mul_of_nonneg_right hscale (by dsimp only [θ]; positivity))
  have heq : A * (2 * θ) = 2 * A * θ := by ring
  rw [heq] at hd hb'
  refine ⟨subset_union_left, subset_union_left, hd, hb', hdsub, hm, ?_⟩
  intro L hLB hgen
  simpa only [decoderFamilyOfPlacements, absorberCoefficientCap, Nat.reduceAdd, mul_assoc]
    using hrep L hLB hgen

theorem localDecoderOutputLaw_half_alpha_failure_lt
    {W : Type*} [Fintype W] [DecidableEq W] {q r n : ℕ}
    (F₀ : Block W (r + 1)) (hW : Fintype.card W = q + (r + 1))
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (B : Hypergraph (Fin n) (r + 1)) (e₀ : Block (Fin n) (r + 1))
    (hB : IsGraphBounded B (2 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2)))) :
    (localDecoderOutputLaw F₀ B e₀ hW
      (2 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))) none).toReal <
        Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) := by
  have htwo : (2 : ℝ) ≤ (4 * q : ℝ) ^ (24 * q) := by
    exact_mod_cast (show 2 ≤ 4 * q by omega).trans
      (Nat.le_self_pow (by omega : 24 * q ≠ 0) (4 * q))
  have hα := paperAlpha_pos hqr
  have hαupper := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  exact localDecoderOutputLaw_failure_lt F₀ hW hqr hn (by norm_num) htwo
    (by linarith only [hα]) (by linarith only [hαupper]) B e₀ hB

end Arxiv2411_18291
