import Arxiv.Arxiv2411_18291.NormalizedSplitting
import Arxiv.Arxiv2411_18291.ExplicitBoundedRepresentation
import Arxiv.Arxiv2411_18291.AbsorberFromGenerators
import Arxiv.Arxiv2411_18291.SmallCarrierExchange

/-! # The finite decoder and splitting stages for multiplicity-16 generators -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_decoder_splitting_paper_threshold
    {W : Type*} [Fintype W] [DecidableEq W] {q r n : ℕ}
    (S : ExchangeSystem W q (r + 1)) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (8 * q))
    (hS : S.graph.card ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (B : Hypergraph (Fin n) (r + 1)) (D₁ : Finset (Block (Fin n) q))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))))
    (hDB : cliqueSupport (r + 1) D₁ ⊆ B)
    (hmult : ∀ e : Block (Fin n) (r + 1), (D₁.filter fun Q => e.val ⊆ Q.val).card ≤ 16) :
    let C := absorberCoefficientCap q (r + 1)
    let A : ℝ := absorberNormalizationFactor q (r + 1)
    ∃ D : Finset (Block (Fin n) q), ∃ B' : Hypergraph (Fin n) (r + 1),
      D₁ ⊆ D ∧ B ⊆ B' ∧
      Nonempty (SplittingFamily S D B' C
        (splittingFactor S C A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)))) ∧
      ∀ L : Hypergraph (Fin n) (r + 1), L ⊆ B → GeneratedBy D₁ (indicator L) →
        ∃ Φ : Block (Fin n) q → ℤ, boundary (r + 1) Φ = indicator L ∧
          (∀ Q, Q ∉ D → Φ Q = 0) ∧ ∀ Q, |Φ Q| ≤ C := by
  dsimp only
  let θ := (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))
  let M := absorberGeneratorMultiplicity q (r + 1)
  let A : ℝ := absorberNormalizationFactor q (r + 1)
  let Kdec : ℝ := 1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1)
  obtain ⟨D₂, hD₂, hB₂, hrep⟩ :=
    exists_bounded_multiplicity_representation_family_paper_threshold hqr hn 16 B D₁ hB hDB hmult
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
  have hb : IsGraphBounded B' ((1 + Kdec) * θ) := by
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
  have hd : IsCliqueFamilyBounded r D (A * θ) := by
    rw [hAeq]
    simpa only [mul_assoc] using hb.cliqueFamilyBounded D hMpos hm hdsub
  have hb' : IsGraphBounded B' (A * θ) :=
    hb.mono (mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have hF := exists_normalized_splitting_family_paper_threshold S hqr hn hw hS D B'
    hd hb' hdsub hm
  refine ⟨D, B', subset_union_left, subset_union_left, hF, ?_⟩
  intro L hLB hgen
  simpa only [absorberCoefficientCap, Nat.reduceAdd, mul_assoc] using hrep L hLB hgen

/-- The decoder and splitting construction at the printed threshold, with
the exchange configuration constructed rather than supplied as an input. -/
theorem exists_exchange_decoder_splitting_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (B : Hypergraph (Fin n) (r + 1)) (D₁ : Finset (Block (Fin n) q))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))))
    (hDB : cliqueSupport (r + 1) D₁ ⊆ B)
    (hmult : ∀ e : Block (Fin n) (r + 1), (D₁.filter fun Q => e.val ⊆ Q.val).card ≤ 16) :
    let C := absorberCoefficientCap q (r + 1)
    let A : ℝ := absorberNormalizationFactor q (r + 1)
    ∃ T : FiniteExchangeSystem q (r + 1), ∃ A₀ : Finset (Block T.Vertex q),
      T.system.graph.card ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2 ∧
      IsExchangeFamily T.system A₀ ∧
      IsCrossSimple (r + 1) T.system.positive T.system.negative ∧
      IsPositiveFrameLocal T.system A₀ ∧
      Fintype.card T.Vertex ≤ (4 * q) ^ (2 * q) ∧
      ∃ D : Finset (Block (Fin n) q), ∃ B' : Hypergraph (Fin n) (r + 1),
        D₁ ⊆ D ∧ B ⊆ B' ∧
        Nonempty (SplittingFamily T.system D B' C
          (splittingFactor T.system C A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)))) ∧
        ∀ L : Hypergraph (Fin n) (r + 1), L ⊆ B → GeneratedBy D₁ (indicator L) →
          ∃ Φ : Block (Fin n) q → ℤ, boundary (r + 1) Φ = indicator L ∧
            (∀ Q, Q ∉ D → Φ Q = 0) ∧ ∀ Q, |Φ Q| ≤ C := by
  dsimp only
  obtain ⟨T, A₀, hc, hA₀, hs, hl, hv⟩ :=
    exists_small_carrier_clique_exchange q (r + 1) (Nat.succ_pos r) hqr
  have hw : Fintype.card T.Vertex ≤ (4 * q) ^ (8 * q) :=
    hv.trans (Nat.pow_le_pow_right (by omega) (by omega))
  exact ⟨T, A₀, hc, hA₀, hs, hl, hv,
    exists_decoder_splitting_paper_threshold T.system hqr hn hw hc B D₁ hB hDB hmult⟩

end Arxiv2411_18291
