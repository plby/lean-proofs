/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos622.AlmostBipartite
import ErdosProblems.Erdos622.AlmostBipartiteRegimeCounts
import ErdosProblems.Erdos622.BalancedCutWindowDKM
import ErdosProblems.Erdos622.BoundedInternal
import ErdosProblems.Erdos622.ForestTransfer
import ErdosProblems.Erdos622.GoodCutHamiltonicity
import ErdosProblems.Erdos622.GoodCutUnionBound
import ErdosProblems.Erdos622.IntermediateImbalance
import ErdosProblems.Erdos622.OneSmallIntermediate
import ErdosProblems.Erdos622.SuitableCertificate
import ErdosProblems.Erdos622.TwoLargeCase
import ErdosProblems.Erdos622.TwoLargeForest

/-!
# The unconditional almost-bipartite case of Erdos Problem 622

This downstream module combines the three cover regimes with sampled
good-cut Hamiltonicity.  The final export is
`Erdos622.AlmostBipartiteCase.uniformCaseDensityBound_almostBipartite`.
-/

open Filter
open Finset
open scoped SimpleGraph

namespace Erdos622.AlmostBipartiteCase

open AlmostBipartiteRegimeCounts

attribute [local instance] Classical.propDecidable

def protectedBudget (n : ℕ) : ℕ := n / 2048

def highCrossThreshold (n : ℕ) : ℕ := 19 * n / 64

theorem samplingRho_pos : 0 < samplingRho := by
  norm_num [samplingRho]

theorem samplingRho_le_quarter : samplingRho ≤ (1 / 4 : ℝ) := by
  norm_num [samplingRho]

/-- Regularity is independent of the chosen finite structures on the
neighbour subtypes.  This transports an explicitly bound `LocallyFinite`
instance to the canonical one used by finite-ambient counting lemmas. -/
theorem isRegularOfDegree_of_locallyFinite_instances
    {V : Type*} {G : SimpleGraph V} {d : ℕ}
    (inst₁ inst₂ : G.LocallyFinite)
    (h : @SimpleGraph.IsRegularOfDegree V G inst₁ d) :
    @SimpleGraph.IsRegularOfDegree V G inst₂ d := by
  intro v
  rw [← @SimpleGraph.card_neighborSet_eq_degree V G v (inst₂ v)]
  have hv := h v
  rw [← @SimpleGraph.card_neighborSet_eq_degree V G v (inst₁ v)] at hv
  exact (@Fintype.card_congr _ _ (inst₂ v) (inst₁ v)
    (Equiv.refl _)).trans hv

/- Target helper interfaces for the final application of
`uniformCaseDensityBound_almostBipartite_of_sample_bounds`:

* `eventually_goodSample_count delta hdelta` returns, uniformly in every
  regular graph in `AlmostBipartiteRegime`, an original tailored cut `A,B`
  with at least `(1/2-delta)*2^(2*n)` samples satisfying
  `IsKGoodSample G A B S 0`.
* `eventually_suitable_goodSample_isSpannedByCycle` says, uniformly for large
  `n`, that regularity, `IsAlmostBipartiteCut G A B`, suitability at
  `samplingRho`, and `IsKGoodSample G A B S 0` imply
  `IsSpannedByCycle G S`.
-/

/-- Final integration seam: once the cover-regime counting theorem is
available, the already checked suitable-sample certificate and uniform
concentration give the canonical case-density statement. -/
theorem uniformCaseDensityBound_almostBipartite_of_goodSample_count
    (hgood : ∀ delta : ℝ, 0 < delta →
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (G : SimpleGraph (Fin (2 * n))) [G.LocallyFinite],
          G.IsRegularOfDegree (n + 1) → AlmostBipartiteRegime n G →
            ∃ A B : Finset (Fin (2 * n)),
              IsAlmostBipartiteCut G A B ∧
              ((1 / 2 : ℝ) - delta) * (2 : ℝ) ^ (2 * n) ≤
                (almostBipartiteCount
                  (Finset.univ : Finset (Fin (2 * n)))
                  (fun S ↦ IsKGoodSample G A B S 0) : ℝ)) :
    UniformCaseDensityBound AlmostBipartiteRegime :=
  uniformCaseDensityBound_almostBipartite_of_sample_bounds
    samplingRho_pos hgood eventually_suitable_goodSample_isSpannedByCycle

/-- Finite cover-regime assembly.  This isolates the two remaining counting
endpoints (the joined right-product arm and the two-large-cover arm) from the
already checked large-imbalance and left-product estimates. -/
theorem eventually_goodSample_count_of_cover_endpoints
    {delta : ℝ} (hdelta : 0 < delta) {K : ℕ}
    (hleft : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin (2 * n)))
        (A B T A₀ C : Finset (Fin (2 * n))),
        IsCut A B → n ≤ A.card → A.card - n ≤ Nat.sqrt n →
        A₀ = A \ T → IsMinimumVertexCoverOn G A₀ C →
        n + 1 ≤ sqrtCoverThreshold K n * (C.card + 1) →
        ((1 / 2 : ℝ) - delta) * (2 : ℝ) ^ (2 * n) ≤
          (almostBipartiteCount
            (Finset.univ : Finset (Fin (2 * n)))
            (fun S ↦ IsKGoodSample G A B S 0) : ℝ))
    (hright : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin (2 * n)))
        (A B T A₀ B₀ E D : Finset (Fin (2 * n))),
        G.IsRegularOfDegree (n + 1) → IsAlmostBipartiteCut G A B →
        T ⊆ A → T.card = A.card - n → A₀ = A \ T → B₀ = B ∪ T →
        IsCut A₀ B₀ → A₀.card = n → B₀.card = n →
        IsMinimumVertexCoverOn G A E →
        IsMinimumVertexCoverOn G B₀ D →
        A.card - n ≤ Nat.sqrt n →
        n + 1 ≤ sqrtCoverThreshold K n * (D.card + 1) →
        ((1 / 2 : ℝ) - delta) * (2 : ℝ) ^ (2 * n) ≤
          (almostBipartiteCount
            (Finset.univ : Finset (Fin (2 * n)))
            (fun S ↦ IsKGoodSample G A B S 0) : ℝ))
    (htwo : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin (2 * n)))
        (A B T A₀ B₀ C D : Finset (Fin (2 * n))),
        G.IsRegularOfDegree (n + 1) → IsAlmostBipartiteCut G A B →
        T ⊆ A → T.card = A.card - n → A₀ = A \ T → B₀ = B ∪ T →
        IsCut A₀ B₀ → A₀.card = n → B₀.card = n →
        IsMinimumVertexCoverOn G A₀ C →
        IsMinimumVertexCoverOn G B₀ D →
        A.card - n ≤ Nat.sqrt n →
        sqrtCoverThreshold K n ≤ C.card →
        sqrtCoverThreshold K n ≤ D.card →
        ((1 / 2 : ℝ) - delta) * (2 : ℝ) ^ (2 * n) ≤
          (almostBipartiteCount
            (Finset.univ : Finset (Fin (2 * n)))
            (fun S ↦ IsKGoodSample G A B S 0) : ℝ)) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin (2 * n))) [G.LocallyFinite],
        G.IsRegularOfDegree (n + 1) → AlmostBipartiteRegime n G →
          ∃ A B : Finset (Fin (2 * n)),
            IsAlmostBipartiteCut G A B ∧
            ((1 / 2 : ℝ) - delta) * (2 : ℝ) ^ (2 * n) ≤
              (almostBipartiteCount
                (Finset.univ : Finset (Fin (2 * n)))
                (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
  have hlarge :=
    AlmostBipartiteRegimeCounts.eventually_largeImbalance_goodSample_count
      hdelta
  filter_upwards [hlarge, hleft, hright, htwo] with
      n hnLarge hnLeft hnRight hnTwo
  intro G hloc hreg hab
  let canonical : G.LocallyFinite := fun v =>
    @Subtype.fintype _ (G.neighborSet v) (Classical.decPred _) inferInstance
  have hreg' : @SimpleGraph.IsRegularOfDegree _ G canonical (n + 1) :=
    isRegularOfDegree_of_locallyFinite_instances hloc canonical hreg
  obtain ⟨A, B, hAB, hcase⟩ :=
    almostBipartite_cover_regime_with_transfer n (Nat.sqrt n)
      (sqrtCoverThreshold K n) G hreg' hab
  refine ⟨A, B, hAB, ?_⟩
  rcases hcase with hlargeImbalance | hbalanced
  · obtain ⟨E, hE⟩ := exists_minimumVertexCoverOn G A
    exact hnLarge G A B E hreg' hAB hE hlargeImbalance
  · rcases hbalanced with ⟨hsmall, T, A₀, B₀, C, D, hTA, hTcard,
      hA₀, hB₀, hcut₀, hA₀card, hB₀card, hC, hD, hcovers⟩
    rcases hcovers with hboth | hproduct
    · exact hnTwo G A B T A₀ B₀ C D hreg' hAB hTA hTcard hA₀ hB₀
        hcut₀ hA₀card hB₀card hC hD hsmall hboth.1 hboth.2
    · rcases hproduct with hrightProduct | hleftProduct
      · obtain ⟨E, hE⟩ := exists_minimumVertexCoverOn G A
        exact hnRight G A B T A₀ B₀ E D hreg' hAB hTA hTcard hA₀ hB₀
          hcut₀ hA₀card hB₀card hE hD hsmall hrightProduct.2
      · exact hnLeft G A B T A₀ C hAB.1
          (by exact_mod_cast hAB.2.1) hsmall hA₀ hC hleftProduct.2

/-- All cover regimes except the two-large arm, which is the final
probabilistic input to the unconditional almost-bipartite count. -/
theorem eventually_goodSample_count_of_twoLarge_endpoint
    (htwo : ∀ delta : ℝ, 0 < delta → ∀ K : ℕ, 16 ≤ K →
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (G : SimpleGraph (Fin (2 * n)))
          (A B T A₀ B₀ C D : Finset (Fin (2 * n))),
          G.IsRegularOfDegree (n + 1) → IsAlmostBipartiteCut G A B →
          T ⊆ A → T.card = A.card - n → A₀ = A \ T → B₀ = B ∪ T →
          IsCut A₀ B₀ → A₀.card = n → B₀.card = n →
          IsMinimumVertexCoverOn G A₀ C →
          IsMinimumVertexCoverOn G B₀ D →
          A.card - n ≤ Nat.sqrt n →
          sqrtCoverThreshold K n ≤ C.card →
          sqrtCoverThreshold K n ≤ D.card →
          ((1 / 2 : ℝ) - delta) * (2 : ℝ) ^ (2 * n) ≤
            (almostBipartiteCount
              (Finset.univ : Finset (Fin (2 * n)))
              (fun S ↦ IsKGoodSample G A B S 0) : ℝ)) :
    ∀ delta : ℝ, 0 < delta →
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (G : SimpleGraph (Fin (2 * n))) [G.LocallyFinite],
          G.IsRegularOfDegree (n + 1) → AlmostBipartiteRegime n G →
            ∃ A B : Finset (Fin (2 * n)),
              IsAlmostBipartiteCut G A B ∧
              ((1 / 2 : ℝ) - delta) * (2 : ℝ) ^ (2 * n) ≤
                (almostBipartiteCount
                  (Finset.univ : Finset (Fin (2 * n)))
                  (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
  intro delta hdelta
  obtain ⟨K, hK, hright, hleft⟩ :=
    exists_common_scale_eventually_sqrtImbalance_oneSmallCover_counts hdelta
  have hright' : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin (2 * n)))
        (A B T A₀ B₀ E D : Finset (Fin (2 * n))),
        G.IsRegularOfDegree (n + 1) → IsAlmostBipartiteCut G A B →
        T ⊆ A → T.card = A.card - n → A₀ = A \ T → B₀ = B ∪ T →
        IsCut A₀ B₀ → A₀.card = n → B₀.card = n →
        IsMinimumVertexCoverOn G A E →
        IsMinimumVertexCoverOn G B₀ D →
        A.card - n ≤ Nat.sqrt n →
        n + 1 ≤ sqrtCoverThreshold K n * (D.card + 1) →
        ((1 / 2 : ℝ) - delta) * (2 : ℝ) ^ (2 * n) ≤
          (almostBipartiteCount
            (Finset.univ : Finset (Fin (2 * n)))
            (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
    filter_upwards [hright] with n hn
    intro G A B T A₀ B₀ E D hreg hAB hTA hTcard _hA₀ hB₀
      _hcut₀ _hA₀card _hB₀card hE hD hsmall hprod
    have hBT : Disjoint B T := hAB.1.1.symm.mono_right hTA
    exact hn G A B E T B₀ D hreg hAB hE hsmall hTcard hBT hB₀ hD hprod
  exact eventually_goodSample_count_of_cover_endpoints hdelta hleft hright'
    (htwo delta hdelta K hK)

/-- Uniform half-density of numerically good samples for every regular graph
in the tailored almost-bipartite regime. -/
theorem eventually_goodSample_count :
    ∀ delta : ℝ, 0 < delta →
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (G : SimpleGraph (Fin (2 * n))) [G.LocallyFinite],
          G.IsRegularOfDegree (n + 1) → AlmostBipartiteRegime n G →
            ∃ A B : Finset (Fin (2 * n)),
              IsAlmostBipartiteCut G A B ∧
              ((1 / 2 : ℝ) - delta) * (2 : ℝ) ^ (2 * n) ≤
                (almostBipartiteCount
                  (Finset.univ : Finset (Fin (2 * n)))
                  (fun S ↦ IsKGoodSample G A B S 0) : ℝ) :=
  eventually_goodSample_count_of_twoLarge_endpoint
    TwoLargeCase.eventually_twoLargeCover_goodSample_count

/-- The unconditional almost-bipartite case bound used by the final
trichotomy assembly for Erdős Problem 622. -/
theorem uniformCaseDensityBound_almostBipartite :
    UniformCaseDensityBound AlmostBipartiteRegime :=
  uniformCaseDensityBound_almostBipartite_of_goodSample_count
    eventually_goodSample_count

end Erdos622.AlmostBipartiteCase
