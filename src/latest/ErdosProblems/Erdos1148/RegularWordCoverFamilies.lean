import ErdosProblems.Erdos1148.CoherentRegularWordCount

/-! # Nested large-mass word families from two coherent covers -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

theorem regular_word_families_of_covers {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : FiniteMeasurablePartition ModularOrbitSpace ι)
    (μ : Measure ModularOrbitSpace) [IsProbabilityMeasure μ]
    (hf : MeasurePreserving modularTimeOne μ μ)
    (C : ι → Set ModularOrbitSpace) (hCsub : ∀ i, C i ⊆ P.atom i)
    {η ε τ β : ℝ} {n Ng Na : ℕ} (hn : 0 < n) (hτ : 0 < τ)
    (hQ : MeasurableSet (⋃ i, C i)ᶜ) (hQmass : μ.real (⋃ i, C i)ᶜ / τ ≤ β)
    (hstable : ∀ i, ∀ x ∈ C i, ∀ u : SL(2, ℝ),
      EntryCloseOne η u → modularRightTranslate u x ∈ P.atom i)
    (hwords : ∀ (v : Fin n → ι) (F : Finset (Fin n → ι)),
      (∀ w ∈ F, (wordMismatchCount v w : ℝ) ≤ τ * n) →
      (F.card : ℝ) ≤ Real.exp (ε * n))
    (Bg : Fin Ng → Set SL(2, ℝ)) (Ba : Fin Na → Set SL(2, ℝ))
    (hBg : ∀ i, LiftForwardClose η n (Bg i)) (hBa : ∀ i, LiftForwardClose η n (Ba i))
    (hgmass : (3 / 4 : ℝ) ≤ μ.real (⋃ i, modularMk '' Bg i))
    (hamass : 1 - β ≤ μ.real (⋃ i, modularMk '' Ba i)) :
    ∃ G H : Finset (Fin n → ι), G ⊆ H ∧
      (G.card : ℝ) ≤ Ng * Real.exp (ε * n) ∧
      (H.card : ℝ) ≤ ((Ng : ℝ) + Na) * Real.exp (ε * n) ∧
      3 / 4 - β ≤ ∑ w ∈ G, μ.real (P.orbitAtom modularTimeOne n w) ∧
      1 - 2 * β ≤ ∑ w ∈ H, μ.real (P.orbitAtom modularTimeOne n w) := by
  classical
  let G := regularOrbitWords P modularTimeOne (⋃ i, C i)ᶜ τ n (⋃ i, modularMk '' Bg i)
  let J := regularOrbitWords P modularTimeOne (⋃ i, C i)ᶜ τ n (⋃ i, modularMk '' Ba i)
  have hGcard := regularOrbitWords_card_le_coherent_cover P C hCsub hstable hwords Bg hBg (le_refl _)
  have hJcard := regularOrbitWords_card_le_coherent_cover P C hCsub hstable hwords Ba hBa (le_refl _)
  have hGmass := regularOrbitWords_mass_lower P μ hf hQ hτ hn (⋃ i, modularMk '' Bg i)
  have hJmass := regularOrbitWords_mass_lower P μ hf hQ hτ hn (⋃ i, modularMk '' Ba i)
  refine ⟨G, G ∪ J, Finset.subset_union_left, hGcard, ?_, ?_, ?_⟩
  · have hcard : ((G ∪ J).card : ℝ) ≤ (G.card : ℝ) + J.card := by
      exact_mod_cast Finset.card_union_le G J
    dsimp only [G, J] at hcard ⊢
    nlinarith only [hcard, hGcard, hJcard]
  · dsimp only [G]
    linarith only [hgmass, hGmass, hQmass]
  · have hsub : (∑ w ∈ J, μ.real (P.orbitAtom modularTimeOne n w)) ≤
        ∑ w ∈ G ∪ J, μ.real (P.orbitAtom modularTimeOne n w) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
        (fun _ _ _ => measureReal_nonneg)
    dsimp only [J] at hsub
    linarith only [hamass, hJmass, hQmass, hsub]

end Erdos1148.DukeArithmetic
