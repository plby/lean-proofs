import Arxiv.Arxiv2411_18291.LegalEmbeddingCount
import Arxiv.Arxiv2411_18291.TargetEmbeddingCount
import Mathlib.Probability.Distributions.Uniform

/-!
# One-step probabilities for uniform legal extensions

These are genuine probability measures on the finite set of extensions.
The target-edge bound follows by dividing its factorial count by the
proved lower bound on the number of available choices.
-/

open MeasureTheory Finset
open scoped ENNReal

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r : ℕ}

/-- Uniformly choose one of the legal extensions of the given root map. -/
def uniformLegalExtension (φ : F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (hs : (legalExtensions φ H B).Nonempty) :
    PMF (EmbeddingExtension φ) := PMF.uniformOfFinset (legalExtensions φ H B) hs

omit [DecidableEq V] in
theorem uniformExtensions_target_probability_le_scaled (φ : F ↪ V)
    [MeasurableSpace (EmbeddingExtension φ)] [MeasurableSingletonClass (EmbeddingExtension φ)]
    (s : Finset (EmbeddingExtension φ)) (hs : s.Nonempty) {η : ℝ} (hη : 0 < η)
    (hcount : (η / 2) * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) ≤ s.card)
    (hn : 0 < Fintype.card V) (e : Block W r) (g : Block V r) :
    (PMF.uniformOfFinset s hs).toMeasure.real {f | mapBlock f.val e = g} ≤
      (2 * (e.val \ F).card.factorial / (Fintype.card V : ℝ) ^ (e.val \ F).card) / η := by
  classical
  have hmeas : MeasurableSet {f : EmbeddingExtension φ | mapBlock f.val e = g} :=
    (Set.toFinite _).measurableSet
  rw [measureReal_def, PMF.toMeasure_uniformOfFinset_apply hs _ hmeas,
    ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  simp only [Set.mem_ofPred_eq]
  have hc : (s.filter fun f => mapBlock f.val e = g).card ≤
      (edgeTargetExtensions φ e g).card := by
    apply card_le_card
    intro f hf
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hf).2⟩
  have hbound : ((s.filter fun f => mapBlock f.val e = g).card : ℝ) ≤
      (e.val \ F).card.factorial *
        (Fintype.card V : ℝ) ^ (Fintype.card W - F.card - (e.val \ F).card) := by
    exact_mod_cast hc.trans (edgeTargetExtensions_card_le φ e g)
  have hV : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hsmall : (e.val \ F).card ≤ Fintype.card W - F.card := by
    have hc := card_sdiff_add_card e.val F
    have hu := card_le_univ (e.val ∪ F)
    omega
  calc
    _ ≤ ((e.val \ F).card.factorial *
        (Fintype.card V : ℝ) ^ (Fintype.card W - F.card - (e.val \ F).card)) /
        ((η / 2) * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card)) :=
      div_le_div₀ (by positivity) hbound (by positivity) hcount
    _ = _ := by
      rw [pow_sub₀ (Fintype.card V : ℝ) hV.ne' hsmall]
      field_simp [hV.ne', hη.ne']

omit [DecidableEq V] in
theorem uniformExtensions_target_probability_le (φ : F ↪ V)
    [MeasurableSpace (EmbeddingExtension φ)] [MeasurableSingletonClass (EmbeddingExtension φ)]
    (s : Finset (EmbeddingExtension φ)) (hs : s.Nonempty)
    (hcount : (1 / 2 : ℝ) * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) ≤ s.card)
    (hn : 0 < Fintype.card V) (e : Block W r) (g : Block V r) :
    (PMF.uniformOfFinset s hs).toMeasure.real {f | mapBlock f.val e = g} ≤
      2 * (e.val \ F).card.factorial / (Fintype.card V : ℝ) ^ (e.val \ F).card := by
  simpa only [div_one] using uniformExtensions_target_probability_le_scaled φ s hs
    (η := 1) (by norm_num) hcount hn e g

theorem uniformLegalExtension_target_probability_le (φ : F ↪ V)
    [MeasurableSpace (EmbeddingExtension φ)] [MeasurableSingletonClass (EmbeddingExtension φ)]
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1))
    (hs : (legalExtensions φ H B).Nonempty) {θ : ℝ}
    (hB : IsGraphBounded B θ) (hθ : 0 ≤ θ)
    (hn : 4 * (Fintype.card W) ^ 2 ≤ Fintype.card V) (hsmall : H.card * θ ≤ 1 / 4)
    (hnpos : 0 < Fintype.card V) (e : Block W (r + 1)) (g : Block V (r + 1)) :
    (uniformLegalExtension φ H B hs).toMeasure.real {f | mapBlock f.val e = g} ≤
      2 * (e.val \ F).card.factorial / (Fintype.card V : ℝ) ^ (e.val \ F).card :=
  uniformExtensions_target_probability_le φ _ hs
    (legalExtensions_card_half φ H B hB hθ hn hsmall) hnpos e g

end Arxiv2411_18291
