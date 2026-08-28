import Wikipedia.SmoothSixDPoincare.ManifoldMorseExtension
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# A constructed global Morse function on a compact smooth manifold

Choose compact neighborhoods inside the unit plateaus of genuine smooth
chart bumps. Compactness gives a finite cover. Starting from the zero
function, extend the Morse region across that cover, preserving the earlier
compact union at each step. The parameter choices use the proved Sard and
compact-stability lemmas, not an assumed global genericity theorem.
-/

noncomputable section

open Set MeasureTheory MeasureTheory.Measure Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

section Haar

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]

include μ in
/-- Finite chart induction constructs a genuine globally smooth Morse function. -/
theorem exists_morse_function_of_haar :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f := by
  classical
  choose φ U L hU hUs hφ hL hn hLU using exists_compact_plateau (E := E) (M := M)
  obtain ⟨s, hs⟩ := finite_cover_nhds hn
  have hfinite : ∀ t : Finset M, ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorseOn E f (⋃ p ∈ t, L p) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      refine ⟨fun _ => 0, contMDiff_const, ?_⟩
      intro x hx
      simp at hx
    | @insert p t hp ih =>
      obtain ⟨f, hf, hm⟩ := ih
      have hK : IsCompact (⋃ q ∈ t, L q) := t.isCompact_biUnion (fun q _ => hL q)
      obtain ⟨a, -, hfa, hma⟩ := exists_morse_extension μ (φ p)
        (hU p) (hUs p) (hφ p) (hL p) (hLU p) hf hK hm (ε := 1) zero_lt_one
      refine ⟨ManifoldPerturbation.perturb (φ p) f a, hfa, ?_⟩
      have heq : (⋃ q ∈ insert p t, L q) = L p ∪ ⋃ q ∈ t, L q := by
        ext x
        simp only [mem_iUnion, Finset.mem_insert, mem_union]
        constructor
        · rintro ⟨q, hq | hq, hx⟩
          · subst q
            exact Or.inl hx
          · exact Or.inr ⟨q, hq, hx⟩
        · rintro (hx | ⟨q, hq, hx⟩)
          · exact ⟨p, Or.inl rfl, hx⟩
          · exact ⟨q, Or.inr hq, hx⟩
      rw [heq]
      exact hma
  obtain ⟨f, hf, hm⟩ := hfinite s
  refine ⟨f, hf, fun x => hm x ?_⟩
  rw [hs]
  exact mem_univ x

end Haar

variable (E M) in
/-- A compact smooth manifold in any finite-dimensional real normed model has a Morse function. -/
theorem exists_morse_function :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  exact exists_morse_function_of_haar (E := E) (M := M) Measure.addHaar

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
