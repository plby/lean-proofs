import Wikipedia.HopfProblem.DegreeCollapseIndexedMorseCancellation
import Wikipedia.SmoothSixDPoincare.MorseNegation

/-!
# Native Morse negation and complementary intrinsic indices

Negating the original function preserves its Morse condition and critical
set. The actual signed chart reverses every sign, so the intrinsic index
is complemented in the original dimension. Exact indexed counts therefore
reflect across that dimension, preparing the dual cancellation argument.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}

theorem isMorseAt_neg (hm : IsMorseAt E f p) : IsMorseAt E (fun x => -f x) p := by
  obtain ⟨e, he, hp, hregular | hH⟩ := hm
  · refine ⟨e, he, hp, Or.inl ?_⟩
    change fderiv ℝ (fun x => -f (e.symm x)) (e p) ≠ 0
    rw [fderiv_fun_neg, neg_ne_zero]
    exact hregular
  · refine ⟨e, he, hp, Or.inr ?_⟩
    have hd : fderiv ℝ ((fun x => -f x) ∘ e.symm) =
        fun z => -fderiv ℝ (f ∘ e.symm) z := by
      funext z
      exact fderiv_fun_neg
    rw [hd, fderiv_fun_neg]
    change Bijective (fun v => -(fderiv ℝ (fderiv ℝ (f ∘ e.symm)) (e p) v))
    exact neg_bijective.comp hH

theorem isMorse_neg (hm : IsMorse E f) : IsMorse E (fun x => -f x) :=
  fun x => isMorseAt_neg (hm x)

open Classical in
theorem negative_finrank_neg_chart (c : SignedMorseChart (E := E) f p) :
    Module.finrank ℝ c.neg.NegativeCoordinates = Module.finrank ℝ c.PositiveCoordinates := by
  simp only [SignedMorseChart.NegativeCoordinates, SignedMorseChart.PositiveCoordinates,
    MorseHandle.NegativeSpace, MorseHandle.PositiveSpace, finrank_euclideanSpace]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro i
  change -c.weights i = -1 ↔ c.weights i ≠ -1
  rcases c.signs i with h | h <;> norm_num [h]

theorem nativeMorseIndex_neg_add (c : SignedMorseChart (E := E) f p) :
    nativeMorseIndex E (fun x => -f x) p + nativeMorseIndex E f p = Module.finrank ℝ E := by
  rw [nativeMorseIndex_eq_chart c.neg, nativeMorseIndex_eq_chart c, negative_finrank_neg_chart]
  exact (Nat.add_comm _ _).trans c.finrank_negative_add_positive

variable [FiniteDimensional ℝ E]

theorem nativeMorseCount_neg
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {k : ℕ} (hk : k ≤ Module.finrank ℝ E) :
    nativeMorseCount E (fun x => -f x) (Module.finrank ℝ E - k) = nativeMorseCount E f k := by
  unfold nativeMorseCount
  congr 1
  ext z
  rw [criticalPoints_neg]
  change (z ∈ criticalPoints E f ∧ nativeMorseIndex E (fun x => -f x) z =
    Module.finrank ℝ E - k) ↔ (z ∈ criticalPoints E f ∧ nativeMorseIndex E f z = k)
  constructor
  · rintro ⟨hz, hi⟩
    obtain ⟨c⟩ := nonempty_signedMorseChart hf hm z hz
    have hsum := nativeMorseIndex_neg_add c
    exact ⟨hz, by omega⟩
  · rintro ⟨hz, hi⟩
    obtain ⟨c⟩ := nonempty_signedMorseChart hf hm z hz
    have hsum := nativeMorseIndex_neg_add c
    exact ⟨hz, by omega⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
