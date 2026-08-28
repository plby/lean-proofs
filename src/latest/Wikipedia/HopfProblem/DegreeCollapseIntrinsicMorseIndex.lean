import Wikipedia.HopfProblem.DegreeCollapseMorseIndexInvariance

/-!
# A chart-independent native Morse index

At a point admitting a signed Morse chart the index is its negative
dimension, independent of the chosen chart. The definition is assigned
zero when no such chart exists; the Morse-function applications always
supply actual charts. Complete function germs preserve this index.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p : M}

open Classical in
def nativeMorseIndex (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (p : M) : ℕ :=
  if h : Nonempty (SignedMorseChart (E := E) f p) then
    Module.finrank ℝ (Classical.choice h).NegativeCoordinates else 0

open Classical in
theorem nativeMorseIndex_eq_chart (c : SignedMorseChart (E := E) f p) :
    nativeMorseIndex E f p = Module.finrank ℝ c.NegativeCoordinates := by
  unfold nativeMorseIndex
  rw [dif_pos ⟨c⟩]
  exact signed_morse_chart_negative_finrank_eq _ c

theorem nativeMorseIndex_congr_germ (hgerm : g =ᶠ[𝓝 p] f) :
    nativeMorseIndex E g p = nativeMorseIndex E f p := by
  classical
  by_cases h : Nonempty (SignedMorseChart (E := E) f p)
  · obtain ⟨c⟩ := h
    obtain ⟨d, -, -, -, -⟩ := exists_signed_morse_chart_of_germ c hgerm
    rw [nativeMorseIndex_eq_chart c, nativeMorseIndex_eq_chart d]
    exact (signed_morse_chart_negative_finrank_eq_of_germ c d hgerm).symm
  · have hg : ¬ Nonempty (SignedMorseChart (E := E) g p) := by
      rintro ⟨d⟩
      obtain ⟨c, -, -, -, -⟩ := exists_signed_morse_chart_of_germ d hgerm.symm
      exact h ⟨c⟩
    simp only [nativeMorseIndex, dif_neg h, dif_neg hg]

theorem nativeMorseIndex_le : nativeMorseIndex E f p ≤ Module.finrank ℝ E := by
  classical
  by_cases h : Nonempty (SignedMorseChart (E := E) f p)
  · obtain ⟨c⟩ := h
    rw [nativeMorseIndex_eq_chart c]
    have hc := c.finrank_negative_add_positive
    omega
  · simp only [nativeMorseIndex, dif_neg h, Nat.zero_le]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
