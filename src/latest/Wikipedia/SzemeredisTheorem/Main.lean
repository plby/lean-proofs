/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Wikipedia.SzemeredisTheorem.Hypergraph.SourceFullBundleRemovalAssembly
import Wikipedia.SzemeredisTheorem.Szemeredi.OrderedRemoval

/-!
# Szemerédi's theorem

This file assembles the hypergraph-removal development into the quantitative
cyclic form of Szemerédi's theorem. For every progression length `k ≥ 2` and
positive density `δ`, there is a positive constant `c` such that every subset
of every nontrivial finite cyclic group having density at least `δ` contains
at least normalized mass `c` of `k`-term arithmetic progressions.
-/

namespace Wikipedia.SzemeredisTheorem

/-- **Szemerédi's theorem**, in uniform quantitative cyclic counting form. -/
theorem szemeredi (k : ℕ) (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ HasUniformDenseAPCount k δ c := by
  refine
    exists_uniformDenseAPCount_of_orderedRemoval_of_two_le
      k hk ?_ hδ
  have hrank : k - 1 = (k - 2) + 1 := by omega
  rw [hrank]
  exact hasUniformOrderedPatternRemoval_sourceFull
    k (k - 2) (by omega)

#print axioms szemeredi

end Wikipedia.SzemeredisTheorem
