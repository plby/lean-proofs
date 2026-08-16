import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedSimplexBridge

/-!
# Dense Szemerédi consequences of ordered hypergraph removal

The equal-vertex bridge turns ordered rank-`r + 1` removal on `r + 2`
classes into cyclic partite simplex removal.  The standard arithmetic-
progression hypergraph construction then gives uniform dense and weighted
Szemerédi bounds.
-/

namespace Wikipedia.SzemeredisTheorem

/-- Ordered rank-`r + 1` removal on `r + 2` equal classes gives a positive
uniform lower bound for dense cyclic `(r + 2)`-term progression counts. -/
theorem exists_uniformDenseAPCount_of_orderedRemoval
    (r : ℕ)
    (hordered :
      HasUniformOrderedPatternRemoval (r + 2) (r + 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformDenseAPCount (r + 2) δ c :=
  exists_uniformDenseAPCount_of_simplexRemoval r
    (hasUniformCyclicPartiteSimplexRemoval_add_two_of_ordered
      r hordered)
    hδ

/-- The same ordered-removal hypothesis gives the corresponding uniform
weighted cyclic Szemerédi bound. -/
theorem exists_uniformWeightedAPCount_of_orderedRemoval
    (r : ℕ)
    (hordered :
      HasUniformOrderedPatternRemoval (r + 2) (r + 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformWeightedAPCount (r + 2) δ c :=
  exists_uniformWeightedAPCount_of_simplexRemoval r
    (hasUniformCyclicPartiteSimplexRemoval_add_two_of_ordered
      r hordered)
    hδ

/-- A length-indexed formulation of the dense consequence. -/
theorem exists_uniformDenseAPCount_of_orderedRemoval_of_two_le
    (k : ℕ) (hk : 2 ≤ k)
    (hordered :
      HasUniformOrderedPatternRemoval k (k - 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformDenseAPCount k δ c := by
  have hcolors : k - 2 + 2 = k := by
    omega
  have hrank : k - 2 + 1 = k - 1 := by
    omega
  have hordered' :
      HasUniformOrderedPatternRemoval
        (k - 2 + 2) (k - 2 + 1) := by
    simpa only [hcolors, hrank] using hordered
  simpa only [hcolors] using
    (exists_uniformDenseAPCount_of_orderedRemoval
      (k - 2) hordered' hδ)

/-- A length-indexed formulation of the weighted consequence. -/
theorem exists_uniformWeightedAPCount_of_orderedRemoval_of_two_le
    (k : ℕ) (hk : 2 ≤ k)
    (hordered :
      HasUniformOrderedPatternRemoval k (k - 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformWeightedAPCount k δ c := by
  have hcolors : k - 2 + 2 = k := by
    omega
  have hrank : k - 2 + 1 = k - 1 := by
    omega
  have hordered' :
      HasUniformOrderedPatternRemoval
        (k - 2 + 2) (k - 2 + 1) := by
    simpa only [hcolors, hrank] using hordered
  simpa only [hcolors] using
    (exists_uniformWeightedAPCount_of_orderedRemoval
      (k - 2) hordered' hδ)

end Wikipedia.SzemeredisTheorem
