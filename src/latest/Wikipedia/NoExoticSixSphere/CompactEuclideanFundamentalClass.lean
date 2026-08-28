import Wikipedia.NoExoticSixSphere.FiniteConvexSupportNeighborhood

/-!
# Existence of a fundamental class on every compact Euclidean support

Take a finite-convex support neighborhood and restrict its constructed
fundamental class using the original identity map of pairs. This proves
existence on the original compact set, without yet asserting detection or
vanishing on arbitrary compact supports.
-/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

/-- Every compact Euclidean subset admits an actual relative fundamental class over `ZMod 2`. -/
theorem compactEuclidean_exists_fundamentalClass (K : Set E) (hK : IsCompact K) :
    ∃ c : Homology (ModuleCat.of ℤ (ZMod 2)) K (n + 3), IsFundamentalOn (E := E) n K c := by
  obtain ⟨L, hL, hKL, _⟩ := exists_finiteConvex_support_neighborhood n K Set.univ
    hK isOpen_univ (Set.subset_univ K)
  obtain ⟨c, hc⟩ := hL.fundamental
  have h : K ⊆ L := hKL.trans interior_subset
  exact ⟨restrict (ModuleCat.of ℤ (ZMod 2)) h (n + 3) c, hc.restrict n h⟩

end NoExoticSixSphere.SupportedRelativeHomology
