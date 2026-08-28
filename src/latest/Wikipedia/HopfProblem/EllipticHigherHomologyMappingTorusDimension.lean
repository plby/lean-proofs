import Wikipedia.HopfProblem.MappingTorusHomology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroups

/-!
# Actual homology vanishing above dimension four

The genuine Wang sequence and the already proved homology of the actual
three-torus imply that every mapping torus of a three-torus homeomorphism
has zero integral singular homology above degree four.  No manifold
dimension theorem, Poincaré duality, or homology vanishing is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology

/-- Vanishing in dimensions above four follows from the actual Wang
sequence of any genuine three-torus mapping torus. -/
theorem threeTorusMappingTorus_homology_subsingleton
    (f : ProductTorus 3 ≃ₜ ProductTorus 3) {n : ℕ} (hn : 4 < n) :
    Subsingleton (SingularHomology (MappingTorus.Torus f) n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have := productTorus_homology_subsingleton_of_lt (show 3 < k + 1 by omega)
  have := productTorus_homology_subsingleton_of_lt (show 3 < k by omega)
  have hzero : ∀ a : SingularHomology (MappingTorus.Torus f) (k + 1), a = 0 := by
    intro a
    have ha : a ∈ LinearMap.ker (MappingTorusHomology.wangBoundary f k) := by
      change MappingTorusHomology.wangBoundary f k a = 0
      exact Subsingleton.elim _ _
    rw [← MappingTorusHomology.wang_exact_at_mappingTorus f k] at ha
    obtain ⟨x, hx⟩ := ha
    have hx0 : x = 0 := Subsingleton.elim _ _
    rw [hx0, map_zero] at hx
    exact hx.symm
  exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩

end Wikipedia.HopfProblem.Elliptic.HigherHomology
