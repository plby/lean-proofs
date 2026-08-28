import Wikipedia.NoExoticSixSphere.SupportedHomologyNeighborhoodLift
import Wikipedia.NoExoticSixSphere.FiniteConvexSupportNeighborhood

/-!
# Vanishing above dimension for arbitrary compact Euclidean supports

Lift each actual relative class to a sufficiently small finite-convex
support neighborhood. The proved vanishing on that neighborhood, followed
by the original restriction map, makes the original class zero as well.
-/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

/-- Native mod-two relative homology of any compact support vanishes above dimension. -/
theorem compactEuclidean_above_subsingleton (K : Set E) (hK : IsCompact K)
    (k : ℕ) (hk : n + 3 < k) : Subsingleton (Homology (ModuleCat.of ℤ (ZMod 2)) K k) := by
  have hz : ∀ a : Homology (ModuleCat.of ℤ (ZMod 2)) K k, a = 0 := by
    intro a
    obtain ⟨U, hU, hKU, hlift⟩ := exists_lift_neighborhood (ModuleCat.of ℤ (ZMod 2)) K k a
    obtain ⟨L, hL, hKL, hLU⟩ := exists_finiteConvex_support_neighborhood n K U hK hU hKU
    have h : K ⊆ L := hKL.trans interior_subset
    obtain ⟨b, hb⟩ := hlift L hLU h
    have hb0 : b = 0 := (hL.above k hk).elim b 0
    exact hb.symm.trans ((congrArg (restrict (ModuleCat.of ℤ (ZMod 2)) h k) hb0).trans
      (map_zero _))
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end NoExoticSixSphere.SupportedRelativeHomology
