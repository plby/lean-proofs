import Wikipedia.NoExoticSixSphere.JamesSphereFiberFiniteToFull
import Wikipedia.NoExoticSixSphere.JamesSphereFiniteQuotientHomotopy

/-!
# The original full James fiber-to-quotient comparison in the metastable range

The finite sphere-fiber comparison, finite-to-full fiber map, and
finite-to-full quotient map are all proved bijective in the required
degrees. Their square commutes on the original cube representatives.
Canceling the finite-to-full fiber map proves bijectivity of the
original full `FiberQuotient.hom`, without a comparison hypothesis.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.JamesSphere.FiniteFiberQuotient

theorem hom_toFull (n d : ℕ) [NeZero d]
    (c : π_ d (Fiber n (spherePole n)) (basepoint n (spherePole n))) :
    FiberQuotient.hom n d (toFullHom n d c) =
      HigherHomotopy.map (N := Fin (d + 1)) (FirstStageQuotient.stageMap n)
        (FirstStageQuotient.stageMap_basepoint n) (hom n (spherePole n) d c) := by
  refine Quotient.inductionOn c fun p ↦ ?_
  rfl

end NoExoticSixSphere.JamesSphere.FiniteFiberQuotient

namespace NoExoticSixSphere.JamesSphere.FiberQuotient

theorem hom_bijective_range (n d : ℕ) [NeZero d] (hn : 2 ≤ n) (hdn : d + 3 ≤ 3 * n) :
    Function.Bijective (hom n d) := by
  have hb := (FirstStageQuotient.stageMap_pi_bijective n (d + 1) hn (by omega) (by omega)).comp
    (FiniteFiberQuotient.hom_bijective n (spherePole n) d hn (by omega))
  have he : hom n d ∘ FiniteFiberQuotient.toFullHom n d =
      HigherHomotopy.map (N := Fin (d + 1)) (FirstStageQuotient.stageMap n)
        (FirstStageQuotient.stageMap_basepoint n) ∘
          FiniteFiberQuotient.hom n (spherePole n) d :=
    funext (FiniteFiberQuotient.hom_toFull n d)
  rw [← he] at hb
  exact (Function.Bijective.of_comp_iff _
    (FiniteFiberQuotient.toFullHom_bijective n d hn (by omega))).mp hb

end NoExoticSixSphere.JamesSphere.FiberQuotient
