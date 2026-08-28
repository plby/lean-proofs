import Wikipedia.NoExoticSixSphere.SupportedModTwoCohomology
import Wikipedia.NoExoticSixSphere.CompactSupportedFundamentalClass
import Wikipedia.NoExoticSixSphere.ManifoldCapMap

/-!
# Compatible caps with compact-supported fundamental classes

Each map caps with the actual fundamental class on its compact support.
Original pair-map naturality and proved uniqueness of fundamental classes
give compatibility as the support grows. On compact manifolds the map is
the original absolute cap after forgetting the cohomology support.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.CompactSupportedCapMap

open SupportedModTwoCohomology

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]

/-- Cap with the constructed class on this actual compact support. -/
def dualityMap (K : Set M) (hK : IsCompact K) (p q : ℕ) (h : p + q = n + 3) :
    Cohomology K p →ₗ[ℤ] ModHomology 2 M q :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    { toFun := fun a => RelativeModTwoCap.capProductInDegree Kᶜ h a
        (CompactSupportedFundamentalClass.fundamentalClass (E := E) n K hK)
      map_zero' := congrArg
        (fun f => f (CompactSupportedFundamentalClass.fundamentalClass (E := E) n K hK))
        (RelativeModTwoCap.capProductInDegree Kᶜ h).map_zero
      map_add' a b := congrArg
        (fun f => f (CompactSupportedFundamentalClass.fundamentalClass (E := E) n K hK))
        ((RelativeModTwoCap.capProductInDegree Kᶜ h).map_add a b) }

theorem dualityMap_apply (K : Set M) (hK : IsCompact K) (p q : ℕ) (h : p + q = n + 3)
    (a : Cohomology K p) :
    dualityMap (E := E) n K hK p q h a = RelativeModTwoCap.capProductInDegree Kᶜ h a
      (CompactSupportedFundamentalClass.fundamentalClass (E := E) n K hK) := rfl

/-- Extending the cohomology support does not change the actual capped class. -/
theorem dualityMap_extend {K L : Set M} (hKL : K ⊆ L) (hK : IsCompact K) (hL : IsCompact L)
    (p q : ℕ) (h : p + q = n + 3) (a : Cohomology K p) :
    dualityMap (E := E) n L hL p q h (extend hKL p a) =
      dualityMap (E := E) n K hK p q h a := by
  have he := RelativeModTwoCap.capProductInDegree_naturality (ContinuousMap.id M)
    (show Set.MapsTo (ContinuousMap.id M) Lᶜ Kᶜ from fun _ hx hy => hx (hKL hy)) h a
    (CompactSupportedFundamentalClass.fundamentalClass (E := E) n L hL)
  rw [modHomologyMap_id, LinearMap.id_apply] at he
  change RelativeModTwoCap.capProductInDegree Lᶜ h (extend hKL p a) _ =
    RelativeModTwoCap.capProductInDegree Kᶜ h a
      (SupportedRelativeHomology.restrict (ModuleCat.of ℤ (ZMod 2)) hKL (n + 3) _) at he
  rw [CompactSupportedFundamentalClass.restrict_fundamentalClass] at he
  exact he

/-- On a compact manifold this is the original cap map after forgetting support. -/
theorem dualityMap_eq_absolute [CompactSpace M] (K : Set M) (hK : IsCompact K)
    (p q : ℕ) (h : p + q = n + 3) (a : Cohomology K p) :
    dualityMap (E := E) n K hK p q h a =
      ManifoldCapMap.dualityMap (E := E) n M p q h
        (RelativeModTwoCochains.toAbsoluteCohomology Kᶜ p a) := by
  rw [dualityMap_apply, ← CompactSupportedFundamentalClass.fromAbsolute_fundamentalClass]
  exact RelativeModTwoCap.capProductInDegree_projection Kᶜ h a
    (ManifoldFundamentalClass.fundamentalClass (E := E) n M)

end NoExoticSixSphere.CompactSupportedCapMap
