import Wikipedia.HopfProblem.DegreeCollapseIntegralCoherentSupportRestriction
import Wikipedia.HopfProblem.DegreeCollapseIntegralPrimitiveCap

/-!
# Primitive integral support families restrict to actual open subsets

The original local excision map intertwines the two point evaluations.
Consequently a primitive ambient evaluation remains primitive in the
open subset. The constructed manifold fundamental family satisfies
this property without a supplied orientation or generator.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCoherentSupport

open NoExoticSixSphere SupportedRelativeHomology
open IntegralCompactSupportCohomology (imageCompact)

variable (X : Type) [TopologicalSpace X] (d : ℕ)

/-- Every original local evaluation of every compact-support class generates its integer group. -/
def Primitive (c : ClassFamily X d) : Prop :=
  ∀ K : Compacts X, IntegralPrimitiveCap.IsPrimitiveOn (K : Set X) d (c K)

variable {X d} [T2Space X] (U : Set X) (hU : IsOpen U) (c : ClassFamily X d)

/-- Inverse original excision retains all primitive point evaluations. -/
theorem restrictToOpen_primitive (hp : Primitive X d c) :
    Primitive U d (restrictToOpen U hU c) := by
  intro K x hx a
  let e : Homology (ModuleCat.of ℤ ℤ) {x} d ≃ₗ[ℤ]
      Homology (ModuleCat.of ℤ ℤ) {(x : X)} d :=
    RelativeSingularHomology.neighborhoodEquiv U hU x d
  have hlocal := (LinearMap.congr_fun
    (IntegralOpenSupport.evaluate_inclusion U (K : Set U) x hx d)
    (restrictToOpen U hU c K)).symm.trans
      (congrArg (evaluate (ModuleCat.of ℤ ℤ) (imageCompact U K : Set X)
        (x : X) ⟨x, hx, rfl⟩ d) (restrictToOpen_inclusion U hU c K))
  obtain ⟨k, hk⟩ := hp (imageCompact U K) (x : X) ⟨x, hx, rfl⟩ (e a)
  refine ⟨k, e.injective ?_⟩
  exact (map_zsmul e k (evaluate (ModuleCat.of ℤ ℤ) (K : Set U) x hx d
    (restrictToOpen U hU c K))).trans ((congrArg (fun z => k • z) hlocal).trans hk)

section Manifold

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M]

/-- The actual constructed manifold family has primitive localizations on every compact support. -/
theorem manifoldFamily_primitive : Primitive M (n + 3) (manifoldFamily (E := E) n (M := M)) :=
  fun K x hx a => IntegralManifoldFundamentalClass.supportedClass_evaluate_generates
    (E := E) n M (K : Set M) x hx a

end Manifold

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCoherentSupport
